-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
function Defense.detectHttpSpy(raw)
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if type(cur) == "function" and iscc then
			local ok, isc = pcall(iscc, cur)
			if ok and isc == false then return true, n .. " is hooked" end
		end
		-- if we captured the original and the global no longer matches it -> swapped
		if raw and raw.http and rawget(realG, n) and rawget(realG, n) ~= raw.http and n == "request" then
			-- only a soft signal (executors legitimately wrap request); skip hard flag
		end
	end
	return false
end

-- 2) namecall hook: get the real __namecall fn via an errored game:IsA() ------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end
Defense._baseNC, Defense._baseCaller = actualNamecall()

function Defense.detectNamecallHook()
	local nc = actualNamecall()
	if Defense._baseNC and nc and nc ~= Defense._baseNC then
		return true, "__namecall identity changed (metatable hook)"
	end
	return false
end

-- 3) remote spy: fire a THROWAWAY remote; a spy's arg-clone causes a gc spike --
function Defense.detectRemoteSpy()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	if ok and type(spike) == "number" and spike > 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- substring patterns (tools sometimes suffix/version their GUI names)
local SPY_GUI = { "dex", "remotespy", "remote spy", "simplespy", "hydroxide", "spygui", "infiniteyield" }
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				local nm = string.lower(c.Name)
				for _, pat in ipairs(SPY_GUI) do
					if string.find(nm, pat, 1, true) then return true, "GUI: " .. c.Name end
				end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- catches Dex/RemoteSpy/IY window
	run(opts.http ~= false,      Defense.detectHttpSpy,      "http-spy", opts.raw)
	run(opts.namecall ~= false,  Defense.detectNamecallHook, "namecall-hook")
	run(opts.remote == true,     Defense.detectRemoteSpy,    "remote-spy")   -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,          "dex")          -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		local n = 0
		while ctx.alive do
			n = n + 1
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui,
				http = opts.http, namecall = opts.namecall,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}
	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				if o.kick ~= false then
					pcall(function()
						local lp = game:GetService("Players").LocalPlayer
						lp:Kick(o.kickMessage or ("Tamper detected (" .. tostring(name) .. ")"))
					end)
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)
		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}
	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'l3PNqzDNEzjTQnTxpFdKenkF'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, antiSpy = { kick = true, halt = true } })
