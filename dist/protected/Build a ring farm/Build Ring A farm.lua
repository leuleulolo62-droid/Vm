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
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
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
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
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
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
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

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
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
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

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
local Neuter      = Neuter
local License     = License

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

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
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

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

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
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
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

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

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

local __k = 'EEkHmXyPCIrHYgw9TuDtJKj7'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-e4GmRQ6dfOWH
return Vm.run(__src, { name = 'Build a ring farm/Build Ring A farm', checksum = 703594195, interval = 2, watermark = 'Y2k-e4GmRQ6dfOWH', neuterAC = true, antiSpy = { kick = true, halt = true } })
