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
		spike = remoteSpike(),
	}
	return true
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
				iy = opts.iy, gui = opts.gui,
				http = opts.http, namecall = opts.namecall,
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

local __k = 'aEiC5wJNPz8E1kIFKXEvgIW8'
local __p = 'TGgyGD+V396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NVjYxVXagwFM3QBESppFAIWAlYhCAV1Qafp1xUueAVwMm0HER14aHt2dVZHaXcYQWVJYxVXam5wWhhlEUtpZmt4bQUOJzBUBGgPKlkSaiwlE1QhGGFpZmt4FQQILSJbFSwGLRgGPy88E0w8EQo8MiR1IxcVJHdLAjcAM0FXLCEiWmgpUAgsDy94dEZQf2MOVXdfcwJBfXtmWhACUAYsJTk9JAICOn4yQWVJY2A+cG5wWncnQgItLyo2EB9HYQ4KKmU6IEceOjpwOFkmWlkLJygzbHxHaXcYMjEQL1BNByE0H0orEQUsKSV4HEQsZXdfDSoeY1ARLCszDktpERgkKSQsLVYTPjJdDzZFY1MCJiJwCVkzVEQ9Li41IFYUPCdIDjcdSdfi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8af809fi2qzF6trQoYnc1qnN1ZTy2bWt8U9jYxVXah8FM3sOETgdBxkMZV4VPDkYCCsaKlESai8+AxgXXgklKTN4IA4CKiJMDjdAeT9Xam5wWhhlEQcmJy8rMQQOJzAQBiQEJg8/PjogPV0xGUkhMj8oNkxIZi5XFDdEK1oEPmEdG1ErHwc8J2lxbF5OQ10YQWVJDEdXOi8jDl1l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Uh8gKSV4EAIOJSQWDSoGMx0eJDo1CE4kXUdpND42Kx8JLnsYBytASRVXam4kG0suHxg5Jzw2bRASJzRMCCoHaxx9am5wWhhlEUs+LiI0IFYVPDlWCCsOaxxXLiFaWhhlEUtpZmt4ZVZHJThbAClJLF5baisiCBh4ERsqJyc0bRAJYF0YQWVJYxVXam5wWhgsV0snKT94Kh1HPT9dD2UeIkcZYmwLIwoOESM8JGs0KhkXFHcaQWtHY0EYOToiE1YiGQ47NGJxZRMJLV0YQWVJYxVXam5wWhgxUBgiaDw5LAJPIDlMBDcfIlleQG5wWhhlEUtpIyU8T1ZHaXddDyFASVAZLkRaHE0rUh8gKSV4EAIOJSQWBiAdAFQEIgI1G1wgQxg9Jz9wbHxHaXcYDSoKIllXJj1wRxgJXggoKhs0JA8CO21+CCsNBVwFOToTElEpVUNrKi45IRMVOiNZFTZLaj9Xam5wE15lXRhpMiM9K3xHaXcYQWVJY1kYKS88WlskQgNpe2s0NkwhIDlcJywbMEE0Iic8HhBncgo6LmlxT1ZHaXcYQWVJKlNXKS8jEhgxWQ4nZjk9MQMVJ3dMDjYdMVwZLWYzG0stHz0oKj49bFYCJzMyQWVJY1AZLkRwWhhlQw49Mzk2ZVRDeXUyBCsNST9aZ26y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76hPHEZpdWV4FzMqBgN9Mk9EbhWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa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CSodaxx9am5wWlQqUgolZjl4eFYCJyRNEyA7JkUbYmdaWhhlEQIvZiU3MVYVaThKQSsGNxUFZBE5F0gpEQQ7ZiU3MVYVZwhRDDUFbWoaIzwiFUplRQMsKGsqIAISOzkYGjhJJlsTQG5wWhg3VB88NCV4N1g4IDpIDWs2LlwFOCEiVGchUB8oZiQqZQ0aQzJWBU8PNlsUPic/FBgVXQowIzkcJAIGZzBdFRYMJlE+JCo1AhBsEUtpZjk9MQMVJ3doDSQQJkczKzoxVEsrUBs6LiQsbV9JGjJdBQwHJ1APaiEiWkM4EQ4nIkE+MBgEPT5XD2U5L1QOLzwUG0wkHwwsMhs9MT8JPzJWFSobOh1eajw1Dk03X0sZKiohIAQjKCNZTzYHIkUEIiEkUhFrYQ49DyUuIBgTJiVBQSobY04Kais+HjIjRAUqMiI3K1Y3JTZBBDctIkEWZCk1DmgpXh8NJz85bV9HaXcYQTcMN0AFJG4AFlk8VBkNJz85awUJKCdLCSodaxxZGiI/DnwkRQppKTl4PgtHLDlca09EbhWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV395aVxVlBEVpFgcXEVZPOzJLDikfJhUYPSA1Hhg1XQQ9ams8LAQTaTJWFCgMMVQDIyE+UzJoHEur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76in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QWVJYxVXam5wWhhlEUslKSg5KVYLKzsYXGULIQ8xIyA0PFE3Qh8KLiI0ISEPIDRQKDYoaxcjLzYkNlknVAdrb0F4ZVZHaXcYQWVJYxVXam5wWhhlEQIvZic6KVYTITJWQSkLLxsjLzYkWgVlQh87LyU/axAIOzpZFW1LZkZXEWs0WlA1bEllZjs0N1gpKDpdTWUEIkEfZCg8FVc3GQM8K2UQIBcLPT8RSGUMLVF9am5wWhhlEUtpZmt4ZVZHaTJWBU9JYxVXam5wWhhlEUssKC9SZVZHaXcYQWUMLVF9am5wWl0rVUJDIyU8TxASJzRMCCoHY2MeOTsxFktrQg49AxgIBhkLJiUQAmxJFVwEPy88CRYWRQo9I2U9NgYkJjtXE2VUY1ZXLyA0cDJoHEur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09tSaFtHeGMWQRAgY3c4BRpwmLjREQcmJy94ChQUIDNRACs8KhVfE3wbUxgkXw9pJD4xKRJHPT9dQTIALVEYPUR9VxinpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPur09u60OaF3Mfa9NWL1qWV396y76inpPtDNjkxKwJPYXVjOHciY30CKBNwNlckVQInIWsXJwUOLT5ZDxAAY1MFJSNwX0tlH0VnZGJiIxkVJDZMSQYGLVMeLWAFM2cXdDsGb2JSTxoIKjZUQQkAIUcWODd8Wmwt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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Build a ring farm/Build Ring A farm', checksum = 703594195, interval = 2, antiSpy = { kick = true, halt = true } })
