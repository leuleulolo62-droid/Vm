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
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] then return nil end return s end end)
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
local SPY_GUI = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true,
	["simplespy"] = true, ["hydroxide"] = true, ["remote spy"] = true,
}
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
				if SPY_GUI[string.lower(c.Name)] then return true, "GUI: " .. c.Name end
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

-- watchdog: scan on an interval, call onDetect(name, detail) on first hit -----
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	local body = function()
		local wait_ = (task and task.wait) or wait
		while ctx.alive do
			wait_(opts.interval or 3)
			if not ctx.alive then return end
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui,
				http = opts.http, namecall = opts.namecall,
				remote = opts.remote, dex = opts.dex, raw = ctx.raw,
			})
			if #hits > 0 then
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
			end
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

		-- execute, then ALWAYS tear down (return or error)
		local results = { pcall(fn, ...) }
		ctx.alive = false                 -- stop the watchdog
		pcall(function() ctx.mem:cleanup() end)  -- cancel threads, disconnect, GC
		if not results[1] then
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end
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

local __k = 'mTVGp2kiHWBenhlSIECA6aqW'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Build a ring farm/Build Ring A farm', checksum = 703594195, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
