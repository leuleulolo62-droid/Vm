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

local __k = 'UdQPjtqdGU8WyDX2khp82JwG'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2 })
