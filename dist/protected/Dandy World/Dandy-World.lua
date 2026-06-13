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
				if o.halt then
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

local __k = 'nxnnoeRtBgnIjpjwAohRzrzu'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2 })
