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

local __k = 'DensXXqWQzah34RHZxhjBrTv'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, antiSpy = { kick = true, halt = true } })
