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

local __k = 'lWgj2wUgLdizMhjKLO8tGHf4'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2 })
