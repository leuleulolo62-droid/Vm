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

	mt.__metatable = "locked"  -- getmetatable returns this string, hiding mt

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store
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
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envMT)
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
			local okE = Integrity.checkEnv(ctx.env, ctx.envMT)
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
-- replace realG[name] preserving cclosure-ness; remember replacement as ours.
local function spoof(name, build)
	local real = rawget(realG, name)
	if type(real) ~= "function" then return end
	local repl = newcc(build(real))
	genuineFns[repl] = true
	hiddenObjs[repl] = true
	local ok = false
	if hookfunction then ok = pcall(hookfunction, real, repl) end
	if not ok then pcall(rawset, realG, name, repl) end
end

-- replace tbl[name] (e.g. debug.getupvalue) the same way.
local function spoofIn(tbl, name, build)
	if type(tbl) ~= "table" then return end
	local real = rawget(tbl, name)
	if type(real) ~= "function" then return end
	local repl = newcc(build(real))
	genuineFns[repl] = true
	hiddenObjs[repl] = true
	local ok = false
	if hookfunction then ok = pcall(hookfunction, real, repl) end
	if not ok then pcall(rawset, tbl, name, repl) end
end

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
	local env, envMT = Environment.build(proxies, realG)

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

local __k = '6xbvuDsAwDaAAATddMN8v4Da'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2 })
