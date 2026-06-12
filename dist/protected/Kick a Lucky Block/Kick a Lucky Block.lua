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

local __k = 'rWSoUooFcSwCpgnbbBA69tEk'
local __p = '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UEdOQkJiYRYZVGVLUndzT3VPT2ZDPxggEQtOABc2NVlXVHhLOgIXTzQBC2YrBjN5Ng4ABiQrM0VNNy0CHjN7TR4GDC0hJgM3HwlMS2hiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkIrJxZbATEfHTlzDjsLTyQWJwMsHkk4CxErI1pcVDEDFzlZT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPTyQXPSEqAw4MDgdifBZNBjAOeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUjI/HDBlT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDcwMiAwxAFQMrNR4JWnRCeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUjI9C19PT2ZDc1djUEdOQkJiYRYZVGVLUjI9C19PT2ZDc1djUEdOQkJiYRYZVGVLUl1zT3VPT2ZDc1djUEdOQkJiYRYZVCwNUjUnAQMGHC8BPxJjBA8LDGhiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJvbBYLWmU/AD40CDAdTy0KMBxjEh5OABsyIEVKHSsMUiM7CnUkBiUIEQI3BAgAQgMsJRZKACQZBj49CHUbByNDPh4tGQAPDwdiJV9LESYfHi5ZT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzGycGCCEGITwqEwxGS2hiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJIYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJibBsZR2tLJTY6G3UJADRDPh4tGQAPDwdiNVkZBzEKACNZT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzAzoMDipDIAMiAhM6Ql9iNV9aH21CeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUiA7BjkKTygMJ1cIGQQFIQ0sNURWGCkOAHkaARgGAS8EMhomUAYABkI2KFVSXGxLX3cgGzQdGxJDb1dxUAYABkIBJ1EXNTAfHRw6DD5PCylpc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUBMPEQlsNldQAG1CeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUjI9C19PT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VlT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPBiBDGB4gGyQBDBYwLlpVETdFOzkeBjsGCCcONlc3GAIAaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRZVGyYKHnc+ADEKT3tDHAc3GQgAEUwJKFVSJCAZFDIwGzwAAWg1Mhs2FUcBEEJgBllWEGVDSmd+VmBKRmRpc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUAsBAQMuYUJYBiIOBho6AXlPGycRNBI3PQYWaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYzVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUnp+TxEKGyMRPh4tFUcaCgdiNVdLEyAfUiQwDjkKTzQCPRAmUAUPEQcmYVlXVDEDF3c+ADEKTycNN1cwBAYKCxcvYVNPESsfeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3UDACUCP1cqAzQaAwYrNFsZSWUNEzsgCl9PT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDIxQiHAtGBBcsIkJQGytDW11zT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDcx4wIxMPBgs3LBYEVBIOEyM7Cic8CjQVOhQmLyQCCwcsNRh8AiAFBiR9PCEOCy8WPlciHgNONQcjNV5cBhYOACE6DDAwLCoKNhk3XiIYBww2MhhqACQPGyI+T2tPGCkROAQzEQQLWCUnNWVcBjMOAAM6AjAhADFLen1jUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOBwwmaDwZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3UGCWYKICQ3EQMHFw9iNV5cGk9LUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPTy8FcxosFAJOX19iY2ZcBiMOESNzR2RfX2NDflcxGRQFG0tgYUJRESthUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djBAYcBQc2DF9XWGUfEyU0CiEiDj5DbldzXl9dTkJybw8NVGhGUgc2HTMKDDJpc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkInLUVcHSNLHzg3CnVSUmZBFBgsFEdGWlJveAMcXWdLBj82AV9PT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkI2IEReETEmGzl/TyEOHSEGJzoiCEdTQlJsdwEVVHVFSmZzQnhPKj4ANhsvFQkaaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLFzsgCjwJTysMNxJjTVpOQCYnIlNXAGVDRGd+V2VKRmRDJx8mHm1OQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUncnDicICjIuOhlvUBMPEAUnNXtYDGVWUmd9WmVDT3ZNZUJjXUpOJRAnIEIzVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3UKAzUGc1puUDUPDAYtLDwZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2YXMgUkFRMjCwxuYUJYBiIOBhoyF3VST3ZNYUdvUFdAW1pIYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUnc2ATFlT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDcxIvAwJkQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGUCFHc+ADEKT3tec1UTFRUIBwE2YR4IRHVOUnpzHTwcBD9KcVc3GAIAaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzTyEOHSEGJzoqHktOFgMwJlNNOSQTUmpzX3tWWGpDYllzUEpDQjInM1BcFzFhUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2YGPwQmGQFODw0mJBYESWVJNTg8C3VHV3ZOakJmWUVOFgonLzwZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2YXMgUkFRMjCwxuYUJYBiIOBhoyF3VST3ZNa0ZvUFdAW1RibBsZMT0IFzs/CjsbZWZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOBw4xJF9fVCgEFjJzUmhPTQIGMBItBEdGVFJveQYcXWdLBj82AV9PT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkI2IEReETEmGzl/TyEOHSEGJzoiCEdTQlJsdwcVVHVFRW5zQnhPKDQGMgNJUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRZcGDYOUnp+TwcOASIMPn1jUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGUfEyU0CiEiBihPcwMiAgALFi8jORYEVHVFQGd/T2VBVn9pc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkInL1IzVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUjI9C19PT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDWVdjUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdDT0IVIF9NVDAFBj4/Tx4GDC0gPBk3AggCDgcwb2VaFSkOUjEyAzkcTzEKJx8qHkcaAxAlJEJ0HStLEzk3TyEOHSEGJzoiCG1OQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiLVlaFSlLETYjGyAdCiIwMBYvFUdTQgwrLTwZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLHjgwDjlPHCUCPxIAHwkAaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRZVGyYKHncgDDQDChQGMhQrFQNOX0IkIFpKEU9LUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzHDYOAyMgPBktUFpOMBcsElNLAiwIF3kDHTA9CigHNgV5MwgADAchNR5fASsIBj48AX1GZWZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOCwRiL1lNVA4CETwQADsbHSkPPxIxXi4ALwssKFFYGSBLBj82AV9PT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkIxIldVEQYEHDlpKzwcDCkNPRIgBE9HaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzTycKGzMRPX1jUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYVNXEE9LUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPTyoMMBYvUBQNAw4nYQsZPywIGRQ8ASEdACoPNgVtIwQPDgdIYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUnc6CXUcDCcPNld9TUcaAxAlJEJ0HStLEzk3TyYMDioGc0t+UBMPEAUnNXtYDGUfGjI9ZXVPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQhEhIFpcJiAKET82C3VSTzIRJhJJUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1dj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UndzT3VPTyMNN31jUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOBwwmaDwZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VCQmYwNgNjAxIeBxBiKV9eHGU8Ezs4PCUKCiJDJxhjHxIaEBcsYUJREWUcEyE2ZXVPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2YLJhptJwYCCTEyJFNdVHhLBTYlCgYfCiMHc11jQklbaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRZRAShRMT8yATIKPDICJxJrNQkbD0wKNFtYGioCFgQnDiEKOz8TNlkRBQkACwwlaDwZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VCQmYuPAEmJAhOFg01IERdVC4CETxzHzQLZWZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1crBQpULw00JGJWXDEKADA2GwUAHG9pc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUG1OQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJibBsZIyQCBncmASEGA2YAPxgwFUcaDUIpKFVSVDUKFl1zT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPAykAMhtjHQgYBzE2IERNVHhLBj4wBH1GZWZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1c0GA4CB0I2KFVSXGxLX3c+ACMKPDICIQNjTEdfV0IjL1IZNyMMXBYmGzokBiUIcxMsekdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZGCoIEztzDCAdHSMNJzQrERVOX0IOLlVYGBUHEy42HXssBycRMhQ3FRVkQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGUHHTQyA3UMGjQRNhk3IggBFkJ/YVVMBjcOHCMQBzQdTycNN1cgBRUcBww2Al5YBms7AD4+DicWPycRJ31jUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYV9fVCYeACU2ASE9ACkXcwMrFQlkQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzAzoMDipDNx4wBEdTQkohNERLESsfIDg8G3s/ADUKJx4sHkdDQhYjM1FcABUEAX59IjQIAS8XJhMmekdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUj41TzEGHDJDb1d7UBMGBwxIYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDcxUxFQYFaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzTzABC0xDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYUWWU5F3o6HCYaCmYuPAEmJAhOCwRiNVlWVCMKAHd7HTAcCjIQcwMqHQIBFxZrSxYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPTy8FcxMqAxNOXEJxcRZNHCAFeHdzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkIqNFsDOSodFwM8RyEOHSEGJycsA05kQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzCjsLZWZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOBwwmSxYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzGzQcBGgUMh43WFdAUUtIYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVCAFFl1zT3VPT2ZDc1djUEdOQkJiYRYZVGVLUndzT3VPZWZDc1djUEdOQkJiYRYZVGVLUndzT3VPT2ZDc1duXUc8BxE2LkRcVCsEADoyA3U4DioIAAcmFQNkQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYV5MGWs8Ezs4PCUKCiJDbldyRm1OQkJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiSxYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRYZVGVGX3cHCjkKHykRJ1cmCAYNFg47YVlXACpLGT4wBHUfDiJDJxhjFxIPEAMsNVNcVCceBiM8AXUZBjUKMR4vGRMXaEJiYRYZVGVLUndzT3VPT2ZDc1djUEdOQkJiYRZLGyofXBQVHTQCCmZeczQFAgYDB0wsJEERHywIGQcyC3s/ADUKJx4sHkdFQjQnIkJWBnZFHDIkR2VDT3VPc0dqWW1OQkJiYRYZVGVL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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2 })
