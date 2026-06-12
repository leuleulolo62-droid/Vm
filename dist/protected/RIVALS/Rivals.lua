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

local __k = 'Doyl44Ie7sjqk5DAsn3s0bAJ'
local __p = 'aUIiNz49GyxhMiYiS9fE1VM3ARgQSg4oNwYdBVVaYEViOmB4O0crJQYNRxpfDGEoMQYVCBoUDBNSARNRDVAlNQYcVlNHECA6N08NBFEULgRaFk0CS3oTD1MNXxpVDDVqCBoYTFhVMABFeWNZAls3NRIAUBYdDiQ8IQNZAVFAIQpTUxkZClErNhoAVFoQDTNqIgYLCUcUKEVFFgsdS0chLBwaVl8QAy0mZB8aDVhYZAJCEhgVDlFqS3lncjAQEi45MBoLCRQcOwBUHBwUGVAgYRUcXB4QFikvZCMMHlVEIUVhPkoSBFs3NRIAR1NADS4mbVVZGFxRaQRZBwNcCF0hIAdkOhdVFiQpMBxZBFtbIhYXBQMQS1w3IhACXABFECRlLRwVD1hbOhBFFkpZCFkrMgYcVl5EGzEvZAkVBURHYEVWHQ5RBlAwIAcPUR9VaEgmKwwSHxgUKAtTUxgUG1o2NQBOXAVVEGECMBsJP1FGPwxUFkRRP10hMxYIXAFVQjUiLRxZH1dGIBVDUyQ0PXAWYRsBXBhWFy8pMAYWAhNHQ2xWUwQQH1wyJFw8XBFcDTlqBT8wTFJBJwZDGgUfS1QqJVMgdiV1MGEiKwASHxRVaQJbHAgQBxUpJAcPXhZECi4uak8wGBRbJwlOeWMCA1QgLgQdEx5VFiklIBxZA1oUPQ1SUw0QBlBjMlMBRB0QLjQrZAwVDUdHaQxZAB4QBVYhMlNGXwZRQiImKxwMHlFHYEkXAQ8QD0ZOSAMPQABZFCQmPUNZDVpQaRdSHQ4UGUZkIh8HVh1ETzIjIApXTGdROxNSAUcXClYtLxROUhBECy4kN08KGFVNaRVbEh8CAlcoJF1kOXp8FyBqcUFIQUdVLwAXPx8QHg9kLxxOGE4cQi8lZAwWAkBdJxBSX0ofBBUlfhFUUFNEBzMkJR0AQj5pFG89XkdeRBUXJAEYWhBVEUsmKwwYABRkJQROFhgCSxVkYVNOE1MQQnxqIw4UCQ5zLBFkFhgHAlYhaVE+XxJJBzM5ZkZzAFtXKAkXIR8fOFA2NxoNVlMQQmFqZE9ETFNVJAANNA8FOFA2NxoNVlsSMDQkFwoLGl1XLEceeQYeCFQoYSYdVgF5DDE/MDwcHkJdKgAXTkoWClghezQLRyBVEDcjJwpRTmFHLBd+HRoEH2YhMwUHUBYSS0smKwwYABRjJhdcABoQCFBkYVNOE1MQQnxqIw4UCQ5zLBFkFhgHAlYhaVE5XAFbETErJwpbRT5YJgZWH0o9AlIsNRoAVFMQQmFqZE9ZTAkULgRaFlA2DkEXJAEYWhBVSmMGLQgRGF1aLkceeQYeCFQoYTABXx9VATUjKwFZTBQUaUUXTkoWClghezQLRyBVEDcjJwpRTndbJQlSEB4YBFsXJAEYWhBVQGhAKAAaDVgUGwBHHwMSCkEhJSAaXAFRBSR3ZAgYAVEODgBDIA8DHVwnJFtMYRZADigpJRscCGdAJhdWFA9TQj9OLRwNUh8QLi4pJQMpAFVNLBcXTkohB1Q9JAEdHT9fASAmFAMYFVFGQwlYEAsdS3YlLBYcUlMQQmFqZFJZO1tGIhZHEgkURXYxMwELXQdzAywvNg5zZhkZZkoXJiNRB1wmMxIcSlMYO3MhZEBZI1ZHIAFeEgRRGEElIhhHOR9fASAmZB0cHFsUdEUVGx4FG0Z+blwcUgQeBSg+LBobGUdROwZYHR4UBUFqIhwDHCoCCRIpNgYJGHZVKg4FMQsSABoLIwAHVxpRDBQjawIYBVoba29bHAkQBxUIKBEcUgFJQmFqZE9ZURRYJgRTAB4DAlsjaRQPXhYKKjU+NCgcGBxGLBVYU0RfSxcIKBEcUgFJTC0/JU1QRRwdQwlYEAsdS2EsJB4LfhJeAyYvNk9ETFhbKAFEBxgYBVJsJhIDVkl4FjU6AwoNREZROQoXXURRSVQgJRwAQFxkCiQnISIYAlVTLBcZHx8QSRxtaVpkXxxTAy1qFw4PCXlVJwRQFhhRSwhkLRwPVwBEECgkI0ceDVlRcy1DBxo2DkFsMxYeXFMeTGFoJQsdA1pHZjZWBQ88ClslJhYcHR9FA2NjbUdQZj5YJgZWH0o+G0EtLh0dE04QLigoNg4LFRp7ORFeHAQCYVkrIhICEydfBSYmIRxZURR4IAdFEhgIRWErJhQCVgA6aGxnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl46T2xqFzs4OHE+ZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQT5YJgZWH0o3B1QjMlNTEwg6a2xnZAwWAVZVPW8+IAMdDlswABoDE1MQQmFqZFJZClVYOgAbeWMiAlkhLwc8UhRVQmFqZE9ZURRSKAlEFkZRSxVpbFMIUh9DB2F3ZAMcC11AaU1xPDxRDFQwJBdHH1NEEDQvZFJZHlVTLEUfHwUSABUqJBIcVgBES0tDBQYUKltCGwRTGh8CSxVkYU5OAkIATktDBQYUJF1AKwpPU0pRSxVkYU5OETtVAyVoaE9ZQRkUAQBWF0peS3crJQpOHFN+ByA4IRwNZj11IAhhGhkYCVkhAhsLUBgQX2E+NhocQD49CAxaJw8QBnYsJBAFE1MQQnxqMB0MCRg+QCReHjoDDlEtIgcHXB0QQmF3ZF9XXBg+QCtYIBoDDlQgYVNOE1MQQmF3ZAkYAEdRZW8+PQUjDlYrKB9OE1MQQmFqZFJZClVYOgAbeWMlGVwjJhYcURxEQmFqZE9ZURRSKAlEFkZ7YmE2KBQJVgF0By0rPU9ZTBQJaVUZQ1ldYTwMKAcMXAt1GjErKgscHhQUdEVREgYCDhlOSDsHRxFfGhIjPgpZTBQUaUUKU1JdYTwXKRwZdRxGQmFqZE9ZTBQUdEVREgYCDhlOSF5DExZDEktDARwJKVpVKwlSF0pRSwhkJxICQBYcaEgPNx87A0wUaUUXU0pRVhUwMwYLH3k5JzI6Cg4UCRQUaUUXU1dRH0cxJF9kOjZDEgkvJQMNBBQUaUUKUx4DHlBoS3orQAN0CzI+JQEaCRQUdEVDAR8URz9NBAAeZwFRASQ4ZE9ZTAkULwRbAA9dYTwBMgM6VhJdISkvJwRZURRAOxBSX2B4LkY0DBIWdxpDFmFqZFJZXQQEeUk9ei8CG3YrLRwcE1MQQmF3ZCwWAFtGektRAQUcOXIGaUNCE0EBUm1qdl1ARRg+QEgaUwceHVApJB0aOXpnAy0hFx8cCVB7J0UKUwwQB0YhbVM5Uh9bMTEvIQtZURQFf0k9eiAEBkULL1NOE1MQQnxqIg4VH1EYaS9CHhohBEIhM1NTE0YATktDDQEfJkFZOUUXU0pRVhUiIB8dVl86awcmPSAXTBQUaUUXU1dRDVQoMhZCEzVcGxI6IQodTAkUf1UbeWM/BFYoKAMhXVMQQmF3ZAkYAEdRZW8+XkdRG1klOBYcOXpxDDUjBQkSTBQUdEVREgYCDhlOSDAbQAdfDwclMk9ETFJVJRZSX0o3BEMSIB8bVlMNQnZ6aGVwKkFYJQdFGg0ZHwhkJxICQBYcaEhnaU8eDVlRQ2x2Bh4eOkAhNBZODlNWAy05IUNzET4+JQpUEgZRKFoqLxYNRxpfDDJqeU8CERQUaUgaUzgzM2YnMxoeRzBfDC8vJxsQA1pHaRFYUwkdDlQqSx8BUBJcQhUiNgoYCEcUaUUXU1dREEhkYVNDHlNRATUjMgpZAFtbOUVaEhgaDkc3Sx8BUBJcQhMvNxsWHlFHaUUXU1dREEhkYVNDHlNWFy8pMAYWAkcUPQoXBgQVBBUsLhwFQFxCBzIjPgoKTFtaaRBZHwUQDz8oLhAPX1N0ECA9LQEeHxQUaUUKUxEMSxVkbF5OdiBgQiU4JRgQAlMUJgddFgkFGBU0JAFOQx9RGyQ4TmUVA1dVJUVRBgQSH1wrL1MaQRJTCWkpKwEXRT49CgpZHQ8SH1wrLwA1EDBfDC8vJxsQA1pHaU4XQjdRVhUnLh0AOXpCBzU/NgFZD1taJ29SHQ57YRhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkd7RhhkEjIodlNiJxIFCDk8PmcUYQZWEAIUDxlkMxZDQRZDDS08IQtZCFFSLAtEGhwUB0xtS15DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhOLRwNUh8QMhJqeU81A1dVJTVbEhMUGQ8TIBoadRxCISkjKAtRTmRYKBxSATkSGVw0NQBMGnk6Di4pJQNZCkFaKhFeHARRH0c9ExYfRhpCB2kjKhwNRT49IAMXHQUFS1wqMgdORxtVDGE4IRsMHloUJwxbUw8fDz9NLRwNUh8QDSpmZAIWCBQJaRVUEgYdQ0chMAYHQRYcQigkNxtQZj1dL0VYGEoFA1AqYQELRwZCDGEnKwtZCVpQQ2xFFh4EGVtkLxoCORZeBktAKAAaDVgUDwxQGx4UGXYrLwccXB9cBzNAKAAaDVgULxBZEB4YBFtkJhYadTAYS0tDLQlZKl1TIRFSASkeBUE2Lh8CVgEQFikvKk8LCUBBOwsXNQMWA0EhMzABXQdCDS0mIR1ZCVpQQ2xbHAkQBxUqLhcLE04QMhJwAgYXCHJdOxZDMAIYB1FsYzABXQdCDS0mIR0KTh0+QAtYFw9RVhUqLhcLExJeBmEkKwscVnJdJwFxGhgCH3YsKB8KG1F2CyYiMAoLL1taPRdYHwYUGRdtS3ooWhRYFiQ4BwAXGEZbJQlSAUpMS0E2OCELQgZZECRiKgAdCR0+QBdSBx8DBRUCKBQGRxZCIS4kMB0WAFhRO29SHQ57YVkrIhICExVFDCI+LQAXTFNRPSNeFAIFDkdsaHlnXxxTAy1qAixZURRTLBFxMEJYYTwtJ1MAXAcQJAJqMAccAhRGLBFCAQRRBVwoYRYAV3k5Di4pJQNZChQJaRdWBA0UHx0CAl9OET9fASAmAgYeBEBRO0ceeWMYDRUiYU5TEx1ZDmE+LAoXZj09JQpUEgZRBF5oYQFODlNAASAmKEcfGVpXPQxYHUJYS0chNQYcXVN2IW8GKwwYAHJdLg1DFhhRDlsgaHlnOhpWQi4hZBsRCVoUL0UKUxhRDlsgS3oLXRc6azMvMBoLAhRSQwBZF2B7RhhkMxYdXB9GB2ErZB0cAVtALEVCHQ4UGRUWJAMCWhBRFiQuFxsWHlVTLEtlFgceH1A3YREXEwNRFilqNwoeAVFaPRY9HwUSCllkExYDXAdVEQclKAscHhQJaTdSAwYYCFQwJBc9RxxCAyYvfikQAlByIBdEBykZAlkgaVE8Vh5fFiQ5ZkZzAFtXKAkXFR8fCEEtLh1OVBZEMCQnKxscRBoaZ0w9egMXS1srNVM8Vh5fFiQ5AgAVCFFGaRFfFgRRGVAwNAEAEx1ZDmEvKgtzZVhbKgRbUwQeD1BkfFM8Vh5fFiQ5AgAVCFFGQ2xbHAkQBxU3JBQdE04QGWFkakFZET49JQpUEgZRAhV5YUJkOgRYCy0vZAEWCFEUKAtTUwNRVwhkYgALVAAQBi5ATWYXA1BRaVgXHQUVDg8CKB0KdRpCETUJLAYVCBxHLAJEKAMsQj9NSBpODlNZQmpqdWVwCVpQQ2xFFh4EGVtkLxwKVnlVDCVATkJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xAaUJZOHVmDiBjOiQ2Sx00IAAdWgVVQjMvJQsKTFtaJRweeUdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEg9HwUSCllkCTo6cTxoPQ8LCSoqTAkUMm8+Ow8QDxV5YQhOETtZFiMlPCccDVAWZUUVOwMFCVo8CRYPVyBdAy0mZkNZTnxRKAEVUxddYTwGLhcXE04QGWFoDAYNDltMCwpTCkhdSxcMKAcMXAtyDSUzFwIYAFgWZUUVOx8cClsrKBc8XBxEMiA4ME1VTBZhORVSAT4eGUYrY1MTH3lNaEsmKwwYABRSPAtUBwMeBRUiKAEdRzBYCy0ubAIWCFFYZUVZEgcUGBxOSB8BUBJcQihqeU9IZj1DIQxbFkoYSwl5YVAAUh5VEWEuK2VwZVhbKgRbUxpRVhUpLhcLX0l2Cy8uAgYLH0B3IQxbF0IfClghMigHblo6a0gjIk8JTEBcLAsXAQ8FHkcqYQNOVh1UaEhDLU9ETF0UYkUGeWMUBVFOSAELRwZCDGEkLQNzCVpQQ29bHAkQBxUiNB0NRxpfDGEjNy4VBUJRYQZfEhhYYTwoLhAPX1NYFyxqeU8aBFVGaQRZF0oSA1Q2ezUHXRd2CzM5MCwRBVhQBgN0HwsCGB1mCQYDUh1fCyVobWVwBVIUIRBaUwsfDxUsNB5AexZRDjUiZFNETAQUPQ1SHUoDDkExMx1OVRJcESRqIQEdZj1GLBFCAQRRCF0lM1MQDlNeCy1AIQEdZj5YJgZWH0oXHlsnNRoBXVNZEQQkIQIARERYO0kXBw8QBnYsJBAFGnk5CydqNAMLTAkJaSlYEAsdO1klOBYcEwdYBy9qNgoNGUZaaQNWHxkUS1AqJXlnWhUQDC4+ZBscDVl3IQBUGEoFA1AqYQELRwZCDGE+NhocTFFaLW8+HwUSCllkLBoAVlMQX2EGKwwYAGRYKBxSAVA2DkEFNQccWhFFFiRiZjscDVl9DUceeWMdBFYlLVMaWxZZEGF3ZB8VHg5zLBF2Bx4DAlcxNRZGESdVAywDAE1QZj1dL0VaGgQUSwh5YR0HX1NfEGE+LAoQHhQJdEVZGgZRH10hL1McVgdFEC9qMB0MCRRRJwE9ehgUH0A2L1MDWh1VQj93ZBsRCV1GQwBZF2B7B1onIB9OVQZeATUjKwFZG1tGJQFjHDkSGVAhL1seXAAZaEgmKwwYABRCZUVYHUpMS3YlLBYcUklnDTMmIDsWOl1RPhVYAR4hBFwqNVseXAAZaEg4IRsMHloUHwBUBwUDWRsqJARGRV1oTmE8ajZQQBRbJ0kXBUQrYVAqJXlkHl4QECAzJw4KGBRCIBZeEQMdAkE9YRUcXB4QASAnIR0YTEBbaRFWAQ0UHxlkKBQAXAFZDCZqKAAaDVgUYkVDEhgWDkFkIhsPQXlcDSIrKE8fGVpXPQxYHUoYGGMtMhoMXxYYFiA4IwoNPFVGPUkXBwsDDFAwAhsPQVo6ay0lJw4VTERVOwRaAEpMS2clOBAPQAdgAzMrKRxXAlFDYUw9ehoQGVQpMl0oWh9EBzMePR8cTAkUDAtCHkQjCkwnIAAadRpcFiQ4EBYJCRpxMQZbBg4UYTwoLhAPX1NWCy0+IR1ZURRPaSZWHg8DChU5S3oHVVN8DSIrKD8VDU1RO0t0GwsDClYwJAFORxtVDGEsLQMNCUZvagNeHx4UGRVvYUIzE04QLi4pJQMpAFVNLBcZMAIQGVQnNRYcExZeBktDLQlZGFVGLgBDMAIQGRUwKRYAExVZDjUvNjRaCl1YPQBFU0FRWmhkfFMaUgFXBzUJLA4LTFFaLW8+AwsDClg3bzUHXwdVEAUvNwwcAlBVJxFEOgQCH1QqIhYdE04QBCgmMAoLZj1YJgZWH0oeGVwjKB1ODlNzAywvNg5XL3JGKAhSXToeGFwwKBwAOXpcDSIrKE8dBUYUdEVDEhgWDkEUIAEaHSNfESg+LQAXTBkUJhdeFAMfYTwoLhAPX1NCBzJqeU8uA0ZfOhVWEA9LOVQ9IhIdR1tfECgtLQFVTFBdO0kXAwsDClg3aHlnQRZEFzMkZB0cHxQJdEVZGgZ7DlsgS3lDHlNTCi4lNwpZGFxRaQdSAB5RGFwoJB0aHhJZD2E+JR0eCUAPaRdSBx8DBUZkOlMeUgFEX21qJQYUPFtHdEkXEAIQGQhkPFMBQVNeCy1AKAAaDVgULxBZEB4YBFtkJhYaYBpcBy8+EA4LC1FAYUw9egYeCFQoYRALXQdVEGF3ZCwYAVFGKEthGg8GG1o2NSAHSRYQSGF6alpzZVhbKgRbUwgUGEFoYRELQAdjAS44IWVwAFtXKAkXAwYQElA2MlNTEyNcAzgvNhxDK1FAGQlWCg8DGB1tS3oCXBBRDmEjZFJZXT49Pg1eHw9RAhV4fFNNQx9RGyQ4N08dAz49QAlYEAsdS0UoM1NTEwNcAzgvNhwiBWk+QGxbHAkQBxUnKRIcE04QEi04aiwRDUZVKhFSAWB4YlwiYRAGUgEQAy8uZAYKLVhdPwAfEAIQGRxkIB0KExpDJy8vKRZRHFhGZUVxHwsWGBsFKB46VhJdISkvJwRQTEBcLAs9emN4B1onIB9ORBJeFg8rKQoKZj09QAxRUywdClI3bzIHXjtZFiMlPE9EURQWCwpTCkhRH10hL3lnOno5FSAkMCEYAVFHaVgXOyMlKXocHj0vfjZjTAMlIBZzZT09LAlEFmB4YjxNNhIARz1RDyQ5ZFJZJH1gCypvLCQwJnAXbzsLUhc6a0hDIQEdZj09QAlYEAsdS0UlMwdODlNWCzM5MCwRBVhQYQZfEhhdS0IlLwcgUh5VEWhqKx1ZCl1GOhF0GwMdDx0nKRIcH1N4KxUICzcmInV5DDYZMQUVEhxOSHpnWhUQEiA4ME8NBFFaQ2w+emMdBFYlLVMdUAFVBy9mZAAXP1dGLABZX0oVDkUwKVNTEwRfEC0uEAAqD0ZRLAsfAwsDHxsULgAHRxpfDGhATWZwZV1SaQpZIAkDDlAqYRIAV1NUBzE+LE9HTAQUPQ1SHWB4YjxNSB8BUBJcQiUjNxtZURQcOgZFFg8fSxhkIhYARxZCS28HJQgXBUBBLQA9emN4YjwoLhAPX1NAAzI5TmZwZT09IAMXNQYQDEZqEhoCVh1EMCAtIU8NBFFaQ2w+emN4YkUlMgBODlNEEDQvTmZwZT09LAlEFmB4YjxNSHoeUgBDQnxqIAYKGBQIdEVxHwsWGBsFKB4oXAViAyUjMRxzZT09QGxSHQ57YjxNSHoHVVNAAzI5ZA4XCBQcJwpDUywdClI3bzIHXiVZESgoKAo6BFFXIkVYAUoYGGMtMhoMXxYYEiA4MENZD1xVO0weUx4ZDltOSHpnOno5CydqKgANTFZROhFkEAUDDhUrM1MKWgBEQn1qJgoKGGdXJhdSUx4ZDltOSHpnOno5ayMvNxsqD1tGLEUKUw4YGEFOSHpnOno5a2xnZB8LCVBdKhFeHARRQ1khIBdOUQoQFCQmKwwQGE0dQ2w+emN4YjwoLhAPX1NRCyxqeU8JDUZAZzVYAAMFAloqS3pnOno5a0gjIk8/AFVTOkt2GgchGVAgKBAaWhxeQn9qdE8NBFFaQ2w+emN4YjxNLRwNUh8QFCQmZFJZHFVGPUt2ABkUBlcoOD8HXRZREBcvKAAaBUBNQ2w+emN4YjxNIBoDE04QAygnZERZGlFYaU8XNQYQDEZqABoDYwFVBigpMAYWAj49QGw+emN4DlsgS3pnOno5a0goIRwNTAkUMkVHEhgFSwhkMRIcR18QAygnFAAKTAkUKAxaX0oSA1Q2YU5OUBtREGE3TmZwZT09QABZF2B4YjxNSBYAV3k5a0hDIQEdZj09QABZF2B4YlAqJXlnOhoQX2EjZERZXT49LAtTeWMDDkExMx1OURZDFksvKgtzZhkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJzQRkUCip6MSslS30LDjg9E1tZDDI+JQEaCRtHIAtQHw8FBFtkLBYaWxxUQjIiJQsWG11aLkXV8/5RBVpkLxIaWgVVQiklKwQKRT4ZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUZlhbKgRbUyFBRxUPcF9OeEEcQgp5ZFJZH0BGIAtQXQkZCkdscVpCEwBEECgkI0EaBFVGYVQeX0oCH0ctLxRAUBtREGl4bUNZH0BGIAtQXQkZCkdsclpkOV4dQhIjKAoXGBR1IAgNUxkZClErNlMpVgdzAywvNg49DUBVaQpZUx4ZDhUILhAPXzVZBSk+IR1ZBVpHPQRZEA9RGFpkNRsLExRRDyRtN2VUQRRbPgsXBQsdAlElNRYKExVZECRqNA4NBBRHLAtTAEoeHkdkMxYKWgFVATUvIE8YBVkaaTdSXgsBG1ktJBdOXB0QECQ5NA4OAho+JQpUEgZRDUAqIgcHXB0QBy85MR0cP11YLAtDMgMcI1orKltHOXpcDSIrKE8fBVNcPQBFU1dRDFAwBxoJWwdVEGljTmYQChRaJhEXFQMWA0EhM1MaWxZeQjMvMBoLAhRRJwE9egMXS0clNhQLR1tWCyYiMAoLQBQWFjpOQQEuDFYgY1pORxtVDGE4IRsMHloULAtTeWMdBFYlLVMBQRpXQnxqIgYeBEBRO0twFh4yClghMxIqUgdRQmFqZE9UQRRGLBZYHxwUGBUwKRZOUB9RETJqKQoNBFtQQ2xeFUoFEkUhaRwcWhQZQj93ZE0fGVpXPQxYHUhRH10hL1McVgdFEC9qIQEdZj1GKBJEFh5ZDVwjKQcLQV8QQB4VPV0SM1NXLUcbUwUDAlJtS3oIWhRYFiQ4aigcGHdVJABFEi4QH1RkfFMIRh1TFiglKkcKCVhSZUUZXURYYTxNLRwNUh8QASVqeU8WHl1TYRZSHwxdSxtqb1pkOnpZBGEMKA4eHxpnIAlSHR4wAlhkIB0KEwBVDidqeVJZC1FADwxQGx4UGR1tYRIAV1NEGzEvbAwdRRQJdEUVBwsTB1BmYQcGVh06a0hDNAwYAFgcLxBZEB4YBFtsaHlnOno5Di4pJQNZA0ZdLgxZU1dRCFEfCkMzOXo5a0gjIk8XA0AUJhdeFAMfS0EsJB1OQRZEFzMkZAoXCD49QGw+HwUSCllkNRIcVBZEQnxqIwoNP11YLAtDJwsDDFAwaVpkOno5aygsZBsYHlNRPUVDGw8fYTxNSHpnXxxTAy1qKx9ZURRbOwxQGgRfO1o3KAcHXB06a0hDTWYaCG9/eDgXTkoyLUclLBZAXRZHSi46aE8NDUZTLBEZEgMcO1o3aHlnOno5aygsZCkVDVNHZzZeHw8fH2clJhZORxtVDEtDTWZwZT1XLT58QTdRVhUwIAEJVgceEiA4MGVwZT09QGxUFzE6WGhkfFMtdQFRDyRkKgoORB0+QGw+emMUBVFOSHpnOhZeBktDTWYcAlAdQ2w+FgQVYTxNMxYaRgFeQiIuTmYcAlA+QDdSAB4eGVA3GlA8VgBEDTMvN09STAVpaVgXFR8fCEEtLh1GGnk5ay0lJw4VTFIUdEVQFh43AlIsNRYcG1o6a0gjIk8fTFVaLUVFEh0WDkFsJ19OESxvG3MhGwgaCBYdaRFfFgR7YjxNJ10pVgdzAywvNg49DUBVaVgXAQsGDFAwaRVCE1FvPTh4LzAeD1AWYG8+emMDCkI3JAdGVV8QQB4VPV0SM1NXLUcbUwQYBxxOSHoLXRc6ayQkIGUcAlA+Q0gaUyQeS2Y0MxYPV0kQESkrIAAOTHNRPTZHAQ8QDxUrL1MaWxYQJSAnIR8VDU1hPQxbGh4IS0YtLxQCVgdfDGFnek8QCFFaPQxDCkR7B1onIB9OVQZeATUjKwFZCVpHPBdSPQUiG0chIBcmXBxbSmhATQMWD1VYaSJiU1dRH0c9ExYfRhpCB2kYIR8VBVdVPQBTIB4eGVQjJF0jXBdFDiQ5fikQAlByIBdEBykZAlkgaVEpUh5VEi0rPToNBVhdPRwVWkN7YlwiYR0BR1N3N2E+LAoXTEZRPRBFHUoUBVFOSBoIEwFRFSYvMEc+ORgUazpoClgaNEY0MxYPV1EZQjUiIQFZHlFAPBdZUw8fDz9NLRwNUh8QDzVqeU8eCUBZLBFWBwsTB1BsBiZHOXpcDSIrKE8WG1pRO0UKU0IcHxUlLxdOQRJHBSQ+bAINQBQWFjpeHQ4UExdtaFMBQVN3N0tDLQlZGE1ELE1YBAQUGRxkP05OEQdRAC0vZk8NBFFaaQpAHQ8DSwhkBiZOVh1UaEg6Jw4VABxHLBFFFgsVBFsoOF9OXAReBzNmZAkYAEdRYG8+HwUSCllkLgEHVFMNQi49KgoLQnNRPTZHAQ8QDz9NKBVORwpAB2klNgYeRRRKdEUVFR8fCEEtLh1MEwdYBy9qNgoNGUZaaQBZF2B4GVQzMhYaGzRlTmFoGzAAXl9rOhVFFgsVSRlkNQEbVlo6ay49KgoLQnNRPTZHAQ8QDxV5YRUbXRBECy4kbBwcAFIYaUsZXUN7YjwtJ1MoXxJXEW8EKzwJHlFVLUVDGw8fS0chNQYcXVNzJDMrKQpXAlFDYUwXFgQVYTxNMxYaRgFeQi44LQhRH1FYL0kXXURfQj9NJB0KOXpiBzI+Kx0cH28XGwBEBwUDDkZkalNfblMNQic/KgwNBVtaYUw9emMBCFQoLVsIRh1TFiglKkdQTFtDJwBFXS0UH2Y0MxYPV1MNQi44LQhZCVpQYG8+FgQVYVAqJXlkHl4QLC5qFgoaA11Yc0VFFhodClYhYSw8VhBfCy1qKwFZGFxRaSJCHUoYH1ApYRACUgBDQmx0ZAEWQVtEaRJfGgYUS1MoIBQJVhceaC0lJw4VTFJBJwZDGgUfS1AqMgYcVj1fMCQpKwYVJFtbIk0eeWMdBFYlLVMAXBdVQnxqFDxDKl1aLSNeARkFKF0tLRdGET5fBjQmIRxbRT49JwpTFkpMS1srJRZOUh1UQi8lIApDKl1aLSNeARkFKF0tLRdGETpEBywePR8cHxYdQ2xZHA4USwhkLxwKVlNRDCVqKgAdCQ5yIAtTNQMDGEEHKRoCV1sSJTQkZkZzZVhbKgRbUy0EBXYoIAAdE04QFjMzFgoIGV1GLE1ZHA4UQj9NKBVOXRxEQgY/KiwVDUdHaRFfFgRRGVAwNAEAExZeBktDLQlZHlVDLgBDWy0EBXYoIAAdH1MSPR4zdgQmHlFXJgxbUUNRH10hL1McVgdFEC9qIQEdZj1EKgRbH0ICDkE2JBIKXB1cG21qAxoXL1hVOhYbUwwQB0YhaHlnXxxTAy1qKx0QCxQJaRdWBA0UHx0DNB0tXxJDEW1qZjArCVdbIAkVWmB4AlNkNQoeVltfECgtbU8HURQWLxBZEB4YBFtmYQcGVh0QECQ+MR0XTFFaLW8+AQsGGFAwaTQbXTBcAzI5aE9bM2tNew5oAQ8SBFwoY19ORwFFB2hATSgMAndYKBZEXTUjDlYrKB9ODlNWFy8pMAYWAhxHLAlRX0pfRRttS3pnWhUQJC0rIxxXIltmLAZYGgZRH10hL1McVgdFEC9qIQEdZj09OwBDBhgfS1o2KBRGQBZcBG1qakFXRT49LAtTeWMjDkYwLgELQCgTMCQ5MAALCUcUYkUGLkpMS1MxLxAaWhxeSmhATWYJD1VYJU1RBgQSH1wrL1tHEzRFDAImJRwKQmtmLAZYGgZRVhUrMxoJExZeBmhATQoXCD5RJwE9eUdcS1glKB0aVh1RDCIvZAMWA0QOaQ5SFhpRA1orKgBOUgNADigvIE8YD0ZbOhYXAQ8CG1QzLwBORBtZDiRqJQEATFdbJAdWB0oXB1QjYRodExxeaC0lJw4VTFJBJwZDGgUfS0YwIAEacBxdACA+CQ4QAkBVIAtSAUJYYTwtJ1M6WwFVAyU5agwWAVZVPUVDGw8fS0chNQYcXVNVDCVATTsRHlFVLRYZEAUcCVQwYU5ORwFFB0tDMA4KBxpHOQRAHUIXHlsnNRoBXVsZaEhDMwcQAFEUHQ1FFgsVGBsnLh4MUgcQBi5ATWZwHFdVJQkfFgQCHkchEhoCVh1EIygnDAAWBx0+QGw+AwkQB1lsJB0dRgFVLC4ZNB0cDVB8JgpcWmB4Yjw0IhICX1tVDDI/Ngo3A2ZRKgpeHyIeBF5tS3pnOgdRESpkMw4QGBwEZ1AeeWN4DlsgS3oLXRcZaCQkIGVzQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaWVUQRRgGyxwNC8jKXoQYVsIWgFVEWE+LApZC1VZLEJEUwUGBRU3KRwBR1NZDDE/ME8OBFFaaQReHg8VS1QwYRIAExZeBywzbWVUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnTgMWD1VYaQNCHQkFAloqYRAcXABDCiAjNioXCVlNYUw9ekdcS1w3YQcGVlNTEC45NwcYBUYUKhBFAQ8fH1k9YRwYVgEQAy9qIQEcAU0UIQxDEQUJVD9NLRwNUh8QFiA4IwoNTAkULgBDIAMdDlswFRIcVBZESmhATQYfTFpbPUVDEhgWDkFkNRsLXVNCBzU/NgFZClVYOgAXFgQVYTwoLhAPX1NTBy8+IR1ZURR3KAhSAQtfPVwhNgMBQQdjCzsvZEVZXBoBQ2xbHAkQBxU3IgELVh0QX2E9Kx0VCGBbGgZFFg8fQ0ElMxQLR11AAzM+aj8WH11AIApZWmB4GVAwNAEAE1tDATMvIQFZQRRXLAtDFhhYRXglJh0HRwZUB2F2eU9IVD5RJwE9eQYeCFQoYRUbXRBECy4kZBwNDUZAHRdeFA0UGVcrNVtHOXpZBGEeLB0cDVBHZxFFGg0WDkdkNRsLXVNCBzU/NgFZCVpQQ2xjGxgUClE3bwccWhRXBzNqeU8NHkFRQ2xDEhkaRUY0IAQAGxVFDCI+LQAXRB0+QGxAGwMdDhUQKQELUhdDTDU4LQgeCUYUKAtTUywdClI3byccWhRXBzMoKxtZCFs+QGw+HwUSCllkJxocVhcQX2EsJQMKCT49QGxHEAsdBx0iNB0NRxpfDGljTmZwZT1dL0VUAQUCGF0lKAErXRZdG2ljZBsRCVo+QGw+emMdBFYlLVMIWhRYFiQ4ZFJZC1FADwxQGx4UGR1tS3pnOno5CydqIgYeBEBRO0VDGw8fYTxNSHpnOhVZBSk+IR1DJVpEPBEfUTkFCkcwEhsBXAdZDCZobWVwZT09QGxRGhgUDxV5YQccRhY6a0hDTWYcAlA+QGw+eg8fDz9NSHoLXRcZaEhDTQYfTFJdOwBTUx4ZDltOSHpnOgdRESpkMw4QGBxyJQRQAEQlGVwjJhYcdxZcAzhjTmZwZVFYOgA9emN4YkElMhhARBJZFml6al9MRT49QGxSHQ57YjwhLxdkOnpkCjMvJQsKQkBGIAJQFhhRVhUqKB9kOhZeBmhAIQEdZj4ZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUZhkZaS1+Jyg+MxUBGSMvfTd1MGFiJwMQCVpAaRdWCgkQGEFkIBoKCFNCBzI+Kx0cHxRbJ0VTGhkQCVkhaHlDHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpSx8BUBJcQiQyNA4XCFFQGQRFBxlRVhU/PHkCXBBRDmEsMQEaGF1bJ0VEBwsDH30tNREBSzZIEiAkIAoLRB0+QAxRUz4ZGVAlJQBAWxpEAC4yZBsRCVoUOwBDBhgfS1AqJXlnZxtCByAuN0ERBUBWJh0XTkoFGUAhS3oaUgBbTDI6JRgXRFJBJwZDGgUfQxxOSHoZWxpcB2EeLB0cDVBHZw1eBwgeExUlLxdOdR9RBTJkDAYNDltMDB1HEgQVDkdkJRxkOno5EiIrKANRCkFaKhFeHARZQj9NSHpnXxxTAy1qNAMYFVFGOkUKUzodCkwhMwBUdBZEMi0rPQoLHxwdQ2w+emMdBFYlLVMHE04QU0tDTWZwG1xdJQAXGkpNVhVnMR8PShZCEWEuK2VwZT09QAlYEAsdS0UoM1NTEwNcAzgvNhwiBWk+QGw+emMdBFYlLVMNWxJCQnxqNAMLQndcKBdWEB4UGT9NSHpnOhpWQiIiJR1ZDVpQaQxENgQUBkxsMR8cH1NEEDQvbU8YAlAUIBZ2HwMHDh0nKRIcGlNECiQkTmZwZT09QAlYEAsdS10mYU5OUBtREHsMLQEdKl1GOhF0GwMdDx1mCRoaURxIIC4uPU1QZj09QGw+egMXS10mYRIAV1NYAHsDNy5RTnZVOgBnEhgFSRxkNRsLXXk5a0hDTWZwBVIUJwpDUw8JG1QqJRYKYxJCFjIRLA0kTEBcLAs9emN4YjxNSHoLSwNRDCUvID8YHkBHEg1VLkpMS10mbyAHSRY6a0hDTWZwZVFaLW8+emN4YjxNKRFAYBpKB2F3ZDkcD0BbO1YZHQ8GQ3MoIBQdHTtZFiMlPDwQFlEYaSNbEg0CRX0tNREBSyBZGCRmZCkVDVNHZy1eBwgeE2YtOxZHOXo5a0hDTWYRDhpgOwRZABoQGVAqIgpODlMBaEhDTWZwZT1cK0t0EgQyBFkoKBcLE04QBCAmNwpzZT09QGw+FgQVYTxNSHpnVh1UaEhDTWZwBRQJaQwXWEpAYTxNSHoLXRc6a0hDIQEdRT49QGxDEhkaRUIlKAdGA10ES0tDTQoXCD49QEgaUxgUGEErMxZkOnpWDTNqNA4LGBgUOgxNFkoYBRU0IBocQFtVGjErKgscCGRVOxFEWkoVBD9NSHoeUBJcDmksMQEaGF1bJ00eUwMXS0UlMwdOUh1UQjErNhtXPFVGLAtDUx4ZDltkMRIcR11jCzsvZFJZH11OLEVSHQ5RDlsgaHlnOhZeBktDTQoBHFVaLQBTIwsDH0ZkfFMVTnk5axUiNgoYCEcaIQxDEQUJSwhkLxoCOXpVDCVjTgoXCD4+ZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQT4ZZEVyIDpRQ3E2IAQHXRQQIxEDbWVUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnTgMWD1VYaQNCHQkFAloqYR0LRDdCAzYjKghRD1hVOhYbUxoDBEU3aHlnXxxTAy1qKwRVTFAUdEVHEAsdBx0iNB0NRxpfDGljZB0cGEFGJ0VzAQsGAlsjbx0LRFtTDiA5N0ZZCVpQYG8+GgxRBVowYRwFEwdYBy9qNgoNGUZaaQteH0oUBVFOSBUBQVNbTmE8ZAYXTERVIBdEWxoDBEU3aFMKXHk5azEpJQMVRFJBJwZDGgUfQxxkJSgFblMNQjdqIQEdRT49LAtTeWMDDkExMx1OV3lVDCVATgMWD1VYaQNCHQkFAloqYR4PWBZ1ETFiNAMLRT49IAMXNxgQHFwqJgA1Qx9CP2E+LAoXTEZRPRBFHUo1GVQzKB0JQChADjMXZAoXCD49JQpUEgZRGFAwYU5OSHk5ayMlPE9ZTBQUdEVZFh01GVQzKB0JG1FjEzQrNgpbQBQUaR4XJwIYCF4qJAAdE04QU21qAgYVAFFQaVgXFQsdGFBoYSUHQBpSDiRqeU8fDVhHLEVKWkZ7YjwmLgshRgcQQnxqKgoOKEZVPgxZFEJTOEQxIAELEV8QQmExZDsRBVdfJwBEAEpMSwZoYTUHXx9VBmF3ZAkYAEdRZUVhGhkYCVkhYU5OVRJcESRmZCwWAFtGaVgXMAUdBEd3bx0LRFsATnFmdEZZER0YQ2w+HQscDhVkYVNTEx1VFQU4JRgQAlMcazFSCx5TRxVkYVNOSFNjCzsvZFJZXQcYaSZSHR4UGRV5YQccRhYcQg4/MAMQAlEUdEVDAR8URxUSKAAHUR9VQnxqIg4VH1EUNEwbeWN4D1w3NVNOE1MNQi8vMysLDUNdJwIfUT4UE0FmbVNOE1MQGWEZLRUcTAkUeFcbUykUBUEhM1NTEwdCFyRmZCAMGFhdJwAXTkoFGUAhbVM4WgBZAC0vZFJZClVYOgAXDkNdYTxNKRYPXwdYQmF3ZAEcG3BGKBJeHQ1ZSXktLxZMH1MQQmFqP08tBF1XIgtSABlRVhV2bVM4WgBZAC0vZFJZClVYOgAXDkNdYTxNKRYPXwdYICZ3ZAEcG3BGKBJeHQ1ZSXktLxZMH1MQQmFqP08tBF1XIgtSABlRVhV2bVM4WgBZAC0vZFJZClVYOgAbUykeB1o2YU5OcBxcDTN5agEcGxwEZVUbQ0NRFhxoS3pnRwFRASQ4ZE9ETFpRPiFFEh0YBVJsYz8HXRYSTmFqZE9ZFxRgIQxUGAQUGEZkfFNfH1NmCzIjJgMcTAkULwRbAA9RFhxoS3oTOXp0ECA9LQEeH29EJRdqU1dRGFAwS3ocVgdFEC9qNwoNZlFaLW89HwUSCllkJwYAUAdZDS9qLAYdCXFHOU1EFh5YYTwiLgFObF8QBmEjKk8JDV1GOk1EFh5YS1ErS3pnWhUQBmE+LAoXTERXKAlbWwwEBVYwKBwAG1oQBm8cLRwQDlhRaVgXFQsdGFBkJB0KGlNVDCVATQoXCD5RJwE9eQYeCFQoYRUbXRBECy4kZAwVCVVGDBZHW0N7YlMrM1MeXwEcQjIvME8QAhREKAxFAEI1GVQzKB0JQFoQBi5ATWYfA0YUFkkXF0oYBRU0IBocQFtDBzVjZAsWZj09QAxRUw5RH10hL1MeUBJcDmksMQEaGF1bJ00eUw5LOVApLgULG1oQBy8ubU8cAlA+QGxSHQ57YjwAMxIZWh1XERo6KB0kTAkUJwxbeWMUBVFOJB0KOXlcDSIrKE8fGVpXPQxYHUoEG1ElNRYrQAMYS0tDLQlZAltAaSNbEg0CRXA3MTYAUhFcByVqMAccAj49QANYAUouRxU3JAdOWh0QEiAjNhxRKEZVPgxZFBlYS1ErYRsHVxZ1ETFiNwoNRRRRJwE9emMDDkExMx1kOhZeBktDKAAaDVgUKgpbHBhRVhUCLRIJQF11ETEJKwMWHj49JQpUEgZRG1klOBYcQFMNQhEmJRYcHkcODgBDIwYQElA2MltHOXpcDSIrKE8QTAkUeG8+BAIYB1BkKFNSDlMTEi0rPQoLHxRQJm8+egYeCFQoYQMCQVMNQjEmJRYcHkdvIDg9emMdBFYlLVMdVgcQX2EnJQQcKUdEYRVbAUN7YjwoLhAPX1NTCiA4ZFJZHFhGZyZfEhgQCEEhM3lnOh9fASAmZAcLHBQJaQZfEhhRClsgYRAGUgEKJCgkICkQHkdACg1eHw5ZSX0xLBIAXBpUMC4lMD8YHkAWYG8+egYeCFQoYRsLUhcQX2EpLA4LTFVaLUVUGwsDUXMtLxcoWgFDFgIiLQMdRBZ8LARTUUN7YjwoLhAPX1NGAy0jIE9ETFJVJRZSeWN4AlNkIhsPQVNRDCVqLB0JTFVaLUVfFgsVS1QqJVMeXwEQHHxqCAAaDVhkJQROFhhRClsgYRodch9ZFCRiJwcYHh0UPQ1SHWB4YjwoLhAPX1NVDCQnPU9ETF1HDAtSHhNZG1k2bVMoXxJXEW8PNx8tCVVZCg1SEAFYYTxNSBoIExZeBywzZAALTFpbPUVxHwsWGBsBMgM6VhJdISkvJwRZGFxRJ28+emN4B1onIB9OVxpDFmF3ZEc6DVlROwQZMCwDClghbyMBQBpECy4kZEJZBEZEZzVYAAMFAloqaF0jUhReCzU/IApzZT09QAxRUw4YGEFkfU5OdR9RBTJkARwJIVVMDQxEB0oFA1AqS3pnOno5Di4pJQNZGFtEGQpEX0oeBWErMVNTEwRfEC0uEAAqD0ZRLAsfGw8QDxsULgAHRxpfDGFhZDkcD0BbO1YZHQ8GQwVoYUNABF8QUmhjTmZwZT09JQpUEgZRCVowERwdH1NfDAMlME9ETENbOwlTJwUiCEchJB1GWwFATBElNwYNBVtaaUgXJQ8SH1o2cl0AVgQYUm1qd0FLQBQEYEw9emN4YjwtJ1MBXSdfEmElNk8WAnZbPUVDGw8fYTxNSHpnOgVRDiguZFJZGEZBLG8+emN4YjwoLhAPX1NYQnxqKQ4NBBpVKxYfEQUFO1o3bypOHlNEDTEaKxxXNR0+QGw+emN4B1onIB9ORFMNQilqbk9JQgEBQ2w+emN4YlkrIhICEwsQX2E+Kx8pA0caEUUaUx1RRBV2S3pnOno5ay0lJw4VTE0UdEVDHBohBEZqGHlnOno5a0hnaU8bA0w+QGw+emN4AlNkBx8PVAAeJzI6BgABTEBcLAs9emN4YjxNSAALR11SDTkFMRtXP11OLEUKUzwUCEErM0FAXRZHSjZmZAdQVxRHLBEZEQUJJEAwbyMBQBpECy4kZFJZOlFXPQpFQUQfDkJsOV9OSloLQjIvMEEbA0x7PBEZJQMCAlcoJFNTEwdCFyRATWZwZT09QBZSB0QTBE1qEhoUVlMNQhcvJxsWHgYaJwBAWx1dS11telMdVgceAC4yaj8WH11AIApZU1dRPVAnNRwcAV1eBzZiPENZFR0PaRZSB0QTBE1qAhwCXAEQX2EpKwMWHg8UOgBDXQgeExsSKAAHUR9VQnxqMB0MCT49QGw+emMUB0YhS3pnOno5a0g5IRtXDltMZzNeAAMTB1BkfFMIUh9DB3pqNwoNQlZbMSpCB0QnAkYtIx8LE04QBCAmNwpzZT09QGw+FgQVYTxNSHpnOl4dQi8rKQpzZT09QGw+GgxRLVklJgBAdgBALCAnIU8NBFFaQ2w+emN4Yjw3JAdAXRJdB28eIRcNTAkUOQlFXS4YGEUoIAogUh5VQi44ZB8VHhp6KAhSeWN4YjxNSHodVgceDCAnIUEpA0ddPQxYHUpMS2MhIgcBQUEeDCQ9bBsWHGRbOktvX0oISxhkcEZHOXo5a0hDTWYKCUAaJwRaFkQyBFkrM1NTExBfDi44f08KCUAaJwRaFkQnAkYtIx8LE04QFjM/IWVwZT09QGxSHxkUYTxNSHpnOnpDBzVkKg4UCRpiIBZeEQYUSwhkJxICQBY6a0hDTWZwCVpQQ2w+emN4YhhpYRcHQAdRDCIvTmZwZT09QAxRUywdClI3bzYdQzdZETUrKgwcTEBcLAs9emN4YjxNSAALR11UCzI+ajscFEAUdEVEBxgYBVJqJxwcXhJESmNvIAJbQBRZKBFfXQwdBFo2aRcHQAcZS0tDTWZwZT09OgBDXQ4YGEFqERwdWgdZDS9qeU8vCVdAJhcFXQQUHB0wLgM+XAAeOm1qPU9STFwUYkUFWmB4YjxNSHpnQBZETCUjNxtXL1tYJhcXTkoSBFkrM0hOQBZETCUjNxtXOl1HIAdbFkpMS0E2NBZkOno5a0hDIQMKCT49QGw+emN4GFAwbxcHQAceNCg5LQ0VCRQJaQNWHxkUYTxNSHpnOhZeBktDTWZwZT0ZZEVfFgsdH11kIxIcOXo5a0hDTQMWD1VYaQ1CHkpMS1YsIAFUdRpeBgcjNhwNL1xdJQF4FSkdCkY3aVEmRh5RDC4jIE1QZj09QGw+egMXS3MoIBQdHTZDEgkvJQMNBBRVJwEXGx8cS0EsJB1kOno5a0hDTQMWD1VYaRVUB0pMS1glNRtAUB9RDzFiLBoUQnxRKAlDG0peS1glNRtAXhJISnBmZAcMARp5KB1/FgsdH11tbVNeH1MBS0tDTWZwZT09JQpUEgZRA01kfFMWE14QVktDTWZwZT09OgBDXQIUClkwKTEJHTVCDSxqeU8vCVdAJhcFXQQUHB0sOV9OSloLQjIvMEERCVVYPQ11FEQlBBV5YSULUAdfEHNkKgoORFxMZUVOU0FRAxx/YQALR11YByAmMAc7CxpiIBZeEQYUSwhkNQEbVnk5a0hDTWZwH1FAZw1SEgYFAxsCMxwDE04QNCQpMAALXhpaLBIfGxJdS0xkalMGE1kQSnBqaU8JD0AdYF4XAA8FRV0hIB8aW11kDWF3ZDkcD0BbO1cZHQ8GQ108bVMXE1gQCmhATWZwZT09QBZSB0QZDlQoNRtAcBxcDTNqeU86A1hbO1YZFRgeBmcDA1tcBkYQT2EnJRsRQlJYJgpFW1hEXhVuYQMNR1ocQiwrMAdXClhbJhcfQV9ESx9kMRAaGl8QVHFjTmZwZT09QGxEFh5fA1AlLQcGHSVZESgoKApZURRAOxBSeWN4YjxNSBYCQBY6a0hDTWZwZUdRPUtfFgsdH11qFxodWhFcB2F3ZAkYAEdRckVEFh5fA1AlLQcGcRQeNCg5LQ0VCRQJaQNWHxkUYTxNSHpnOhZeBktDTWZwZT0ZZEVDAQsSDkdOSHpnOno5CydqAgMYC0caDBZHJxgQCFA2YQcGVh06a0hDTWZwZUdRPUtDAQsSDkdqBwEBXlMNQhcvJxsWHgYaJwBAWykQBlA2IF04WhZHEi44MDwQFlEaEUUYU1hdS3YlLBYcUl1mCyQ9NAALGGddMwAZKkN7YjxNSHpnOgBVFm8+Ng4aCUYaHQoXTkonDlYwLgFcHR1VFWk+Kx8pA0caEUkXCkpaS11tS3pnOno5a0g5IRtXGEZVKgBFXSkeB1o2YU5OUBxcDTNxZBwcGBpAOwRUFhhfPVw3KBECVlMNQjU4MQpzZT09QGw+FgYCDj9NSHpnOno5ESQ+ahsLDVdRO0thGhkYCVkhYU5OVRJcESRATWZwZT09LAtTeWN4YjxNJB0KOXo5a0gvKgtzZT09LAtTeWN4DlsgS3pnWhUQDC4+ZBkYAF1QaRFfFgRRA1wgJDYdQ1tDBzVjZAoXCD49QAwXTkoYSx5kcHlnVh1UaCQkIGVzQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaWVUQRR5BjNyPi8/Pz9pbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcYVkrIhICExVFDCI+LQAXTFNRPS1CHkJYYTwoLhAPX1NTQnxqCAAaDVhkJQROFhhfKF0lMxINRxZCaEg4IRsMHloUKkVWHQ5RCA8CKB0KdRpCETUJLAYVCHtSCglWABlZSX0xLBIAXBpUQGhmZAxzCVpQQ29bHAkQBxUiNB0NRxpfDGE5MA4LGHlbPwBaFgQFJlQtLwcPWh1VEGljTmYQChRgIRdSEg4CRVgrNxZORxtVDGE4IRsMHloULAtTeWMlA0chIBcdHR5fFCRqeU8NHkFRQ2xDAQsSAB0WNB09VgFGCyIvaiccDUZAKwBWB1AyBFsqJBAaGxVFDCI+LQAXRB0+QGxeFUofBEFkFRscVhJUEW8nKxkcTEBcLAsXAQ8FHkcqYRYAV3k5ay0lJw4VTFxBJEUKUw0UH30xLFtHOXo5CydqLBoUTEBcLAs9emN4AlNkBx8PVAAeNSAmLzwJCVFQBgsXBwIUBRUsNB5AZBJcCRI6IQodTAkUDwlWFBlfPFQoKiAeVhZUQiQkIGVwZT1dL0VxHwsWGBsONB4efB0QFikvKk8RGVkaAxBaAzoeHFA2YU5OdR9RBTJkDhoUHGRbPgBFSEoZHlhqFAALeQZdEhElMwoLTAkUPRdCFkoUBVFOSHoLXRc6ayQkIEZQZlFaLW89XkdRAlsiKB0HRxYQCDQnNGUNHlVXIk1iAA8DIls0NAc9VgFGCyIvaiUMAURmLBRCFhkFUXYrLx0LUAcYBDQkJxsQA1ocYG8+GgxRLVklJgBAeh1WKDQnNE8NBFFaQ2w+HwUSCllkKQYDE04QBSQ+DBoURB0+QGxeFUoZHlhkNRsLXVNAASAmKEcfGVpXPQxYHUJYS10xLEktWxJeBSQZMA4NCRxxJxBaXSIEBlQqLhoKYAdRFiQePR8cQn5BJBVeHQ1YS1AqJVpOVh1UaEgvKgtzCVpQYEw9eUdcS1MoOHkCXBBRDmEsKBYvCVg+JQpUEgZRDUAqIgcHXB0QETUrNhs/AE0cYG8+GgxRP102JBIKQF1WDjhqMAccAhRGLBFCAQRRDlsgS3o6WwFVAyU5agkVFRQJaRFFBg97YkElMhhAQANRFS9iIhoXD0BdJgsfWmB4YlkrIhICExtFD21qJwcYHhQJaQJSByIEBh1tS3pnXxxTAy1qLB0JTAkUKg1WAUoQBVFkIhsPQUl2Cy8uAgYLH0B3IQxbF0JTI0ApIB0BWhdiDS4+FA4LGBYdQ2w+BAIYB1BkFRscVhJUEW8sKBZZDVpQaSNbEg0CRXMoODwAExdfaEhDTQcMARgUKg1WAUpMS1IhNTsbXlsZaEhDTQcLHBQJaQZfEhhRClsgYRAGUgEKJCgkICkQHkdACg1eHw5ZSX0xLBIAXBpUMC4lMD8YHkAWYG8+emMYDRUsMwNORxtVDEtDTWZwBVIUJwpDUwwdEmMhLVMaWxZeaEhDTWZwClhNHwBbU1dRIls3NRIAUBYeDCQ9bE07A1BNHwBbHAkYH0xmaHlnOno5aycmPTkcABp5KB1xHBgSDhV5YSULUAdfEHJkKgoORAUYaVQbU1tYSx9keBZXOXo5a0hDIgMAOlFYZzUXTkpIDgFOSHpnOnpWDjgcIQNXOlFYJgZeBxNRVhUSJBAaXAEDTC8vM0dJQBQEZUUHWmB4YjxNSBUCSiVVDm8aJR0cAkAUdEVfARp7YjxNSBYAV3k5a0hDKAAaDVgUJApBFkpMS2MhIgcBQUAeDCQ9bF9VTAQYaVUeeWN4YjwoLhAPX1NTBGF3ZCwYAVFGKEt0NRgQBlBOSHpnOhpWQhQ5IR0wAkRBPTZSARwYCFB+CAAlVgp0DTYkbCoXGVkaAgBOMAUVDhsTaFMaWxZeQiwlMgpZURRZJhNSU0FRCFNqDRwBWCVVATUlNk8cAlA+QGw+egMXS2A3JAEnXQNFFhIvNhkQD1EOABZ8FhM1BEIqaTYARh4eKSQzBwAdCRpnYEVDGw8fS1grNxZODlNdDTcvZEJZD1IaBQpYGDwUCEErM1MLXRc6a0hDTQYfTGFHLBd+HRoEH2YhMwUHUBYKKzIBIRY9A0NaYSBZBgdfIFA9AhwKVl1xS2E+LAoXTFlbPwAXTkocBEMhYV5OUBUeMCgtLBsvCVdAJhcXFgQVYTxNSHoHVVNlESQ4DQEJGUBnLBdBGgkUUXw3ChYXdxxHDGkPKhoUQn9RMCZYFw9fLxxkNRsLXVNdDTcvZFJZAVtCLEUcUwkXRWctJhsaZRZTFi44ZAoXCD49QGw+GgxRPkYhMzoAQwZEMSQ4MgYaCQ59Oi5SCi4eHFtsBB0bXl17BzgJKwscQmdEKAZSWkoFA1AqYR4BRRYQX2EnKxkcTB8UHwBUBwUDWBsqJARGA18QU21qdEZZCVpQQ2w+emMYDRURMhYceh1AFzUZIR0PBVdRcyxEOA8IL1ozL1srXQZdTAovPSwWCFEaBQBRBzkZAlMwaFMaWxZeQiwlMgpZURRZJhNSU0dRPVAnNRwcAF1eBzZidENZXRgUeUwXFgQVYTxNSHoIXwpmBy1kEgoVA1ddPRwXTkocBEMhYVlOdR9RBTJkAgMAP0RRLAE9emN4DlsgS3pnOiFFDBIvNhkQD1EaGwBZFw8DOEEhMQMLV0lnAyg+bEZzZT1RJwE9emMYDRUiLQo4Vh8QFikvKk8fAE1iLAkNNw8CH0crOFtHCFNWDjgcIQNZURRaIAkXFgQVYTxNFRscVhJUEW8sKBZZURRaIAk9eg8fDxxOJB0KOXkdT2EkKwwVBUQ+JQpUEgZRDUAqIgcHXB0QETUrNhs3A1dYIBUfWmB4AlNkFRscVhJUEW8kKwwVBUQUPQ1SHUoDDkExMx1OVh1UaEgeLB0cDVBHZwtYEAYYGxV5YQccRhY6azU4JQwSRGZBJzZSARwYCFBqEgcLQwNVBnsJKwEXCVdAYQNCHQkFAloqaVpkOnpZBGEkKxtZKlhVLhYZPQUSB1w0Dh1ORxtVDGE4IRsMHloULAtTeWN4B1onIB9OUBtREGF3ZCMWD1VYGQlWCg8DRXYsIAEPUAdVEEtDTQYfTFdcKBcXBwIUBT9NSHoIXAEQPW1qNE8QAhRdOQReARlZCF0lM0kpVgd0BzIpIQEdDVpAOk0eWkoVBD9NSHpnWhUQEnsDNy5RTnZVOgBnEhgFSRxkIB0KEwMeISAkBwAVAF1QLEVDGw8fYTxNSHpnQ11zAy8JKwMVBVBRaVgXFQsdGFBOSHpnOhZeBktDTWYcAlA+QGxSHQ57YlAqJVpHORZeBktAaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT0tnaU8pIHVtDDc9XkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZG8aXkoQBUEtbBIIWHlEECApL0c1A1dVJTVbEhMUGRsNJR8LV0lzDS8kIQwNRFJBJwZDGgUfQxxOSBoIEzVcAyY5ai4XGF11Lw4XBwIUBT9NSAMNUh9cSic/KgwNBVtaYUw9emN4B1onIB9ORQYQX2EtJQIcVnNRPTZSARwYCFBsYyUHQQdFAy0fNwoLTh0+QGw+BR9LKFQ0NQYcVjBfDDU4KwMVCUYcYG8+emMHHg8HLRoNWDFFFjUlKl1ROlFXPQpFQUQfDkJsaFpkOnpVDCVjTmYcAlA+LAtTWkN7YRhpYRAbQAdfD2EsKxlZQxRSPAlbERgYDF0wYR4PWh1EAygkIR1zAFtXKAkXAAsHDlECLhRkXxxTAy1qIhoXD0BdJgsXAB4QGUEULRIXVgF9AygkMA4QAlFGYUw9egMXS2EsMxYPVwAeEi0rPQoLTEBcLAsXAQ8FHkcqYRYAV3k5Nik4IQ4dHxpEJQROFhhRVhUwMwYLOXpEECApL0crGVpnLBdBGgkURWchLxcLQSBEBzE6IQtDL1taJwBUB0IXHlsnNRoBXVsZaEhDLQlZAltAaTFfAQ8QD0ZqMR8PShZCQjUiIQFZHlFAPBdZUw8fDz9NSBoIEzVcAyY5aiwMH0BbJCNYBUoFA1AqYQMNUh9cSic/KgwNBVtaYUwXMAscDkclbzUHVh9ULSccLQoOTAkUDwlWFBlfLVoyFxICRhYQBy8ubU8cAlA+QGxeFUo3B1QjMl0oRh9cADMjIwcNTEBcLAs9emN4J1wjKQcHXRQeIDMjIwcNAlFHOkUKU1l7YjxNDRoJWwdZDCZkBwMWD19gIAhSU1dRWgdOSHpnfxpXCjUjKghXKltTDAtTU1dRWlB9S3pnOj9ZBSk+LQEeQnNYJgdWHzkZClErNgBODlNWAy05IWVwZVFaLW8+FgQVQhxOJB0KOXkdT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DOV4dQgYLCSpZQxR5ADZ0eUdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEg9HwUSCllkJwYAUAdZDS9qLgAQAmVBLBBSW0N7YlkrIhICEwFWQnxqIwoNPlFZJhFSW0g8CkEnKR4PWBpeBWNmZE0zA11aGBBSBg9TQj9NKBVOQRUQAy8uZB0fVn1HCE0VIQ8cBEEhBwYAUAdZDS9obU8NBFFaQ2w+AwkQB1lsJwYAUAdZDS9ibU8LCg59JxNYGA8iDkcyJAFGGlNVDCVjTmYcAlA+LAtTeWAdBFYlLVMIRh1TFiglKk8LCVBRLAh0HA4UQ1YrJRZHOXpcDSIrKE8LChQJaQJSBzgUBlowJFtMdxJEA2NmZE0rCVBRLAh0HA4USRxOSBoIEwFWQiAkIE8LCg59OiQfUTgUBlowJDUbXRBECy4kZkZZDVpQaQZYFw9RClsgYVANXBdVQn9qdE8NBFFaQ2w+HwUSCllkLhhCEwFVEWF3ZB8aDVhYYQNCHQkFAloqaVpOQRZEFzMkZB0fVn1aPwpcFjkUGUMhM1sNXBdVS2EvKgtQZj09IAMXHAFRH10hL3lnOnp8CyM4JR0AVnpbPQxRCkIKS2EtNR8LE04QQAIlIApbQBRwLBZUAQMBH1wrL1NTE1FjFyMnLRsNCVAOaUcXXURRCFogJF9OZxpdB2F3ZFtZER0+QGxSHQ57YlAqJXkLXRc6aC0lJw4VTFJBJwZDGgUfS0chMgMPRB1+DTZibWVwAFtXKAkXAQ9RVhUjJAc8Vh5fFiRiZisMCVhHa0kXUTgUGEUlNh0gXAQSS0tDLQlZHlEUKAtTUxgUUXw3AFtMYRZdDTUvARkcAkAWYEVDGw8fYTxNMRAPXx8YBDQkJxsQA1ocYEVFFlA3AkchEhYcRRZCSmhqIQEdRT49LAtTeQ8fDz9OLRwNUh8QBDQkJxsQA1oUOhFWAR4wHkErEAYLRhYYS0tDLQlZOFxGLARTAEQAHlAxJFMaWxZeQjMvMBoLAhRRJwE9ej4ZGVAlJQBAQgZVFyRqeU8NHkFRQ2xDEhkaRUY0IAQAGxVFDCI+LQAXRB0+QGxAGwMdDhUQKQELUhdDTDA/IRocTFVaLUVxHwsWGBsFNAcBYgZVFyRqIABzZT09OQZWHwZZAVotLyIbVgZVS0tDTWYNDUdfZxJWGh5ZXRxOSHoLXRc6a0geLB0cDVBHZxRCFh8USwhkLxoCOXpVDCVjTgoXCD4+ZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQT4ZZEVyIDpROXAKBTY8Ez9/LRFAaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT0s+Ng4aBxxmPAtkFhgHAlYhbyELXRdVEBI+IR8JCVAOCgpZHQ8SHx0iNB0NRxpfDGljTmYJD1VYJU1CAw4QH1ABMgNHOXodT2EMCzlZD11GKglSeWMYDRUCLRIJQF1jCi49AgAPTEBcLAs9emMYDRUqLgdOdwFRFSgkIxxXM2tSJhMXBwIUBT9NSHoqQRJHCy8tN0EmM1JbP0UKUwQUHHE2IAQHXRQYQAIjNgwVCRYYaR4XJwIYCF4qJAAdE04QU21qAgYVAFFQaVgXFQsdGFBoYT0bXiBZBiQ5ZFJZWgAYaSZYHwUDSwhkAhwCXAEDTCc4KwIrK3YceUkFQlpdWQd9aFMTGnk5ayQkIGVwZVhbKgRbUwlRVhUAMxIZWh1XEW8VGwkWGj49QAxRUwlRH10hL3lnOnpTTBMrIAYMHxQJaSNbEg0CRXQtLDUBRSFRBig/N2VwZT1XZzVYAAMFAloqYU5OcBJdBzMrajkQCUNEJhdDIAMLDhVuYUNABnk5a0gpajkQH11WJQAXTkoFGUAhS3pnVh1UaEgvKBwcBVIUDRdWBAMfDEZqHiwIXAUQFikvKmVwZXBGKBJeHQ0CRWobJxwYHSVZESgoKApZURRSKAlEFmB4DlsgSxYAV1oZaEs+Ng4aBxxkJQROFhgCRWUoIAoLQSFVDy48LQEeVndbJwtSEB5ZDUAqIgcHXB0YEi04bWVwAFtXKAkXAA8FSwhkBQEPRBpeBTIRNAMLMT49IAMXAA8FS0EsJB1kOnpWDTNqG0NZCBRdJ0VHEgMDGB03JAdHExdfQigsZAtZGFxRJ0VHEAsdBx0iNB0NRxpfDGljZAtDPlFZJhNSW0NRDlsgaFMLXRcQBy8uTmZwKEZVPgxZFBkqG1k2HFNTEx1ZDktDIQEdZlFaLUweeWBcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaeUdcS2INDzchZFMbQhULBjxzQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaWU1BVZGKBdOXSweGVYhAhsLUBhSDTlqeU8fDVhHLG89HwUSCllkFhoAVxxHQnxqCAYbHlVGMF90AQ8QH1ATKB0KXAQYGUtDEAYNAFEUdEUVISMnKnkXY19kOjVfDTUvNk9ETBZtew4XIAkDAkUwYTEPUBgCICApL01VZj16JhFeFRMiAlEhYU5OESFZBSk+ZkNzZWdcJhJ0BhkFBFgHNAEdXAEQX2E+NhocQD49CgBZBw8DSwhkNQEbVl86awA/MAAqBFtDaVgXBxgEDhlOSCELQBpKAyMmIU9ETEBGPAAbeWMyBEcqJAE8UhdZFzJqeU9IXBg+NEw9eQYeCFQoYScPUQAQX2ExTmY6A1lWKBEXU0pMS2ItLxcBRElxBiUeJQ1RTndbJAdWB0hdSxVkYwAZXAFUEWNjaGVwOl1HPARbAEpRVhUTKB0KXAQKIyUuEA4bRBZiIBZCEgYCSRlkYVELShYSS21ATSIWGlFZLAtDU1dRPFwqJRwZCTJUBhUrJkdbIVtCLAhSHR5TRxVmIBAaWgVZFjhobUNzZWRYKBxSAUpRSwhkFhoAVxxHWAAuIDsYDhwWGQlWCg8DSRlkYVNMRgBVEGNjaGVwK1VZLEUXU0pRVhUTKB0KXAQKIyUuEA4bRBZzKAhSUUZRSxVkYVEeUhBbAyYvZkZVZj13JgtRGg0CSxV5YSQHXRdfFXsLIAstDVYcayZYHQwYDEZmbVNOERdRFiAoJRwcTh0YQ2xkFh4FAlsjMlNTEyRZDCUlM1U4CFBgKAcfUTkUH0EtLxQdEV8QQDIvMBsQAlNHa0wbeWMyGVAgKAcdE1MNQhYjKgsWGw51LQFjEghZSXY2JBcHRwASTmFqZgYXClsWYEk9DmB7RhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXmBcRhUHDj4scicQNgAITkJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xAKAAaDVgUCgpaEQsFJxV5YScPUQAeIS4nJg4NVnVQLSlSFR42GVoxMREBS1sSIygnZkNZTldGJhZEGwsYGRdtSx8BUBJcQgIlKQ0YGGYUdEVjEggCRXYrLBEPR0lxBiUYLQgRGHNGJhBHEQUJQxcHLh4MUgcSTmFoNwcQCVhQa0w9eSkeBlclNT9UchdUNi4tIwMcRBZnIAlSHR4wAlhmbVMVOXpkBzk+ZFJZTmddJQBZB0owAlhmbVMqVhVRFy0+ZFJZClVYOgAbUzgYGF49YU5ORwFFB21ATTsWA1hAIBUXTkpTOVAgKAELUAdDQjUiIU8eDVlRbhYXHB0fS0YsLgdORxwQFikvZBsYHlNRPUsXPw8WAkFkfFMofCUdBSA+IQtXThg+QCZWHwYTClYvYU5OVQZeATUjKwFRGh0UDwlWFBlfOFwoJB0achpdQnxqMlRZBVIUP0VDGw8fS0YwIAEacBxdACA+CQ4QAkBVIAtSAUJYS1AqJVMLXRccaDxjTiwWAVZVPSkNMg4VL0crMRcBRB0YQAAjKSIWCFEWZUVMeWMlDk0wYU5OET5fBiRoaE8vDVhBLBYXTkoKSxcIJBQHR1EcQmMYJQgcThRJZUVzFgwQHlkwYU5OET9VBSg+ZkNzZXdVJQlVEgkaSwhkJwYAUAdZDS9iMkZZKlhVLhYZIAMdDlswExIJVlMNQmk8ZFJETBZmKAJSUUNRDlsgbXkTGnlzDSwoJRs1VnVQLSFFHBoVBEIqaVEvWh54CzUoKxdbQBRPQ2xjFhIFSwhkYzsHRxFfGmNmZDkYAEFROkUKUxFRSX0hIBdMH1MSIC4uPU1ZERgUDQBREh8dHxV5YVEmVhJUQG1ATSwYAFhWKAZcU1dRDUAqIgcHXB0YFGhqAgMYC0caCAxaOwMFCVo8YU5ORVNVDCVmThJQZndbJAdWByZLKlEgEh8HVxZCSmMLLQI/A0IWZUVMeWMlDk0wYU5OETV/NGEYJQsQGUcWZUVzFgwQHlkwYU5OAkIATmEHLQFZURQGeUkXPgsJSwhkdENeH1NiDTQkIAYXCxQJaVUbUzkEDVMtOVNTE1EQEjloaGVwL1VYJQdWEAFRVhUiNB0NRxpfDGk8bU8/AFVTOkt2Ggc3BEMWIBcHRgAQX2E8ZAoXCBg+NEw9MAUcCVQwDUkvVxdjDiguIR1RTnVdJDVFFg5TRxU/S3o6VgtEQnxqZj8LCVBdKhFeHARTRxUAJBUPRh9EQnxqdENZIV1aaVgXQ0ZRJlQ8YU5OAl8QMC4/KgsQAlMUdEUFX2B4P1orLQcHQ1MNQmMGIQ4dTFlbPwxZFEoFCkcjJAcdE1tCAyg5IU8fA0YUCwpAXDkfAkUhM1MeQRxaByI+LQMcHx0aa0k9eikQB1kmIBAFE04QBDQkJxsQA1ocP0wXNQYQDEZqABoDYwFVBigpMAYWAhQJaRMXFgQVRz85aHktXB5SAzUGfi4dCGBbLgJbFkJTKlwpFxodWhFcB2NmZBRzZWBRMREXTkpTPVw3KBECVlNzCiQpL01VTHBRLwRCHx5RVhUwMwYLH3k5ISAmKA0YD18UdEVRBgQSH1wrL1sYGlN2DiAtN0E4BVliIBZeEQYUKF0hIhhODlNGQiQkIENzER0+CgpaEQsFJw8FJRc6XBRXDiRiZi4QAWBRKAgVX0oKYTwQJAsaE04QQBUvJQJZL1xRKg4VX0o1DlMlNB8aE04QFjM/IUNzZXdVJQlVEgkaSwhkJwYAUAdZDS9iMkZZKlhVLhYZMgMcP1AlLDAGVhBbQnxqMk8cAlAYQxgeeSkeBlclNT9UchdUNi4tIwMcRBZnIQpANQUHSRlkOnlnZxZIFmF3ZE09HlVDaSN4JUoyAkcnLRZMH1N0BycrMQMNTAkULwRbAA9dYTwHIB8CURJTCWF3ZAkMAldAIApZWxxYS3MoIBQdHSBYDTYMKxlZURRCaQBZF0Z7FhxOSzABXhFRFhNwBQsdOFtTLglSW0g/BGY0MxYPV1EcQjpATTscFEAUdEUVPQVROEU2JBIKEV8QJiQsJRoVGBQJaQNWHxkURxUWKAAFSlMNQjU4MQpVZj13KAlbEQsSABV5YRUbXRBECy4kbBlQTHJYKAJEXSQeOEU2JBIKE04QFHpqLQlZGhRAIQBZUxkFCkcwAhwDURJELyAjKhsYBVpRO00eUw8fDxUhLxdCOQ4ZaAIlKQ0YGGYOCAFTJwUWDFkhaVEgXCFVAS4jKE1VTE8+QDFSCx5RVhVmDxxOYRZTDSgmZkNZKFFSKBBbB0pMS1MlLQALH3k5ISAmKA0YD18UdEVRBgQSH1wrL1sYGlN2DiAtN0E3A2ZRKgpeH0pMS0N/YRoIEwUQFikvKk8KGFVGPSZYHggQH3glKB0aUhpeBzNibU8cAlAULAtTX2AMQj8HLh4MUgdiWAAuIDsWC1NYLE0VJxgYDFIhMxEBR1EcQjpATTscFEAUdEUVJxgYDFIhMxEBR1EcQgUvIg4MAEAUdEVREgYCDhlkExodWAoQX2E+NhocQD49HQpYHx4YGxV5YVEoWgFVEWE+LApZC1VZLEJEUxkZBFowYRoAQwZEQjYiIQFZFVtBO0VUAQUCGF0lKAFOWgAQDS9qJQFZCVpRJBwZUUZ7YnYlLR8MUhBbQnxqIhoXD0BdJgsfBUNRLVklJgBAZwFZBSYvNg0WGBQJaRMMUwMXS0NkNRsLXVNDFiA4MDsLBVNTLBdVHB5ZQhUhLxdOVh1UTks3bWU6A1lWKBFlSSsVD2YoKBcLQVsSNjMjIyscAFVNa0kXCGB4P1A8NVNTE1FkECgtIwoLTHBRJQROUUZRL1AiIAYCR1MNQnFkdFxVTHldJ0UKU1pdS3glOVNTE0MeV21qFgAMAlBdJwIXTkpDRxUXNBUIWgsQX2FoZBxbQD49CgRbHwgQCF5kfFMIRh1TFiglKkcPRRRyJQRQAEQlGVwjJhYcdxZcAzhqeU8PTFFaLUk9DkN7KFopIxIaYUlxBiUeKwgeAFEcay1eBwgeE3A8MVFCEwg6axUvPBtZURQWAQxDEQUJS3A8MRIAVxZCQG1qAAofDUFYPUUKUwwQB0YhbVM8WgBbG2F3ZBsLGVEYQ2x0EgYdCVQnKlNTExVFDCI+LQAXREIdaSNbEg0CRX0tNREBSzZIEiAkIAoLTAkUP14XGgxRHRUwKRYAEwBEAzM+DAYNDltMDB1HEgQVDkdsaFMLXRcQBy8uaGUERT53JghVEh4jUXQgJSACWhdVEGloDAYNDltMGgxNFkhdS05OSCcLSwcQX2FoDAYNDltMaTZeCQ9TRxUAJBUPRh9EQnxqfENZIV1aaVgXR0ZRJlQ8YU5OAUYcQhMlMQEdBVpTaVgXQ0Z7YnYlLR8MUhBbQnxqIhoXD0BdJgsfBUNRLVklJgBAexpEAC4yFwYDCRQJaRMXFgQVRz85aHlkHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbHlDHlNmKxIfBSMqTGB1C28aXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZQwlYEAsdS2MtMj9ODlNkAyM5ajkQH0FVJRYNMg4VJ1AiNTQcXAZAAC4ybE08P2QWZUUVFhMUSRxOLRwNUh8QNCg5Fk9ETGBVKxYZJQMCHlQoMkkvVxdiCyYiMCgLA0FEKwpPW0gmBEcoJVFCE1FdAzFobWVzOl1HBV92Fw4lBFIjLRZGETZDEgQkJQ0VCVAWZUVMUz4UE0FkfFNMdh1RAC0vZCoqPBYYaSFSFQsEB0FkfFMIUh9DB21ATSwYAFhWKAZcU1dRDUAqIgcHXB0YFGhqAgMYC0caDBZHNgQQCVkhJVNTEwUQBy8uZBJQZmJdOikNMg4VP1ojJh8LG1F1ETEIKxdbQBQUaUUXCEolDk0wYU5OETFfGiQ5ZkNZTBQUaSFSFQsEB0FkfFMaQQZVTmFqBw4VAFZVKg4XTkoXHlsnNRoBXVtGS2EMKA4eHxpxOhV1HBJRVhUyYRYAV1NNS0scLRw1VnVQLTFYFA0dDh1mBAAefRJdB2NmZE9ZTE8UHQBPB0pMSxcKIB4LQFEcQmFqZE89CVJVPAlDU1dRH0cxJF9OEzBRDi0oJQwSTAkULxBZEB4YBFtsN1pOdR9RBTJkARwJIlVZLEUKUxxRDlsgYQ5HOSVZEQ1wBQsdOFtTLglSW0g0GEUMJBICRxsSTmFqP08tCUxAaVgXUSIUClkwKVFCE1MQQgUvIg4MAEAUdEVDAR8URxVkAhICXxFRASpqeU8fGVpXPQxYHUIHQhUCLRIJQF11ETECIQ4VGFwUdEVBUw8fDxU5aHk4WgB8WAAuIDsWC1NYLE0VNhkBL1w3NRIAUBYSTjpqEAoBGBQJaUdzGhkFClsnJFFCE1N0BycrMQMNTAkUPRdCFkZRS3YlLR8MUhBbQnxqIhoXD0BdJgsfBUNRLVklJgBAdgBAJig5MA4XD1EUdEVBUw8fDxU5aHk4WgB8WAAuIDsWC1NYLE0VNhkBP0clIhYcEV8QQjpqEAoBGBQJaUdjAQsSDkc3Y19OE1N0BycrMQMNTAkULwRbAA9dS3YlLR8MUhBbQnxqIhoXD0BdJgsfBUNRLVklJgBAdgBANjMrJwoLTAkUP0VSHQ5RFhxOFxodf0lxBiUeKwgeAFEcayBEAz4UClhmbVNOE1NLQhUvPBtZURQWHQBWHkoyA1AnKlFCEzdVBCA/KBtZURRAOxBSX0pRKFQoLREPUBgQX2EsMQEaGF1bJ01BWko3B1QjMl0rQANkByAnBwccD18UdEVBUw8fDxU5aHk4WgB8WAAuIDwVBVBRO00VNhkBJlQ8BRodR1EcQjpqEAoBGBQJaUd6EhJRL1w3NRIAUBYSTmEOIQkYGVhAaVgXQlpBWxlkDBoAE04QU3F6aE80DUwUdEUEQ1pBRxUWLgYAVxpeBWF3ZF9VTGdBLwNeC0pMSxdkLFFCOXpzAy0mJg4aBxQJaQNCHQkFAloqaQVHEzVcAyY5aioKHHlVMSFeAB5RVhUyYRYAV1NNS0scLRw1VnVQLSlWEQ8dQxcBEiNOcBxcDTNobVU4CFB3JglYAToYCF4hM1tMdgBAIS4mKx1bQBRPQ2xzFgwQHlkwYU5OcBxcDTN5agkLA1lmDicfQ0ZRWQR0bVNcAUoZTmEeLRsVCRQJaUdyIDpRKFooLgFMH3k5ISAmKA0YD18UdEVRBgQSH1wrL1sYGlN2DiAtN0E8H0R3JglYAUpMS0NkJB0KH3lNS0tAEgYKPg51LQFjHA0WB1BsYzUbXx9SECgtLBtbQBRPaTFSCx5RVhVmBwYCXxFCCyYiME1VTHBRLwRCHx5RVhUiIB8dVl86awIrKAMbDVdfaVgXFR8fCEEtLh1GRVoQJC0rIxxXKkFYJQdFGg0ZHxV5YQVVExpWQjdqMAccAhRHPQRFBzodCkwhMz4PWh1EAygkIR1RRRRRJRZSUyYYDF0wKB0JHTRcDSMrKDwRDVBbPhYXTkoFGUAhYRYAV1NVDCVqOUZzOl1HG192Fw4lBFIjLRZGETBFETUlKSkWGhYYaR4XJw8JHxV5YVEtRgBEDSxqAiAvThgUDQBREh8dHxV5YRUPXwBVTktDBw4VAFZVKg4XTkoXHlsnNRoBXVtGS2EMKA4eHxp3PBZDHAc3BENkfFMYCFNZBGE8ZBsRCVoUOhFWAR4hB1Q9JAEjUhpeFiAjKgoLRB0ULAtTUw8fDxU5aHk4WgBiWAAuIDwVBVBRO00VNQUHPVQoNBZMH1NLQhUvPBtZURQWDyphUUZRL1AiIAYCR1MNQnZ6aE80BVoUdEUDQ0ZRJlQ8YU5OAkEATmEYKxoXCF1aLkUKU1pdYTwHIB8CURJTCWF3ZAkMAldAIApZWxxYS3MoIBQdHTVfFBcrKBocTAkUP0VSHQ5RFhxOS15DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhObF5OfjxmJwwPCjtZOHV2Q0gaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRk+JQpUEgZRJloyJD9ODlNkAyM5aiIWGlFZLAtDSSsVD3khJwcpQRxFEiMlPEdbP0RRLAEVX0pTClYwKAUHRwoSS0smKwwYABR5JhNSIUpMS2ElIwBAfhxGBywvKhtDLVBQGwxQGx42GVoxMREBS1sSIyQ4LQ4VThgUawhYBQ9cD1wlJhwAUh8dUGNjTmU0A0JRBV92Fw4lBFIjLRZGESRRDioZNAocCHtaa0kXCEolDk0wYU5OESRRDioZNAocCBYYaSFSFQsEB0FkfFMIUh9DB21ATSwYAFhWKAZcU1dRDUAqIgcHXB0YFGhqAgMYC0caHgRbGDkBDlAgDh1ODlNGWWEjIk8PTEBcLAsXAB4QGUEJLgULXhZeFgwrLQENDV1aLBcfWkoUB0YhYR8BUBJcQil3IwoNJEFZYUwXGgxRAxUwKRYAExseNSAmLzwJCVFQdFQBUw8fDxUhLxdOVh1UQjxjTiIWGlF4cyRTFzkdAlEhM1tMZBJcCRI6IQodThgUMkVjFhIFSwhkYyAeVhZUQG1qAAofDUFYPUUKU1tHRxUJKB1ODlMBVG1qCQ4BTAkUeFcHX0ojBEAqJRoAVFMNQnFmTmY6DVhYKwRUGEpMS1MxLxAaWhxeSjdjZCkVDVNHZzJWHwEiG1AhJVNTEwUQBy8uZBJQZnlbPwB7SSsVD2ErJhQCVlsSKDQnNCAXThgUMkVjFhIFSwhkYzkbXgMQMi49IR1bQBRwLANWBgYFSwhkJxICQBYcaEgJJQMVDlVXIkUKUwwEBVYwKBwAGwUZQgcmJQgKQn5BJBV4HUpMS0N/YRoIEwUQFikvKk8KGFVGPShYBQ8cDlswDBIHXQdRCy8vNkdQTFFaLUVSHQ5RFhxODBwYVj8KIyUuFwMQCFFGYUd9BgcBO1ozJAFMH1NLQhUvPBtZURQWGQpAFhhTRxUAJBUPRh9EQnxqcV9VTHldJ0UKU19BRxUJIAtODlMCV3FmZD0WGVpQIAtQU1dRWxlOSDAPXx9SAyIhZFJZCkFaKhFeHARZHRxkBx8PVAAeKDQnND8WG1FGaVgXBUoUBVFkPFpkOT5fFCQYfi4dCGBbLgJbFkJTIlsiCwYDQ1EcQjpqEAoBGBQJaUd+HQwYBVwwJFMkRh5AQG1qAAofDUFYPUUKUwwQB0YhbXlncBJcDiMrJwRZURRSPAtUBwMeBR0yaFMoXxJXEW8DKgkzGVlEaVgXBUoUBVFkPFpkfhxGBxNwBQsdOFtTLglSW0g3B0wLL1FCEwgQNiQyME9ETBZyJRwXWz0wOHFrEgMPUBYfMSkjIhtQThgUDQBREh8dHxV5YRUPXwBVTmEYLRwSFRQJaRFFBg9dYTwHIB8CURJTCWF3ZAkMAldAIApZWxxYS3MoIBQdHTVcGw4kZFJZGg8UIAMXBUoFA1AqYQAaUgFEJC0zbEZZCVpQaQBZF0oMQj8JLgULYUlxBiUZKAYdCUYcayNbCjkBDlAgY19OSFNkBzk+ZFJZTnJYMEVkAw8UDxdoYTcLVRJFDjVqeU9PXBgUBAxZU1dRWQVoYT4PS1MNQnN/dENZPltBJwFeHQ1RVhV0bXlncBJcDiMrJwRZURRSPAtUBwMeBR0yaFMoXxJXEW8MKBYqHFFRLUUKUxxRDlsgYQ5HOT5fFCQYfi4dCGBbLgJbFkJTJVonLRoefB0STmExZDscFEAUdEUVPQUSB1w0Y19OdxZWAzQmME9ETFJVJRZSX0ojAkYvOFNTEwdCFyRmTmY6DVhYKwRUGEpMS1MxLxAaWhxeSjdjZCkVDVNHZytYEAYYG3oqYU5ORUgQCydqMk8NBFFaaRZDEhgFJVonLRoeG1oQBy8uZAoXCBRJYG89XkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZG8aXkohJ3QdBCFOZzJyaGxnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl46Di4pJQNZPFhVMCkXTkolClc3byMCUgpVEHsLIAs1CVJADhdYBhoTBE1sYyYaWh9ZFjhoaE9bG0ZRJwZfUUN7YWUoIAoiCTJUBhUlIwgVCRwWCAtDGisXABdoYQhOZxZIFmF3ZE04AkBdaSRxOEhdS3EhJxIbXwcQX2EsJQMKCRg+QCZWHwYTClYvYU5OVQZeATUjKwFRGh0UDwlWFBlfKlswKDIIWFMNQjdqIQEdTEkdQzVbEhM9UXQgJTEbRwdfDGkxZDscFEAUdEUVIQ8CG1QzL1MgXAQSTmEeKwAVGF1EaVgXUS4EDlk3e1MHXQBEAy8+ZB0cH0RVPgsVX0o3HlsnYU5OQRZDEiA9KiEWGxRJYG9nHwsIJw8FJRcsRgdEDS9iP08tCUxAaVgXUTgUGFAwYTAGUgFRATUvNk1VTHJBJwYXTkoXHlsnNRoBXVsZaEgmKwwYABRcaVgXFA8FI0ApaVpVExpWQilqMAccAhREKgRbH0IXHlsnNRoBXVsZQilkDAoYAEBcaVgXQ0oUBVFtYRYAV3lVDCVqOUZzZhkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJzQRkUDiR6NkolKndObF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRj8oLhAPX1N3AywvCE9ETGBVKxYZNAscDg8FJRciVhVEJTMlMR8bA0wcayhWBwkZBlQvKB0JEV8QQDI9Kx0dHxYdQwlYEAsdS3IlLBY8E04QNiAoN0E+DVlRcyRTFzgYDF0wBgEBRgNSDTliZj0cG1VGLRYVX0pTG1QnKhIJVlEZaEsNJQIcIA51LQF1Bh4FBFtsOlM6VgtEQnxqZiUWBVoUGBBSBg9TRxUCNB0NE04QCC4jKj4MCUFRaRgeeS0QBlAIezIKVydfBSYmIUdbLUFAJjRCFh8USRlkOlM6VgtEQnxqZi4MGFsUGBBSBg9TRxUAJBUPRh9EQnxqIg4VH1EYQ2x0EgYdCVQnKlNTExVFDCI+LQAXREIdaSNbEg0CRXQxNRw/RhZFB2F3ZBlCTF1SaRMXBwIUBRU3NRIcRzJFFi4bMQoMCRwdaQBZF0oUBVFkPFpkOTRRDyQYfi4dCH1aORBDW0gyBFEhAxwWEV8QGWEeIRcNTAkUazdSFw8UBhUHLhcLEV8QJiQsJRoVGBQJaUcVX0ohB1QnJBsBXxdVEGF3ZE0aA1BRZ0sZUUZRLVwqKAAGVhcQX2E+NhocQD49CgRbHwgQCF5kfFMIRh1TFiglKkcPRRRGLAFSFgcyBFEhaQVHExZeBmE3bWVzQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaWVUQRRnDDFjOiQ2OBUQADFkHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbHkCXBBRDmEHIQEMTAkUHQRVAEQiDkEwKB0JQElxBiUGIQkNK0ZbPBVVHBJZSXwqNRYcVRJTB2NmZE0UA1pdPQpFUUN7YXghLwZUchdUNi4tIwMcRBZnIQpAMB8CH1opAgYcQBxCQG1qP08tCUxAaVgXUSkEGEErLFMtRgFDDTNoaE89CVJVPAlDU1dRH0cxJF9kOjBRDi0oJQwSTAkULxBZEB4YBFtsN1pOfxpSECA4PUEqBFtDChBEBwUcKEA2MhwcE04QFGEvKgtZER0+BABZBlAwD1EAMxweVxxHDGloCgANBVJnIAFSUUZREBUQJAsaE04QQA8lMAYfFRRnIAFSUUZRPVQoNBYdE04QGWFoCAofGBYYaUdlGg0ZHxdkPF9OdxZWAzQmME9ETBZmIAJfB0hdYTwHIB8CURJTCWF3ZAkMAldAIApZWxxYS3ktIwEPQQoKMSQ+CgANBVJNGgxTFkIHQhUhLxdOTlo6LyQkMVU4CFBwOwpHFwUGBR1mBSMnEV8QGWEeIRcNTAkUazB+UzkSClkhY19OZRJcFyQ5ZFJZFxQWflASUUZRSQR0cVZMH1MSU3N/YU1VTBYFfFUSUUoMRxUAJBUPRh9EQnxqZl5JXBEWZW8+MAsdB1clIhhODlNWFy8pMAYWAhxCYEV7GggDCkc9eyALRzdgKxIpJQMcREBbJxBaEQ8DQx0yexQdRhEYQGRvZkNZThYdYEweUw8fDxU5aHkjVh1FWAAuICsQGl1QLBcfWmA8DlsxezIKVz9RACQmbE00CVpBaS5SCggYBVFmaEkvVxd7BzgaLQwSCUYcayhSHR86DkwmKB0KEV8QGWEOIQkYGVhAaVgXUTgYDF0wEhsHVQcSTmEEKzowTAkUPRdCFkZRP1A8NVNTE1FkDSYtKApZIVFaPEcXDkN7JlAqNEkvVxdyFzU+KwFRFxRgLB1DU1dRSWAqLRwPV1EcQhMjNwQATAkUPRdCFkZRLUAqIlNTExVFDCI+LQAXRB0UBQxVAQsDEg8RLx8BUhcYS2EvKgtZER0+QyleERgQGUxqFRwJVB9VKSQzJgYXCBQJaSpHBwMeBUZqDBYARjhVGyMjKgtzZhkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJzQRkUCjdyNyMlOBUQADFkHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbHkCXBBRDmEJNgodTAkUHQRVAEQyGVAgKAcdCTJUBg0vIhs+HltBOQdYC0JTIlsiLgEDUgdZDS9oaE9bBVpSJkceeSkDDlF+ABcKfxJSBy1iZj0wOnV4GkXV8/5RMgcvYSANQRpAFmEIJQwSXnZVKg4VWmAyGVAgezIKVz9RACQmbBRZOFFMPUUKU0g0HVA2OFMIVhJEFzMvZBgLDURHaRFfFkoWClghZgBOXAReQiImLQoXGBRYKBxSAUoeGRUiKAELQFNRQjMvJQNZHlFZJhFSX0oBCFQoLV4JRhJCBiQuak1VTHBbLBZgAQsBSwhkNQEbVlNNS0sJNgodVnVQLSlWEQ8dQxcSJAEdWhxeWGF7al9XXBYdQ28aXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZQ0gaUys1L3oKElNGRxtVDyRqb08aA1pSIAIXAAsHDhooLhIKHBJFFi4mKw4dRT4ZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUZmBcLAhSPgsfClIhM0k9Vgd8CyM4JR0ARHhdKxdWARNYYWYlNxYjUh1RBSQ4fjwcGHhdKxdWARNZJ1wmMxIcSlo6MSA8ISIYAlVTLBcNOg0fBEchFRsLXhZjBzU+LQEeHxwdQzZWBQ88ClslJhYcCSBVFggtKgALCX1aLQBPFhlZEBVmDBYARjhVGyMjKgtbTEkdQzFfFgcUJlQqIBQLQUljBzUMKwMdCUYcazdeBQsdGGx2KlFHOSBRFCQHJQEYC1FGczZSByweB1EhM1tMYRpGAy05HV0SQ1dbJwNeFBlTQj8XIAULfhJeAyYvNlU7GV1YLSZYHQwYDGYhIgcHXB0YNiAoN0E6A1pSIAJEWmAlA1ApJD4PXRJXBzNwBR8JAE1gJjFWEUIlClc3byALRwdZDCY5bWUqDUJRBARZEg0UGQ8ILhIKcgZEDS0lJQs6A1pSIAIfWmB7RhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXmBcRhUHDTYvfVNlLA0FBStzQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaUJUQRkZZEgaXkdcRhhpbF5DHl4dT2xnaWU1BVZGKBdOSSUfPlsoLhIKGxVFDCI+LQAXRB0+QEgaUxkFBEVkIB8CEwdYECQrIBxzZVJbO0VcUwMfS0UlKAEdGydYECQrIBxQTFBbaTFfAQ8QD0YfKi5ODlNeCy1qIQEdZj1yJQRQAEQiAlkhLwcvWh4QX2EsJQMKCQ8UDwlWFBlfJVoXMQELUhcQX2EsJQMKCQ8UDwlWFBlfJVoWJBABWh8QX2EsJQMKCT49DwlWFBlfP0ctJhQLQRFfFmF3ZAkYAEdRckVxHwsWGBsMKAcMXAt1GjErKgscHhQJaQNWHxkUYTwCLRIJQF11ETEPKg4bAFFQaVgXFQsdGFB/YTUCUhRDTAcmPSAXTAkULwRbAA9KS3MoIBQdHT1fAS0jNCAXTAkULwRbAA97YhhpYQELQAdfECRqLAAWB0cUZkVFFhkYEVAgYQMPQQdDaEgsKx1ZMxgULwsXGgRRAkUlKAEdGyFVETUlNgoKRRRQJkVHEAsdBx0iL1pOVh1UaEgsKx1ZHFVGPUkXAAMLDhUtL1MeUhpCEWkvPB8YAlBRLTVWAR4CQhUgLlMeUBJcDmksMQEaGF1bJ00eUwMXS0UlMwdOUh1UQjErNhtXPFVGLAtDUx4ZDltkMRIcR11jCzsvZFJZH11OLEVSHQ5RDlsgaFMLXRc6a2xnZAsLDUNdJwJEeWMSB1AlMzYdQ1sZaEgjIk89HlVDIAtQAEQuNFMrN1MaWxZeQjEpJQMVRFJBJwZDGgUfQxxkBQEPRBpeBTJkGzAfA0IOGwBaHBwUQxxkJB0KGkgQJjMrMwYXC0caFjpRHBxRVhUqKB9OVh1UaEhnaU8aA1paLAZDGgUfGD9NJxwcEywcQiJqLQFZBURVIBdEWykeBVshIgcHXB1DS2EuK08JD1VYJU1RBgQSH1wrL1tHExAKJig5JwAXAlFXPU0eUw8fDxxkJB0KOXodT2E4IRwNA0ZRaQZWHg8DChooKBQGRxpeBUtDNAwYAFgcLxBZEB4YBFtsaFMiWhRYFigkI0E+AFtWKAlkGwsVBEI3YU5ORwFFB2EvKgtQZlFaLUw9eSYYCUclMwpUfRxECyczbBRZOF1AJQAXTkpTOXwSAD89EV8QJiQ5Jx0QHEBdJgsXTkpTJ1olJRYKHVNiCyYiMDwRBVJAaRFYUx4eDFIoJF1MH1NkCywvZFJZWRRJYG8='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2 })
