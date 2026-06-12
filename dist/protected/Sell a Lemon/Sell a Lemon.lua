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

local __k = 'CTt8Ih3RuuFTRsDVPIPn8w0v'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2 })
