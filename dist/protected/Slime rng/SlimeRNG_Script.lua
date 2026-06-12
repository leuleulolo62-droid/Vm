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

local __k = 'JA12Oageik800TDmKUyy6upg'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2 })
