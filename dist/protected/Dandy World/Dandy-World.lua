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

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		-- h = h * 16777619 mod 2^32, done with bit32 to stay 32-bit
		h = (h * 16777619) % 4294967296
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

local __k = 'bhDP26Qaldv5F61RlvBfCnFT'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2 })
