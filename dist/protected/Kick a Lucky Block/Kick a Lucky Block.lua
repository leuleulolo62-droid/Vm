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

local __k = 'BJ57XW1WHCMvCPCDj62jGev4'
local __p = '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wqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSg0kAYGni1pdVoYw45DRYKA0oWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVbW1sg/GnV308Pcodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czPOzsnICwaYxMlI0oLEhFNRVYUYgtAQzcDQzYhLW1WY3BjZEoWEldnAxdYMS8ZPXh3EXcJNjkZCDkgL0oWEkpnRVYUYmoIFz42XSQtb0dWY3BjBR9CXTorBBVRYmoVF3h3EXdofm0QIjwwIUY8EkpnRTdBNiVgRz8lUDMtASEZIDswZFcWVAsrFhMYSGoVF3gWRCMnECgaL3BjZEoWEkpnRVYJYixUWysyHV1oY21WAiU3KyhDSz0iDBFcNjkVF3h3DHcuIiEFJnxJZEoWEisyERl2NzNmRz0yVXdoY21WY21jIgtaQQ9rb1YUYmphZw82XTwNLSwULzUnZEoWEkp6RRBVLjlQG1J3EXdoFx0hIjwoFxpTVw5nRVYUYmoVCnhiAXtCY21WYx4sJwZfQkpnRVYUYmoVF3h3EWpoJSwaMDVvTkoWEkoOCxB+NydFF3h3EXdoY21WY3B+ZAxXXhkiSXwUYmoVdjYjWBYOCG1WY3BjZEoWEkpnWFZSIyZGUnRdTF1CbmBWocTPpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodnmSX1uZIiisEpnLTN4Eg9nZHh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY6/iwVpuaUrUpv6l8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0PI8XgUkBBoUJD9bVCw+XjloJCgCDikTKAVCGkNNRVYUYixaRXgIHXc4LyICYzktZANGUwM1Fl5jLTheRCg2UjJmEyEZNyN5Aw9CcQIuCRJGJyQdHnF3VThCY21WY3BjZEpaXQkmCVZbNSRQRXhqESckLDlMBTktICxfQBkzJh5dLi4dFRcgXzI6YWR8Y3BjZEoWEkouA1ZbNSRQRXg2XzNoLDoYJiJ5DRl3GkgKChJRLmgcFyw/VDlCY21WY3BjZEoWEkpnCRlXIyYVRzQ4RRg/LSgEY21jNAZZRlAAAAJ1Nj5HXjoiRTJgYQIBLTUxZkMWXRhnFRpbNnByUiwWRSM6Ki8DNzVrZjpaUxMiF1QdSGoVF3h3EXdoY21WYzklZBpaXR4IEhhRMGoICngbXjQpLx0aIikmNkR4UwciRRlGYjpZWCwYRjktMW1LfnAPKwlXXjorBA9RMGRgRD0leDNoNyUTLVpjZEoWEkpnRVYUYmoVF3h3QzI8Nj8YYyAvKx48EkpnRVYUYmoVF3h3VDksSW1WY3BjZEoWVwQjb1YUYmpQWTxdEXdoY2BbYxYiKAZUUwksRRRNYi5cRCw2XzQtYzkZYwMzJR1YYgs1EXwUYmoVWzc0UDtoICUXMXB+ZCZZUQsrNRpVOy9HGRs/UCUpIDkTMVpjZEoWXgUkBBoUMCVaQ3hqETQgIj9WIj4nZAleUxh9Ix9aJgxcRSsjcj8hLyleYRg2KQtYXQMjNxlbNhpURSx1GF1oY21WKjZjNgVZRkozDRNaSGoVF3h3EXdoLyIVIjxjKQNYdgM0EVYJYidUQzB5WSIvJkdWY3BjZEoWEgYoBhdYYihQRCwHXTg8Y3BWLTkvTkoWEkpnRVYUJCVHFwd7ESckLDlWKj5jLRpXWxg0TSFbMCFGRzk0VHkYLyICMGoEIR51WgMrAQRRLGIcHngzXl1oY21WY3BjZEoWEkorChVVLmpGRzkgXwcpMTlWfnAzKAVCCCwuCxJyKzhGQxs/WDssa28lMzE0KjpXQB5lTHwUYmoVF3h3EXdoY20fJXAwNAtBXDomFwIUNiJQWVJ3EXdoY21WY3BjZEoWEkpnCRlXIyYVUzEkRXd1Y2UELD83ajpZQQMzDBlaYmcVRCg2RjkYIj8CbQAsNwNCWwUpTFh5Iy1bXiwiVTJCY21WY3BjZEoWEkpnRVYUYiNTFzw+QiNof20bKj4HLRlCEh4vABg+YmoVF3h3EXdoY21WY3BjZEoWEkoqDBhwKzlBF2V3VT47N0dWY3BjZEoWEkpnRVYUYmoVF3h3ETUtMDkmLz83ZFcWQgYoEXwUYmoVF3h3EXdoY21WY3BjIQRSOEpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEg8pAXwUYmoVF3h3ESUtNzgELXAhIRlCYgYoEXwUYmoVUjYzO3doY20EJiQ2NgQWXAMrbxNaJkA/GnV3djI8Yz4ZMSQmIEpaWxkzRRlSYj1QXj8/RSRCLyIVIjxjIh9YUR4uChgUJS9BZDclRTIsFCgfJDg3N0IfOEpnRVZYLSlUW3g7WCQ8Y3BWOC1JZEoWEgwoF1ZaIydQG3gzUCMpYyQYYyAiLRhFGj0iDBFcNjlxViw2HwAtKioeNyNqZA5ZOEpnRVYUYmoVWzc0UDtoNBsXL3B+ZB5ZXB8qBxNGai5UQzl5ZjIhJCUCanAsNkoPC1N+XE8Ne3M/F3h3EXdoY20CIjIvIURfXBkiFwIcLiNGQ3R3SjkpLihWfnAtJQdTHkowAB9TKj4VCnggZzYkb20VLCM3ZFcWVgszBFh3LTlBSnFdEXdoYygYJ1pjZEoWRgslCRMaMSVHQ3A7WCQ8b20QNj4gMANZXEImSVZWa0AVF3h3EXdoYz8TNyUxKkpXHB0iDBFcNmoJFzp5RjIhJCUCSXBjZEpTXA5ub1YUYmpHUiwiQzloLyQFN1omKg48OAYoBhdYYjlaRSwyVQAtKioeNyNjeUpRVx4UCgRAJy5iUjEwWSM7a2R8STwsJwtaEgwyCxVAKyVbFz8yRQAtKioeNx4iKQ9FGkNNRVYUYiZaVDk7ETkpLigFY21jPxc8EkpnRRBbMGpqG3g+RTIlYyQYYzkzJQNEQUI0CgRAJy5iUjEwWSM7am0SLFpjZEoWEkpnRQJVICZQGTE5QjI6N2UYIj0mN0YWWx4iCFhaIydQHlJ3EXdoJiMSSXBjZEpEVx4yFxgULCtYUitdVDksSUcaLDMiKEpFVxk0DBlaFSNbRHhqEWdCLyIVIjxjMBhXWwQQDBhHYncVB1I7XjQpL20dKjMoFwNRXAsrRUsULCNZPTQ4UjYkYyEXMCQILQlddwQjRUsUckBZWDs2XXchMB8TNyUxKgNYVT4oLh9XKRpUU3hqETEpLz4TSVpuaUp0SxomFgUUNiJQFxM+UjwKNjkCLD5jAz9/EgspAVZQKzhQVCw7SHc7NywEN3A3LA8WWQMkDlZZKyRcUDk6VHc+KixWKj43IRhYUwZnCBlQNyZQRFI7XjQpL20QNj4gMANZXEozFx9TJS9HfDE0Wn9hSW1WY3AvKwlXXkokDRdGYncVezc0UDsYLywPJiJtBwJXQAskERNGSGoVF3g+V3cmLDlWazMrJRgWUwQjRRVcIzgbZyo+XDY6Oh0XMSRqZB5eVwRnFxNANzhbFz05VV1oY21WKjZjDwNVWSkoCwJGLSZZUip5eDkFKiMfJDEuIUpCWg8pRQRRNj9HWXgyXzNCY21WYzklZCZZUQsrNRpVOy9HDR8yRRY8Nz8fISU3IUIUYAUyCxJwJyhaQjY0VHVhYzkeJj5JZEoWEkpnRVZGJz5ARTZdEXdoYygYJ1pJZEoWEkdqRT5dJi8VQzAyETApLihRMHAILQldcB8zERlaYjlaFzEjETMnJj4YZCRjLQRCVxghAARRSGoVF3g7XjQpL20+FhRjeUp6XQkmCSZYIzNQRXYHXTYxJj8xNjl5AgNYViwuFwVAASJcWzx/Ex8dB29fSXBjZEpaXQkmCVZfKyledSw5EWpoCxgyYzEtIEp+Zy59Ix9aJgxcRSsjcj8hLyleYRsqJwF0Rx4zChgWa0AVF3h3WDFoKCQVKBI3KkpCWg8pRR1dISF3QzZ5Zz47Ki8aJnB+ZAxXXhkiRRNaJkA/F3h3EXplYwwYIDgsNkpVWgs1BBVAJzgVVjYzESQ8LD1WIj4qKRkWGhkmCBMUIzkVZCw2QyMDKi4dKj4kbWAWEkpnBh5VMGRlRTE6UCUxEywEN34CKgleXRgiAVYJYj5HQj1dEXdoYyQQYzMrJRgMdAMpATBdMDlBdDA+XTNgYQUDLjEtKwNSEENnER5RLEAVF3h3EXdoYyEZIDEvZAtYWwcmERlGYncVVDA2Q3kANiAXLT8qIFBwWwQjIx9GMT52XzE7VX9qAiMfLjE3KxgUG2BnRVYUYmoVFzExETYmKiAXNz8xZB5eVwRNRVYUYmoVF3h3EXdoJSIEYw9vZB5EUwksRR9aYiNFVjElQn8pLSQbIiQsNlBxVx4XCRdNKyRSdjY+XDY8KiIYFyIiJwFFGkNuRRJbSGoVF3h3EXdoY21WY3BjZEpfVEozFxdXKWR7VjUyESl1Y28+LDwnBQRfX0hnER5RLEAVF3h3EXdoY21WY3BjZEoWEkpnRQJGIyleDQsjXidgakdWY3BjZEoWEkpnRVYUYmoVUjYzO3doY21WY3BjZEoWEg8pAXwUYmoVF3h3ETImJ0dWY3BjIQRSOGBnRVYUb2cVZCw2QyNoNyUTYzsqJwFUUxhnMD8+YmoVFyg0UDskaysDLTM3LQVYGkNNRVYUYmoVF3g7XjQpL209KjMoJgtEEldnFxNFNyNHUnAFVCckKi4XNzUnFx5ZQAsgAFh5LS5AWz0kHwIBDyIXJzUxaiFfUQElBAQdSGoVF3h3EXdoCCQVKDIiNlBlRgs1EV4dSGoVF3gyXzNhSUdWY3BjaUcWdgM0BBRYJ2pcWS4yXyMnMTRWFhlJZEoWEhokBBpYaixAWTsjWDgma2R8Y3BjZEoWEkorChVVLmp7Ui8eXyEtLTkZMSljeUpEVxsyDARRahhQRzQ+UjY8JiklNz8xJQ1THCcoAQNYJzkbdDc5RSUnLyETMRwsJQ5TQEQJAAF9LDxQWSw4Qy5hSW1WY3BjZEoWfA8wLBhCJyRBWCouCxMhMCwULzVrbWAWEkpnABhQa0A/F3h3EXplYx4CIiI3ZB5eV0oqDBhdJStYUni1scNoNyUfMHAxIR5DQAQ0RRcUMSNSWTk7ESAtYysfMTVjKAtCVxhnERkUJyRRFzEjO3doY20dKjMoFwNRXAsrRUsUCSNWXBs4XyM6LCEaJiJ5FA9EVAU1CD1dISEdVDA2Q35CJiMSSVpuaUpzXA5nER5RYidcWTEwUDotYy8PMzEwN0pXXA5nFhNaJmpBXz13UjglLiQCYyImKQVCV0ozClZAKi8VRD0lRzI6SSEZIDEvZAxDXAkzDBlaYj5HXj8wVCUNLSk9KjMobAlXQh4yFxNQESlUWz1+O3doY20fJXAtKx4WWQMkDiVdJSRUW3gjWTImYz8TNyUxKkpTXA5Nb1YUYmoYGngRWCUtYzkeJnAwLQ1YUwZnERkUMT5aR3gjWTJoMC4XLzVjKxlVWwYrBAJbMEAVF3h3Wj4rKB4fJD4iKFBwWxgiTV8+SGoVF3g7XjQpL20FIDEvIUoLEgkmFQJBMC9RZDs2XTJoLD9WLjE3LERVXgsqFV5/KyledDc5RSUnLyETMX4QJwtaV0ZnVVoUc2M/PXh3EXdlbm0zLTRjMAJTEgEuBh1WIzgVYhF3UDksYz0aIiljNg9FRwYzRQVbNyRRPXh3EXc4ICwaL3glMQRVRgMoC14dSGoVF3h3EXdoLyIVIjxjDwNVWQgmF1YJYjhQRi0+QzJgESgGLzkgJR5TVjkzCgRVJS8bejczRDstMGMjChwsJQ5TQEQMDBVfICtHHlJ3EXdoY21WYxsqJwFUUxh9IBhQajlWVjQyGF1oY21WJj4nbWA8EkpnRVsZYhlQWTx3RT8tYyYfIDtjJwVbXwMzRQJbYj5dUngkVCU+Jj9WayQrLRkWRhguAhFRMDkVeDYERTY6NwYfIDtjaVQWUwkzEBdYYiFcVDN3QjI5NigYIDVqTkoWEko3BhdYLmJTQjY0RT4nLWVfSXBjZEoWEkpnCRlXIyYVfAsUEWpoMSgHNjkxIUJkVxorDBVVNi9RZCw4QzYvJmM7LDQ2KA9FHDkiFwBdIS9Gezc2VTI6bQYfIDsQIRhAWwkiJhpdJyRBHlJ3EXdoY21WYx4mMB1ZQAFpIx9GJxlQRS4yQ39qCCQVKBU1IQRCEEZnFhVVLi8ZFxMEcnkYJj8VJj43bWAWEkpnABhQa0A/F3h3EXplYxgYIj4gLAVEEgkvBARVIT5QRVJ3EXdoLyIVIjxjJwJXQEp6RTpbIStZZzQ2SDI6bQ4eIiIiJx5TQGBnRVYUKywVVDA2Q3cpLSlWIDgiNkRmQAMqBARNEitHQ3gjWTImSW1WY3BjZEoWUQImF1hkMCNYViouYTY6N2M3LTMrKxhTVkp6RRBVLjlQPXh3EXctLSl8SXBjZEobH0oVAFtRLCtXWz13WDk+JiMCLCI6ZD9/OEpnRVZEIStZW3AxRDkrNyQZLXhqTkoWEkpnRVYULiVWVjR3fzI/CiMAJj43KxhPEldnFxNFNyNHUnAFVCckKi4XNzUnFx5ZQAsgAFh5LS5AWz0kHxQnLTkELDwvIRh6XQsjAAQaDC9CfjYhVDk8LD8PalpjZEoWEkpnRThRNQNbQT05RTg6OnczLTEhKA8eG2BnRVYUJyRRHlJdEXdoYyYfIDsQLQ1YUwZnWFZaKyY/UjYzO10kLC4XL3AlMQRVRgMoC1ZAMh5adTkkVH9hSW1WY3AvKwlXXkoqHCZYLT4VCngwVCMFOh0aLCRrbWAWEkpnDBAULzNlWzcjESMgJiN8Y3BjZEoWEkorChVVLmpGRzkgXwcpMTlWfnAuPTpaXR59Ix9aJgxcRSsjcj8hLyleYQMzJR1YYgs1EVQdSGoVF3h3EXdoLyIVIjxjJwJXQEp6RTpbIStZZzQ2SDI6bQ4eIiIiJx5TQGBnRVYUYmoVFzQ4UjYkYz8ZLCRjeUpVWgs1RRdaJmpWXzklCxEhLSkwKiIwMCleWwYjTVR8NydUWTc+VQUnLDkmIiI3ZkM8EkpnRVYUYmpcUXglXjg8YzkeJj5JZEoWEkpnRVYUYmoVXj53QicpNCMmIiI3ZB5eVwRNRVYUYmoVF3h3EXdoY21WYyIsKx4YcSw1BBtRYncVRCg2RjkYIj8CbRMFNgtbV0psRSBRIT5aRWt5XzI/a31aY2NvZFofOEpnRVYUYmoVF3h3ETIkMCh8Y3BjZEoWEkpnRVYUYmoVFzQ4UjYkYz4aLCQwZFcWXxMXCRlAeAxcWTwRWCU7Nw4eKjwnbEhlXgUzFlQdSGoVF3h3EXdoY21WY3BjZEpaXQkmCVZSKzhGQws7XiNofm0FLz83N0pXXA5nFhpbNjkPcD0jcj8hLykEJj5rbTEHb2BnRVYUYmoVF3h3EXdoY21WKjZjIgNEQR4UCRlAYj5dUjZdEXdoY21WY3BjZEoWEkpnRVYUYmpHWDcjHxQOMSwbJnB+ZAxfQBkzNhpbNmR2cSo2XDJoaG0gJjM3KxgFHAQiEl4EbmoGG3hnGF1oY21WY3BjZEoWEkpnRVYUJyRRPXh3EXdoY21WY3BjZA9YVmBnRVYUYmoVF3h3EXc8Ij4dbSciLR4eA0R1THwUYmoVF3h3ETImJ0dWY3BjIQRSOA8pAXw+b2cVfzklVSApMShWADwqJwEWYQMqEBpVNiNaWXggWCMgYwojCnAqKhlTRkomARxBMT5YUjYjOzsnICwaYzY2KglCWwUpRR5VMC5CVioycjshICZeISQtbWAWEkpnDBAUID5bFzk5VXcqNyNYAjIwKwZDRg8UDAxRYj5dUjZdEXdoY21WY3AvKwlXXkoAEB9nJzhDXjsyEWpoJCwbJmoEIR5lVxgxDBVRamhyQjEEVCU+Ki4TYXlJZEoWEkpnRVZYLSlUW3g+XyQtN2FWHHB+ZC1DWzkiFwBdIS8PcD0jdiIhCiMFJiRrbWAWEkpnRVYUYiZaVDk7EScnMG1LYzI3KkR3UBkoCQNAJxpaRDEjWDgmY2ZWISQtaitUQQUrEAJRESNPUnh4EWVCY21WY3BjZEpaXQkmCVZXLiNWXAB3DHc4LD5YG3BoZANYQQ8zSy4+YmoVF3h3EXckLC4XL3AgKANVWTNnWFZELTkbbnh8ET4mMCgCbQlJZEoWEkpnRVZiKzhBQjk7eDk4Njk7Ij4iIw9ECDkiCxJ5LT9GUhoiRSMnLQgAJj43bAlaWwksPVoUISZcVDMOHXd4b20CMSUmaEpRUwciSVYEa0AVF3h3EXdoYzkXMDttMwtfRkJ3S0YBa0AVF3h3EXdoYxsfMSQ2JQZ/XBoyETtVLCtSUiptYjImJwAZNiMmBh9CRgUpIABRLD4dVDQ+UjwQb20VLzkgLzMaElprRRBVLjlQG3gwUDotb21GalpjZEoWVwQjbxNaJkA/GnV3dzYhLz0ELD8lZChDRh4oC1Z1IT5cQTkjXiVoawsfMTUwZAhZRgJnBhlaLC9WQzE4XyRoIiMSYzgiNg5BUxgiRRVYKyleHlI7XjQpL20QNj4gMANZXEomBgJdNCtBUhoiRSMnLWUUNz5qTkoWEkouA1ZaLT4VVSw5ESMgJiNWMTU3MRhYEg8pAXwUYmoVUTclEQhkYygAJj43CgtbV0ouC1ZdMitcRSt/SnUJIDkfNTE3IQ4UHkplKBlBMS93QiwjXjl5ACEfIDthaEoUfwUyFhN2Nz5BWDZmdTg/LW8LanAnK2AWEkpnRVYUYjpWVjQ7GTE9LS4CKj8tbEM8EkpnRVYUYmoVF3h3Vzg6YxJaYzMsKgQWWwRnDAZVKzhGHz8yRTQnLSMTICQqKwRFGggzCy1RNC9bQxY2XDIVamRWJz9JZEoWEkpnRVYUYmoVF3h3ETQnLSNMBTkxIUIfOEpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEg8pAV8+YmoVFz05VV1oY21WMzMiKAYeVB8pBgJdLSQdHlJ3EXdoY21WYzgiNg5BUxgiJhpdISEdVSw5GF1oY21WJj4nbWBTXA5Nb1sZYqihu7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSgwqiht7rDsbXcw6/iw7LXxIiisojT5ZSg0kAYGni1pdVoYxg/YwMGED9mEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVbW1sg/GnV308Pcodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czPOzsnICwaYwcqKg5ZRUp6RTpdIDhURSFtciUtIjkTFDktIAVBGhETDAJYJ3cXfDE0WncpYwEDIDs6ZChaXQksRQoUG3heFXQUVDk8Jj9LNyI2IUZ3Rx4oNh5bNXdBRS0yTH5CSWBbYwMiIg8WfAUzDBBdIStBXjc5ESA6Ij0GJiJjMAUWQhgiExNaNmoXWzk0Wj4mJG0VIiAiJgNaWx4+RSZYNy1cWXp3UiUpMCUTMFovKwlXXko1BAF6LT5cUSF3DHcEKi8EIiI6aiRZRgMhHHx4KyhHViouHxknNyQQOnB+ZAxDXAkzDBlaajlQWz57EXlmbWR8Y3BjZAZZUQsrRRdGJTkVCngsH3lmPkdWY3BjNAlXXgZvAwNaIT5cWDZ/GF1oY21WY3BjZBhXRSQoER9SO2JGUjQxHXc8Ii8aJn42KhpXUQFvBARTMWMcPXh3EXctLSlfSTUtIGA8XgUkBBoUFitXRHhqESxCY21WYx0iLQQWEkpnRUsUFSNbUzcgCxYsJxkXIXhhBR9CXUoBBARZYGYVFTk0RT4+KjkPYXlvTkoWEkoUDRlEMWoVF3hqEQAhLSkZNGoCIA5iUwhvRyVcLTpGFXR3EXdoYT0XIDsiIw8UG0ZNRVYUYgdcRDt3EXdoY3BWFDktIAVBCCsjASJVIGIXejchVDotLTlUb3BhKQVAV0huSXwUYmoVZD0jRXdoY21WfnAULQRSXR19JBJQFitXH3oEVCM8KiMRMHJvZEhFVx4zDBhTMWgcG1IqO10kLC4XL3AOIQRDdRgoEAYUf2phVjokHwQtNzlMAjQnCA9QRi01CgNEICVNH3oaVDk9YWFUMDU3MANYVRllTHx5JyRAcCo4RCdyAikSASU3MAVYGhETAA5Af2hgWTQ4UDNqbwsDLTN+Ih9YUR4uChgca2p5XjolUCUxeRgYLz8iIEIfEg8pAQsdSAdQWS0QQzg9M3c3JzQPJQhTXkJlKBNaN2pXXjYzE35yAikSCDU6FANVWQ81TVR5JyRAfD0uUz4mJ29aOBQmIgtDXh56RyRdJSJBZDA+VyNqbwMZFhl+MBhDV0YTAA5Af2h4UjYiETwtOi8fLTRhOUM8fgMlFxdGO2RhWD8wXTIDJjQUKj4nZFcWfRozDBlaMWR4UjYiejIxISQYJ1pJEAJTXw8KBBhVJS9HDQsyRRshIT8XMSlrCANUQAs1HF8+EStDUhU2XzYvJj9MEDU3CANUQAs1HF54KyhHViouGF0bIjsTDjEtJQ1TQFAOAhhbMC9hXz06VAQtNzkfLTcwbEM8YQsxADtVLCtSUiptYjI8CioYLCImDQRSVxIiFl5PYAdQWS0cVC4qKiMSYS1qTjlXRA8KBBhVJS9HDQsyRREnLykTMXhhDwNVWSYyBh1NACZaVDN4aGUjYWR8EDE1ISdXXAsgAAQOAD9cWzwUXjkuKiolJjM3LQVYGj4mBwUaES9BQ3FdZT8tLig7Ij4iIw9ECCs3FRpNFiVhVjp/ZTYqMGMlJiQ3bWA8H0dnh+K4oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Xb1sZYqihtXh3ZRYKEG01DB4FDS1jYCsTLDl6YmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEojT53wZb2rXo8y1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1tI/PXV6ERopKiNWFzEhfkp3Rx4oRTBVMCcVcCo4RCcqLDUTMFovKwlXXkoMDBVfACVNF2V3ZTYqMGM7IjktfitSViYiAwJzMCVARzo4SX9qAjgCLHAILQldEEZlBBVAKzxcQyF1GF1CCCQVKBIsPFB3Vg4TChFTLi8dFRkiRTgDKi4dYXw4TkoWEkoTAA5Af2h0Qiw4ERwhICZUb1pjZEoWdg8hBANYNndTVjQkVHtCY21WYxMiKAZUUwksWBBBLClBXjc5GSFhY0dWY3BjZEoWEikhAlh1Nz5afDE0Wmo+Y0dWY3BjZEoWEgMhRQAUNiJQWVJ3EXdoY21WY3BjZEpFVxk0DBlaFSNbRHhqEWdCY21WY3BjZEpTXA5NRVYUYi9bU3RdTH5CSQYfIDsBKxIMcw4jIQRbMi5aQDZ/ExwhICYmJiIlIQlCWwUpR1oUOUAVF3h3ZzYkNigFY21jP0oUdQUoAVYcenoYDm1yGHVkY28yJjMmKh4WGlx3SE4EZ2MXG3h1YTI6JSgVN3BrdVoGF0pqRQRdMSFMHnp7EXUaIiMSLD1jbF4GH1t3VVMdYGpIG1J3EXdoBygQIiUvMEoLEltrb1YUYmp4QjQjWHd1YysXLyMmaGAWEkpnMRNMNmoIF3ocWDQjYx0TMTYmJx5fXQRnKRNCJyYXG1IqGF1CCCQVKBIsPFB3Vg4DFxlEJiVCWXB1YjI7MCQZLQQiNg1TRkhrRQ0+YmoVFw42XSItMG1LYytjZiNYVAMpDAJRYGYVFWl1HXdqdm9aY3JydEgaEkh1UFQYYmgAB3p7EXV5c31UYy1vTkoWEkoDABBVNyZBF2V3AHtCY21WYx02KB5fEldnAxdYMS8ZPXh3EXccJjUCY21jZjlTQRkuChgWbkBIHlJdHHpoAjgCLHAXNgtfXEoAFxlBMihaT1I7XjQpL20iMTEqKihZSkp6RSJVIDkbejk+X20JJyk6JjY3AxhZRxolCg4cYAtAQzd3ZSUpKiNUb3I5JRoUG2BNMQRVKyR3WCBtcDMsFyIRJDwmbEh3Rx4oMQRVKyQXGyNdEXdoYxkTOyR+ZitDRgVnMQRVKyQVHw8yWDAgNz5fYXxJZEoWEi4iAxdBLj4IUTk7QjJkSW1WY3AAJQZaUAskDktSNyRWQzE4X38+am18Y3BjZEoWEkoEAxEaAz9BWAwlUD4mfjtWSXBjZEoWEkpnDBAUNGpBXz05O3doY21WY3BjZEoWEh41BB9aFSNbRHhqEWdCY21WY3BjZEpTXA5NRVYUYi9bU3RdTH5CSRkEIjktBgVOCCsjASJbJS1ZUnB1cCI8LA4aKjMoHFgUHhFNRVYUYh5QTyxqExY9NyJWADwqJwEWSlhnJxlaNzkXG1J3EXdoBygQIiUvMFdQUwY0AFo+YmoVFxs2XTsqIi4dfjY2KglCWwUpTQAdYglTUHYWRCMnACEfIDsbdldAEg8pAVo+P2M/PQwlUD4mASIOeREnIC5EXRojCgFaamhhRTk+XwQtMD4fLD5haEpNOEpnRVZiIyZAUit3DHczY28/LTYqKgNCV0hrRVQFcmgZF3piAXVkY29Hc2BhaEoUAF93R1oUYH8FB3p7EXV5c31GYXA+aGAWEkpnIRNSIz9ZQ3hqEWZkSW1WY3AOMQZCW0p6RRBVLjlQG1J3EXdoFygON3B+ZEhiQAsuC1ZgIzhSUix1HV01akd8bn1jBR9CXUoUABpYYg1HWC0nUzgwSSEZIDEvZDlTXgYFCg4Uf2phVjokHxopKiNMAjQnCA9QRi01CgNEICVNH3oWRCMnYx4TLzxhaEoUVgUrCRdGbzlcUDZ1GF1CECgaLxIsPFB3Vg4TChFTLi8dFRkiRTgbJiEaYXw4TkoWEkoTAA5Af2h0Qiw4EQQtLyFWASIiLQREXR40R1o+YmoVFxwyVzY9LzlLJTEvNw8aOEpnRVZ3IyZZVTk0WmouNiMVNzksKkJAG0oEAxEaAz9BWAsyXTt1NW0TLTRvThcfOGAUABpYACVNDRkzVRM6LD0SLCctbEhlVwYrKBNAKiVRFXR3Sl1oY21WFTEvMQ9FEldnHlYWES9ZW3gWXTtqb21UEDUvKEp3XgZnJw8UECtHXiwuE3toYR4TLzxjFwNYVQYiR1ZJbkAVF3h3dTIuIjgaN3B+ZFsaOEpnRVZ5NyZBXnhqETEpLz4Tb1pjZEoWZg8/EVYJYmhmUjQ7ERotNyUZJ3JvThcfOGBqSFZ1Nz5aFwg7UDQtY2tWFiAkNgtSV0oAFxlBMihaT3h/Yz4vKzlfSTwsJwtaEj83AgRVJi93WCB3DHccIi8FbR0iLQQMcw4jNx9TKj5yRTciQTUnO2VUAiU3K0pmXgskAFYSYh9FUCo2VTJqb21UIiIxKx0bRxpqBh9GISZQFXFdOwI4JD8XJzUBKxIMcw4jMRlTJSZQH3oWRCMnEyEXIDVhaBE8EkpnRSJROj4IFRkiRThoEyEXIDVjBhhXWwQ1CgJHYGY/F3h3ERMtJSwDLyR+IgtaQQ9rb1YUYmp2VjQ7UzYrKHAQNj4gMANZXEIxTFZ3JC0bdi0jXgckIi4TfiZjIQRSHmA6THw+FzpSRTkzVBUnO3c3JzQXKw1RXg9vRzdBNiVgRz8lUDMtASEZIDswZkZNOEpnRVZgJzJBCnoWRCMnYxgGJCIiIA8WYgYmBhNQYghHVjE5Qzg8MG9aSXBjZEpyVwwmEBpAfyxUWysyHV1oY21WADEvKAhXUQF6AwNaIT5cWDZ/R35oACsRbRE2MAVjQg01BBJRACZaVDMkDCFoJiMSb1o+bWA8XgUkBBoUMSZaQysbWCQ8Y3BWOHBhBQZaEEo6bxBbMGpcF2V3AHtocH1WJz9JZEoWEh4mBxpRbCNbRD0lRX87LyICMBwqNx4aEkgUCRlAYmgVGXZ3WH5CJiMSSVoWNA1EUw4iJxlMeAtRUxwlXicsLDoYa3IWNA1EUw4iMRdGJS9BFXR3Sl1oY21WFTEvMQ9FEldnFhpbNjl5XisjHV1oY21WBzUlJR9aRkp6RUcYSGoVF3gaRDs8Km1LYzYiKBlTHmBnRVYUFi9NQ3hqEXUKMSwfLSIsMEpCXUoSFRFGIy5QFXRdTH5CSWBbYwMrKxpFEj4mB3xYLSlUW3gEWTg4ASIOY21jEAtUQUQUDRlEMXB0UzwbVDE8BD8ZNiAhKxIeECsyERkUESJaR3p7EycpICYXJDVhbWBlWgU3JxlMeAtRUww4VjAkJmVUAiU3KyhDSz0iDBFcNjkXGyNdEXdoYxkTOyR+ZitDRgVnJwNNYghQRCx3ZjIhJCUCMHJvTkoWEkoDABBVNyZBCj42XSQtb0dWY3BjBwtaXggmBh0JJD9bVCw+XjlgNWRWADYkaitDRgUFEA9jJyNSXywkDCFoJiMSb1o+bWBlWgU3JxlMeAtRUww4VjAkJmVUAiU3KyhDSzk3ABNQYGZOPXh3EXccJjUCfnICMR5ZEigyHFZnMi9QU3gCQTA6IikTMHJvTkoWEkoDABBVNyZBCj42XSQtb0dWY3BjBwtaXggmBh0JJD9bVCw+XjlgNWRWADYkaitDRgUFEA9nMi9QU2UhETImJ2F8PnlJTgZZUQsrRTNFNyNFdTcvEWpoFywUMH4QLAVGQVAGARJ4JyxBcCo4RCcqLDVeYRUyMQNGEj0iDBFcNjkXG3okWT4tLylUaloGNR9fQigoHUx1Ji5xRTcnVTg/LWVUDCctIQ5hVwMgDQJHYGYVTFJ3EXdoFSwaNjUwZFcWSUplMhlbJi9bFwsjWDQjYW0Lb1pjZEoWdg8hBANYNmoIF2l7O3doY207Njw3LUoLEgwmCQVRbkAVF3h3ZTIwN21LY3IQIQZTUR5nNQNGISJURD0zEQAtKioeN3JvThcfOC82EB9EACVNDRkzVRU9NzkZLXg4EA9ORldlIAdBKzoVZD07VDQ8JilWFDUqIwJCEEZnIwNaIWoIFz4iXzQ8KiIYa3lJZEoWEgYoBhdYYjlQWz00RTIsY3BWDCA3LQVYQUQIEhhRJh1QXj8/RSRmFSwaNjVJZEoWEgMhRQVRLi9WQz0zETYmJ20FJjwmJx5TVko5WFYWDCVbUnp3RT8tLUdWY3BjZEoWEhokBBpYaixAWTsjWDgma2R8Y3BjZEoWEkpnRVYUDC9BQDclWnkOKj8TEDUxMg9EGkgQAB9TKj5wRi0+QXVkYz4TLzUgMA9SG2BnRVYUYmoVF3h3EXcEKi8EIiI6fiRZRgMhHF4WBztAXignVDNoFCgfJDg3fkoUEkRpRQVRLi9WQz0zGF1oY21WY3BjZA9YVkNNRVYUYi9bU1IyXzM1akd8Lz8gJQYWfwspEBdYESJaRxo4SXd1YxkXISNtFwJZQhl9JBJQECNSXywQQzg9My8ZO3hhCQtYRwsrRSZBMCldVisyE3tqMCUZMyAqKg0bUQs1EVQdSCZaVDk7ESAtKioeNx4iKQ9FEldnAhNAFS9cUDAjfzYlJj5ealpJCQtYRwsrNh5bMghaT2IWVTMMMSIGJz80KkIUYQIoFSFRKy1dQ3p7ESxCY21WYwYiKB9TQUp6RQFRKy1dQxY2XDI7b0dWY3BjAA9QUx8rEVYJYnsZPXh3EXcFNiECKnB+ZAxXXhkiSXwUYmoVYz0vRXd1Y28lJjwmJx4WZQ8uAh5AYj5aFxoiSHVkSTBfSVoOJQRDUwYUDRlEACVNDRkzVRU9NzkZLXg4EA9ORldlJwNNYhlQWz00RTIsYxoTKjcrMEgaEiwyCxUUf2pTQjY0RT4nLWVfSXBjZEpaXQkmCVZHJyZQVCwyVXd1YwIGNzksKhkYYQIoFSFRKy1dQ3YBUDs9JkdWY3BjLQwWQQ8rABVAJy4VQzAyX11oY21WY3BjZBpVUwYrTRBBLClBXjc5GX5CY21WY3BjZEoWEkpnKxNANSVHXHYRWCUtECgENTUxbEhlWgU3OjRBO2gZF3oAVD4vKzklKz8zZkYWQQ8rABVAJy4cPXh3EXdoY21WY3BjZCZfUBgmFw8ODCVBXj4uGXUKLDgRKyRjEw9fVQIzX1YWYmQbFysyXTIrNygSalpjZEoWEkpnRRNaJmM/F3h3ETImJ0cTLTQ+bWA8fwspEBdYESJaRxo4SW0JJykyMT8zIAVBXEJlNh5bMhlFUj0zcDonNiMCYXxjP2AWEkpnMxdYNy9GF2V3SndqaHxWECAmIQ4UHkplTkAUETpQUjx1HXdqaHxEYwMzIQ9SEEo6SXwUYmoVcz0xUCIkN21LY2FvTkoWEkoKEBpAK2oIFz42XSQtb0dWY3BjEA9ORkp6RVRnJyZQVCx3YictJilWNz9jBh9PEEZNGF8+SAdUWS02XQQgLD00LCh5BQ5ScB8zERlaajFhUiAjDHUKNjRWEDUvIQlCVw5nNgZRJy4XG3gRRDkrY3BWJSUtJx5fXQRvTHwUYmoVWzc0UDtoMCgaJjM3IQ4WD0oIFQJdLSRGGQs/XicbMygTJxEuKx9YRkQRBBpBJ0AVF3h3XTgrIiFWIj0sMQRCEldnVHwUYmoVXj53QjIkJi4CJjRjeVcWEEFxRSVEJy9RFXgjWTImSW1WY3BjZEoWUwcoEBhAYncVAVJ3EXdoJiEFJjklZBlTXg8kERNQYncIF3p8AGVoED0TJjRhZB5eVwRNRVYUYmoVF3g2XDg9LTlWfnBydmAWEkpnABhQSGoVF3gnUjYkL2UQNj4gMANZXEJub1YUYmoVF3h3YictJiklJiI1LQlTcQYuABhAeBhQRi0yQiMdMyoEIjQmbAtbXR8pEV8+YmoVF3h3EXcEKi8EIiI6fiRZRgMhHF4WEj9HVDA2QjIsY29WbX5jNw9aVwkzABIUbGQVFXl1GF1oY21WJj4nbWBTXA46THw+b2cVejchVDotLTlWFzEhTgZZUQsrRTtbNC95F2V3ZTYqMGM7KiMgfitSViYiAwJzMCVARzo4SX9qDiIAJj0mKh4UHkgqCgBRYGM/PRU4RzIEeQwSJwQsIw1aV0JlMSZjIyZecjY2UzstJ29aYytJZEoWEj4iHQIUf2oXYwh3ZjYkKG9aSXBjZEpyVwwmEBpAYncVUTk7QjJkSW1WY3AAJQZaUAskDlYJYixAWTsjWDgmaztfYxMlI0RiYj0mCR1xLCtXWz0zEWpoNW0TLTRvThcfOGArChVVLmphZwcEXT4sJj9WfnAOKxxTflAGARJnLiNRUip/EwMYFCwaKAMzIQ9SEEZnHnwUYmoVYz0vRXd1Y28iE3AUJQZdEjk3ABNQYGY/F3h3ERohLW1LY2F1aGAWEkpnKBdMYncVBGhnHV1oY21WBzUlJR9aRkp6RUMEbkAVF3h3Yzg9LSkfLTdjeUoGHmA6THxgEhVmWzEzVCVyDCM1KzEtIw9SGgwyCxVAKyVbHy5+ERQuJGMiEwciKAFlQg8iAVYJYjwVUjYzGF1CDiIAJhx5BQ5SZgUgAhpRamh8WT4dRDo4YWENFzU7MFcUewQhDBhdNi8VfS06QXVkBygQIiUvMFdQUwY0AFp3IyZZVTk0WmouNiMVNzksKkJAG0oEAxEaCyRTfS06QWo+YygYJy1qTidZRA8LXzdQJh5aUD87VH9qDSIVLzkzZkZNZg8/EUsWDCVWWzEnE3sMJisXNjw3eQxXXhkiSTVVLiZXVjs8DDE9LS4CKj8tbBwfEikhAlh6LSlZXihqR3ctLSkLaloOKxxTflAGARJgLS1SWz1/ExYmNyQ3BRthaBFiVxIzWFR1LD5cFxkRenVkBygQIiUvMFdQUwY0AFp3IyZZVTk0WmouNiMVNzksKkJAG0oEAxEaAyRBXhkRemo+YygYJy1qTmBaXQkmCVZ5LTxQZXhqEQMpIT5YDjkwJ1B3Vg4VDBFcNg1HWC0nUzgwa28iJjwmNAVERhllSVRTLiVXUnp+OxonNSgkeREnIChDRh4oC15PFi9NQ2V1ZQdoNyJWDz8hJhMUHkoBEBhXfyxAWTsjWDgma2R8Y3BjZAZZUQsrRRVcIzgVCngbXjQpLx0aIikmNkR1Wgs1BBVAJzg/F3h3ET4uYy4eIiJjJQRSEgkvBAQOBCNbUx4+QyQ8ACUfLzRrZiJDXwspCh9QECVaQwg2QyNqam0CKzUtTkoWEkpnRVYUISJURXYfRDopLSIfJwIsKx5mUxgzSzVyMCtYUnhqERQOMSwbJn4tIR0eBVhxSVYHbmoHA2l+O3doY21WY3BjCANUQAs1HEx6LT5cUSF/EwMtLygGLCI3IQ4WRgVnKRlWIDMUFXFdEXdoYygYJ1omKg5LG2AKCgBREHB0UzwVRCM8LCNeOAQmPB4LED4XRQJbYgFcVDN3YTYsYWFWBSUtJ1dQRwQkER9bLGIcPXh3EXckLC4XL3AgLAtEEldnKRlXIyZlWzkuVCVmACUXMTEgMA9EOEpnRVZdJGpWXzklETYmJ20VKzExfixfXA4BDARHNgldXjQzGXUANiAXLT8qIDhZXR4XBARAYGMVQzAyX11oY21WY3BjZAleUxhpLQNZIyRaXjwFXjg8EywEN34AAhhXXw9nWFZjLTheRCg2UjJmAj8TIiNtDwNVWTgiBBJNbAlzRTk6VHdjYxsTICQsNlkYXA8wTUYYYnkZF2h+O3doY21WY3BjCANUQAs1HEx6LT5cUSF/EwMtLygGLCI3IQ4WRgVnLh9XKWplVjx2E35CY21WYzUtIGBTXA46THx5LTxQZWIWVTMKNjkCLD5rPz5TSh56RyJkYj5aFw8yWDAgN20lKz8zZkYWdB8pBktSNyRWQzE4X39hSW1WY3AvKwlXXkokDRdGYncVezc0UDsYLywPJiJtBwJXQAskERNGSGoVF3g+V3crKywEYzEtIEpVWgs1XzBdLC5zXiokRRQgKiESa3ILMQdXXAUuASRbLT5lViojE35oIiMSYwcsNgFFQgskAFhnKiVFRGIRWDksBSQEMCQALANaVkJlMhNdJSJBZDA4QXVhYzkeJj5JZEoWEkpnRVZXKitHGRAiXDYmLCQSET8sMDpXQB5pJjBGIydQF2V3Zjg6KD4GIjMmajleXRo0SyFRKy1dQws/XidyBCgCEzk1Kx4eG0psRSBRIT5aRWt5XzI/a31aY2NvZFofOEpnRVYUYmoVezE1QzY6Onc4LCQqIhMeED4iCRNELThBUjx3RThoFCgfJDg3ZDleXRpmR18+YmoVFz05VV0tLSkLaloOKxxTYFAGARJ2Nz5BWDZ/SgMtOzlLYQQTZB5ZEjkiCRoUEitRFXR3dyImIHAQNj4gMANZXEJub1YUYmpZWDs2XXcrKywEY21jCAVVUwYXCRdNJzgbdDA2QzYrNygESXBjZEpfVEokDRdGYitbU3g0WTY6eQsfLTQFLRhFRikvDBpQamh9QjU2XzghJx8ZLCQTJRhCEENnBBhQYh1aRTMkQTYrJncwKj4nAgNEQR4EDR9YJmIXZD07XXVhYzkeJj5JZEoWEkpnRVZXKitHGRAiXDYmLCQSET8sMDpXQB5pJjBGIydQF2V3Zjg6KD4GIjMmajlTXgZ9IhNAEiNDWCx/GHdjYxsTICQsNlkYXA8wTUYYYnkZF2h+O3doY21WY3BjCANUQAs1HEx6LT5cUSF/EwMtLygGLCI3IQ4WRgVnNhNYLmplVjx2E35CY21WYzUtIGBTXA46THw+b2cV1czb08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN611czX08PIodn2ocTDpv620P7Hh+K0oN6lPXV6EbXcwW1WAREADy1kfT8JIVZ4DQVlZHh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYqihtVJ6HHeq19mU19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pdeq182U19Ch0OrUpuql8fbW1srXo9i1pc9CSWBbYxE2MAUWZhgmDBgUDiVaR3h/dCY9Kj0FYzImNx4WRQ8uAh5AYitbU3gjQzYhLT5fSSQiNwEYQRomEhgcJD9bVCw+XjlgakdWY3BjMwJfXg9nEQRBJ2pRWFJ3EXdoY21WYzklZClQVUQGEAJbFjhUXjZ3RT8tLUdWY3BjZEoWEkpnRVZYLSlUW3g1UDQjMywVKHB+ZCZZUQsrNRpVOy9HDR4+XzMOKj8FNxMrLQZSGkgFBBVfMitWXHp+O3doY21WY3BjZEoWEgYoBhdYYildVip3DHcELC4XLwAvJRNTQEQEDRdGIylBUipdEXdoY21WY3BjZEoWOEpnRVYUYmoVF3h3EXplYwsfLTRjJg9FRkooEhhRJmpCUjEwWSNoNyIZL3AqKkpUUwksFRdXKWpaRXgyQCIhMz0TJ1pjZEoWEkpnRVYUYmpZWDs2XXcqJj4CFz8sKEoLEgQuCXwUYmoVF3h3EXdoY20aLDMiKEpeWw0vAAVAFS9cUDAjZzYkY3BWbmFJZEoWEkpnRVYUYmoVPXh3EXdoY21WY3BjZAZZUQsrRRBBLClBXjc5ETQgJi4dFz8sKEJCG2BnRVYUYmoVF3h3EXdoY21WKjZjMFB/QStvRyJbLSYXHng2XzNoN3c+IiMXJQ0eEDk2EBdAFiVaW3p+ESMgJiN8Y3BjZEoWEkpnRVYUYmoVF3h3EXckLC4XL3A0AAtCU0p6RSFRKy1dQysTUCMpbRoTKjcrMBltRkQJBBtRH0AVF3h3EXdoY21WY3BjZEoWEkpnRRpbIStZFy8BUDtofm0BBzE3JUpXXA5nEjJVNisbYD0+Vj88YyIEY2BJZEoWEkpnRVYUYmoVF3h3EXdoY20fJXA0EgtaElRnDR9TKi9GQw8yWDAgNxsXL3A3LA9YOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEgIuAh5RMT5iUjEwWSMeIiFWfnA0EgtaOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEggiFgJgLSVZF2V3RV1oY21WY3BjZEoWEkpnRVYUYmoVFz05VV1oY21WY3BjZEoWEkpnRVYUJyRRPXh3EXdoY21WY3BjZA9YVmBnRVYUYmoVF3h3EXdCY21WY3BjZEoWEkpnDBAUICtWXCg2UjxoNyUTLVpjZEoWEkpnRVYUYmoVF3h3Vzg6YxJaYyRjLQQWWxomDARHaihUVDMnUDQjeQoTNxMrLQZSQA8pTV8dYi5aFzs/VDQjFyIZL3g3bUpTXA5NRVYUYmoVF3h3EXdoJiMSSXBjZEoWEkpnRVYUYiNTFzs/UCVoNyUTLVpjZEoWEkpnRVYUYmoVF3h3Vzg6YxJaYyRjLQQWWxomDARHaildViptdjI8ACUfLzQxIQQeG0NnARkUISJQVDMDXjgkazlfYzUtIGAWEkpnRVYUYmoVF3gyXzNCY21WY3BjZEoWEkpnb1YUYmoVF3h3EXdoY2BbYxUyMQNGEggiFgIUNiVaW3g+V3cmLDlWIjwxIQtSS0oiFANdMjpQU1J3EXdoY21WY3BjZEpfVEolAAVAFiVaW3g2XzNoICUXMXA3LA9YOEpnRVYUYmoVF3h3EXdoY20fJXAhIRlCZgUoCVhkIzhQWSx3T2poICUXMXA3LA9YOEpnRVYUYmoVF3h3EXdoY21WY3BjKAVVUwZnDQNZYncVVDA2Q20OKiMSBTkxNx51WgMrATlSASZURCt/Ex89LiwYLDknZkM8EkpnRVYUYmoVF3h3EXdoY21WY3AqIkpeRwdnER5RLEAVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpdQjVtZDktMjgfMwQsKwZFGkNNRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnERdHKWRCVjEjGWdmcmR8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WITUwMD5ZXQZpNRdGJyRBF2V3Uj8pMUdWY3BjZEoWEkpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEkpnRVYUYmoVUjYzO3doY21WY3BjZEoWEkpnRVY+YmoVF3h3EXdoY21WY3BjZEcbEj41BB9abRlEQjkjEF1oY21WY3BjZEoWEkpnRVYULiVWVjR3RSUpKiMlNjMgIRlFEldnAxdYMS8/F3h3EXdoY21WY3BjZEoWEhokBBpYaixAWTsjWDgma2R8Y3BjZEoWEkpnRVYUYmoVF3h3EXcqJj4CFz8sKFB3UR4uExdAJ2IcPXh3EXdoY21WY3BjZEoWEkpnRVYUNjhUXjYERDQrJj4FY21jMBhDV2BnRVYUYmoVF3h3EXdoY21WJj4nbWAWEkpnRVYUYmoVF3h3EXdoSW1WY3BjZEoWEkpnRVYUYmpcUXgjQzYhLR4DIDMmNxkWRgIiC3wUYmoVF3h3EXdoY21WY3BjZEoWEh41BB9aFSNbRHhqESM6IiQYFDktN0odEltNRVYUYmoVF3h3EXdoY21WY3BjZEpaXQkmCVZYKydcQwsjQ3d1YwIGNzksKhkYZhgmDBhnJzlGXjc5HwEpLzgTYz8xZEh/XAwuCx9AJ2g/F3h3EXdoY21WY3BjZEoWEkpnRVZdJGpZXjU+RQQ8MW0IfnBhDQRQWwQuERMWYj5dUjZdEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3XTgrIiFWLzkuLR4WD0ozChhBLyhQRXA7WDohNx4CMXlJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjLQwWXgMqDAIUIyRRFywlUD4mFCQYMHB9eUpaWwcuEVZAKi9bPXh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXcLJSpYAiU3Kz5EUwMpRUsUJCtZRD1dEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYz0VIjwvbAxDXAkzDBlaamMVYzcwVjstMGM3NiQsEBhXWwR9NhNAFCtZQj1/VzYkMChfYzUtIEM8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRTpdIDhURSFtfzg8KisPa3IXNgtfXEozBARTJz4VRT02Uj8tJ21eYXBtakpaWwcuEVYabGoXFysmRDY8MGRYYwM3KxpGVw5pR18+YmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUJyRRPXh3EXdoY21WY3BjZEoWEkpnRVYUJyRRPXh3EXdoY21WY3BjZEoWEkoiCxI+YmoVF3h3EXdoY21WJj4nTkoWEkpnRVYUJyRRPXh3EXdoY21WNzEwL0RBUwMzTUYacWM/F3h3ETImJ0cTLTRqTmAbH0oGEAJbYglZXjs8ES96Yw8ZLSUwZCZZXRpNSFsUFiJQFz82XDJoMD0XND4wZAhZXB80RRRBNj5aWSt3GS96b20OdnxjPFsGG0ouC1Z/KyleYigwQzYsJj5WJCUqZA5DQAMpAlZAMCtcWTE5Vl1lbm0hJnAnIR5TUR5nBBhQYilZXjs8ESMgJiBWIiU3KwdXRgMkBBpYO2pBWHg0XTYhLm0CKzVjKR9aRgM3CR9RMGpXWDYiQl08Ij4dbSMzJR1YGgwyCxVAKyVbH3FdEXdoYzoeKjwmZB5ERw9nARk+YmoVF3h3EXchJW01JTdtBR9CXSkrDBVfGngVQzAyX11oY21WY3BjZEoWEkorChVVLmpeXjs8ZCcvMSwSJiNjeUp6XQkmCSZYIzNQRXYHXTYxJj8xNjl5AgNYViwuFwVAASJcWzx/ExwhICYjMzcxJQ5TQUhub1YUYmoVF3h3EXdoYyQQYzsqJwFjQg01BBJRMWpBXz05O3doY21WY3BjZEoWEkpnRVYZb2p5WDc8ETEnMW0FMzE0Kg9SEggoCwNHYihAQyw4XyRoay4aLD4mIEpQQAUqRTRbLD9GFywyXCckIjkTalpjZEoWEkpnRVYUYmoVF3h3Vzg6YxJaYzMrLQZSEgMpRR9EIyNHRHA8WDQjFj0RMTEnIRkMdQ8zIRNHIS9bUzk5RSRgamRWJz9JZEoWEkpnRVYUYmoVF3h3EXdoY20fJXAgLANaVlAOFjccYANYVj8ycyI8NyIYYXljJQRSEgkvDBpQeAJURAw2Vn9qATgCNz8tZkMWRgIiC3wUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYZb2pzWC05VXcpYy8ZLSUwZAhDRh4oC1oUISZcVDN3WCNpSW1WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYz0VIjwvbAxDXAkzDBlaamM/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXplYwsfMTVjBQlCWxwmERNQYjlcUDY2XXdjYy4aKjMoZBxfQB4yBBpYO0AVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3XTgrIiFWID8tKkoLEgkvDBpQbAtWQzEhUCMtJ3c1LD4tIQlCGgwyCxVAKyVbH3F3VDksakdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjIgVEEjVrRQVdJSRUW3g+X3chMywfMSNrP0h3UR4uExdAJy4XG3h1fDg9MCg0NiQ3KwQHcQYuBh0WP2MVUzddEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3AzJwtaXkIhEBhXNiNaWXB+O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEgkvDBpQGTlcUDY2XQpyBSQEJnhqTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUJyRRHlJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoJiMSSXBjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpVXQQpXzJdMSlaWTYyUiNgakdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjaUcWcwY0ClZSKzhQFy4+UHceKj8CNjEvDQRGRx4KBBhVJS9HFzkjETU9NzkZLXAzKxlfRgMoC3wUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVWzc0UDtoIi8FEz8wZFcWUQIuCRIaAyhGWDQiRTIYLD4fNzksKmAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnCRlXIyYVVjokYj4yJm1LYzMrLQZSHCslFhlYNz5QZDEtVF1oY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WLz8gJQYWUQ8pERNGGmoIFzk1QgcnMGMuY3tjJQhFYQM9AFhsYmUVBVJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoLyIVIjxjJw9YRg81PFYJYitXRAg4QnkRY2ZWIjIwFwNMV0QeRVkUcEAVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3Zz46NzgXLxktNB9CfwspBBFRMHBmUjYzfDg9MCg0NiQ3KwRzRA8pEV5XJyRBUioPHXcrJiMCJiIaaEoGHkozFwNRbmpSVjUyHXd4akdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjMAtFWUQwBB9AanobB21+O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY20gKiI3MQtaewQ3EAJ5IyRUUD0lCwQtLSk7LCUwIShDRh4oCzNCJyRBHzsyXyMtMRVaYzMmKh5TQDNrRUYYYixUWysyHXcvIiATb3BzbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpTXA5ub1YUYmoVF3h3EXdoY21WY3BjZEoWVwQjb1YUYmoVF3h3EXdoY21WY3AmKg48EkpnRVYUYmoVF3h3VDksSW1WY3BjZEoWVwQjb1YUYmoVF3h3RTY7KGMBIjk3bFoYA0NNRVYUYi9bU1IyXzNhSUdbbnACMR5ZEiEuBh0UDiVaR3h/eTY6JzoXMTVuDQRGRx5nJw9EIzlGUjx3dC8tIDgCKj8tbWBCUxksSwVEIz1bHz4iXzQ8KiIYa3lJZEoWEh0vDBpRYj5HQj13VThCY21WY3BjZEpfVEoEAxEaAz9BWBM+UjxoNyUTLVpjZEoWEkpnRVYUYmpZWDs2XXcrKywEY21jCAVVUwYXCRdNJzgbdDA2QzYrNygESXBjZEoWEkpnRVYUYiZaVDk7ESUnLDlWfnAgLAtEEgspAVZXKitHDR4+XzMOKj8FNxMrLQZSGkgPEBtVLCVcUwo4XiMYIj8CYXlJZEoWEkpnRVYUYmoVWzc0UDtoKzgbY21jJwJXQEomCxIUISJURWIRWDksBSQEMCQALANaViUhJhpVMTkdFRAiXDYmLCQSYXlJZEoWEkpnRVYUYmoVPXh3EXdoY21WY3BjZANQEhgoCgIUIyRRFzAiXHc8KygYSXBjZEoWEkpnRVYUYmoVF3g7XjQpL20dKjMoFAtSEldnMhlGKTlFVjsyHxY6JiwFbRsqJwFkVwsjHHwUYmoVF3h3EXdoY21WY3BjKAVVUwZnAR9HNmoIF3AlXjg8bR0ZMDk3LQVYEkdnDh9XKRpUU3YHXiQhNyQZLXltCQtRXAMzEBJRSGoVF3h3EXdoY21WY3BjZEo8EkpnRVYUYmoVF3h3EXdoY2BbYwMiIg8WWwQ0ERdaNmpBUjQyQTg6N20CLHAoLQldEhomAVZALWpFRT0hVDk8YywYOnAnLRlCUwQkAFYbYilaWzQ+Qj4nLW0CMTkkIw9EQWBnRVYUYmoVF3h3EXdoY21Wbn1jFwFfQkozABpRMiVHQ3g+V3c/Jm0cNiM3ZAxfXAM0DRNQYisVXDE0WncnMW0XMTVjJx9EQA8pERpNYj1UWzM+XzBoISwVKFpjZEoWEkpnRVYUYmoVF3h3WDFoJyQFN3B9ZFwWUwQjRRhbNmpcRAoyRSI6LSQYJAQsDwNVWTomAVZAKi9bPXh3EXdoY21WY3BjZEoWEkpnRVYUMCVaQ3YUdyUpLihWfnAoLQldYgsjSzVyMCtYUnh8EQEtIDkZMWNtKg9BGlprRUUYYnocPXh3EXdoY21WY3BjZEoWEkpnRVYUb2cVcTclUjJoOSIYJnA2NA5XRg9nFhkUAStbfDE0Wnc7NywCJnAqN0pTXB4iFxNQYjhQWzE2UzsxSW1WY3BjZEoWEkpnRVYUYmoVF3h3QTQpLyFeJSUtJx5fXQRvTHwUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZYLSlUW3gNXjktACIYNyIsKAZTQEp6RQRRMz9cRT1/YzI4LyQVIiQmIDlCXRgmAhMaDyVRQjQyQnkLLCMCMT8vKA9EfgUmARNGbBBaWT0UXjk8MSIaLzUxbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpsXQQiJhlaNjhaWzQyQ20dMykXNzUZKwRTGkNNRVYUYmoVF3h3EXdoY21WY3BjZEpTXA5ub1YUYmoVF3h3EXdoY21WY3BjZEoWRgs0DlhDIyNBH2h5AH5CY21WY3BjZEoWEkpnRVYUYmoVF3gzWCQ8Y3BWayIsKx4YYgU0DAJdLSQVGng8WDQjEywSbQAsNwNCWwUpTFh5Iy1bXiwiVTJCY21WY3BjZEoWEkpnRVYUYi9bU1J3EXdoY21WY3BjZEoWEkpnb1YUYmoVF3h3EXdoY21WY3BuaUplRgspAVZbLGpFVjx3UDksYzkEKjckIRgWRgIiRRFVLy8VWzc4QSRoLSwCKiYmKBMWRAMmRQVdLz9ZViwyVXcrLyQVKCNJZEoWEkpnRVYUYmoVF3h3ET4uYykfMCRjeFcWBEozDRNaSGoVF3h3EXdoY21WY3BjZEoWEkpnSFsUc2QVYDk+RXcuLD9WCDkgLyhDRh4oC1ZALWpURygyUCVoaw4XLRsqJwEWQR4mERMUJyRBUioyVX5CY21WY3BjZEoWEkpnRVYUYmoVF3g7XjQpL20UNz4VLRlfUAYiRUsUJCtZRD1dEXdoY21WY3BjZEoWEkpnRVYUYmpZWDs2XXcqNyMhIjk3Fx5XQB5nWFZAKyleH3FdEXdoY21WY3BjZEoWEkpnRVYUYmpCXzE7VHcmLDlWISQtEgNFWwgrAFZVLC4VQzE0Wn9hY2BWISQtEwtfRjkzBARAYnYVBHg2XzNoACsRbRE2MAV9WwksRRJbSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYiZaVDk7ER8dB21LYxwsJwtaYgYmHBNGbBpZViEyQxA9KncwKj4nAgNEQR4EDR9YJmIXfw0TE35CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoLyIVIjxjJh9CRgUpRUsUCh9xFzk5VXcAFglMBTktICxfQBkzJh5dLi4dFRM+UjwKNjkCLD5hbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpfVEolEAJALSQVVjYzETU9NzkZLX4VLRlfUAYiRQJcJyQ/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3ETU8LRsfMDkhKA8WD0ozFwNRSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYi9ZRD1dEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYzkXMDttMwtfRkJ3S0cdSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYi9bU1J3EXdoY21WY3BjZEoWEkpnRVYUYi9bU1J3EXdoY21WY3BjZEoWEkpnRVYUYkAVF3h3EXdoY21WY3BjZEoWEkpnRR9SYihBWQ4+Qj4qLyhWNzgmKmAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEobH0p1S1ZgMCNSUD0lETwhICZWISljJhNGUxk0DBhTYj5dUngcWDQjATgCNz8tZAtYVko0ERdGNiNbUHgjWTJoLiQYKjciKQ8WVgM1ABVALjM/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVQyo+VjAtMQYfIDtrbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEo8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWH0dnVlgUFStcQ3gxXiVoLiQYKjciKQ8WRgVnFgJVMD4/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVWzc0UDtoMDkXMSQXZFcWRgMkDl4dSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYj1dXjQyETknN209KjMoBwVYRhgoCRpRMGR8WRU+Xz4vIiATYzEtIEpCWwksTV8Ub2pGQzklRQNof21EYzEtIEp1VA1pJANALQFcVDN3VThCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYyQiNwEYRQsuEV4dSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYi9bU1J3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3hdEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3WDFoCCQVKBMsKh5EXQYrAAQaCyR4XjY+VjYlJm0CKzUtTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkorChVVLmpYWDwyEWpoDD0CKj8tN0R9WwksNRNGJC9WQzE4X3keIiEDJnAsNkoUdQUoAVYcenoYDm1yGHVCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYzwsJwtaEh4mFxFRNgdcWXR3RTY6JCgCDjE7TkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpNRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmcYFxwyRTI6LiQYJnA3LA8WRgs1AhNAYjlWVjQyESUpLSoTYzIiNw9SEgUpRQJcJ2pYWDwyETYmJ20FNzEnLR9bEg8xABhASGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3g7XjQpL20fMAM3JQ5fRwdnWFZSIyZGUlJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoMy4XLzxrIh9YUR4uChgca0AVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYyQFECQiIANDX0p6RSFRIz5dUioEVCU+Ki4THBMvLQ9YRkQCExNaNjkbZCw2VT49Lm0XLTRjEw9XRgIiFyVRMDxcVD0IcjshJiMCbRU1IQRCQUQUERdQKz9YF2Z3Rjg6KD4GIjMmfi1TRjkiFwBRMB5cWj0ZXiBgakdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjIQRSG2BnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3g+V3chMB4CIjQqMQcWRgIiC3wUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3ET4uYyAZJzVjeVcWEDoiFxBRIT4VH2lnAXJobm0EKiMoPUMUEh4vABg+YmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WNzExIw9CfwMpSVZAIzhSUiwaUC9ofm1GbWhwaEoGHFNzRVsZYhpQRT4yUiNCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpTXhkiDBAULyVRUnhqDHdqBCIZJ3BrfFobC19iTFQUNiJQWVJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpCUxggAAJ5KyQZFyw2QzAtNwAXO3B+ZFoYBF1rRUYaensVGnV3dC8rJiEaJj43TkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUJyZGUjExETonJyhWfm1jZi5TUQ8pEVYcdHoYD2hyGHVoNyUTLVpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpBViowVCMFKiNaYyQiNg1TRicmHVYJYnobAmh7EWdmdXhWbn1jAxhTUx5NRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3gyXSQtY2BbYwIiKg5ZX2BnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXc8Ij8RJiQOLQQaEh4mFxFRNgdUT3hqEWdmcX1aY2BtfVI8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpQWTxdEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYygaMDVJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZdJGpYWDwyEWp1Y28mJiIlIQlCEkJ2VUYRYmcVRTEkWi5hYW0CKzUtTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVFyw2QzAtNwAfLXxjMAtEVQ8zKBdMYncVB3ZuBntocmNGY31uZDpTQAwiBgI+YmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXctLz4TKjZjKQVSV0p6WFYWBSVaU3h/CWdlenhTanJjMAJTXGBnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXc8Ij8RJiQOLQQaEh4mFxFRNgdUT3hqEWdme3xaY2BtfVwWH0dnIA5XJyZZUjYjO3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjIQZFVwMhRRtbJi8VCmV3ExMtICgYN3BrclobClpiTFQUNiJQWVJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpCUxggAAJ5KyQZFyw2QzAtNwAXO3B+ZFoYBFtrRUYadXMVGnV3diUtIjl8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkoiCQVRYmcYFwo2XzMnLkdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZAIzhSUiwaWDlkYzkXMTcmMCdXSkp6RUYacHoZF2h5CG5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpTXA5NRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYi9bU1J3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoSW1WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BuaUphUwMzRQNaNiNZFxM+UjwLLCMCMT8vKA9EHDkkBBpRYixUWzQkESAhNyUfLXA3JRhRVx4KDBgUIyRRFyw2QzAtNwAXO1pjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWXgUkBBoUIStFQy0lVDMbICwaJnB+ZARfXmBnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYULiVWVjR3QjQpLyg1LD4tTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkorChVVLmpGVDk7VAUtIi4eJjRjeUpQUwY0AHwUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVRDs2XTILLCMYY21jFh9YYQ81Ex9XJ2RlRT0FVDksJj9MAD8tKg9VRkIhEBhXNiNaWXB+O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjLQwWXAUzRT1dISF2WDYjQzgkLygEbRktCQNYWw0mCBMUNiJQWVJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpFUQsrADVbLCQPczEkUjgmLSgVN3hqTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVFyoyRSI6LUdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEg8pAXwUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3ETsnICwaYyMgJQZTEldnLh9XKQlaWSwlXjskJj9YEDMiKA88EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpcUXgkUjYkJm1IfnA3JRhRVx4KDBgUIyRRFys0UDstY3FLYyQiNg1TRicmHVZAKi9bPXh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZBlVUwYiNxNVISJQU3hqESM6Nih8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUIStFQy0lVDMbICwaJnB+ZBlVUwYib1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYz4VIjwmBwVYXFADDAVXLSRbUjsjGX5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpTXA5NRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYi9bU3FdEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY0dWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjaUcWZQsuEVZBMmpBWHhmH2JoMCgVLD4nN0pQXRhnER5RYjlWVjQyESMnYyUfN3A3LA8WRgs1AhNAYmJdUjklRTUtIjlWJT8xZAdXSko0FRNRJmM/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3ETsnICwaYzMrIQldYR4mFwIUf2pBXjs8GX5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYycrLQZTEgQoEVZHIStZUgoyUDQgJilWIj4nZCFfUQEEChhAMCVZWz0lHx4mDiQYKjciKQ8WUwQjRQJdISEdHnh6ETQgJi4dECQiNh4WDkp2S0MUIyRRFxsxVnkJNjkZCDkgL0pSXWBnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVFwoiXwQtMTsfIDVtDA9XQB4lABdAeB1UXix/GF1oY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WJj4nTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkouA1ZHIStZUhs4XzlmACIYLTUgMA9SEh4vABgUMSlUWz0UXjkmeQkfMDMsKgRTUR5vTFZRLC4/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EV1oY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21Wbn1jd0QWdwQjRQJcJ2pYXjY+VjYlJm0BKiQrZB5eV0oEJCZgFxhwc3gkUjYkJm0AIjw2IWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnEQRdJS1QRR05VRwhICZeIDEzMB9EVw4UBhdYJ2M/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVUjYzO3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EV1oY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdlbm0wLzEkZB5eV0o1AAJBMCQVeRcAESQnYyAXKj5jKAVZQkokBBgTNmpBUjQyQTg6N20SNiIqKg0WRQsuEV1ANS9QWVJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3g+QgUtNzgELTktIz5ZeQMkDiZVJmoIFywlRDJCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoSW1WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY2BbY2RtZD1XWx5nAxlGYhlBViwiQnc8LG0UJjMsKQ8WED40EBhVLyMXF3A2VyMtMW0aIj4nLQRREkFnBwRVKyRHWCx3RSUpLT4QLCIubWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEobH0oTDR9HYidQVjYkESMgJm0RIj0mZAJXQUo3FxlXJzlGUjx3RT8tYyYfIDtjJQRSEhkzBARAJy4VQzAyESUtNzgELXAwIRtDVwQkAHwUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZYLSlUW3gjQiIbNywEN3B+ZB5fUQFvTHwUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZDKiNZUngQUDotCywYJzwmNkRlRgszEAUUPHcVFQwkRDkpLiRUYzEtIEpCWwksTV8Ub2pBRC0ERTY6N21KY2F2ZAtYVkoEAxEaAz9BWBM+UjxoJyJ8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZB5XQQFpEhddNmIFGWp+O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY218Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21Wbn1jCQVAV0ozClZfKyleFyg2VXc9MCQYJHALMQdXXAUuAVZEKjNGXjskEX89LSwYIDgsNg9SHkowBABRYjpARDAyQncmIjkDMTEvKBMfOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEgYoBhdYYidaQT0UWTY6Y3BWDz8gJQZmXgs+AAQaASJURTk0RTI6SW1WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYyEZIDEvZBhZXR5nWFZZLTxQdDA2Q3cpLSlWLj81ISleUxhpNQRdLytHTgg2QyNCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoLyIVIjxjLB9bEldnCBlCJwldVip3UDksYyAZNTUALAtECCwuCxJyKzhGQxs/WDssDCs1LzEwN0IUeh8qBBhbKy4XHlJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3g+V3c6LCICYzEtIEpeRwdnBBhQYg1UWj0fUDksLygEbQM3JR5DQUp6WFYWFjlAWTk6WHVoNyUTLVpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWXgUkBBoUNitHUD0jYTg7Y3BWKDkgLzpXVkQXCgVdNiNaWXh8EQEtIDkZMWNtKg9BGlprRUUYYnocPXh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY31uZC5TRg81CB9aJ2pCVi4yESQ4JigSYzYxKwcWUwkzDABRYj1UQT13WDloNCIEKCMzJQlTOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZYLSlUW3ggUCEtED0TJjRjeUoHB19NRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYjpWVjQ7GTE9LS4CKj8tbEM8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpZWDs2XXcfB21LYyImNR9fQA9vNxNELiNWViwyVQQ8LD8XJDVtFwJXQA8jSzJVNisbYDkhVBMpNyxfSXBjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnAxlGYhUZFy82RzJoKiNWKiAiLRhFGh0oFx1HMitWUnYAUCEtMHcxJiQALANaVhgiC14da2pRWFJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpaXQkmCVZQIz5UF2V3ZhNmFCwAJiMYMwtAV0QJBBtRH0AVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3AqIkpSUx4mRRdaJmpRViw2HwQ4JigSYyQrIQQ8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYzoXNTUQNA9TVkp6RRJVNisbZCgyVDNCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYihHUjk8O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEg8pAXwUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjIQRSG2BnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h6HHcbJjlWMCUzIRgWWgMgDVZjIyZeZCgyVDNoNyJWLCU3Nh9YEh4vAFZDIzxQPXh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXcgNiBYFDEvLzlGVw8jRUsUNStDUgsnVDIsY2dWcX52TkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkovEBsOASJUWT8yYiMpNyheBj42KUR+RwcmCxldJhlBViwyZS44JmMkNj4tLQRRG2BnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h6HHcFLDsTFz9jMAVBUxgjRR1dISEVRzkzO3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY20eNj15CQVAVz4oTQJVMC1QQwg4Qn5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY1pjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWH0dnMhddNmpAWSw+XXcrLyIFJnA3K0pdWwksRQZVJkAVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3XTgrIiFWLj81ITlCUxgzRUsUNiNWXHB+O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY20BKzkvIUpCWwksTV8Ub2pYWC4yYiMpMTlWf3BycUpXXA5nJhBTbAtAQzccWDQjYykZSXBjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnCRlXIyYVVC0lQzImNw4eIiJjeUp6XQkmCSZYIzNQRXYUWTY6Ii4CJiJJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZYLSlUW3g0RCU6JiMCET8sMEoLEgkyFwRRLD52XzklETYmJ20VNiIxIQRCcQImF1hkMCNYViouYTY6N0dWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEgMhRRVBMDhQWSwFXjg8YzkeJj5JZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVWzc0UDtoJyQFN3B+ZEJVRxg1ABhAECVaQ3YHXiQhNyQZLXBuZB5XQA0iESZbMWMbejkwXz48NikTSXBjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYiNTFzw+QiNof21OYyQrIQQ8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYy8EJjEoTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVFz05VV1oY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpqSFZmJ2dcRCsiVHcFLDsTFz9jLQwWRgUoRRBVMGodRT0kVCM7YzkfLjUsMR4fOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3ET4uYykfMCRjekoFAkozDRNaSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpeRwd9KBlCJx5aHyw2QzAtNx0ZMHlJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVUjYzO3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjIQRSOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVQzkkWnk/IiQCa2Btd0M8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRRNaJkAVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21bbnARIRlCXRgiRRhbMCdUW3gAUDsjED0TJjRJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEgIyCFhjIyZeZCgyVDNofm1HdVpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYZb2phUjQyQTg6N20TOzEgMAZPEgUpERkUKSNWXHgnUDNoNyJWJCUiNgtYRg8iRRRBNj5aWXghWCQhISQaKiQ6TkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEko1ChlAbAlzRTk6VHd1Yw4wMTEuIURYVx1vDh9XKRpUU3YHXiQhNyQZLXBoZDxTUR4oF0UaLC9CH2h7EWRkY31falpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYZb2pzWCo0VHcyLCMTYyUzIAtCV0o0ClZ/KyledS0jRTgmYywGMzUiNhkWWwcqABJdIz5QWyFdEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYz0VIjwvbAxDXAkzDBlaamM/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY20aLDMiKEpsXQQiJhlaNjhaWzQyQ3d1Yz8TMiUqNg8eYA83CR9XIz5QUwsjXiUpJChYDj8nMQZTQUQEChhAMCVZWz0lfTgpJygEbQosKg91XQQzFxlYLi9HHlJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYwosKg91XQQzFxlYLi9HDQ0nVTY8JhcZLTVrbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnABhQa0AVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpQWTxdEXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXplYwwEMTk1IQ4WUx5nDh9XKWpFVjx5ER4lLigSKjE3IQZPEhgiFgJVMD4VVCE0XTJmSW1WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYz4TMCMqKwRhWwQ0RUsUMS9GRDE4XwAhLT5WaHByTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZGAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEobH0oECRNVMGpTWzkwESQnYyEZLCBjJwtYEhgiFgJVMD4VXjU6VDMhIjkTLylJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjLRlkVx4yFxhdLC1hWBM+UjwYIilWfnAlJQZFV2BnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkorBAVACSNWXB05VXd1YzkfIDtrbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEo8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWH0dnLRdaJiZQFz8yXzI6IiFWMDUwNwNZXEorDBtdNkAVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpZWDs2XXc8Ij8RJiQQMBgWD0oIFQJdLSRGGQsyQiQhLCMiIiIkIR4YZAsrEBMULTgVFRE5Vz4mKjkTYVpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3AqIkpCUxggAAJnNjgVSWV3Ex4mJSQYKiQmZkpCWg8pb1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpZWDs2XXckKiAfN3B+ZB5ZXB8qBxNGaj5URT8yRQQ8MWR8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZANQEgYuCB9AYitbU3gkVCQ7KiIYFDktN0oID0orDBtdNmpBXz05O3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjBwxRHCsyERl/KyleF2V3VzYkMCh8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEko3BhdYLmJTQjY0RT4nLWVfYwQsIw1aVxlpJANALQFcVDNtYjI8FSwaNjVrIgtaQQ9uRRNaJmM/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY206KjIxJRhPCCQoER9SO2IXZD0kQj4nLW0aKj0qMEpEVwskDRNQYmIXF3Z5ETshLiQCY35tZEgWRQMpFl8aYgtAQzd3ej4rKG0FNz8zNA9SHEhub1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmpQWysyO3doY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjCANUQAs1HEx6LT5cUSF/EwQtMD4fLD5jFBhZVRgiFgUOYmgVGXZ3QjI7MCQZLQcqKhkWHERnR1kWYmQbFzQ+XD48akdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjIQRSOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEg8pAXwUYmoVF3h3EXdoY21WY3BjZEoWEg8rFhM+YmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUNitGXHYgUD48a31YdnlJZEoWEkpnRVYUYmoVF3h3EXdoY20TLTRJZEoWEkpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEkpnRVZRLC4/F3h3EXdoY20TLTRJZEoWEkpnRVZAIzleGS82WCNgakdWY3BjIQRSOA8pAV8+SGcYFxkiRThoECgaL3APKwVGOB4mFh0aMTpUQDZ/VyImIDkfLD5rbWAWEkpnEh5dLi8VQyoiVHcsLEdWY3BjZEoWEgMhRTVSJWR0Qiw4YjIkL20CKzUtTkoWEkpnRVYUYmoVFzQ4UjYkYyAPEzwsMEoLEg0iETtNEiZaQ3B+O3doY21WY3BjZEoWEgMhRRtNEiZaQ3gjWTImSW1WY3BjZEoWEkpnRVYUYmpZWDs2XXclJjkeLDRjeUp5Qh4uChhHbBlQWzQaVCMgLClYFTEvMQ8WXRhnRyVRLiYVdjQ7E11oY21WY3BjZEoWEkpnRVYULiVWVjR3QzIlLDkTDTEuIUoLEkgFOiVRLiZ0WzR1O3doY21WY3BjZEoWEkpnRVY+YmoVF3h3EXdoY21WY3BjZANQEgciER5bJmoICnh1YjIkL203LzxjBhMWYAs1DAJNYGpBXz05O3doY21WY3BjZEoWEkpnRVYUYmoVRT06XiMtDSwbJnB+ZEh0bTkiCRp1LiZ3Tgo2Qz48Om98Y3BjZEoWEkpnRVYUYmoVFz07QjIhJW0bJiQrKw4WD1dnRyVRLiYVZDE5VjstYW0CKzUtTkoWEkpnRVYUYmoVF3h3EXdoY21WMTUuKx5TfAsqAFYJYmh3aAsyXTtqSW1WY3BjZEoWEkpnRVYUYmpQWTxdEXdoY21WY3BjZEoWEkpnRXwUYmoVF3h3EXdoY21WY3BjNAlXXgZvAwNaIT5cWDZ/GF1oY21WY3BjZEoWEkpnRVYUYmoVFxYyRSAnMSZYCj41KwFTYQ81ExNGajhQWjcjVBkpLihfSXBjZEoWEkpnRVYUYmoVF3gyXzNhSW1WY3BjZEoWEkpnRRNaJkAVF3h3EXdoYygYJ1pjZEoWEkpnRQJVMSEbQDk+RX97akdWY3BjIQRSOA8pAV8+SGcYFxkiRThoEyEXIDVjBhhXWwQ1CgJHSD5URDN5QicpNCNeJSUtJx5fXQRvTHwUYmoVQDA+XTJoNz8DJnAnK2AWEkpnRVYUYiNTFxsxVnkJNjkZEzwiJw8WRgIiC3wUYmoVF3h3EXdoY20aLDMiKEpbSzorCgIUf2pSUiwaSAckLDlealpjZEoWEkpnRVYUYmpcUXg6SAckLDlWNzgmKmAWEkpnRVYUYmoVF3h3EXdoLyIVIjxjNwZZRhlnWFZZOxpZWCxtdz4mJwsfMSM3BwJfXg5vRyVYLT5GFXFdEXdoY21WY3BjZEoWEkpnRR9SYjlZWCwkESMgJiN8Y3BjZEoWEkpnRVYUYmoVF3h3EXcuLD9WKnB+ZFsaEll3RRJbSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYiNTFzY4RXcLJSpYAiU3KzpaUwkiRQJcJyQVVSoyUDxoJiMSSXBjZEoWEkpnRVYUYmoVF3h3EXdoY21WYzwsJwtaEhkrCgJ6IydQF2V3EwQkLDlUY35tZAM8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWXgUkBBoUMWoIFys7XiM7eQsfLTQFLRhFRikvDBpQajlZWCwZUDotakdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY20fJXAwZAtYVkopCgIUMXBzXjYzdz46MDk1KzkvIEIUYgYmBhNQEitHQ3p+ESMgJiN8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZBpVUwYrTRBBLClBXjc5GX5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEp4Vx4wCgRfbAxcRT0EVCU+Jj9eYQMcDQRCVxgmBgIWbmpcHlJ3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoJiMSalpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWRgs0DlhDIyNBH2h5BH5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoJiMSSXBjZEoWEkpnRVYUYmoVF3h3EXdoJiMSSXBjZEoWEkpnRVYUYmoVF3gyXzNCY21WY3BjZEoWEkpnABhQSGoVF3h3EXdoJiMSSXBjZEoWEkpnERdHKWRCVjEjGWRhSW1WY3AmKg48VwQjTHw+b2cVdi0jXncdMyoEIjQmZDpaUwkiAVZ2MCtcWSo4RSRoaxgFJiNjFwZZRkouCxJROmpcWSwyVjI6MGxfSSQiNwEYQRomEhgcJD9bVCw+XjlgakdWY3BjMwJfXg9nEQRBJ2pRWFJ3EXdoY21WYzklZClQVUQGEAJbFzpSRTkzVBUkLC4dMHA3LA9YOEpnRVYUYmoVF3h3ESM4FyI0IiMmbEM8EkpnRVYUYmoVF3h3XTgrIiFWLikTKAVCEldnAhNADzNlWzcjGX5CY21WY3BjZEoWEkpnDBAULzNlWzcjESMgJiN8Y3BjZEoWEkpnRVYUYmoVFzQ4UjYkYz4aLCQwZFcWXxMXCRlAeAxcWTwRWCU7Nw4eKjwnbEhlXgUzFlQdSGoVF3h3EXdoY21WY3BjZEpfVEo0CRlAMWpBXz05O3doY21WY3BjZEoWEkpnRVYUYmoVWzc0UDtoNywEJDU3ZFcWfRozDBlaMWRgRz8lUDMtFywEJDU3ajxXXh8iRRlGYmh0WzR1O3doY21WY3BjZEoWEkpnRVYUYmoVXj53RTY6JCgCY21+ZEh3XgZlRQJcJyQ/F3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVUTclET5ofm1Hb3BwdEpSXWBnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUKywVWTcjERQuJGM3NiQsERpRQAsjADRYLSleRHgjWTImYy8EJjEoZA9YVmBnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYULiVWVjR3Qnd1Yz4aLCQwfixfXA4BDARHNgldXjQzGXUbLyICYXBtakpfG2BnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUKywVRHg2XzNoMHcwKj4nAgNEQR4EDR9YJmIXZzQ2UjIsEywEN3JqZB5eVwRNRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3gnUjYkL2UQNj4gMANZXEJub1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYwMTNycsNgEYdAM1ACVRMDxQRXB1cwgdMyoEIjQmZkYWW0NNRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3gyXzNhSW1WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWRgs0DlhDIyNBH2h5A35CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYzUtIGAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpTXA5NRVYUYmoVF3h3EXdoY21WY3BjZEpTXhkib1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRRpbIStZFys7XiMGNiBWfnA3JRhRVx59CBdAISIdFQs7XiNoa2gSaHlhbWAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpfVEo0CRlADD9YFyw/VDlCY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYzwsJwtaEgQyCFYJYj5aWS06UzI6az4aLCQNMQcfOEpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZYLSlUW3gkEWpoMCEZNyN5AgNYViwuFwVAASJcWzx/EwQkLDlUY35tZARDX0NNRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYiNTFyt3UDksYz5MBTktICxfQBkzJh5dLi4dFQg7UDQtJx0XMSRhbUpCWg8pb1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3XTgrIiFWIDgiNkoLEiYoBhdYEiZUTj0lHxQgIj8XICQmNmAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYiZaVDk7ESUnLDlWfnAgLAtEEgspAVZXKitHDR4+XzMOKj8FNxMrLQZSGkgPEBtVLCVcUwo4XiMYIj8CYXlJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZdJGpHWDcjESMgJiN8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUMCVaQ3YUdyUpLihWfnAwailwQAsqAFYfYhxQVCw4Q2RmLSgBa2BvZFkaElpub1YUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoYzkXMDttMwtfRkJ3S0UdSGoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoJiMSSXBjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnFRVVLiYdUS05UiMhLCNealpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmp7UiwgXiUjbQsfMTUQIRhAVxhvRzRrFzpSRTkzVHVkYyMDLnlJZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEkpnRVZRLC4cPXh3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3EXctLSl8Y3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WJj4nTkoWEkpnRVYUYmoVF3h3EXdoY21WJj4nTkoWEkpnRVYUYmoVF3h3EXctLSl8Y3BjZEoWEkpnRVYUJyRRPXh3EXdoY21WJj4nTkoWEkpnRVYUNitGXHYgUD48a35fSXBjZEpTXA5NABhQa0A/GnV3czYrKCoELCUtIEpaXQU3RQJbYi5MWTk6WDQpLyEPYyUzIAtCV0oDFxlEJiVCWSt3GQI4JD8XJzVjNwZZRhlnBBhQYgVCWT0zESAtKioeNyNqTh5XQQFpFgZVNSQdUS05UiMhLCNealpjZEoWRQIuCRMUNjhAUngzXl1oY21WY3BjZEcbEltpRSRRJDhQRDB3XiAmJilWNDUqIwJCQUojFxlEJiVCWVJ3EXdoY21WYyAgJQZaGgwyCxVAKyVbH3FdEXdoY21WY3BjZEoWXgUkBBoULT1bUjx3DHcfJiQRKyQQIRhAWwkiJhpdJyRBGRcgXzIsYyIEYys+TkoWEkpnRVYUYmoVFzExEXQnNCMTJ3B+eUoGEh4vABg+YmoVF3h3EXdoY21WY3BjZAVBXA8jRUsUOWoXYDc4VTImYx4CKjMoZkpLOEpnRVYUYmoVF3h3ETImJ0dWY3BjZEoWEkpnRVZ7Mj5cWDYkHxg/LSgSFDUqIwJCQVAUAAJiIyZAUit/XiAmJilfSXBjZEoWEkpnABhQa0A/F3h3EXdoY21bbnBxakpkVww1AAVcYjlZWCwjVDNoIT8XKj4xKx5FEg41CgZQLT1bFzQ+QiNCY21WY3BjZEpGUQsrCV5SNyRWQzE4X39hSW1WY3BjZEoWEkpnRRpbIStZFzUuYTsnN21LYzcmMCdPYgYoEV4dSGoVF3h3EXdoY21WYzwsJwtaEhwmCQNRMWoIFyN3ExYkL29WPlpjZEoWEkpnRVYUYmo/F3h3EXdoY21WY3BjLQwWXxMXCRlAYitbU3g6SAckLDlMBTktICxfQBkzJh5dLi4dFQs7XiM7YWRWNzgmKmAWEkpnRVYUYmoVF3h3EXdoLyIVIjxjNwZZRhlnWFZZOxpZWCx5YjsnNz58Y3BjZEoWEkpnRVYUYmoVFz44Q3chY3BWcnxjd1oWVgVNRVYUYmoVF3h3EXdoY21WY3BjZEpaXQkmCVZHLiVBeTk6VHd1Y28lLz83ZkoYHEoub1YUYmoVF3h3EXdoY21WY3BjZEoWXgUkBBoUMWoIFys7XiM7eQsfLTQFLRhFRikvDBpQajlZWCwZUDotakdWY3BjZEoWEkpnRVYUYmoVF3h3ETsnICwaYzIxJQNYQAUzKxdZJ2oIF3oZXjktYUdWY3BjZEoWEkpnRVYUYmoVF3h3EV1oY21WY3BjZEoWEkpnRVYUYmoVFzQ4UjYkYy8aLDMoZFcWQUomCxIUMXBzXjYzdz46MDk1KzkvIEIUYgYmBhNQEitHQ3p+O3doY21WY3BjZEoWEkpnRVYUYmoVXj53UzsnICZWNzgmKmAWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEpUQAsuCwRbNgRUWj13DHcqLyIVKGoEIR53Rh41DBRBNi8dFRETE35oLD9WazIvKwldCCwuCxJyKzhGQxs/WDssDCs1LzEwN0IUfwUjABoWa2pUWTx3UzsnICZMBTktICxfQBkzJh5dLi56URs7UCQ7a287LDQmKEgfHCQmCBMdYiVHF3oHXTYrJilUSXBjZEoWEkpnRVYUYmoVF3h3EXdoJiMSSXBjZEoWEkpnRVYUYmoVF3h3EXdoNywULzVtLQRFVxgzTQBVLj9QRHR3QiM6KiMRbTYsNgdXRkJlNhpbNmoQU3h/FCRhYWFWKnxjJhhXWwQ1CgJ6IydQHnFdEXdoY21WY3BjZEoWEkpnRRNaJkAVF3h3EXdoY21WY3AmKBlTOEpnRVYUYmoVF3h3EXdoY20QLCJjLUoLEltrRUUEYi5aPXh3EXdoY21WY3BjZEoWEkpnRVYUNitXWz15WDk7Jj8CayYiKB9TQUZnRyVYLT4VFXh5H3chY2NYY3JjbCRZXA9uR18+YmoVF3h3EXdoY21WY3BjZA9YVmBnRVYUYmoVF3h3EXctLSl8Y3BjZEoWEkpnRVYUSGoVF3h3EXdoY21WYx8zMANZXBlpMAZTMCtRUgw2QzAtN3clJiQVJQZDVxlvExdYNy9GHlJ3EXdoY21WYzUtIEM8OEpnRVYUYmoVQzkkWnk/IiQCa2VqTkoWEkoiCxI+JyRRHlJdHHpoAjgCLHABMRMWZQ8uAh5AMWodZyo4ViUtMD4fLD5jJgtFVw5nChgUMiZUTj0lETQpMCVfSSQiNwEYQRomEhgcJD9bVCw+XjlgakdWY3BjMwJfXg9nEQRBJ2pRWFJ3EXdoY21WYzklZClQVUQGEAJbAD9MYD0+Vj88MG0CKzUtTkoWEkpnRVYUYmoVFzQ4UjYkYw4aKjUtMChXXgspBhNnJzhDXjsyEWpoMSgHNjkxIUJkVxorDBVVNi9RZCw4QzYvJmM7LDQ2KA9FHDkiFwBdIS9Gezc2VTI6bQ4aKjUtMChXXgspBhNnJzhDXjsyGF1oY21WY3BjZEoWEkorChVVLmpXVjQ2XzQtY3BWADwqIQRCcAsrBBhXJxlQRS4+UjJmASwaIj4gIWAWEkpnRVYUYmoVF3g+V3cqIiEXLTMmZB5eVwRNRVYUYmoVF3h3EXdoY21WY31uZDlTUxgkDVZSMCVYFzU4QiNoJjUGJj4wLRxTEg4oEhgUNiUVVDAyUCctMDl8Y3BjZEoWEkpnRVYUYmoVFz44Q3chY3BWYCMsNh5TVj0iDBFcNjkZF2l7EXp5YykZSXBjZEoWEkpnRVYUYmoVF3h3EXdoLyIVIjxjM0oLEhkoFwJRJh1QXj8/RSQTKhB8Y3BjZEoWEkpnRVYUYmoVF3h3EXchJW0YLCRjMAtUXg9pAx9aJmJiUjEwWSMbJj8AKjMmBwZfVwQzSzlDLC9RG3ggHzkpLihfYyQrIQQ8EkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWXgUkBBoUISVGQxc1W3d1YwQYJTktLR5TfwszDVhaJz0dQHY0XiQ8akdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY20fJXAhJQZXXAkiRUgJYilaRCwYUz1oNyUTLVpjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWQgkmCRocJD9bVCw+XjlgakdWY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZEoWEiQiEQFbMCEbcTElVAQtMTsTMXhhFwJZQjUFEA8WbmoXYD0+Vj88ECUZM3JvZB0YXAsqAF8+YmoVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVFz05VX5CY21WY3BjZEoWEkpnRVYUYmoVF3h3EXdoY21WYyQiNwEYRQsuEV4Fa0AVF3h3EXdoY21WY3BjZEoWEkpnRVYUYmoVF3h3UyUtIiZWbn1jBh9PEgUpCQ8UNiJQFzoyQiNoIisQLCInJQhaV0owAB9TKj4VXjZ3RT8hMG0CKjMoTkoWEkpnRVYUYmoVF3h3EXdoY21WY3BjZA9YVmBnRVYUYmoVF3h3EXdoY21WY3BjZA9YVmBnRVYUYmoVF3h3EXdoY21WJj4nTkoWEkpnRVYUYmoVFz05VV1oY21WY3BjZA9YVmBnRVYUYmoVFyw2QjxmNCwfN3hwbWAWEkpnABhQSC9bU3FdO3plYwwDNz9jBh9PEjk3ABNQYh9FUCo2VTI7STkXMDttNxpXRQRvAwNaIT5cWDZ/GF1oY21WNDgqKA8WRhgyAFZQLUAVF3h3EXdoYyQQYxMlI0R3Rx4oJwNNETpQUjx3RT8tLUdWY3BjZEoWEkpnRVZEIStZW3AxRDkrNyQZLXhqTkoWEkpnRVYUYmoVF3h3EXcbMygTJwMmNhxfUQ8ECR9RLD4PZT0mRDI7NxgGJCIiIA8eA0NNRVYUYmoVF3h3EXdoJiMSalpjZEoWEkpnRRNaJkAVF3h3EXdoYzkXMDttMwtfRkJ0THwUYmoVUjYzOzImJ2R8SX1uZD5mEj0mCR0UASVbWT00RT4nLUckNj4QIRhAWwkiSz5RIzhBVT02RW0LLCMYJjM3bAxDXAkzDBlaamM/F3h3ET4uYw4QJH4XFD1XXgECCxdWLi9RFyw/VDlCY21WY3BjZEpaXQkmCVZXKitHF2V3fTgrIiEmLzE6IRgYcQImFxdXNi9HPXh3EXdoY21WLz8gJQYWQAUoEVYJYildVip3UDksYy4eIiJ5AgNYViwuFwVAASJcWzx/Ex89LiwYLDknFgVZRjomFwIWa0AVF3h3EXdoYyEZIDEvZAJDX0p6RRVcIzgVVjYzETQgIj9MBTktICxfQBkzJh5dLi56URs7UCQ7a28+Nj0iKgVfVkhub1YUYmoVF3h3O3doY21WY3BjLQwWQAUoEVZVLC4VXy06ETYmJ20eNj1tCQVAVy4uFxNXNiNaWXYaUDAmKjkDJzVjekoGEh4vABg+YmoVF3h3EXdoY21WLz8gJQYWQRoiABIUf2p2UT95ZQcfIiEdECAmIQ4WXRhnUEY+YmoVF3h3EXdoY21WMT8sMER1dBgmCBMUf2pHWDcjHxQOMSwbJnBoZAJDX0QKCgBRBiNHUjsjWDgmY2dWayMzIQ9SEkBnVVgEcn0cPXh3EXdoY21WJj4nTkoWEkoiCxI+JyRRHlJdHHpoCiMQKj4qMA8WeB8qFVZXLSRbUjsjWDgmSRgFJiIKKhpDRjkiFwBdIS8bfS06QQUtMjgTMCR5BwVYXA8kEV5SNyRWQzE4X39hSW1WY3AqIkp1VA1pLBhSCD9YR3gjWTImSW1WY3BjZEoWXgUkBBoUISJURXhqERsnICwaEzwiPQ9EHCkvBARVIT5QRVJ3EXdoY21WYzwsJwtaEgIyCFYJYildVip3UDksYy4eIiJ5AgNYViwuFwVAASJcWzwYVxQkIj4Fa3ILMQdXXAUuAVQdSGoVF3h3EXdoKitWKyUuZB5eVwRNRVYUYmoVF3h3EXdoKzgbeRMrJQRRVzkzBAJRag9bQjV5eSIlIiMZKjQQMAtCVz4+FRMaCD9YRzE5Vn5CY21WY3BjZEpTXA5NRVYUYi9bU1IyXzNhSUdbbnANKwlaWxpnCRlbMkBnQjYEVCU+Ki4TbQM3IRpGVw59JhlaLC9WQ3AxRDkrNyQZLXhqTkoWEkouA1Z3JC0beTc0XT44YzkeJj5JZEoWEkpnRVZYLSlUW3g0WTY6Y3BWDz8gJQZmXgs+AAQaASJURTk0RTI6SW1WY3BjZEoWWwxnBh5VMGpBXz05O3doY21WY3BjZEoWEgwoF1ZrbmpWXzE7VXchLW0fMzEqNhkeUQImF0xzJz5xUis0VDksIiMCMHhqbUpSXWBnRVYUYmoVF3h3EXdoY21WKjZjJwJfXg59LAV1amh3VisyYTY6N29fYzEtIEpVWgMrAVh3IyR2WDQ7WDMtYzkeJj5JZEoWEkpnRVYUYmoVF3h3EXdoY20VKzkvIER1UwQEChpYKy5QF2V3VzYkMCh8Y3BjZEoWEkpnRVYUYmoVFz05VV1oY21WY3BjZEoWEkoiCxI+YmoVF3h3EXctLSl8Y3BjZA9YVmAiCxIdSEAYGngWXyMhYwwwCFoPKwlXXjorBA9RMGR8UzQyVW0LLCMYJjM3bAxDXAkzDBlaajoEHlJ3EXdoKitWADYkaitYRgMGIz0UIyRRFyhmEWlocn1Gc3A3LA9YOEpnRVYUYmoVWzc0UDtoNSQENyUiKCNYQh8zRUsUJStYUmIQVCMbJj8AKjMmbEhgWxgzEBdYCyRFQiwaUDkpJCgEYXlJZEoWEkpnRVZCKzhBQjk7eDk4NjlMEDUtICFTSy8xABhAaj5HQj17ERImNiBYCDU6BwVSV0QQSVZSIyZGUnR3VjYlJmR8Y3BjZEoWEkozBAVfbD1UXix/AXl5akdWY3BjZEoWEhwuFwJBIyZ8WSgiRW0bJiMSCDU6ARxTXB5vAxdYMS8ZFx05RDpmCCgPAD8nIURhHkohBBpHJ2YVUDk6VH5CY21WYzUtIGBTXA5ub3x4KyhHViouCxknNyQQOnhhDwNVWUomRTpBISFMFxo7XjQjYx4VMTkzMEpaXQsjABIVYjYVbmo8EQQrMSQGN3JqTg=='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2 })
