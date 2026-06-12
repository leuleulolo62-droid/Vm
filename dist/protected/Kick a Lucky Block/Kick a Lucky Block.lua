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

local __k = 'sif1bFsIlhHIRVzqgXKGYNgE'
local __p = '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b3YNJwY0QWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ayU8PRMRHAYKEV9mB0NMSGhpcnZaUUd4a2d5bkdlU0lGEQcoF0NMSGhpcnZaUUd4a2d5bkdlFgcCO0JmU2lMSGhpcnZaUQI2L015bkdlU0lGEUJmU2lmSGhpcnZaUUd4a2d5JwFlEQgFWhInECJMHCAsPFxaUUd4a2d5bkdlU0lGEUJmFSYeSBdlciJaGAl4Ijc4JxU2WwsHUgk2EioHUg8sJhUSGAs8OSI3Zk5sUw0JEQEuFioHPCcmPn4OWEc9JSNTbkdlU0lGEUJmU2lMDSYtWHZaUUd4a2d5bkdlUwAAEQEuEjtMHCAsPFxaUUd4a2d5bkdlU0lGEUJmFSYeSBdlciJaGAl4Ijc4JxU2WwoOUBB8NCwYKyAgPjIIFAlwYm55KghlEAEDUgkSHCYAQDxgcjMUFW14a2d5bkdlU0lGEUIjHS1mSGhpcnZaUUd4a2d5REdlU0lGEUJmU2lMSGVkchMLBA4oayU8PRNlBwYJXUIvFWkCBzxpMzoIFAY8Mmc8PxIsAxkDVWhmU2lMSGhpcnZaUUcxLWc7KxQxJwYJXUInHS1MCyAoIHYOGQI2QWd5bkdlU0lGEUJmU2lMSGggNHYYFBQsHyg2IkkVEhsDXxZmDXRMCyAoIHYOGQI2QWd5bkdlU0lGEUJmU2lMSGhpcnZaHQg7Kit5JhIoU1RGUgonAXMqASYtFD8IAhMbIy41KigjMAUHQhFuUQEZBSknPT8eU05Sa2d5bkdlU0lGEUJmU2lMSGhpcnYTF0cwPip5Og8gHWNGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kORA98JicJGT0gIgIVHgsrY25TbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5OgY2GEcRUAsyW3lCWWFDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpMDMJBTM3JCt3HgY3FgcSEV9mECENGkJpcnZaUUd4a2d5bkdlU0lGEUJmUywCDEJpcnZaUUd4a2d5bkdlU0lGVAwieWlMSGhpcnZaUUd4a2d5bkdPU0lGEUJmU2lMSGhpcnZaUUp1axMrLw4rXDoXRAMyUkNMSGhpcnZaUUd4a2d5bkdlHwYFUA5mBzsNASYaJzUZFBQra3p5KAYpAAxsEUJmU2lMSGhpcnZaUUd4azc6Lwsp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U0lGEUJmU2lMSGhpcnYKEgY0J28/OwkmBwAJX0pveWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ayQxJwshKBoPVgwnHxRWLiE7N35Te0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlFgcCGGhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMDSYtWHZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc7JCk3dCMsAAoJXwwjED1EQUJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaXEp4CisqIUcjGhsDERQvEmk6ATo9JzcWOAkoPjMULwkkFAwUEQMyUysZHDwmPHYKHhQxPy42IG1lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGXQ0lEiVMCSo6AjkJUVp4KC8wIgNrMgsVXg4zByw8BzsgJj8VH214a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5IggmEgVGUAA1ICAWDWh0cjUSGAs8ZQY7PQgpBh0DYgs8FkNMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpPjkZEAt4KCI3OgI3K0lbEQMkABkDG2YRcn1aEAUrGC4jK0kdU0ZGA2hmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMBCcqMzpaEgI2PyIrF0d4UwgEQjIpAGc1SGNpMzQJIg4iLmkAbkhlQWNGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmJSAeHD0oPh8UARIsBiY3LwAgAVM1VAwiPiYZGy0LJyIOHgkdPSI3Ok8mFgcSVBAeX2kPDSY9NyQjXUdoZ2ctPBIgX0kBUA8jX2lcQUJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaBQYrIGkuLw4xW1lIAVdveWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGgfOyQOBAY0AikpOxMIEgcHVgc0SRoJBiwEPSMJFCUtPzM2ICIzFgcSGQEjHT0JGhBlcjUfHxM9OR51bldpUw8HXREjX2kLCSUsfnZKWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc9JSNwREdlU0lGEUJmU2lMSGhpcnZaUUd4Lik9REdlU0lGEUJmU2lMSGhpcnYfHwNSa2d5bkdlU0lGEUJmFicIYmhp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cnZaUUd4a2d5bkdlU0lGEUJmU2lMBCcqMzpaExIsPyg3blplOzwiEQMoF2kkPQxzFD8UFSExOTQtDQ8sHw1OEykvECIuHTw9PThYWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUcxLWc7OxMxHAdGUAwiUysZHDwmPHgsGBQxKSs8bhMtFgdsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUysYBh4gIT8YHQJ4dmctPBIgeUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwwKQgdMU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSDwoIT1UBgYxP29pYFZseUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwwIVWhmU2lMSGhpcnZaUUd4a2d5bkdlUwwIVWhmU2lMSGhpcnZaUUd4a2d5bkdlU2NGEUJmU2lMSGhpcnZaUUd4a2d5bg4jUwsSXzQvACAOBC1pJj4fH214a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd1ZmdrYEcRAQABVgc0UyIFCyNpMC9aEx4oKjQqJwkiUx0OVEINGioHKj09JjkUUQY2L2cqOgY3BwAIVkIyGyxMBSEnOzEbHAJ4Ly4rKwQxHxBsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGRRAvFC4JGgMgMT1SWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUdSa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4Zmp5fUllJAgPRUIgHDtMBSEnOzEbHAJ4Pyh5PRMkAR1sEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGXQ0lEiVMGzwoICIuUVp4Py46JU9seUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUx4OWA4jUycDHGgCOzURMgg2PzU2IgsgAUcvXy8vHSALCSUscjcUFUcsIiQyZk5lXkkVRQM0Bx1MVGh7cjcUFUcbLSB3DxIxHCIPUglmFyZmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpciIbAgx2PCYwOk9seUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwwIVWhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJMU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmGi9MIyEqORUVHxMqJCs1KxVrOgcrWAwvFCgBDWg9OjMUe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2c1IQQkH0kLXgYjU3RMJzg9OzkUAkkTIiQyHgI3FQwFRQspHWc6CSQ8N3YVA0d6DCg2KkdtS1lLCFdjWmtmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcjoVEgY0azM4PAAgByQPX05mBygeDy09HzcCe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2dTbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0RLESYjByweBSEnN3YOGQJ4PyYrKQIxUxoFUA4jUzsNBi8scjQbAgI8ayg3bhMtFkkLXgYjUygCDGg6JjceGBI1ayIvKwkxeUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUIqHCoNBGggIQUOEAMxPip5c0cjEgUVVGhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMGCsoPjpSFxI2KDMwIQltWmNGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSCE6ASIbFQ4tJmdkbjAgEh0OVBAVFjsaASssDRUWGAI2P2kcOAIrBxpIYhYnFyAZBWgoPDJaJgI5Py88PDQgAR8PUgcZMCUFDSY9fBMMFAksOGkKOgYhGhwLEVxmBCYeAzs5MzUfSyA9PxQ8PBEgAT0PXAcIHD5EQUJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaFAk8Yk15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdleUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUIvFWkFGxs9MzITBAp4Py88IG1lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUyAKSCUmNjNaTFp4aRc8PAEgEB1GGVN2Q2xMRWg7OyURCE56azMxKwlPU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpJjcIFgIsBi43YkcxEhsBVBYLEjFMVWh5fG5JXUdoZX5tbkpoUzkDQwQjED1mSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc9JzQ8JwFlHgYCVEJ7TmlOLycmNnZSSVd1cnJ8Z0VlBwEDX2hmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUcsKjU+KxMIGgdKERYnAS4JHAUoKnZHUVd2fXB1bldrS1hGHE9mNjEPDSQlNzgOe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlFgUVVAsgUyQDDC1pb2taUyM9KCI3OkdtRVlLCVJjWmtMHCAsPFxaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kSUBAhFj0hASZlciIbAwA9Pwo4Nkd4U1lIBFJqU3lCXn1pf3taNhU9KjNTbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUIjHzoJSGVkcgQbHwM3Jk15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2kYCTouNyI3GAl0azM4PAAgByQHSUJ7U3lCWnhlcmZUSF9Sa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kDXwZMU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSC0lITNwUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcsFUkLXgYjU3RRSGoZNyQcFAQsa29ofldgU0RGQws1GDBFSmg9OjMUe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGERYnAS4JHAUgPHpaBQYqLCItAwY9U1RGAUx/RGVMWWZ5cntXUTc9OSE8LRNPU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2kJBDssOzBaHAg8Lmdkc0dnNAYJVUJuS3lBUX1se3RaBQ89JU15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2kYCTouNyI3GAl0azM4PAAgByQHSUJ7U3lCUHllcmZUSFF4Zmp5Cx8mFgUKVAwyeWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaFAsrLi4/bgoqFwxGDF9mUQ0JCy0nJnZSR1d1c3d8Z0VlBwEDX2hmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUcsKjU+KxMIGgdKERYnAS4JHAUoKnZHUVd2fXZ1bldrRFBGHE9mNDsJCTxDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2c8IhQgU0RLETAnHS0DBUJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcxEhsBVBYLGidASDwoIDEfBSo5M2dkbldrQVlKEVJoSnBmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc9JSNTbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwwIVWhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMYmhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZXXEcPKi4tbhIrBwAKESkvECIvByY9IDkWHQIqZRQ6LwsgUw8HXQ41Uz4FHCAgPHYOEBU/LjMUJwllEgcCERYnAS4JHAUoKlxaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4Jyg6LwtlEAgWRRc0Fi0/CyklN3ZHUQkxJ015bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlHwYFUA5mACoNBC0KPTgUe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2c1IQQkH0kVUgMqFhsJCSshNzJaTEc+KisqK21lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGQgEnHywvByYncmtaIxI2GCIrOA4mFkc2QwcUFicIDTpzETkUHwI7P28/OwkmBwAJX0pveWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaGAF4JSgtbiwsEAIlXgwyASYABC07fB8UPA42IiA4IwJlBwEDX2hmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUcrKCY1KyQqHQdcdQs1ECYCBi0qJn5Te0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGERAjBzweBkJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ayI3Km1lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUyUDCyklciUZEAs9a3p5BQ4mGCoJXxY0HCUADTpnATUbHQJSa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kPV0I1ECgADWh3b3YOEBU/LjMUJwllEgcCERElEiUJSHR0ciIbAwA9Pwo4NkcxGwwIO0JmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaURQ7Kis8HAIkEAEDVUJ7Uz0eHS1DcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlEAgWRRc0Fi0/CyklN3ZHURQ7Kis8REdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSDsqMzofMgg2JX0dJxQmHAcIVAEyW2BmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc9JSNTbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwwIVUtMU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSEJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaXEp4HCYwOkcwA0kSXkJ3XXxMGy0qPTgeAkc+JDV5Og8gUxoFUA4jUz0DSCAgJnYOGQJ4PyYrKQIxU0EOVAM0BysJCTxpNDkIUQo5M2cqPgIgF0BsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUyUDCyklcjUSFAQzGDM4PBNlTkkSWAEtW2BmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpciESGAs9ayk2Okc2EAgKVDAjEioEDSxpMzgeUSwxKCwaIQkxAQYKXQc0XQACJSEnOzEbHAJ4Kik9bhMsEAJOGEJrUyoEDSsiASIbAxN4d2doYFJlEgcCESEgFGctHTwmGT8ZGkc8JE15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGETAzHRoJGj4gMTNUOQI5OTM7KwYxST4HWBZuWkNMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpNzgee0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2cwKEc2EAgKVCEpHSdCKycnPDMZBQI8azMxKwllAAoHXQcFHCcCUgwgITUVHwk9KDNxZ0cgHQ1sEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU0NMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpf3taQkl4Dik9bhMtFkkLWAwvFCgBDWg+OyISURMwLmcaDzcRJjsjdUI1ECgADWg/MzoPFG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5OhUsFA4DQycoFwIFCyNhMTcKBRIqLiMKLQYpFkBsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGVAwieWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU0NMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lBRWgPPjcdURMwLmcrKxMwAQdGfy0RUzoDSCUoOzhaHQg3O2c6LwliB0kSVA4jAyYeHGgtJyQTHwB4PCYwOkwxBAwDX2hmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUIvABsJHD07PD8UFjM3AC46JTckF0lbERY0BixmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMYmhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGVkcmJUUTA5IjN5KAg3UzoSUBYzAGkYB2grNzUVHAJ4aRMqOwkkHgBEEUonFT0JGmglMzgeGAk/a2x5LBUkGgcUXhZmBzsNBjsvPSQXWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd1ZmcNJg42UwQDUAw1Uz0EDWguMzsfUQ85OGcpPAgmFhoVVAZmByEJSCMgMT1aEAk8azQtLxUxFg1GRQojUzsJHD07PHYJFBYtLik6K21lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcpHAoHXUIyADw/HCk7JnZHURMxKCxxZ21lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcyGwAKVEIBEiQJICknNjofA0kLPyYtOxRlDVRGEzY1BicNBSFrcjcUFUcsIiQyZk5lXkkSQhcVBygeHGh1cmdPUQY2L2caKABrMhwSXikvECJMDCdDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaURM5OCx3OQYsB0FWH1BveWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUywCDEJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpf3taPAguLmctIUcuGgoNERInF2kZGyEnNXYyBAo5JSgwKkc1GxAVWAE1U2EZBiknMT4VAwI8Z2cuLxEgUxkTQgojAGkCCTw8IDcWHR5xQWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ays2LQYpUwQJRwcFGygeSHVpHjkZEAsIJyYgKxVrMAEHQwMlByweYmhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSCQmMTcWURU3JDN5c0coHB8DcgonAWkNBixpPzkMFCQwKjV3HhUsHggUSDInAT1mSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMBCcqMzpaGRI1a3p5IwgzFioOUBBmEicISCUmJDM5GQYqcQEwIAMDGhsVRSEuGiUIJy4KPjcJAk96AzI0LwkqGg1EGGhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUIvFWkeByc9cjcUFUcwPip5LwkhUy4HXAcOEicIBC07fAUOEBMtOGdkc0dnJxoTXwMrGmtMHCAsPFxaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4Jyg6LwtlBwgUVgcyIyYfSHVpOT8ZGjc5L2kJIRQsBwAJX0JtUx8JCzwmIGVUHwIvY3d1blRpU1lPO0JmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcntXUSM9PyIrIw4rFkkRUBQjUzocDS0tcjAIHgp4KiQtJxEgUx4HRwdmGidMHyc7OSUKEAQ9QWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcpHAoHXUIxEj8JOzgsNzJaTEdpfnJTbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUxkFUA4qWy8ZBis9OzkUWU5Sa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kKXgEnH2k7LGh0ciQfABIxOSJxHAI1HwAFUBYjFxoYBzooNTNUIg85OSI9YCMkBwhIZgMwFg0NHClgWHZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5KAg3UzZKERUnBSxMASZpOyYbGBUrYzA2PAw2AwgFVEwREj8JG3IONyI5GQ40LzU8IE9sWkkCXmhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc0JCQ4IkchEh0HEV9mJA1CPyk/NyUhBgYuLmkXLwogLmNGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnYTF0c8KjM4bgYrF0kCUBYnXRocDS0tciISFAlSa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSD8oJDMpAQI9L2dkbgMkBwhIYhIjFi1mSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwsUVAMteWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ayI3Km1lU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUywCDEJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaFAk8Yk15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdleUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJrXmk/DTxpISMKFBV4Iy4+JkcSEgUNYhIjFi1MHCdpPSMOAxI2azMxK0cyEh8DO0JmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2kEHSVnBTcWGjQoLiI9blplBAgQVDE2FiwISGJpYHhPe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2cxOwp/MAEHXwUjID0NHC1hFzgPHEkQPio4IAgsFzoSUBYjJzAcDWYbJzgUGAk/Yk15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdleUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJrXmkhBz4sBjlaBQgvKjU9bgwsEAJGQQMieWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGghJztAPAguLhM2ZhMkAQ4DRTIpAGBmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpclxaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4Zmp5GQYsB0kTXxYvH2kPBCc6N3YOHkczIiQybhckF2NGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmHyYPCSRpPzkMFDQsKjUtblplBwAFWkpveWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGg+Oj8WFEcsIiQyZk5lXkkLXhQjID0NGjxpbnZLREc5JSN5DQEiXSgTRQ0NGioHSCwmWHZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5IggmEgVGUhc0ASwCHAshMyRaTEcUJCQ4IjcpEhADQ0wFGygeCSs9NyRwUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcpHAoHXUIlBjseDSY9ADkVBUdlayQsPBUgHR0lWQM0UygCDGgqJyQIFAksCC84PEkVAQALUBA/IygeHEJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ay4/bgQwARsDXxYUHCYYSDwhNzhwUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGXQ0lEiVMDCE6JnZHUU87PjUrKwkxIQYJRUwWHDoFHCEmPHZXURM5OSA8OjcqAEBIfAMhHSAYHSwsWHZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwAAEQYvAD1MVGhxciISFAlSa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSCo7NzcRe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEQcoF0NMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d0Y0cXFkQPQhEzFmkhBz4sBjlaGAF4Pyg2bgEkAUlOQwc1Fj0fSDwgPzMVBBNxQWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmUyAKSCwgISJaT0dre2ctJgIreUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUcwPipjAwgzFj0JGRYnAS4JHBgmIX9wUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGVAwieWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaFAk8QWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGRQM1GGcbCSE9emZUQk5Sa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bgIrF2NGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmeWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhkf3YoFBQsJDU8bgkqAQQHXUIREiUHOzgsNzJwUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ay8sI0kSEgUNYhIjFi1MVWh4ZFxaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4QWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdoXkkyVA4jAyYeHGgsKjcZBQshayg3OghlGAAFWkI2Ei1MHCdpNSMbAwY2PyI8bgUwBx0JX0IwGjoFCiElOyIDe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2crIQgxXSogQwMrFmlRSAsPIDcXFEk2LjBxJQ4mGDkHVUwWHDoFHCEmPHZRUTE9KDM2PFRrHQwRGVJqU3pASHhge1xaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4QWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdoXkkgXhAlFmkWByYsciMKFQYsLmcqIUcOGgoNcxcyByYCSCk5IjMbAxR4Iio0KwMsEh0DXRtMU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSDgqMzoWWQEtJSQtJwgrW0BsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGglPTUbHUcCJCk8DQgrBxsJXQ4jAWlRSDosIyMTAwJwGSIpIg4mEh0DVTEyHDsNDy1nHzkeBAs9OGkaIQkxAQYKXQc0PyYNDC07fAwVHwIbJCktPAgpHwwUGGhmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcgwVHwIbJCktPAgpHwwUCzc2FygYDRImPDNSWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5KwkhWmNGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kDXwZMU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmeWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2RBSAk7ID8MFAN4KjN5JQ4mGEkWUAZoUwABBS0tOzcOFAshazU8PRMkAR1GUhslHyxCYmhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSDssISUTHgkPIikqblplAAwVQgspHR4FBjtpeXZLe0d4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUW14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd1ZmcaIgIkAUkAXQMhUzoDSCQmPSZaEgY2azU8PRMkAR1GWA8rFi0FCTwsPi9wUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaGBQKLjMsPAksHQ4yXikvECI8CSxpb3YcEAsrLk15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2c1LxQxOAAFWicoF2lRSDwgMT1SWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUdSa2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4Zmp5BgYrFwUDEQUjHSweCSRpITMJAg43JWc1JwosB2NGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kKXgEnH2kYCTouNyIpBRV4dmcWPhMsHAcVHzEjADoFByYdMyQdFBN2HSY1OwJlHBtGEysoFSACATwscFxaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnYTF0csKjU+KxMWBxtGT19mUQACDiEnOyIfU0csIyI3REdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kKXgEnH2kAASUgJnZHURM3JTI0LAI3Wx0HQwUjBxoYGmFDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUQ4+ayswIw4xUwgIVUI1FjofAScnBT8UAkdmdmc1JwosB0kSWQcoeWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaMgE/ZQYsOggOGgoNEV9mFSgAGy1DcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2cpLQYpH0EARAwlByADBmBgcgIVFgA0LjR3DxIxHCIPUgl8ICwYPiklJzNSFwY0OCJwbgIrF0BsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGgFOzQIEBUhcQk2Og4jCkFEYgc1ACADBmglOzsTBUcqLiY6JgIhU0FEEUxoUyUFBSE9cnhUUUV4PC43PU5rUygTRQ1mOCAPA2g6JjkKAQI8ZWVwREdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0kDXREjeWlMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaPQ46OSYrN10LHB0PVxtuURoJGzsgPThaIRU3LDU8PRR/U0tGH0xmACwfGyEmPAETHxR4ZWl5bEhnU0dIEQ4vHiAYQUJpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaFAk8QWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4ayI3Km1lU0lGEUJmU2lMSGhpcnZaUUd4ayI1PQJPU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlBwgVWkwxEiAYQHhnZ39wUUd4a2d5bkdlU0lGEUJmU2lMSGgsPDJwUUd4a2d5bkdlU0lGEUJmUywCDEJpcnZaUUd4a2d5bkcgHQ1sEUJmU2lMSGgsPDJwUUd4a2d5bkcxEhoNHxUnGj1EQUJpcnZaFAk8QSI3Kk5PeURLESMzByZMOy0lPnY2HggoQTM4PQxrABkHRgxuFTwCCzwgPThSWG14a2d5OQ8sHwxGRRAzFmkIB0JpcnZaUUd4ay4/biQjFEcnRBYpICwABGg9OjMUe0d4a2d5bkdl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U0lGXQ0lEiVMHCk7NTMOUVp4BDctJwgrAEczQQU0Ei0JPCk7NTMOXzE5JzI8bgg3U0snXQ5keWlMSGhpcnZaUUd4a2d5bkdlU0lGWARmBygeDy09cmtHUUUZJyt7bhMtFgdsEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGVw00UyBMVWh4fnZJQUc8JE15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlGg9GXw0yUwoKD2YIJyIVJBc/OSY9KyUpHAoNQkIyGywCSCo7NzcRUQI2L015bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlHwYFUA5mAGlRSDslPSIJSyExJSMfJxU2ByoOWA4iW2s/BCc9cHZUX0cxYk15bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlGg9GQkInHS1MG3IPOzgeNw4qODMaJg4pF0FEYQ4nECwIOCk7JnRTURMwLilTbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUI2ECgABGAvJzgZBQ43JW9wREdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSAYsJiEVAwx2DS4rKzQgAR8DQ0pkMRY5GC87MzIfU0t4Im5TbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUIjHS1FYmhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4PyYqJUkyEgASGVJoQWBmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcjMUFW14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUc9JSNTbkdlU0lGEUJmU2lMSGhpcnZaUUc9JzQ8REdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bgsqEAgKEREqHD0iHSVpb3YOEBU/LjNjIwYxEAFOEzEqHD1MQG0teX9YWG14a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUcxLWcqIggxPRwLERYuFidmSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcjoVEgY0ayksI0d4Ux0JXxcrESweQDslPSI0BApxQWd5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcpHAoHXUI1U3RMGyQmJiVANw42LwEwPBQxMAEPXQZuURoABzxrcnhUUQktJm5TbkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwAAERFmEicISDtzFD8UFSExOTQtDQ8sHw1OEzIqEioJDBgoICJYWEcsIyI3REdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmHyYPCSRpMT4bA0dlaws2LQYpIwUHSAc0XQoECTooMSIfA214a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlUwUJUgMqUzsDBzxpb3YZGQYqayY3KkcmGwgUCyQvHS0qATo6JhUSGAs8Y2UROwokHQYPVTApHD08CTo9cH9wUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcsFUkUXg0yUz0EDSZDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlAQYJRUwFNTsNBS1pb3YJXyQeOSY0K0duUz8DUhYpAXpCBi0+emZWUVR0a3dwREdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMSDwoIT1UBgYxP29pYFRseUlGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2lMDSYtWHZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5PgQkHwVOVxcoED0FByZhe1xaUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkdlU0koVBYxHDsHRg4gIDMpFBUuLjVxbCUaJhkBQwMiFmtASCY8P39wUUd4a2d5bkdlU0lGEUJmU2lMSGhpcnZaUUd4a2d5bkcgHQ1PO0JmU2lMSGhpcnZaUUd4a2d5bkdlU0lGEUJmU2kJBixDcnZaUUd4a2d5bkdlU0lGEUJmU2lMSGhpNzgee0d4a2d5bkdlU0lGEUJmU2lMSGhpNzgee0d4a2d5bkdlU0lGEUJmU2kJBixDcnZaUUd4a2d5bkdlFgcCO0JmU2lMSGhpNzgee0d4a2d5bkdlBwgVWkwxEiAYQHtgWHZaUUc9JSNTKwkhWmNsHE9mMSgPAy87PSMUFUc0JCgpbhMqUw0fXwMrGioNBCQwciMKFQYsLmcdPAg1FwYRXxFmWxwcDzooNjNaAgs3PzR5LwkhUyYRXwciUz4JAS8hJiVTexM5OCx3PRckBAdOVxcoED0FByZhe1xaUUd4PC8wIgJlBxsTVEIiHENMSGhpcnZaUUp1a3Z3bjUg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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2 })
