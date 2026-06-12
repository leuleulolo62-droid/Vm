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

local __k = 'Dd9FKvyY9k0p7J7OGXy9qhIL'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2 })
