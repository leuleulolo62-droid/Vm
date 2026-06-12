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

local __k = 'jEqgngoUI0WH6da0uEzkBy49'
local __p = 'R2gqPGRuPRwfcRsbFobhpFUcSABiUXtbGSwVDg8JRnUceV1BZhYOVAAmDgItFxRbHywdA0BHKiMsQi5oUAEARAA3H0s1C1VJGWUFDwtHCDQkVXA7Fis2flUmFgInF0AZJjAQRwIGFjA7Ol5gXwoSRBQrGQ5vFVFPDylRCgsTBzotECQgVwAORxwrHUJiFkYZDCwDAh1HDnU7VTYkFhYEXRoxH0diGFhVSjUSBgILQjI8USUsUwBPOn9MOyhiCVtKHjADAk5PHTAqXyEtRAEFEBM3FQZiDVxcSgkEFQ8XB3UffXcrWQoSRBQrDksyFltVQ39REwYCTzQnRD5lVQwEUQFPcw8nDVFaHjZRDwEIBCZpRj4pFg0SUxYpFRg3C1EWAzYdBAIIHCA7VXdgVQgOQwA3H0Y2AERcSiMdDh4URnUoXjNoWwEVUQEkGAcncz1VBSYaFEJHDjstECUtRgsTRAZlFR0nCxRxHjEBNAsVGTwqVXloYgwEQhAjFRknWUBRAzZRFA0VBiU9EBkNYCEzEB0qFQAkDFpaHiweCUkUZVwoEDkpQg0XVVoXFQkuFkwZKxU4RwgSATY9WTgmFgUPVFULPz0HKxRRBSoaFE4GTzIlXzUpWkQMVQEkFw42EVtdRGU4E04IATkwOl47XgUFXwI2WgYnDVxWDjZRCABHGz0sEDApWwFGQ1UqDQViNUFYSiYdBh0UTzwnQyMpWAcEQ1VtFh4jWVdVBTYEFQsURnlpQjIpUhdrOQUkCRgrD1FVE2lRBgADTycsXjMtRBdBUxksHwU2VEdQDiBfRz0CHSMsQnouVwcIXhJlGwg2EFtXGWUCEw8eTyUlUSI7XwYNVVtPcGIODFUZX2tASh0GCTBpfCIpQ15BXhplUVZuWVpWSiYeCRoOASAsHHcmWUQADxd/GUs2HEZXCzcISWQ6Ml9DHXpnGUQyVQczEwgnCj5VBSYQC043AzQwVSU7FkRBEFVlWktiWQkZDSQcAlQgCiEaVSU+XwcEGFcVFgo7HEZKSGx7CwEEDjlpYiImZQETRhwmH0tiWRQZSmVMRwkGAjBzdzI8ZQETRhwmH0NgK0FXOSADEQcECndgOjsnVQUNECA2HxkLF0RMHhYUFRgODDBpDXcvVwkECjIgDjgnC0JQCSBZRTsUCicAXic9QjcEQgMsGQ5gUD5VBSYQC04wACciQycpVQFBEFVlWktiWQkZDSQcAlQgCiEaVSU+XwcEGFcSFRkpCkRYCSBTTmQLADYoXHcEXwMJRBwrHUtiWRQZSmVRR1NHCDQkVW0PUxAyVQczEwgnURZ1AyIZEwcJCHdgOjsnVQUNEDYqFgcnGkBQBStRR05HT3VpDXcvVwkECjIgDjgnC0JQCSBZRS0IAzksUyMhWQoyVQczEwgnWx0zBioSBgJHPTA5XD4rVxAEVCYxFRkjHlEESiIQCgtdKDA9YzI6QA0CVV1nKA4yFV1aCzEUAz0TACcoVzJqH25rXBomGwdiNVtaCykhCw8eCidpDXcYWgUYVQc2VCctGlVVOikQHgsVZTkmUzYkFicAXRA3G0tiWRQZSnhRMAEVBCY5UTQtGCcUQgcgFB8BGFlcGCR7bUNKQHppZR5oWg0DQhQ3A0tqIAZSSmpRKAwUBjEgUTloRRAAUx5scActGlVVSjcUFwFHUnVrWCM8RhdbH1o3GxxsHl1NAjATEh0CHTYmXiMtWBBPUxooVTJwEmdaGCwBEywGDD57cjYrXUsuUgYsHgIjF2FQRSgQDgBITV8lXzQpWkQtWRc3Gxk7WRQZSmVRWk4LADQtQyM6XwoGGBIkFw54MUBNGgIUE0YVCiUmEHlmFkYtWRc3Gxk7V1hMC2dYTkZOZTkmUzYkFjAJVRggNwosGFNcGGVMRwIIDjE6RCUhWANJVxQoH1EKDUBJLSAFTxwCHzppHnloFAUFVBorCUQWEVFUDwgQCQ8ACidnXCIpFE1IGFxPFgQhGFgZOSQHAiMGATQuVSVoFllBXBokHhg2C11XDW0WBgMCVR09RCcPUxBJQhA1FUtsVxQbCyEVCAAUQAYoRjIFVwoAVxA3VAc3GBYQQ21YbWQLADYoXHcHRhAIXxs2WlZiNV1bGCQDHkAoHyEgXzk7PAgOUxQpWj8tHlNVDzZRWk4rBjc7USUxGDAOVxIpHxhIcxkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZIVBkZOREwMyttQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSmQLADYoXHcOWgUGQ1V4WhBIcBkUSiYeCgwGG19AYz4kUwoVcRwoWktiWRQZSnhRAQ8LHDBlOl4bXwgEXgEXGwwnWRQZSmVRWk4BDjk6VXtoFkRMHVUjGwcxHBQESikUAAcTT30PfwFoUQUVVRFsVks2C0FcSnhRFQ8ACnVhXDgrXUQPVRQ3Hxg2UD4wKywcIQERPTQtWSI7FkRBEEhlS1pyVT4wKywcLwcTDToxEHdoFkRBEEhlWCMnGFAbRmVRSkNHJzAoVHdnFiYOVAxlVUsMHFVLDzYFbWcmBjgfWSQhVAgEcx0gGQBiRBRNGDAUS2RuLjwkZDIpWycJVRYuWktiWQkZHjcEAkJtZhQgXQc6UwAIUwEsFQViWRQESnVfV0JtZhsmYyc6UwUFEFVlWktiWRQESiMQCx0CQ19AfjgaUwcOWRllWktiWRQZSnhRAQ8LHDBlOl4cRA0GVxA3GAQ2WRQZSmVRWk4BDjk6VXtCPzATWRIiHxkGHFhYE2VRR05aT2VnAGRkPG0pWQEnFRMHAURYBCEUFU5HUnUvUTs7U0hrOT0sDgktAWdQECBRR05HT3V0EG9kPG0yWBoyPAQ0WRQZSmVRR05HUnUvUTs7U0hrOVhoWg4xCT4wLzYBIgAGDTksVHdoFllBVhQpCQ5ucz18GTUzCBZHT3VpEHdoC0QVQgAgVmFLPEdJJCQcAk5HT3VpEGpoQhYUVVlPcy4xCXxcCykFD05HT3V0ECM6QwFNOnwACRsGEEdNCysSAk5HUnU9QiItGm5odQY1LhkjGlFLSmVRR1NHCTQlQzJkPG0kQwURHwovOlxcCS5RWk4THSAsHF1BcxcRfRQ9PgIxDRQZSnhRVl5XX3lDORI7RicOXBo3WktiWRQESgYeCwEVXHsvQjglZCMjGEVpWllzSRgZWHdITkJtZnhkEDonQAEMVRsxcGIVGFhSOTUUAgooAXV0EDEpWhcEHFUSGwcpKkRcDyFRWk5WWXlDOR09WxQuXlVlWktiWQkZDCQdFAtLTx88XScYWRMEQlV4Wl5yVT4wIysXLRsKH3VpEHdoC0QHURk2H0dIcHJVEwofR05HT3VpEGpoUAUNQxBpWi0uAGdJDyAVR1NHWWVlOl4GWQcNWQUKFEtiWRQESiMQCx0CQ19AHXpoRggASRA3cGIDF0BQKyMaR05HUnUvUTs7U0hrOTYwCR8tFHJWHGVMRwgGAyYsHHcOWRI3URkwH0t/WQMJRk94IRsLAzc7WTAgQllBVhQpCQ5ucz0UR2UWBgMCZVwIRSMnZxEERRBlR0skGFhKD2l7GmRtAzoqUTtodQsPXhAmDgItF0cZV2UKGk5HT3hkEAUKbjcCQhw1DigtF1pcCTEYCAAUTyEmEDQkUwUPOhkqGQouWWBRGCAQAx1HT3VpEGpoTRlBEFVoV0sjGkBQHCBRCwEIH3UkUSUjUxYSOhkqGQouWWZcGTEeFQsUT3VpEGpoTRlBEFVoV0skDFpaHiweCR1HGzppRTksWUQJXxouCUQwHEdQECACRwEJTyAnXDgpUm4NXxYkFksGC1VOAysWFE5HT3V0ECw1FkRBHVhlPzgSWVBLCzIYCQlHADcjVTQ8RUQRVQdlCgcjAFFLYE8dCA0GA3UvRTkrQg0OXlUxCAohEhxaBSsfTmRuLDonXjIrQg0OXgYeWSgtF1pcCTEYCAAUT35pAQpoC0QCXxsrcGIwHEBMGCtRBAEJAV8sXjNCPElMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXpCG0lBYzQDP0sQPGd2JhM0NT1HRzYoUz8tUkhBQhBoCA4xFlhPDyFRAwsBCjs6WSEtWh1IOlhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lrXBomGwdiKWcZV2U9CA0GAwUlUS4tRF42URwxPAQwOlxQBiFZRT4LDiwsQgQrRA0RRAZnU2FIFVtaCylRARsJDCEgXzloQhYYYhA0DwIwHBxQBDYFTmRuBjNpXjg8Fg0PQwFlDgMnFxRLDzEEFQBHATwlEDImUm5oXBomGwdiFl8VSigeA05aTyUqUTskHhYEQQAsCA5uWV1XGTFYbWcOCXUmW3c8XgEPEAcgDh4wFxRUBSFRAgADZVw7VSM9RApBXhwpcA4sHT4zBioSBgJHKTwuWCMtRCcOXgE3FQcuHEYzBioSBgJHCSAnUyMhWQpBVxAxPChqUD4wAyNRIQcAByEsQhQnWBATXxkpHxliDVxcBGUDAhoSHTtpdj4vXhAEQjYqFB8wFlhVDzdRAgADZVwlXzQpWkQPXxEgWlZiKWcDLCwfAygOHSY9cz8hWgBJEjYqFB8wFlhVDzcCRUdtZjsmVDJoC0QPXxEgWgosHRRXBSEUXSgOATEPWSU7QicJWRkhUkkEEFNRHiADJAEJGycmXDstREZIOnwDEwwqDVFLKSofExwIAzksQnd1FhATSScgCx4rC1ERBCoVAkdtZicsRCI6WEQnWRItDg4wOltXHjceCwICHV8sXjNCPAgOUxQpWg03F1dNAyofRwkCGxMgVz88UxZJGX9MFgQhGFgZLAZRWk4ACiEPc39hPG0IVlUrFR9iP3cZHi0UCU4VCiE8QjloWA0NEBArHmFLFVtaCylRAU5aTycoRzAtQkwnc1llWCctGlVVLCwWDxoCHXdgOl4hUEQHEEh4WgUrFRRNAiAfbWduAzoqUTtoWQ9NEAdlR0syGlVVBm0XEgAEGzwmXn9hFhYERAA3FEsEOhp1BSYQCygOCD09VSVoUwoFGX9McwIkWVtSSjEZAgBHCXV0ECVoUwoFOnwgFA9IcEZcHjADCU4BZTAnVF1CG0lBQhA2FQc0HBRYSjcUCgETCnU8XjMtREQzVQUpEwgjDVFdOTEeFQ8ACnsbVTonQgESEBc8WhsjDVwZGSAWCgsJGyZDXDgrVwhBYhAoFR8nCnJWBiEUFU5aTwcsQDshVQUVVREWDgQwGFNcUAMYCQohBic6RBQgXwgFGFcXHwYtDVFKSGx7CwEEDjlpViImVRAIXxtlHQ42K1FUBTEUT0BJQXxDOT4uFgoORFUXHwYtDVFKLCodAwsVTyEhVTloRAEVRQcrWgUrFRRcBCF7bgIIDDQlEDknUgFBDVUXHwYtDVFKLCodAwsVZVwlXzQpWkQSVRI2WlZiAhQXRGtRGmRuAzoqUTtoX0RcEERPcxwqEFhcSiseAwtHDjstED5oCllBEwYgHRhiHVszY0wfCAoCT2hpXjgsU14nWRshPAIwCkB6AiwdA0YUCjI6az4VH25oORxlR0srWR8ZW094AgADZVw7VSM9RApBXhohH2EnF1AzYGhcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkzR2hRMy81KBAdeRkPFkwRUQY2Ex0nWUZcCyECRwEJAyxgOnplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhDXDgrVwhBeDwROCQaJnp4JwAiR1NHFF9AeDIpUkRcEA5lWCMrDVZWEg0UBgpFQ3VreD48VAsZeBAkHjgvGFhVSGlRRSYCDjFrECpkPG0jXxE8WlZiAhQbIiwFBQEfLTotSXVkFkYpWQEnFRMAFlBAOSgQCwJFQ3VreCIlVwoOWREXFQQ2KVVLHmddR0wyHyUsQgMnRBcOElU4VmE/cz5VBSYQC04BGjsqRD4nWEQHWQc2DigqEFhdQigeAwsLQ3UnUTotRU1rORkqGQouWV0ZV2VAbWcQBzwlVXchFlhcEFYrGwYnChRdBU94bgIIDDQlECdoC0QMXxEgFlEEEFpdLCwDFBokBzwlVH8mVwkEQy4sJ0JIcD1QDGUBRxoPCjtpQjI8QxYPEAVlHwUmcz0wA2VMRwdHRHV4Ol4tWABrOQcgDh4wFxRXAyl7AgADZV8lXzQpWkQHRRsmDgItFxRQGQQdDhgCRzYhUSVhPG0NXxYkFksqDFkZV2USDw8VTzQnVHcrXgUTCjMsFA8EEEZKHgYZDgIDIDMKXDY7RUxDeAAoGwUtEFAbQ094DghHByAkEDYmUkQJRRhrMg4jFUBRSnlMR15HGz0sXnc6UxAUQhtlHAouClEZDysVbWcVCiE8QjloVQwAQlU7R0ssEFgzDysVbWQLADYoXHcuQwoCRBwqFEsrCnFXDygITx4LHXlpRDIpWycJVRYuU2FLEFIZGikDR1NaTxkmUzYkZggASRA3Wh8qHFoZGCAFEhwJTzMoXCQtFgEPVH9MEw1iF1tNSjEUBgMkBzAqW3c8XgEPEAcgDh4wFxRNGDAURwsJC19AXDgrVwhBXRwrH0tiRBR1BSYQCz4LDiwsQm0PUxAgRAE3Ewk3DVERSBEUBgMuK3dgOl4kWQcAXFUxEg4rCxQESjUdFVQgCiEIRCM6XwYURBBtWD8nGFlwLmdYbWcOCXUkWTktFllcEBssFkstCxRNAiAYFU5aUnUnWTtoQgwEXlU3Hx83C1oZHjcEAk4CATFDOSUtQhETXlUoEwUnWUoESjEZAgcVZTAnVF1CWgsCURllHB4sGkBQBStREAEVAzEdXwQrRAEEXl01FRhrcz1VBSYQC04RQ3UmXnd1FicAXRA3G1EVFkZVDhEeMQcCGCUmQiMYWQ0PRF01FRhrcz1LDzEEFQBHOTAqRDg6BEoPVQJtDEUaVRRPRBxYS04IAXlpRnkSPAEPVH9PV0ZiC1VACSQCE04RBiYgUj4kXxAYEBM3FQZiGlVUDzcQRxoITyEoQjAtQkhBWRIrFRkrF1MZBioSBgJHRHU9USUvUxBBUx0kCGEuFldYBmUXEgAEGzwmXnchRTIIQxwnFg5qDVVLDSAFNw8VG3lpRDY6UQEVcx0kCEJIcFhWCSQdRx4GHTQkQ3d1FjYASRYkCR8SGEZYBzZfCQsQR3xDOScpRAUMQ1sDEwc2HEZtEzUUR1NHKjs8XXkaVx0CUQYxPAIuDVFLPjwBAkAiFzYlRTMtPG0NXxYkFkskEFhNDzdRWk4cTxYoXTI6V0QcOnwsHEsOFldYBhUdBhcCHXsKWDY6VwcVVQdlDgMnFxRfAykFAhw8TDMgXCMtRERKEEQYWlZiNVtaCykhCw8eCidncz8pRAUCRBA3Wg4sHT4wAyNREw8VCDA9cz8pREQVWBArWg0rFUBcGB5SAQcLGzA7EHxoBzlBDVUxGxklHEB6AiQDRwsJC19AQDY6VwkSHjMsFh8nC3BcGSYUCQoGASE6eTk7QgUPUxA2WlZiH11VHiADbWcLADYoXHcnRA0GWRtlR0sBGFlcGCRfJCgVDjgsHgcnRQ0VWRorcGIuFldYBmUVDhxHUnU9USUvUxAxUQcxVDstCl1NAyofR0NHACcgVz4mPG0NXxYkFkswHEcZV2UmCBwMHCUoUzJyZAUYUxQ2DkMtC11eAytdRwoOHXlpQDY6VwkSGX9MCA42DEZXSjcUFE5aUnUnWTtCUwoFOn9oV0shEVtWGSBREwYCTzcsQyNoRQ0NVRsxVworFBRNCzcWAhpcTycsRCI6WBdBS1U1Gxk2RBgZCywcNwEUUnlpUz8pRFlBTVUqCEssEFgzBioSBgJHCSAnUyMhWQpBVxAxKQIuHFpNPiQDAAsTR3xDOTsnVQUNEBYgFB8nCxQESgYQCgsVDnsfWTI/RgsTRCYsAA5iUxQJRHB7bgIIDDQlEDUtRRBNEBcgCR8RGltLD094CwEEDjlpQDspTwETQ1V4WjsuGE1cGDZLIAsTPzkoSTI6RUxIOnwpFQgjFRRQSnhRVmRuGD0gXDJoX0RdDVVmCgcjAFFLGWUVCGRuZjkmUzYkFhQNQlV4WhsuGE1cGDYqDjNtZlwlXzQpWkQCWBQ3WlZiCVhLRAYZBhwGDCEsQl1BPw0HEBYtGxliGFpdSiwCJgIOGTBhUz8pRE1BURshWgIxPFpcBzxZFwIVQ3UPXDYvRUogWRgRHwovOlxcCS5YRxoPCjtDOV5BWgsCURllDQosDXpYByACbWduZjwvEBEkVwMSHjQsFyMrDVZWEmVMWk5FLTotSXVoQgwEXn9Mc2JLDlVXHgsQCgsUT2hpeB4cdCs5bzsENy4RV3ZWDjx7bmduCjk6VV1BP21oRxQrDiUjFFFKSnhRLyczLRoRbxkJeyEyHj0gGw9IcD0wDysVbWduZjkmUzYkFhQAQgFlR0skEEZKHgYZDgIDRzYhUSVkFhMAXgELGwYnCh0ZBTdRAQcVHCEKWD4kUkwCWBQ3VksKMGB7JR0uKS8qKgZncjgsT01rOXxMEw1iCVVLHmUFDwsJZVxAOV4kWQcAXFU2GRknHFoVSiofNA0VCjAnHHcsUxQVWFV4WhwtC1hdPioiBBwCCjthQDY6QkoxXwYsDgItFx0zY0x4bgcBTzonYzQ6UwEPEBQrHksmHERNAmVPR15HGz0sXl1BP21oORkqGQouWVBQGTFRWk5PHDY7VTImFklBUxArDg4wUBp0CyIfDhoSCzBDOV5BP20NXxYkFksyGEdKYEx4bmduBjNpdjspURdPYxwpHwU2K1VeD2UFDwsJZVxAOV5BPxQAQwZlR0s2C0FcYEx4bmduCjk6VV1BP21oOXw1GxgxWQkZDiwCE05bUnUPXDYvRUogWRgDFR0QGFBQHzZ7bmduZlwsXjNCP21oOXwsHEsyGEdKSiQfA05PATo9EBEkVwMSHjQsFz0rCl1bBiAyDwsEBHUmQnchRTIIQxwnFg5qCVVLHmlRBAYGHXxgECMgUwprOXxMc2JLEFIZBCoFRwwCHCEaUzg6U0QOQlUhExg2WQgZCCACEz0EACcsECMgUwprOXxMc2JLcFZcGTEiBAEVCnV0EDMhRRBrOXxMc2JLcBkUSjUDAgoODCEgXzloHggEURFlGBJiD1FVBSYYExdOZVxAOV5BP20NXxYkFksjEFkZV2UBBhwTQQUmQz48XwsPOnxMc2JLcD1QDGU3Cw8AHHsIWToYRAEFWRYxEwQsWQoZWmUFDwsJZVxAOV5BP21oXBomGwdiD1FVSnhRFw8VG3sIQyQtWwYNSTksFA4jC2JcBioSDhoeZVxAOV5BP21oURwoWlZiGF1USm5REQsLT39pdjspURdPcRwoKhknHV1aHiweCWRuZlxAOV5BUwoFOnxMc2JLcD1bDzYFR1NHFHU5USU8FllBQBQ3DkdiGF1UOioCR1NHDjwkHHcrXgUTEEhlGQMjCxREYEx4bmduZjAnVF1BP21oORArHmFLcD0wDysVbWduZjAnVF1BPwEPVH9McwJiRBRQSm5RVmRuCjstOl46UxAUQhtlGA4xDT5cBCF7bUNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2h7SkNHLBoEchYcFiwufz4WWkMrF0dNCysSAkEUBjsuXDI8WQpBXRAxEgQmWUdRCyEeEAcJCHWrsMNoWAtBXhQxEx0nWVxWBS4CTmRKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcbQIIDDQlEBx4GkQqAVllMVluWX8KSnhRFBoVBjsuHjQgVxZJAFxpWhg2C11XDWsSDw8VR2RgHHc7QhYIXhJrGQMjCxwLQ2lRFBoVBjsuHjQgVxZJA1xPcEZvWWdQBiAfE04mBjhzECQgVwAOR1UCHx8BGFlcGCQ1BhoGTzonECMgU0QtXxYkFi0rHlxNDzdRDgAUGzQnUzJoRQtBRB0gWgwjFFEeGU9cSk4IGDtpRjYkXwAARBAhWg0rC1EZGiQFD04UCjstQ3cnQxZBQhAhExknGkBcDmUQDgNJTwcsHTY4RggIVRFlFQViC1FKGiQGCUBtAzoqUTtoUBEPUwEsFQViHFpKHzcUNAcLCjs9cT4lfgsOW11scGIuFldYBmUXDgkPGzA7EGpoUQEVdhwiEh8nCxwQYEwYAU4JACFpVj4vXhAEQlUxEg4sWUZcHjADCU4CATFDOT4uFhYARxIgDkMkEFNRHiADS05FMAowAjwXUQcFElxlDgMnFxRLDzEEFQBHCjstOl4kWQcAXFUqCAIlWQkZDCwWDxoCHXsOVSMLVwkEQhQBGx8jWRQZSmVcSk4VCiYmXCEtRUQVWBBlGQcjCkcZByAFDwEDZVwgVnc8TxQEGBo3EwxrWUoESmcXEgAEGzwmXnVoQgwEXlU3Hx83C1oZDysVbWcVDiI6VSNgUA0GWAEgCEdiW2tmE3caOAkEC3dlEDg6XwNIOnwjEwwqDVFLRAIUEy0GAjA7URMpQgVBDVUjDwUhDV1WBG0CAgIBQ3VnHnlhPG1oXBomGwdiGlAZV2UeFQcARyYsXDFkFkpPHlxPc2IrHxR/BiQWFEA0BjksXiMJXwlBURshWhgnFVIZV3hRAAsTKTwuWCMtRExIEBQrHks2AERcQiYVTk5aUnVrRDYqWgFDEAEtHwVIcD0wGiYQCwJPCSAnUyMhWQpJGX9Mc2JLFVtaCylRCBwOCDwnEGpoVQA6e0UYcGJLcD1QDGUfCBpHACcgVz4mFhAJVRtlCA42DEZXSiAfA2RuZlxAXDgrVwhBRBQ3HQ42WQkZDSAFNAcLCjs9ZDY6UQEVGFxPc2JLcF1fSjEQFQkCG3U9WDImPG1oOXxMFgQhGFgZBTVRWk4IHTwuWTlmZgsSWQEsFQVIcD0wY0wSAzUsXghpDXcLcBYAXRBrFA41UVtJRmUFBhwACiFnUT4lZgsSGX9Mc2JLcF1fSgMdBgkUQQYgXDImQjYAVxBlDgMnFz4wY0x4bmcECw4CAgpoC0QVUQciHx9sCVVLHk94bmduZlwqVAwDBTlBDVUGPBkjFFEXBCAGT0dtZlxAOV4tWABrOXxMcw4sHT4wY0wUCQpOZVxAVTksPG1oQhAxDxksWVddYEwUCQptZgcsQyMnRAESa1YXHxg2FkZcGWVaR186T2hpViImVRAIXxttU2FLcFhWCSQdRwhHUnUuVSMOXwMJRBA3UkJIcD1QDGUXRw8JC3U7USAvUxBJVlllWDQdAAZSNSISA0xOTyEhVTlCP21oVlsCHx8BGFlcGCQ1BhoGT2hpQjY/UQEVGBNpWkkdJk0LARoWBApFRl9AOV46VxMSVQFtHEdiW2tmE3caOAkEC3dlEDkhWk1rOXwgFA9IcFFXDk8UCQptZXhkEBknFjcRQhAkHlFiClxYDioGRykCGwY5QjIpUkQOXlUxEg5iPlVUDzUdBhcyGzwlWSMxFhcIXhIpHx8tFxQUVGUYAwsJGzw9SXlCWgsCURllHB4sGkBQBStRAgAUGicsfjgbRhYEURENFQQpUR0zYykeBA8LTxIcEGpoQhYYYhA0DwIwHBxrDzUdDg0GGzAtYyMnRAUGVVsIFQ83FVFKUAMYCQohBic6RBQgXwgFGFcCGwYnCVhYExAFDgIOGyxrGX5CPw0HEBsqDksFLBRNAiAfRxwCGyA7XnctWABrORwjWhkjDlNcHm02MkJHTQoWSWUjaRcRQhAkHklrWUBRDytRFQsTGicnEDImUm5oXBomGwdiFEAZV2UWAhoKCiEoRDYqWgFJdyBscGIuFldYBmUeEAACHXV0EH8lQkQAXhFlCAo1HlFNQigFS05FMAogXjMtTkZIGVUqCEsFLD4wAyNRExcXCn0mRzktRE1BTkhlWB8jG1hcSGUFDwsJTzo+XjI6FllBdyBlHwUmcz1JCSQdC0YUCiE7VTYsWQoNSVllFRwsHEYVSiMQCx0CRl9AXDgrVwhBXwcsHUt/WVtOBCADSSkCGwY5QjIpUm5oWRNlDhIyHBxWGCwWTk4ZUnVrViImVRAIXxtnWh8qHFoZGCAFEhwJTzAnVF1BRAUWQxAxUiwXVRQbNRoIVQU4HCU7VTYsFEhBRAcwH0JIcFtOBCADSSkCGwY5QjIpUkRcEBMwFAg2EFtXQjYUCwhLT3tnHn5CP20IVlUDFgolChp3BRYBFQsGC3U9WDImFhYERAA3FEsBP0ZYByBfCQsQR3xpVTksPG1oQhAxDxksWVtLAyJZFAsLCXlpHnlmH25oVRshcGIQHEdNBTcUFDVEPTA6RDg6UxdBG1V0J0t/WVJMBCYFDgEJR3xDOV44VQUNXF0jDwUhDV1WBG1YRwEQATA7HhAtQjcRQhAkHkt/WVtLAyJRAgADRl9AVTksPAEPVH9PV0ZiN1sZOCASCAcLVXU7VSckVwcEECoXHwgtEFgZBStREwYCTxI8XnchQgEMEBYpGxgxWRkHSiseSgEXTyIhWTstFgINURIiHw9sc1hWCSQdRwgSATY9WTgmFgEPQwA3HyUtK1FaBSwdLwEIBH1gOl4kWQcAXFUrFQ8nWQkZOhZLIQcJCxMgQiQ8dQwIXBFtWCYtHUFVDzZTTmRuATotVXd1FgoOVBBlGwUmWVpWDiBLIQcJCxMgQiQ8dQwIXBFtWCI2HFltEzUUFExOZVwnXzMtFllBXhohH0sjF1AZBCoVAlQhBjstdj46RRAiWBwpHkNgPkFXSGx7bgIIDDQlEBA9WCcNUQY2WlZiDUZAOCAAEgcVCn0nXzMtH25oWRNlFAQ2WXNMBAYdBh0UTyEhVTloRAEVRQcrWg4sHT4wAyNRFQ8QCDA9GBA9WCcNUQY2VktgJmtAWC4uFQsEADwlEn5oQgwEXlU3Hx83C1oZDysVbWcXDDQlXH87UxATVRQhFQUuABgZLTAfJAIGHCZlEDEpWhcEGX9MFgQhGFgZBTcYAE5aTycoRzAtQkwmRRsGFgoxChgZSBojAg0IBjlrGV1BXwJBRAw1H0MtC11eQ2UPWk5FCSAnUyMhWQpDEAEtHwViC1FNHzcfRwsJC19AQjY/RQEVGDIwFCguGEdKRmVTODEeXT4WQjIrWQ0NElllDhk3HB0zYwIECS0LDiY6HggaUwcOWRllR0skDFpaHiweCUYUCjkvHHdmGEpIOnxMEw1iP1hYDTZfKQE1CjYmWTtoQgwEXlU3Hx83C1oZDysVbWduHTA9RSUmFgsTWRJtCQ4uHxgZRGtfTmRuCjstOl4aUxcVXwcgCTBhK1FKHioDAh1HRHV4bXd1FgIUXhYxEwQsUR0zY0wBBA8LA30vRTkrQg0OXl1sWiw3F3dVCzYCSTE1CjYmWTtoC0QOQhwiWg4sHR0zYyAfA2QCATFDOnplFgkAWRsxHwUjF1dcSikeCB5dTz4sVSdoXgsOWwZlGxsyFV1cDmUQBBwIHCZpQjI7RgUWXgZlDQMrFVEZCysIRw0IAjcoRHcuWgUGEBw2WgQsc1hWCSQdRwgSATY9WTgmFhcVUQcxOQQvG1VNJyQYCRoGBjssQn9hPG0IVlUREhknGFBKRCYeCgwGG3U9WDImFhYERAA3FEsnF1AzYxEZFQsGCyZnUzglVAUVEEhlDhk3HD4wHiQCDEAUHzQ+Xn8uQwoCRBwqFENrcz0wHS0YCwtHOz07VTYsRUoCXxgnGx9iHVszY0x4Fw0GAzlhVTk7QxYEYxwpHwU2OF1UIioeDEdtZlxAQDQpWghJVRs2DxknN1tqGjcUBgovADoiGV1BP20RUxQpFkMnF0dMGCA/CDwCDDogXB8nWQ9IOnxMcx8jCl8XHSQYE0ZXQWBgOl5BUwoFOnwgFA9rc1FXDk97SkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR09cSk4zPRwOdxIadCs1EF0jExknChRNAiBRAA8KCnI6EDg/WEQSWBoqDksrF0RMHmUGDwsJTzQgXTIsFgUVEBQrWg4sHFlAQ09cSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUYCkeBA8LTzM8XjQ8XwsPEBY3FRgxEVVQGAAfAgMeR3xDOXplFg0SEAEtH0shC1tKGS0QDhxHDCA7QjImQggYEBozHxliGFoZDysUChdHBzw9UjgwCW5oXBomGwdiDVVLDSAFR1NHCDA9Yz4kUwoVZBQ3HQ42UR0zYywXRwAIG3U9USUvUxBBRB0gFEswHEBMGCtRAQ8LHDBpVTksPG0NXxYkFkshHFpNDzdRWk4kDjgsQjZmYA0ERwUqCB8REE5cSm9RV0BSZVwlXzQpWkQSUwcgHwViRBROBTcdAzoIPDY7VTImHhAAQhIgDkUyGEZNRBUeFAcTBjonGV1BRAEVRQcrWkMxGkZcDytRSk4ECjs9VSVhGCkAVxssDh4mHBQFV2VAX2QCATFDOjsnVQUNEBMwFAg2EFtXSjYFBhwTOycgVzAtRAYORF1scGIrHxRtAjcUBgoUQSE7WTAvUxZBRB0gFEswHEBMGCtRAgADZVwdWCUtVwASHgE3EwwlHEYZV2UFFRsCZVw9USQjGBcRUQIrUg03F1dNAyofT0dtZlw+WD4kU0Q1WAcgGw8xV0BLAyIWAhxHDjstEBEkVwMSHiE3EwwlHEZbBTFRAwFtZlxAXDgrVwhBVhw3Hw9iRBRfCykCAmRuZlw5UzYkWkwHRRsmDgItFxwQYEx4bmcOCXUqQjg7RQwAWQcAFA4vABwQSjEZAgBtZlxAOV4kWQcAXFUjEwwqDVFLSnhRAAsTKTwuWCMtRExIOnxMc2JLEFIZDCwWDxoCHXU9WDImPG1oOXxMcw0rHlxNDzdLLgAXGiFhEgQ8VxYVYx0qFR8rF1MbQ094bmduZlwvWSUtUkRcEAE3Dw5IcD0wY0wUCQptZlxAOTImUm5oOXwgFA9rcz0wYywXRwgOHTAtECMgUwprOXxMcx8jCl8XHSQYE0YhAzQuQ3kcRA0GVxA3Pg4uGE0QYEx4bgsLHDBDOV5BPxAAQx5rDQorDRwJRHVETmRuZlwsXjNCP20EXhFPc2IWEUZcCyECSRoVBjIuVSVoC0QPWRlPcw4sHR0zDysVbWRKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcbUNKTx0AZBUHbkQkaCUENC8HKxQRCSkYAgATTycoSTQpRRBBURwhQUswHEdNBTcUFE4IAXUtWSQpVAgEGX9oV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMOhkqGQouWVFBGiQfAwsDPzQ7RCRoC0QaTX8pFQgjFRRfHysSEwcIAXU6RDY6QiwIRBcqAi46CVVXDiADT0dtZjwvEAMgRAEAVAZrEgI2G1tBSjEZAgBHHTA9RSUmFgEPVH9MLgMwHFVdGWsZDhoFAC1pDXc8RBEEOnwxGxgpV0dJCzIfTwgSATY9WTgmHk1rOXwyEgIuHBRtAjcUBgoUQT0gRDUnTkQAXhFlPAcjHkcXIiwFBQEfKi05UTksUxZBVBpPc2JLCVdYBilZARsJDCEgXzlgH25oOXxMFgQhGFgZGikQHgsVHHV0EAckVx0EQgZ/PQ42KVhYEyADFEZOZVxAOV4kWQcAXFUsWlZiSD4wY0x4EAYOAzBpWXd0C0RCQBkkAw4wChRdBU94bmduZjkmUzYkFhQNQlV4WhsuGE1cGDYqDjNtZlxAOV4kWQcAXFUmEgowWQkZGikDSS0PDicoUyMtRG5oOXxMcwIkWVdRCzdRBgADTzw6dTktWx1JQBk3Vks2C0FcQ2UQCQpHBiYIXD4+U0wCWBQ3U0s2EVFXYEx4bmduZjkmUzYkFgwDEEhlGQMjCw5/AysVIQcVHCEKWD4kUkxDeBwxGAQ6O1tdE2dYbWduZlxAOT4uFgwDEBQrHksqGw5wGQRZRSwGHDAZUSU8FE1BRB0gFGFLcD0wY0x4DghHATo9EDIwRgUPVBAhKgowDUdiAicsRxoPCjtDOV5BP21oOXwgAhsjF1BcDhUQFRoUND0rbXd1FgwDHiYsAA5IcD0wY0x4bgsJC19AOV5BP21oWBdrKQI4HBQEShMUBBoIHWZnXjI/HiINURI2VCMrDVZWEhYYHQtLTxMlUTA7GCwIRBcqAjgrA1EVSgMdBgkUQR0gRDUnTjcIShBscGJLcD0wY0wZBUAzHTQnQycpRAEPUwxlR0tzcz0wY0x4bmcPDXsKUTkLWQgNWREgWlZiH1VVGSB7bmduZlxAVTksPG1oOXxMHwUmcz0wY0x4Dk5aTzxpG3d5PG1oOXwgFA9IcD0wDysVTmRuZlw9USQjGBMAWQFtSkV2UD4wYyAfA2RuZnhkECUtRRAOQhBPc2IkFkYZGiQDE0JHHDwzVXchWEQRURw3CUMnAURYBCEUAz4GHSE6GXcsWW5oOXw1GQouFRxfHysSEwcIAX1gED4uFhQAQgFlGwUmWURYGDFfNw8VCjs9ECMgUwpBQBQ3DkUREE5cSnhRFAcdCnUsXjNoUwoFGX9Mcw4sHT4wYyAJFw8JCzAtYDY6QhdBDVU+B2FLcGBRGCAQAx1JBzw9UjgwFllBXhwpcGInF1AQYCAfA2RtQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSmRKQnUMYwdoHiATUQIsFAxiOGRwQ09cSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUYCkeBA8LTzM8XjQ8XwsPEBsgDS8wGENQBCJZBAIGHCZlECc6WRQSGX9MFgQhGFgZBS5dRwpHUnU5UzYkWkwHRRsmDgItFxwQSjcUExsVAXUNQjY/XwoGHhsgDUMhFVVKGWxRAgADRl9AWTFoWAsVEBouWh8qHFoZGCAFEhwJTzsgXHctWABrORMqCEspVRRPSiwfRx4GBic6GCc6WRQSGVUhFWFLcERaCykdTwgSATY9WTgmHk1BVC4uJ0t/WUIZDysVTmRuCjstOl46UxAUQhtlHmEnF1AzYCkeBA8LTzM8XjQ8XwsPEBgkEQ4HCkQRGikDTmRuBjNpdCUpQQ0PVwYeCgcwJBRNAiAfRxwCGyA7XncMRAUWWRsiCTAyFUZkSiAfA2RuAzoqUTtoRQEVEEhlAWFLcFZWEmVRR05HUnUnVSAMRAUWWRsiUkkRCEFYGCBTS05HTy5pZD8hVQ8PVQY2WlZiSBgZLCwdCwsDT2hpVjYkRQFNECMsCQIgFVEZV2UXBgIUCnU0GXtCP20DXw0KDx9iWQkZBCAGIxwGGDwnV39qZRUUUQcgWEdiWRRCShEZDg0MATA6Q3d1FldNEDMsFgcnHRQESiMQCx0CQ3UfWSQhVAgEEEhlHAouClEVSgYeCwEVT2hpczgkWRZSHhsgDUNyVQQVWmxRGkdLZVxAXjYlU0RBEFV4WgUnDnBLCzIYCQlPTQEsSCNqGkRBEFVlAUsREE5cSnhRVl1LTxYsXiMtRERcEAE3Dw5uWXtMHikYCQtHUnU9QiItGkQ3WQYsGAcnWQkZDCQdFAtHEnxlOl5BUg0SRFVlWkt/WVpcHQEDBhkOATJhEgMtThBDHFVlWktiAhRqAz8UR1NHXmdlEBQtWBAEQlV4Wh8wDFEVSgoEEwIOATBpDXc8RBEEHFUTExgrG1hcSnhRAQ8LHDBpTX5kPG1oWBAkFh8qWRQESisUECoVDiIgXjBgFCgIXhBnVktiWRQZEWUlDwcEBDssQyRoC0RTHFUTExgrG1hcSnhRAQ8LHDBpTX5kPG1oWBAkFh8qO1MESisUECoVDiIgXjBgFCgIXhBnVktiWRQZEWUlDwcEBDssQyRoC0RTHFUTExgrG1hcSnhRAQ8LHDBlEBQnWgsTEEhlOQQuFkYKRCsUEEZXQ2VlAH5oS01NOnxMDhkjGlFLSmVMRwACGBE7USAhWANJEjksFA5gVRQZSmVRHE4zBzwqWzktRRdBDVV0VksUEEdQCCkUR1NHCTQlQzJoS01NOnw4cGIGC1VOAysWFDUXAycUEGpoRQEVOnw3Hx83C1oZGSAFbQsJC19DXDgrVwhBVgArGR8rFloZAiwVAisUH306VSNhPG0HXwdlJUdiHRRQBGUBBgcVHH06VSNhFgAOOnxMEw1iHRRNAiAfRx4EDjklGDE9WAcVWRorUkJiHRpvAzYYBQICT2hpVjYkRQFBVRshU0snF1AzYyAfA2QCATFDOjsnVQUNEBMwFAg2EFtXSiYdAg8VKiY5GH5CPwIOQlU1FhluWUdcHmUYCU4XDjw7Q38MRAUWWRsiCUJiHVszY0wXCBxHMHlpVHchWEQRURw3CUMxHEAQSiEebWduZjwvEDNoQgwEXlU1GQouFRxfHysSEwcIAX1gEDNyZAEMXwMgUkJiHFpdQ2UUCQptZlwsXjNCP20lQhQyEwUlCm9JBjcsR1NHATwlOl4tWABrVRshcGEuFldYBmUXEgAEGzwmXnc9RgAARBAACRtqUD4wAyNRCQETTxMlUTA7GCESQDArGwkuHFAZHi0UCWRuZjMmQncXGkQSVQFlEwViCVVQGDZZIxwGGDwnVyRhFgAOEB0sHg4HCkQRGSAFTk4CATFDOV46UxAUQhtPcw4sHT4wBioSBgJHDDolXyVoC0QnXBQiCUUHCkR6BSkeFWRuAzoqUTtoRggASRA3CUt/WWRVCzwUFR1dKDA9YDspTwETQ11scGIuFldYBmUYR1NHXl9ARz8hWgFBWVV5R0thCVhYEyADFE4DAF9AOTsnVQUNEAUpCEt/WURVCzwUFR08BghDOV4kWQcAXFU2Hx9iRBRUCy4UIh0XRyUlQn5CP20NXxYkFkshEVVLSnhRFwIVQRYhUSUpVRAEQn9McwctGlVVSi0DF05aTzYhUSVoVwoFEBYtGxl4P11XDgMYFR0TLD0gXDNgFCwUXRQrFQImK1tWHhUQFRpFRl9AOTsnVQUNEB0gGw9iRBRaAiQDRw8JC3UqWDY6DCIIXhEDExkxDXdRAykVT0wvCjQtEn5CP20NXxYkFks0GFhQDmVMRwgGAyYsOl5BXwJBUx0kCEsjF1AZAjcBRw8JC3UhVTYsFgUPVFU1FhliBwkZJioSBgI3AzQwVSVoVwoFEBw2OwcrD1ERCS0QFUdHGz0sXl1BP20NXxYkFksnF1FUE2VMRwcUKjssXS5gRggTHFUDFgolChp8GTUlAg8KLD0sUzxhPG1oORwjWg4sHFlASioDRwAIG3UPXDYvRUokQwURHwovOlxcCS5REwYCAV9AOV5BWgsCURllHgIxDRQESm0yBgMCHTRncxE6VwkEHiUqCQI2EFtXSmhRDxwXQQUmQz48XwsPGVsIGwwsEEBMDiB7bmduZjwvEDMhRRBBDEhlPAcjHkcXLzYBKg8fKzw6RHc8XgEPOnxMc2JLFVtaCylREwEXPzo6HHcnWDAOQFV4WhwtC1hdPioiBBwCCjthWDIpUkoxXwYsDgItFxQSShMUBBoIHWZnXjI/HlRNEEVrTUdiSR0QYEx4bmduAzoqUTtoVAsVYBo2VkstF3ZWHmVMRxkIHTktZDgbVRYEVRttEhkyV2RWGSwFDgEJT3hpZjIrQgsTA1srHxxqSRgZWWtDS05XRnxDOV5BP20IVlUqFD8tCRRWGGUeCSwIG3U9WDImPG1oOXxMcx0jFV1dSnhRExwSCl9AOV5BP20NXxYkFksqWQkZByQFD0AGDSZhUjg8ZgsSHixlV0s2FkRpBTZfPkdtZlxAOV5BWgsCURllDUt/WVwZQGVBSVtSZVxAOV5BPwgOUxQpWhNiRBRNBTUhCB1JN3VkECBoGURTOnxMc2JLcFhWCSQdRxdHUnU9XycYWRdPaX9Mc2JLcD0UR2UTCBZtZlxAOV5BXwJBdhkkHRhsPEdJKCoJRxoPCjtDOV5BP21oOQYgDkUgFkx2HzFfNAcdCnV0EAEtVRAOQkdrFA41UUMVSi1YXE4UCiFnUjgweREVHiUqCQI2EFtXSnhRMQsEGzo7AnkmUxNJSFllA0J5WUdcHmsTCBYoGiFnZj47XwYNVVV4Wh8wDFEzY0x4bmduZiYsRHkqWRxPYxw/H0t/WWJcCTEeFVxJATA+GCBkFgxIC1U2Hx9sG1tBRBUeFAcTBjonEGpoYAECRBo3SEUsHEMREmlRHkdcTyYsRHkqWRxPcxopFRliRBRaBSkeFVVHHDA9HjUnTko3WQYsGAcnWQkZHjcEAmRuZlxAOV4tWhcEOnxMc2JLcD1KDzFfBQEfQQMgQz4qWgFBDVUjGwcxHA8ZGSAFSQwIFxo8RHkeXxcIUhkgWlZiH1VVGSB7bmduZlxAVTksPG1oOXxMc0ZvWVpYByB7bmduZlxAWTFocAgAVwZrPxgyN1VUD2UFDwsJZVxAOV5BP20SVQFrFAovHBptDz0FR1NHHzk7HhMhRRQNUQwLGwYnWVtLSjUdFUApDjgsOl5BP21oOXw2Hx9sF1VUD2shCB0OGzwmXnd1FjIEUwEqCFlsF1FOQjEeFz4IHHsRHHcxFklBAUBscGJLcD0wY0wCAhpJATQkVXkLWQgOQlV4WggtFVtLUWUCAhpJATQkVXkeXxcIUhkgWlZiDUZMD094bmduZlwsXCQtPG1oOXxMc2IxHEAXBCQcAkAxBiYgUjstFllBVhQpCQ5IcD0wY0x4AgADZVxAOV5BP0lMEBEsCR8jF1dcYEx4bmduZjwvEBEkVwMSHjA2Ci8rCkBYBCYURxoPCjtDOV5BP21oOQYgDkUmEEdNRBEUHxpHUnU6RCUhWANPVho3Fwo2URYcDihTS04KDiEhHjEkWQsTGBEsCR9rUD4wY0x4bmduHDA9HjMhRRBPYBo2Ex8rFloZV2UnAg0TACd7HjktQUwVXwUVFRhsIRgZE2VaRwZHRHV7GV1BP21oOXxMCQ42V1BQGTFfJAELACdpDXcrWQgOQk5lCQ42V1BQGTFfMQcUBjclVXd1FhATRRBPc2JLcD0wDykCAmRuZlxAOV5BRQEVHhEsCR9sL11KAycdAk5aTzMoXCQtPG1oOXxMcw4sHT4wY0x4bmdKQnUhVTYkQgxBUhQ3cGJLcD0wYykeBA8LTz08XXd1FgcJUQd/PAIsHXJQGDYFJAYOAzEGVhQkVxcSGFcNDwYjF1tQDmdYbWduZlxAOT4uFiINURI2VC4xCXxcCykFD04GATFpWCIlFhAJVRtPc2JLcD0wYykeBA8LTyUqRHd1FgkARB1rGQcjFEQRAjAcSSYCDjk9WHdnFgkARB1rFwo6UQUVSi0ECkAqDi0BVTYkQgxIHFV1VktzUD4wY0x4bmduAzoqUTtoXhxBDVU9WkZiTT4wY0x4bmduHDA9Hj8tVwgVWDciVC0wFlkZV2UnAg0TACd7HjktQUwJSFllA0J5WUdcHmsZAg8LGz0LV3kcWURcECMgGR8tCwYXBCAGTwYfQ3UwEHxoXk1aEAYgDkUqHFVVHi0zAEAxBiYgUjstFllBRAcwH2FLcD0wY0x4FAsTQT0sUTs8XkonQhooWlZiL1FaHioDVUAJCiJhWC9kFh1BG1UtWkFiUQUZR2UBBBpORm5pQzI8GAwEURkxEkUWFhQEShMUBBoIHWdnXjI/HgwZHFU8WkBiER0zY0x4bmduZiYsRHkgUwUNRB1rOQQuFkYZV2UyCAIIHWZnViUnWzYmcl13T15iVBRUCzEZSQgLADo7GGV9A0RLEAUmDkJuWVlYHi1fAQIIACdhAmJ9Fk5BQBYxU0diTwQQYEx4bmduZlw6VSNmXgEAXAEtVD0rCl1bBiBRWk4THSAsOl5BP21oORApCQ5IcD0wY0x4bh0CG3shVTYkQgxPZhw2EwkuHBQESiMQCx0CVHU6VSNmXgEAXAEtOAxsL11KAycdAk5aTzMoXCQtPG1oOXxMcw4sHT4wY0x4bmdKQnU9QjYrUxZrOXxMc2JLEFIZLCkQAB1JKiY5ZCUpVQETEAEtHwVIcD0wY0x4bh0CG3s9QjYrUxZPdgcqF0t/WWJcCTEeFVxJATA+GBQpWwETUVsTEw41CVtLHhYYHQtJN3VmEGVkFicAXRA3G0UUEFFOGioDEz0OFTBnaX5CP21oOXxMcxgnDRpNGCQSAhxJOzppDXceUwcVXwd3VAUnDhxNBTUhCB1JN3lpSXdjFgxIOnxMc2JLcD1KDzFfExwGDDA7HhQnWgsTEEhlGQQuFkYCSjYUE0ATHTQqVSVmYA0SWRcpH0t/WUBLHyB7bmduZlxAVTs7U25oOXxMc2JLClFNRDEDBg0CHXsfWSQhVAgEEEhlHAouClEzY0x4bmduCjstOl5BP21oVRshcGJLcD1cBCF7bmduCjstOl5BUwoFOnxMEw1iF1tNSjMQCwcDTyEhVTloXg0FVTA2CkMxHEAQSiAfA2RuZjxpDXchFk9BAX9MHwUmc1FXDk97SkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR09cSk4qIAMMfRIGYm5MHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplPAgOUxQpWg03F1dNAyofRwkCGx08XX9hPG0NXxYkFkshWQkZJioSBgI3AzQwVSVmdQwAQhQmDg4wcz1LDzEEFQBHDHUoXjNoVV4nWRshPAIwCkB6AiwdAyEBLDkoQyRgFCwUXRQrFQImWx0VSiZ7AgADZV8lXzQpWkQHRRsmDgItFxRKHiQDEyMIGTAkVTk8ewUIXgEkEwUnCxwQYEwYAU4zBycsUTM7GAkORhBlDgMnFxRLDzEEFQBHCjstOl4cXhYEURE2VAYtD1EZV2UFFRsCZVw9QjYrXUwzRRsWHxk0EFdcRA0UBhwTDTAoRG0LWQoPVRYxUg03F1dNAyofT0dtZlwgVncmWRBBZB03HwomChpUBTMURxoPCjtpQjI8QxYPEBArHmFLcFhWCSQdRwYSAnV0EDAtQiwUXV1scGJLEFIZAjAcRxoPCjtDOV5BXwJBdhkkHRhsLlVVARYBAgsDIDtpRD8tWEQJRRhrLQouEmdJDyAVR1NHKTkoVyRmYQUNWyY1Hw4mWVFXDk94bmcOCXUPXDYvRUorRRg1NQViDVxcBGUZEgNJJSAkQAcnQQETEEhlPAcjHkcXIDAcFz4IGDA7C3cgQwlPZQYgMB4vCWRWHSADR1NHGyc8VXctWABrOXwgFA9IcFFXDmxYbQsJC19DHXpoXwoHWRssDg5iE0FUGk8FFQ8EBH0cQzI6fwoRRQEWHxk0EFdcRA8ECh41CiQ8VSQ8DCcOXhsgGR9qH0FXCTEYCABPRl9AWTFocAgAVwZrMwUkM0FUGmUFDwsJZVxAXDgrVwhBWAAoWlZiHlFNIjAcT0dtZlwgVncgQwlBRB0gFEsyGlVVBm0XEgAEGzwmXn9hFgwUXU8GEgosHlFqHiQFAkYiASAkHh89WwUPXxwhKR8jDVFtEzUUSSQSAiUgXjBhFgEPVFxlHwUmcz1cBCF7AgADRnxDOnplFgINSX8pFQgjFRRfBjwnAgJtAzoqUTtoUBEPUwEsFQViCkBYGDE3CxdPRl9AWTFoYgwTVRQhCUUkFU0ZHi0UCU4VCiE8QjloUwoFOnwREhknGFBKRCMdHk5aTyE7RTJCPxAAQx5rCRsjDloRDDAfBBoOADthGV1BPwgOUxQpWgM3FBgZCS0QFU5aTzIsRB89W0xIOnxMFgQhGFgZAjcBR1NHDD0oQncpWABBUx0kCFEEEFpdLCwDFBokBzwlVH9qfhEMURsqEw8QFltNOiQDE0xOZVxARz8hWgFBZB03HwomChpfBjxRBgADTxMlUTA7GCINSTorWg8tcz0wYy0ECkJHDD0oQnd1FgMERD0wF0Nrcz0wYy0DF05aTzYhUSVoVwoFEBYtGxl4P11XDgMYFR0TLD0gXDNgFCwUXRQrFQImK1tWHhUQFRpFRl9AOV4hUEQJQgVlDgMnFz4wY0x4DghHATo9EDEkTzIEXFUxEg4scz0wY0x4AQIeOTAlEGpofwoSRBQrGQ5sF1FOQmczCAoeOTAlXzQhQh1DGX9Mc2JLcFJVExMUC0AqDi0PXyUrU0RcECMgGR8tCwcXBCAGT19LT2RlEGZhFk5BCRB8cGJLcD0wDCkIMQsLQQVpDXdxU1BrOXxMc2IkFU1vDylfMQsLADYgRC5oC0Q3VRYxFRlxV1pcHW1BS05XQ3V5GV1BP21oORMpAz0nFRppCzcUCRpHUnUhQidCP21oORArHmFLcD0wBioSBgJHAjo/VXd1FjIEUwEqCFhsF1FOQnVdR15LT2VgOl5BP20NXxYkFkshHxQESgYQCgsVDnsKdiUpWwFrOXxMcwIkWWFKDzc4CR4SGwYsQiEhVQFbeQYOHxIGFkNXQgAfEgNJJDAwczgsU0o2GVUxEg4sWVlWHCBRWk4KACMsEHxoVQJPfBoqET0nGkBWGGUUCQptZlxAOT4uFjESVQcMFBs3DWdcGDMYBAtdJiYCVS4MWRMPGDArDwZsMlFAKSoVAkA0RnU9WDImFgkORhBlR0svFkJcSmhRBAhJIzomWwEtVRAOQlUgFA9IcD0wYywXRzsUCicAXic9QjcEQgMsGQ54MEdyDzw1CBkJRxAnRTpmfQEYcxohH0UDUBRNAiAfRwMIGTBpDXclWRIEEFhlGQ1sK11eAjEnAg0TACdpVTksPG1oOXwsHEsXClFLIysBEho0Cic/WTQtDC0SexA8PgQ1Fxx8BDAcSSUCFhYmVDJmck1BRB0gFEsvFkJcSnhRCgERCnViEDQuGDYIVx0xLA4hDVtLSiAfA2RuZlxAWTFoYxcEQjwrCh42KlFLHCwSAlQuHB4sSRMnQQpJdRswF0UJHE16BSEUST0XDjYsGXc8XgEPEBgqDA5iRBRUBTMUR0VHOTAqRDg6BUoPVQJtSkdiSBgZWmxRAgADZVxAOV4hUEQ0QxA3MwUyDEBqDzcHDg0CVRw6ezIxcgsWXl0AFB4vV39cEwYeAwtJIzAvRAQgXwIVGVUxEg4sWVlWHCBRWk4KACMsEHpoYAECRBo3SUUsHEMRWmlRVkJHX3xpVTksPG1oOXwjFhIUHFgXPCAdCA0OGyxpDXclWRIEEF9lPAcjHkcXLCkINB4CCjFDOV5BUwoFOnxMczk3F2dcGDMYBAtJPTAnVDI6ZRAEQAUgHlEVGF1NQmx7bmcCATFDOV4hUEQHXAwTHwdiDVxcBGUXCxcxCjlzdDI7QhYOSV1sQUskFU1vDylRWk4JBjlpVTksPG1oZB03HwomChpfBjxRWk4JBjlDOTImUk1rVRshcGFvVBRXBSYdDh5tAzoqUTtoUBEPUwEsFQViCkBYGDE/CA0LBiVhGV1BXwJBZB03HwomChpXBSYdDh5HGz0sXnc6UxAUQhtlHwUmcz1tAjcUBgoUQTsmUzshRkRcEAE3Dw5IcEBLCyYaTzwSAQYsQiEhVQFPYwEgChsnHQ56BSsfAg0TRzM8XjQ8XwsPGFxPc2IrHxRXBTFRIQIGCCZnfjgrWg0RfxtlDgMnFxRLDzEEFQBHCjstOl5BWgsCURllGQMjCxQESgkeBA8LPzkoSTI6GCcJUQckGR8nCz4wYywXRw0PDidpRD8tWG5oOXwjFRliJhgZGmUYCU4OHzQgQiRgVQwAQk8CHx8GHEdaDysVBgATHH1gGXcsWW5oOXxMEw1iCQ5wGQRZRSwGHDAZUSU8FE1BURshWhtsOlVXKSodCwcDCnU9WDImPG1oOXxMCkUBGFp6BSkdDgoCT2hpVjYkRQFrOXxMcw4sHT4wY0wUCQptZlwsXjNCPwEPVFxscA4sHT4zR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVD4UR2UhKy8+KgdDHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQl9kHXcpWBAIHRQjEWE2C1VaAW09CA0GAwUlUS4tREooVBkgHlEBFlpXDyYFTwgSATY9WTgmHk1rORwjWi0uGFNKRAQfEwcmCT5pRD8tWG5oOQUmGwcuUVJMBCYFDgEJR3xDOV5BWgsCURllDB5iRBReCygUXSkCGwYsQiEhVQFJEiMsCB83GFhsGSADRUdtZlxARiJydQURRAA3HygtF0BLBSkdAhxPRl9AOV4+Q14iXBwmESk3DUBWBHdZMQsEGzo7AnkmUxNJGVxPc2InF1AQYEwUCQptCjstGX5CPElMEBYwCR8tFBRfBTNRSE4BGjklUiUhUQwVEBgkEwU2GF1XDzd7CwEEDjlpQzY+UwAnXxJPFgQhGFgZDDAfBBoOADtpQyMpRBAxXBQ8HxkPGF1XHiQYCQsVR3xDOT4uFjAJQhAkHhhsCVhYEyADRxoPCjtpQjI8QxYPEBArHmFLLVxLDyQVFEAXAzQwVSVoC0QVQgAgcGI2C1VaAW0jEgA0Cic/WTQtGDYEXhEgCDg2HERJDyFLJAEJATAqRH8uQwoCRBwqFENrcz0wAyNRCQETTwEhQjIpUhdPQBkkAw4wWUBRDytRFQsTGicnEDImUm5oORwjWi0uGFNKRAYEFBoIAhMmRnc8XgEPEAUmGwcuUVJMBCYFDgEJR3xpczYlUxYAHjMsHwcmNlJvAyAGR1NHKTkoVyRmcAsXZhQpDw5iHFpdQ2UUCQptZlwgVncOWgUGQ1sDDwcuG0ZQDS0FRxoPCjtDOV5Beg0GWAEsFAxsO0ZQDS0FCQsUHHV0EGRCP21ofBwiEh8rF1MXKSkeBAUzBjgsEGpoB1ZrOXxMNgIlEUBQBCJfIQEAKjstEGpoBwFYOnxMcycrHlxNAysWSSkLADcoXAQgVwAORwZlR0skGFhKD094bgsJC19AVTksH01rVRshcGFvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhocEZvWXN4JwBRSE4qJgYKOnplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhDXDgrVwhBVgArGR8rFloZACoYCT8SCiAsGH5CPwgOUxQpWhkkWQkZDSAFNQsKACEsGHUFVxACWBgkEQIsHhYVSmc7CAcJPiAsRTJqH25oWRNlCA1iGFpdSjcXXScULn1rYjIlWRAEdgArGR8rFlobQ2UFDwsJZVxAQDQpWghJVgArGR8rFloRQ2UDAVQuASMmWzIbUxYXVQdtU0snF1AQYEwUCQptCjstOl0kWQcAXFUjDwUhDV1WBGUDAgoCCjgKXzMtHgcOVBBscGIuFldYBmUDAU5aTzIsRAUtWwsVVV1nPgo2GBYVSmcjAgoCCjgKXzMtFE1rORwjWhkkWVVXDmUDAVQuHBRhEgUtWwsVVTMwFAg2EFtXSGxRBgADTzYmVDJoVwoFEFYmFQ8nWQoZWmUFDwsJZVxAXDgrVwhBXx5pWhknChQESjUSBgILRzM8XjQ8XwsPGFxlCA42DEZXSjcXXScJGToiVQQtRBIEQl0mFQ8nUBRcBCFYbWduBjNpXzxoQgwEXn9Mc2IOEFZLCzcIXSAIGzwvSX8zFjAIRBkgWlZiW3dWDiBTS04jCiYqQj44Qg0OXlV4WkkRDFZUAzEFAgpdT3dpHnloVQsFVVllLgIvHBQESnFRGkdtZlwsXjNCPwEPVH8gFA9Ic1hWCSQdRwgSATY9WTgmFhYEQwUkDQUMFkMRQ094CwEEDjlpQjJoC0QGVQEXHwYtDVERSAEEAgIUTXlpEgUtRRQARxsLFRxgUD4wAyNRFQtHDjstECUtDC0ScV1nKA4vFkBcLzMUCRpFRnU9WDImPG1oQBYkFgdqH0FXCTEYCABPRnU7VW0OXxYEYxA3DA4wUR0ZDysVTmRuCjstOjImUm5rXBomGwdiH0FXCTEYCABHHCEoQiMJQxAOYQAgDw5qUD4wAyNRMwYVCjQtQ3k5QwEUVVUxEg4sWUZcHjADCU4CATFDOQMgRAEAVAZrCx4nDFEZV2UFFRsCZVw9USQjGBcRUQIrUg03F1dNAyofT0dtZlw+WD4kU0Q1WAcgGw8xV0VMDzAURw8JC3UPXDYvRUogRQEqKx4nDFEZDip7bmduHzYoXDtgXAsIXiQwHx4nUD4wY0wFBh0MQSIoWSNgAE1rOXwgFA9IcD1tAjcUBgoUQSQ8VSItFllBXhwpcGInF1AQYCAfA2RtQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSmRKQnUMYwdoZCEvdDAXWicNNmQzR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVD5NGCQSDEY1GjsaVSU+XwcEHicgFA8nC2dNDzUBAgpdLDonXjIrQkwHRRsmDgItFxwQYEwBBA8LA308QDMpQgEkQwVscGJvVBR/JRNRBAcVDDksOl4hUEQnXBQiCUUREVtOLCoHRxoPCjtDOV4hUEQPXwFlPhkjDl1XDTZfODEBACNpRD8tWG5oOXwBCAo1EFpeGWsuOAgIGXV0EDktQSATUQIsFAxqW3dQGCYdAkxLTy5pZD8hVQ8PVQY2WlZiSBgZLCwdCwsDT2hpVjYkRQFNEDswFzgrHVFKSnhRUVpLTxYmXDg6FllBcxopFRlxV1JLBSgjICxPX3l7AWdkBFZYGVU4U2FLcFFXDk94bgIIDDQlEDRoC0QlQhQyEwUlChpmNSMeEWRuZjwvEDRoQgwEXn9Mc2IhV2ZYDiwEFE5aTxMlUTA7GCUIXTMqDDkjHV1MGU94bmcEQQUmQz48XwsPEEhlOQovHEZYRBMYAhkXACc9Yz4yU0RLEEVrT2FLcD1aRBMYFAcFAzBpDXc8RBEEOnxMHwUmcz1cBjYUDghHKycoRz4mURdPbyojFR1iDVxcBE94bioVDiIgXjA7GDs+VhozVD0rCl1bBiBRWk4BDjk6VV1BUwoFOhArHkJrcz5NGCQSDEY3AzQwVSU7GDQNUQwgCDknFFtPAysWXS0IATssUyNgUBEPUwEsFQVqCVhLQ094CwEEDjlpQzI8FllBdAckDQIsHkdiGikDOmRuBjNpQzI8FhAJVRtPc2IkFkYZNWlRA04OAXU5UT46RUwSVQFsWg8tWV1fSiFREwYCAXU5UzYkWkwHRRsmDgItFxwQSiFLNQsKACMsGH5oUwoFGVUgFA9iHFpdYEx4IxwGGDwnVyQTRggTbVV4WgUrFT4wDysVbQsJC3xgOl1lG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkOnplFjMofjEKLUtpWWB4KBZ7SkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR089DgwVDicwHhEnRAcEcx0gGQAgFkwZV2UXBgIUCl9DXDgrVwhBZxwrHgQ1WQkZJiwTFQ8VFm8KQjIpQgE2WRshFRxqAj4wPiwFCwtHUnVrYh4edygyEllPcy0tFkBcGGVMR0w+XT5pYzQ6XxQVEDckGQBwO1VaAWddbWcpACEgVi4bXwAEEEhlWDkrHlxNSGl7bj0PACIKRSQ8WQkiRQc2FRliRBRNGDAUS2RuLDAnRDI6FllBRAcwH0dIcHVMHioiDwEQT2hpRCU9U0hrOScgCQI4GFZVD2VMRxoVGjBlOl4LWRYPVQcXGw8rDEcZV2VAV0JtEnxDOjsnVQUNECEkGBhiRBRCYEwyCAMFDiFpEHd1FjMIXhEqDVEDHVBtCydZRS0IAjcoRHVkFkRBEgYyFRkmChYQRk94MQcUGjQlQ3doC0Q2WRshFRx4OFBdPiQTT0wxBiY8UTs7FEhBEFcgAw5gUBgzYwgeEQsKCjs9EGpoYQ0PVBoyQComHWBYCG1TKgERCjgsXiNqGkRDURYxEx0rDU0bQ2l7bj4LDiwsQndoFllBZxwrHgQ1Q3VdDhEQBUZFPzkoSTI6FEhBEFVnDxgnCxYQRk94IA8KCnVpEHdoC0Q2WRshFRx4OFBdPiQTT0wgDjgsEntoFkRBEFc1GwgpGFNcSGxdbWckADsvWTA7FkRcECIsFA8tDg54DiElBgxPTRYmXjEhURdDHFVlWA8jDVVbCzYURUdLZVwaVSM8XwoGQ1V4WjwrF1BWHX8wAwozDjdhEgQtQhAIXhI2WEdiW0dcHjEYCQkUTXxlOl4LRAEFWQE2Wkt/WWNQBCEeEFQmCzEdUTVgFCcTVREsDhhgVRQZSCwfAQFFRnlDTV1CG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHV1lG0QifzgHOz9iLXV7YGhcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkzBioSBgJHLDokUjY8ekRcECEkGBhsOltUCCQFXS8DCxksViMPRAsUQBcqAkNgOF1USGlRRQ0VACY6WDYhREZIOhkqGQouWXdWBycQEzxHUnUdUTU7GCcOXRckDlEDHVBrAyIZEykVACA5UjgwHkYiXxgnGx9gVRQbGS0YAgIDTXxDOhQnWwYARDl/Ow8mLVteDSkUT0w0BjksXiMJXwlDHFU+cGIWHExNSnhRRT0OAzAnRHcJXwlDHFUBHw0jDFhNSnhRAQ8LHDBlEAUhRQ8YEEhlDhk3HBgzYxEeCAITBiVpDXdqZAEFWQcgGR8xWUBRD2UWBgMCSCZpXyAmFhcJXwFlDgRiDVxcSjEQFQkCG3tpfDIvXxBBDVUDNT1vHlVNDyFfRUJtZhYoXDsqVwcKEEhlHB4sGkBQBStZEUdHKTkoVyRmZQ0NVRsxOwIvWQkZHH5RDghHGXU9WDImFhcVUQcxOQQvG1VNJyQYCRoGBjssQn9hFgEPVFUgFA9uc0kQYAYeCgwGGxlzcTMschYOQBEqDQVqW3VQBwgeAwtFQ3UyOl4cUxwVEEhlWCYtHVEbRmUnBgISCiZpDXczFkYtVRIsDkluWRZrCyIURU4aQ3UNVTEpQwgVEEhlWCcnHl1NSGl7bi0GAzkrUTQjFllBVgArGR8rFloRHGxRIQIGCCZnYz4kUwoVYhQiH0t/WRxPSnhMR0w1DjIsEn5oUwoFHH84U2EBFllbCzE9XS8DCxE7XycsWRMPGFcEEwYKEEBbBT1TS04cZVwdVS88FllBEj0sDgktARYVShMQCxsCHHV0ECxoFCwEURFnVktgO1tdE2dRGkJHKzAvUSIkQkRcEFcNHwomWxgzYwYQCwIFDjYiEGpoUBEPUwEsFQVqDx0ZLCkQAB1JLjwkeD48VAsZEEhlDEsnF1AVYDhYbS0IAjcoRBtydwAFYxksHg4wURZ4Ayg3CBhFQ3UyOl4cUxwVEEhlWC0NLxRrCyEYEh1FQ3UNVTEpQwgVEEhlS1pyVRR0AytRWk5VX3lpfTYwFllBBUV1VksQFkFXDiwfAE5aT2VlEAQ9UAIISFV4WkliCUwbRk94JA8LAzcoUzxoC0QHRRsmDgItFxxPQ2U3Cw8AHHsIWToOWRIzUREsDxhiRBRPSiAfA0JtEnxDczglVAUVfE8EHg8RFV1dDzdZRS8OAgU7VTNqGkQaOnwRHxM2WQkZSBUDAgoODCEgXzlqGkQlVRMkDwc2WQkZWmlRKgcJT2hpAHtoewUZEEhlS0diK1tMBCEYCQlHUnV7HF1BYgsOXAEsCkt/WRZ1DyQVRwMIGTwnV3c8VxYGVQE2WkMwGF1KD2UXCBxHLTo+HwQmXxQEQlU1CAQoHFdNAykUFEdJTXlDORQpWggDURYuWlZiH0FXCTEYCABPGXxpdjspURdPcRwoKhknHV1aHiweCU5aTyNpVTksGm4cGX8GFQYgGEB1UAQVAzoICDIlVX9qdw0MZhw2EwkuHBYVSj57bjoCFyFpDXdqYA0SWRcpH0sBEVFaAWddRyoCCTQ8XCNoC0QVQgAgVmFLOlVVBicQBAVHUnUvRTkrQg0OXl0zU0sEFVVeGWswDgMxBiYgUjstdQwEUx5lR0s0WVFXDml7GkdtLDokUjY8el4gVBERFQwlFVERSAQYCjoCDjhrHHczPG01VQ0xWlZiW2BcCyhRJAYCDD5rHHcMUwIARRkxWlZiDUZMD2l7bi0GAzkrUTQjFllBVgArGR8rFloRHGxRIQIGCCZncT4lYgEAXTYtHwgpWQkZHGUUCQpLZShgOhQnWwYARDl/Ow8mLVteDSkUT0w0Bzo+djg+FEhBS39MLg46DRQESmc1FQ8QTxMGZncLXxYCXBBnVksGHFJYHykFR1NHCTQlQzJkPG0iURkpGAohEhQESiMECQ0TBjonGCFhFiINURI2VDgqFkN/BTNRWk4RTzAnVHtCS01rOjYqFwkjDWYDKyEVMwEACDksGHUGWTcRQhAkHkluWU8zYxEUHxpHUnVrfjhoZRQTVRQhWEdiPVFfCzAdE05aTzMoXCQtGkQzWQYuA0t/WUBLHyBdbWckDjklUjYrXURcEBMwFAg2EFtXQjNYRygLDjI6HhknZRQTVRQhWlZiDw8ZAyNREU4TBzAnECQ8VxYVcxooGAo2NFVQBDEQDgACHX1gEDImUkQEXhFpcBZrc3dWBycQEzxdLjEtZDgvUQgEGFcLFTknGltQBmddRxVtZgEsSCNoC0RDfhplKA4hFl1VSGlRIwsBDiAlRHd1FgIAXAYgVmFLOlVVBicQBAVHUnUvRTkrQg0OXl0zU0sEFVVeGWs/CDwCDDogXHd1FhJaEBwjWh1iDVxcBGUCEw8VGxYmXTUpQikAWRsxGwIsHEYRQ2UUCQpHCjstHF01H24iXxgnGx8QQ3VdDhEeAAkLCn1rZCUhUQMEQhcqDkluWU8zYxEUHxpHUnVrZCUhUQMEQhcqDkluWXBcDCQECxpHUnUvUTs7U0hBYhw2ERJiRBRNGDAUS2RuOzomXCMhRkRcEFcDExknChRNAiBRAA8KCnI6ECQgWQsVEBwrCh42WUNRDytRHgESHXUqQjg7RQwAWQdlExhiFloZCytRAgACAixnEntCPycAXBknGwgpWQkZDDAfBBoOADthRn5ocAgAVwZrLhkrHlNcGCceE05aTyNyED4uFhJBRB0gFEsxDVVLHhEDDgkACicrXyNgH0QEXhFlHwUmVT5EQ08yCAMFDiEbChYsUjcNWREgCENgLUZQDQEUCw8eTXlpS11BYgEZRFV4WkkWC11eDSADRyoCAzQwEntocgEHUQApDkt/WQQXWnZdRyMOAXV0EGdkFikASFV4WltsTBgZOCoECQoOATJpDXd6GkQyRRMjExNiRBQbSjZTS2RuLDQlXDUpVQ9BDVUjDwUhDV1WBG0HTk4hAzQuQ3kcRA0GVxA3Pg4uGE0ZV2UHRwsJC3lDTX5CdQsMUhQxKFEDHVBtBSIWCwtPTR0gRDUnTiEZQFdpWhBIcGBcEjFRWk5FJzw9UjgwFiEZQBQrHg4wWxgZLiAXBhsLG3V0EDEpWhcEHFUXExgpABQESjEDEgtLZVwKUTskVAUCW1V4Wg03F1dNAyofTxhOTxMlUTA7GCwIRBcqAi46CVVXDiADR1NHGW5pWTFoQEQVWBArWhg2GEZNIiwFBQEfKi05UTksUxZJGVUgFA9iHFpdRk8MTmQkADgrUSMaDCUFVCYpEw8nCxwbIiwFBQEfPDwzVXVkFh9rOSEgAh9iRBQbIiwFBQEfTwYgSjJqGkQlVRMkDwc2WQkZUmlRKgcJT2hpBHtoewUZEEhlSF5uWWZWHysVDgAAT2hpAHtCPycAXBknGwgpWQkZDDAfBBoOADthRn5ocAgAVwZrMgI2G1tBOSwLAk5aTyNpVTksGm4cGX9PV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHX9oV0sUMGdsKwkiRzomLV9kHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKZTkmUzYkFjIIQzllR0sWGFZKRBMYFBsGAyZzcTMsegEHRDI3FR4yG1tBQmc0ND5FQ3VrVS4tFE1rXBomGwdiL11KOGVMRzoGDSZnZj47QwUNQ08EHg8QEFNRHgIDCBsXDToxGHUfWRYNVFdpWkkvGEQbQ097MQcUI28IVDMcWQMGXBBtWC4xCXFXCycdAgpFQ3UyEAMtThBBDVVnPwUjG1hcSgAiN0xLTxEsVjY9WhBBDVUjGwcxHBgzYwYQCwIFDjYiEGpoUBEPUwEsFQVqDx0ZLCkQAB1JKiY5dTkpVAgEVFV4Wh1iHFpdSjhYbTgOHBlzcTMsYgsGVxkgUkkHCkR7BT1TS05HT3VpS3ccUxwVEEhlWCktAVFKSGlRR05HTxEsVjY9WhBBDVUxCB4nVRQZKSQdCwwGDD5pDXcuQwoCRBwqFEM0UBR/BiQWFEAiHCULXy9oC0QXEBArHks/UD5vAzY9XS8DCwEmVzAkU0xDdQY1NAovHBYVSmVRRxVHOzAxRHd1FkYvURggCUluWRQZSmU1AggGGjk9EGpoQhYUVVllWigjFVhbCyYaR1NHCSAnUyMhWQpJRlxlPAcjHkcXLzYBKQ8KCnV0ECFoUwoFEAhscD0rCngDKyEVMwEACDksGHUNRRQpVRQpDgNgVRQZEWUlAhYTT2hpEh8tVwgVWFdpWktiWXBcDCQECxpHUnU9QiItGkRBcxQpFgkjGl8ZV2UXEgAEGzwmXn8+H0QnXBQiCUUHCkRxDyQdEwZHUnU/EDImUkQcGX8TExgOQ3VdDhEeAAkLCn1rdSQ4cg0SRBQrGQ5gVU8ZPiAJE05aT3cNWSQ8VwoCVVdpWksGHFJYHykFR1NHGyc8VXtoFicAXBknGwgpWQkZDDAfBBoOADthRn5ocAgAVwZrPxgyPV1KHiQfBAtHUnU/EDImUkQcGX8TExgOQ3VdDhEeAAkLCn1rdSQ4YhYAUxA3WEdiWU8ZPiAJE05aT3cdQjYrUxYSElllWksGHFJYHykFR1NHCTQlQzJkFicAXBknGwgpWQkZDDAfBBoOADthRn5ocAgAVwZrPxgyLUZYCSADR1NHGXUsXjNoS01rZhw2NlEDHVBtBSIWCwtPTRA6QAMtVwlDHFVlWks5WWBcEjFRWk5FOzAoXXcLXgECW1dpWi8nH1VMBjFRWk4THSAsHHdodQUNXBckGQBiRBRfHysSEwcIAX0/GXcOWgUGQ1sACRsWHFVUKS0UBAVHUnU/EDImUkQcGX8TExgOQ3VdDhYdDgoCHX1rdSQ4ewUZdBw2DkluWU8ZPiAJE05aT3cEUS9ocg0SRBQrGQ5gVRR9DyMQEgITT2hpAWd4BkhBfRwrWlZiSAQJRmU8BhZHUnV6AGd4GkQzXwArHgIsHhQESnVdRz0SCTMgSHd1FkZBXVdpcGIBGFhVCCQSDE5aTzM8XjQ8XwsPGANsWi0uGFNKRAACFyMGFxEgQyNoC0QXEBArHks/UD5vAzY9XS8DCxkoUjIkHkYkYyVlOQQuFkYbQ38wAwokADkmQgchVQ8EQl1nPxgyOltVBTdTS04cZVwNVTEpQwgVEEhlOQQuFkYKRCMDCAM1KBdhAHtoBFVRHFV3SFJrVRRtAzEdAk5aT3cMYwdodQsNXwdnVmFLOlVVBicQBAVHUnUvRTkrQg0OXl0zU0sEFVVeGWs0FB4kADkmQnd1FhJBVRshVmE/UD4zPCwCNVQmCzEdXzAvWgFJEjMwFgcgC11eAjFTS04cTwEsSCNoC0RDdgApFgkwEFNRHmddRyoCCTQ8XCNoC0QHURk2H0dIcHdYBikTBg0MT2hpViImVRAIXxttDEJiP1hYDTZfIRsLAzc7WTAgQkRcEAN+WgIkWUIZHi0UCU4UGzQ7RAckVx0EQjgkEwU2GF1XDzdZTk4CAyYsEBshUQwVWRsiVCwuFlZYBhYZBgoIGCZpDXc8RBEEEBArHksnF1AZF2x7MQcUPW8IVDMcWQMGXBBtWCg3CkBWBwMeEUxLTy5pZDIwQkRcEFcGDxg2FlkZLAonRUJHKzAvUSIkQkRcEBMkFhgnVT4wKSQdCwwGDD5pDXcuQwoCRBwqFEM0UBR/BiQWFEAkGiY9XzoOWRJBDVUzQUsrHxRPSjEZAgBHHCEoQiMYWgUYVQcIGwIsDVVQBCADT0dHCjstEDImUkQcGX8TExgQQ3VdDhYdDgoCHX1rdjg+YAUNRRBnVks5WWBcEjFRWk5FKRofEntocgEHUQApDkt/WQMJRmU8DgBHUnV9AHtoewUZEEhlS1lyVRRrBTAfAwcJCHV0EGdkPG0iURkpGAohEhQESiMECQ0TBjonGCFhFiINURI2VC0tD2JYBjAUR1NHGXUsXjNoS01rOlhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lrHVhlNyQUPHl8JBFRMy8lZXhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNtAzoqUTtoewsXVTllR0sWGFZKRAgeEQsKCjs9ChYsUigEVgECCAQ3CVZWEm1TNB4CCjFrHHdqVwcVWQMsDhJgUD5VBSYQC04qACMsYnd1FjAAUgZrNwQ0HFlcBDFLJgoDPTwuWCMPRAsUQBcqAkNgOFFLAyQdRUJHTTgmRjJlUg0AVxorGwdvSxYQYE88CBgCI28IVDMcWQMGXBBtWDwjFV9qGiAUAyEJTXlpS3ccUxwVEEhlWDwjFV9qGiAUA0xLTxEsVjY9WhBBDVUjGwcxHBgzYwYQCwIFDjYiEGpoUBEPUwEsFQVqDx0ZLCkQAB1JODQlWwQ4UwEFfxtlR0s0QhRQDGUHRxoPCjtpQyMpRBAsXwMgFw4sDXlYAysFBgcJCidhGXctWhcEEBkqGQouWVwEDSAFLxsKR3xpWTFoXkQVWBArWgNsLlVVARYBAgsDUmR/EDImUkQEXhFlHwUmWUkQYAgeEQsrVRQtVAQkXwAEQl1nLQouEmdJDyAVRUJHFHUdVS88FllBEiY1Hw4mWxgZLiAXBhsLG3V0EGZ+GkQsWRtlR0tzTxgZJyQJR1NHXmd5HHcaWREPVBwrHUt/WQQVYEwyBgILDTQqW3d1FgIUXhYxEwQsUUIQSgMdBgkUQQIoXDwbRgEEVFV4Wh1iHFpdSjhYbSMIGTAFChYsUjAOVxIpH0NgM0FUGgofRUJHFHUdVS88FllBEj8wFxtiKVtODzdTS04jCjMoRTs8FllBVhQpCQ5ucz16CykdBQ8EBHV0EDE9WAcVWRorUh1rWXJVCyICSSQSAiUGXnd1FhJaEBwjWh1iDVxcBGUCEw8VGxgmRjIlUwoVfRQsFB8jEFpcGG1YRwsJC3UsXjNoS01rfRozHyd4OFBdOSkYAwsVR3cDRTo4ZgsWVQdnVks5WWBcEjFRWk5FPzo+VSVqGkQlVRMkDwc2WQkZX3VdRyMOAXV0EGJ4GkQsUQ1lR0twTAQVShceEgADBjsuEGpoBkhrOTYkFgcgGFdSSnhRARsJDCEgXzlgQE1BdhkkHRhsM0FUGhUeEAsVT2hpRnctWABBTVxPcCYtD1FrUAQVAzoICDIlVX9qfwoHegAoCkluWU8ZPiAJE05aT3cAXjEhWA0VVVUPDwYyWxgZLiAXBhsLG3V0EDEpWhcEHH9MOQouFVZYCS5RWk4BGjsqRD4nWEwXGVUDFgolChpwBCM7EgMXT2hpRnctWABBTVxPNwQ0HGYDKyEVMwEACDksGHUOWh0uXldpWhBiLVFBHmVMR0whAyxpGAAJZSBOYwUkGQ5tKlxQDDFYRUJHKzAvUSIkQkRcEBMkFhgnVRRrAzYaHk5aTyE7RTJkPG0iURkpGAohEhQESiMECQ0TBjonGCFhFiINURI2VC0uAHtXSnhREVVHBjNpRnc8XgEPEAYxGxk2P1hAQmxRAgADTzAnVHc1H24sXwMgKFEDHVBqBiwVAhxPTRMlSQQ4UwEFElllAUsWHExNSnhRRSgLFnUaQDItUkZNEDEgHAo3FUAZV2VHV0JHIjwnEGpoBFRNEDgkAkt/WQYMWmlRNQESATEgXjBoC0RRHH9MOQouFVZYCS5RWk4BGjsqRD4nWEwXGVUDFgolChp/BjwiFwsCC3V0ECFoUwoFEAhscCYtD1FrUAQVAzoICDIlVX9qeAsCXBw1NQVgVRRCShEUHxpHUnVrfjgrWg0RElllPg4kGEFVHmVMRwgGAyYsHHcaXxcKSVV4Wh8wDFEVYEwyBgILDTQqW3d1FgIUXhYxEwQsUUIQSgMdBgkUQRsmUzshRisPEEhlDFBiEFIZHGUFDwsJTyY9USU8eAsCXBw1UkJiHFpdSiAfA04aRl9DHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQl9kHXcYeiU4dSdlLioAcxkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZIFVtaCylRNwIGFhlpDXccVwYSHiUpGxInCw54DiE9AggTKCcmRScqWRxJEiAxEwcrDU0bRmVTEBwCATYhEn5CPDQNUQwJQComHWBWDSIdAkZFLjs9WRYuXUZNEA5lLg46DRQESmcwCRoOTxQPe3VkFiAEVhQwFh9iRBRfCykCAkJtZhYoXDsqVwcKEEhlHB4sGkBQBStZEUdHKTkoVyRmdwoVWTQjEUt/WUIZDysVRxNOZQUlUS4EDCUFVDcwDh8tFxxCShEUHxpHUnVrYjI7RgUWXlULFRxgVRRtBSodEwcXT2hpEhM9UwgSClUsFBg2GFpNSjcUFB4GGDtrHHcOQwoCEEhlCA4xCVVOBAseEE4aRl8ZXDYxel4gVBEHDx82FloREWUlAhYTT2hpEgUtRQEVEDYtGxkjGkBcGGddRygSATZpDXcuQwoCRBwqFENrcz1VBSYQC04PT2hpVzI8fhEMGFx+WgIkWVwZHi0UCU4XDDQlXH8uQwoCRBwqFENrWVwXIiAQCxoPT2hpAHctWABIEBArHmEnF1AZF2x7bUNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2h7SkNHKBQEdXccdyZrHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG24NXxYkFksFGFlcJmVMRzoGDSZndzYlU14gVBEJHw02PkZWHzUTCBZPTRgoRDQgWwUKWRsiWEdiW0dOBTcVFExOZTkmUzYkFiMAXRAXWlZiLVVbGWs2BgMCVRQtVAUhUQwVdwcqDxsgFkwRSBcUEA8VCyZrHHdqRgUCWxQiH0lrcz5+CygUK1QmCzELRSM8WQpJS1URHxM2WQkZSA8eDgBHPiAsRTJqGkQnRRsmWlZiE1tQBBQEAhsCTyhgOhApWwEtCjQhHj8tHlNVD21TJhsTAAQ8VSItFEhBS1URHxM2WQkZSAQEEwFHPiAsRTJqGkQlVRMkDwc2WQkZDCQdFAtLZVwKUTskVAUCW1V4Wg03F1dNAyofTxhOTxMlUTA7GCUURBoUDw43HBQESjNKRwcBTyNpRD8tWEQSRBQ3Dio3DVtoHyAEAkZOTzAnVHctWABBTVxPcCwjFFFrUAQVAycJHyA9GHULWQAEcho9WEdiAhRtDz0FR1NHTQcsVDItW0QiXxEgWEdiPVFfCzAdE05aT3drHHcYWgUCVR0qFg8nCxQESmcSCAoCQXtnEntocA0PWQYtHw9iRBRNGDAUS2RuLDQlXDUpVQ9BDVUjDwUhDV1WBG0HTk4VCjEsVToLWQAEGANsWg4sHRREQ097SkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR09cSk40KgEdeRkPZUQ1cTdPV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHX8pFQgjFRR0DysER1NHOzQrQ3kbUxAVWRsiCVEDHVB1DyMFIBwIGiUrXy9gFC0PRBA3HAohHBYVSmccCAAOGzo7En5CPCkEXgB/Ow8mLVteDSkUT0w0Bzo+cyI7QgsMcwA3CQQwWxgZEWUlAhYTT2hpEhQ9RRAOXVUGDxkxFkYbRmU1AggGGjk9EGpoQhYUVVlPcygjFVhbCyYaR1NHCSAnUyMhWQpJRlxlNgIgC1VLE2siDwEQLCA6RDgldRETQxo3WlZiDxRcBCFRGkdtIjAnRW0JUgAlQho1HgQ1FxwbJCoFDgg0BjEsEntoTUQ1VQ0xWlZiW3pWHiwXHk40BjEsEntoYAUNRRA2WlZiAhQbJiAXE0xLT3cbWTAgQkZBTVllPg4kGEFVHmVMR0w1BjIhRHVkPG0iURkpGAohEhQESiMECQ0TBjonGCFhFigIUgckCBJ4KlFNJCoFDggePDwtVX8+H0QEXhFlB0JINFFXH38wAwojHTo5VDg/WExDdCUMWEdiAhRtDz0FR1NHTQAAEAQrVwgEElllLAouDFFKSnhRHE5FWGBsEntoFFVRAFBnVktgSAYMT2ddR0xWWmVsEnc1GkQlVRMkDwc2WQkZSHRBV0tFQ19AczYkWgYAUx5lR0skDFpaHiweCUYRRnUFWTU6VxYYCiYgDi8SMGdaCykUTxoIASAkUjI6HkwXChI2DwlqWxEcSGlRRUxORnxgEDImUkQcGX8IHwU3Q3VdDgEYEQcDCidhGV0FUwoUCjQhHicjG1FVQmc8AgASTx4sSTUhWABDGU8EHg8JHE1pAyYaAhxPTRgsXiIDUx0DWRshWEdiAhR9DyMQEgITT2hpEgUhUQwVYx0sHB9gVRR3BRA4R1NHGyc8VXtoYgEZRFV4WkkWFlNeBiBRKgsJGndpTX5CewEPRU8EHg8ADEBNBStZHE4zCi09EGpoFDEPXBokHkluWWZQGS4IR1NHGyc8VXtocBEPU1V4Wg03F1dNAyofT0dHIzwrQjY6T140XhkqGw9qUBRcBCFRGkdtZRkgUiUpRB1PZBoiHQcnMlFACCwfA05aTxo5RD4nWBdPfRArDyAnAFZQBCF7bUNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2h7SkNHLAcMdB4cZUQ1cTdPV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHX8pFQgjFRR6GCAVR1NHOzQrQ3kLRAEFWQE2QComHXhcDDE2FQESHzcmSH9qfwoHXwcoGx8rFlobRmVTDgABAHdgOhQ6UwBbcREhNgogHFgRSBc4MS8rPHWrsMNob1YKECYmCAIyDRR7CyYaVSwGDD5rGV0LRAEFCjQhHicjG1FVQj5RMwsfG3V0EHUNQAETSVUjHwo2DEZcSjIDBh4UTyEhVXcvVwkEFwZlFRwsWVdVAyAfE04LDiwsQncnREQHWQcgCUsjWUZcCylRFQsKACEsHHc4VQUNXFgiDwowHVFdRGddRyoICiYeQjY4FllBRAcwH0s/UD56GCAVXS8DCxkoUjIkHkY3VQc2EwQsQxQIRHVfV0xOZV9kHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKZXhkEBYMcisvY1VtDgMnFFEZQWUSCAABBjJpQzY+U0sNXxQhVQo3DVtVBSQVTmRKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcbToPCjgsfTYmVwMEQk8WHx8OEFZLCzcITyIODScoQi5hPDcARhAIGwUjHlFLUBYUEyIODScoQi5geg0DQhQ3A0JIKlVPDwgQCQ8ACidzeTAmWRYEZB0gFw4RHEBNAysWFEZOZQYoRjIFVwoAVxA3QDgnDX1eBCoDAicJCzAxVSRgTURDfRArDyAnAFZQBCFTRxNOZQEhVTotewUPURIgCFERHEB/BSkVAhxPTQcgRjYkRT1TW1dscDgjD1F0CysQAAsVVQYsRBEnWgAEQl1nKAI0GFhKM3caSA0IATMgVyRqH24yUQMgNwosGFNcGH8zEgcLCxYmXjEhUTcEUwEsFQVqLVVbGWsyCAABBjI6GV0cXgEMVTgkFAolHEYDKzUBCxczAAEoUn8cVwYSHiYgDh8rF1NKQ08iBhgCIjQnUTAtRF4tXxQhOx42FlhWCyEyCAABBjJhGV1CG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHV1lG0QifDAENEsXN3h2KwF7SkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR2hcSkNKQnhkHXplG0lMHVhoV0ZvVBkUR089DgwVDicwChgmYwoNXxQhUg03F1dNAyofT0dtZnhkECQ8WRRBURkpWh8qC1FYDjZ7bggIHXUiED4mFhQAWQc2Uj8qC1FYDjZYRwoITwEhQjIpUhc6WyhlR0ssEFgZDysVbWchAzQuQ3kbXwgEXgEEEwZiRBRfCykCAlVHKTkoVyRmeAsyQAcgGw9iRBRfCykCAlVHKTkoVyRmeAszVRYqEwdiRBRfCykCAmRuKTkoVyRmYhYIVxIgCAktDRQESiMQCx0CVHUPXDYvRUopWQEnFRMHAURYBCEUFU5aTzMoXCQtPG0nXBQiCUUHCkR8BCQTCwsDT2hpVjYkRQFaEDMpGwwxV3JVEwofR1NHCTQlQzJzFiINURI2VCUtGlhQGgofR1NHCTQlQzJCP0lMEAcgCR8tC1EZAioeDB1HQHU7VSQhTAEFEAUkCB8xcz1fBTdROEJHCTtpWTloXxQAWQc2UjknCkBWGCACTk4DAHU5UzYkWkwHXlxlHwUmcz1fBTdRFw8VG3lpQz4yU0QIXlU1GwIwChxcEjUQCQoCCwUoQiM7H0QFX1U1GQouFRxfHysSEwcIAX1gED4uFhQAQgFlGwUmWURYGDFfNw8VCjs9ECMgUwpBQBQ3DkUREE5cSnhRFAcdCnUsXjNoUwoFGVUgFA9IcBkUSiEDBhkOATI6Ol4rWgEAQjA2CkNrcz1QDGU1FQ8QBjsuQ3kXaQIORlUxEg4sWURaCykdTwgSATY9WTgmHk1BdAckDQIsHkcXNRoXCBhdPTAkXyEtHk1BVRshU1BiPUZYHSwfAB1JMAovXyFoC0QPWRllHwUmcz0UR2USCAAJCjY9WTgmRW5oVho3WjRuWVcZAytRDh4GBic6GBQnWAoEUwEsFQUxUBRdBWUBBA8LA30vRTkrQg0OXl1sWgh4PV1KCSofCQsEG31gEDImUk1BVRshcGJvVBRLDzYFCBwCTzYoXTI6V0sNWRItDgIsHj4wGiYQCwJPCSAnUyMhWQpJGVUJEwwqDV1XDWs2CwEFDjkaWDYsWRMSEEhlDhk3HBRcBCFYbQsJC3xDOhshVBYAQgx/NAQ2EFJAQj5RMwcTAzBpDXdqZC03cTkWWEdiPVFKCTcYFxoOADtpDXdqegsAVBAhVEsQEFNRHhYZDggTTyEmECMnUQMNVVtnVksWEFlcSnhRUk4aRl8='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2 })
