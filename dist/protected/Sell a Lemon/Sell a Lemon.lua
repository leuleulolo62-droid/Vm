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

local __k = 'TQohjQtItyz99USPBBGgLE86'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2 })
