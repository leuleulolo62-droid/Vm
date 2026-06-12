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

local __k = 'YN8s8yuhiARGvgLsL9JsicyH'
local __p = 'dGMYka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35o8fXlPLckdmpqOb5gezYu9uoka3pl/35S39qVkcfFiBVahJJLxwlNiAYO00bVRRJN2NpRm1hXmwZHzpJWVkHOz1RF1EYGz0gYXoeRAxsIC9LIwMdQzspOiUKMVkaHkFjbH9nViAtHikZcFM6BhUkeS8YP10UGgZJbnIREwkoASkZLhYaQxohLTxXHUtZCUg5LTMkEy4oU3sAeEVRUEB7aXkKRwxNf0VEYbDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ466s2pH885vdyayt49rs5Yr80bDS5oXZ40YzIxVJDRY8eSlZHl1DPBslLjMjEwNkWmxNIhYHQx4pNCsWP1cYEQ0NewUmHxNkWmxcJBdjaVRleays/9rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vc2ays89rt9Yr9wbDT9oXY866typH945vcyUQVXhib4epJYR0FJS4IOg13aiYgQ1loeW4YUxhZVUhJYXJnVkdsU2wZalNJQ1loeW4YUxhZVUhJYXJnVkdsU2wZalNJQ1mqzcwyXhVZl/z9o8bHlPPMkdi5qOfpge3Iu9q4kaz5l/zpo8bH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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2 })
