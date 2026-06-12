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

local __k = 'bRJCIdPj37NrHb4naPpXC8aK'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2 })
