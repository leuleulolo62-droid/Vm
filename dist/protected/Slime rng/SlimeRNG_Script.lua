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

local __k = 'nswX7DTauKwK6A4fe7nEgEXi'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2 })
