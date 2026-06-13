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

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
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
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
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
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
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
local clonef = clonefunction
local hookf = hookfunction
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
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

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
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
function Defense.detectHttpSpy(raw)
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if type(cur) == "function" and iscc then
			local ok, isc = pcall(iscc, cur)
			if ok and isc == false then return true, n .. " is hooked" end
		end
		-- if we captured the original and the global no longer matches it -> swapped
		if raw and raw.http and rawget(realG, n) and rawget(realG, n) ~= raw.http and n == "request" then
			-- only a soft signal (executors legitimately wrap request); skip hard flag
		end
	end
	return false
end

-- 2) namecall hook: get the real __namecall fn via an errored game:IsA() ------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end
Defense._baseNC, Defense._baseCaller = actualNamecall()

function Defense.detectNamecallHook()
	local nc = actualNamecall()
	if Defense._baseNC and nc and nc ~= Defense._baseNC then
		return true, "__namecall identity changed (metatable hook)"
	end
	return false
end

-- 3) remote spy: fire a THROWAWAY remote; a spy's arg-clone causes a gc spike --
function Defense.detectRemoteSpy()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	if ok and type(spike) == "number" and spike > 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- substring patterns (tools sometimes suffix/version their GUI names)
local SPY_GUI = { "dex", "remotespy", "remote spy", "simplespy", "hydroxide", "spygui", "infiniteyield" }
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				local nm = string.lower(c.Name)
				for _, pat in ipairs(SPY_GUI) do
					if string.find(nm, pat, 1, true) then return true, "GUI: " .. c.Name end
				end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- catches Dex/RemoteSpy/IY window
	run(opts.http ~= false,      Defense.detectHttpSpy,      "http-spy", opts.raw)
	run(opts.namecall ~= false,  Defense.detectNamecallHook, "namecall-hook")
	run(opts.remote == true,     Defense.detectRemoteSpy,    "remote-spy")   -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,          "dex")          -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		local n = 0
		while ctx.alive do
			n = n + 1
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui,
				http = opts.http, namecall = opts.namecall,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

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
local Defense     = Defense

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
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

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
		envLock = envLock,   -- token getmetatable(env) must keep returning
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

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				if o.kick ~= false then
					pcall(function()
						local lp = game:GetService("Players").LocalPlayer
						lp:Kick(o.kickMessage or ("Tamper detected (" .. tostring(name) .. ")"))
					end)
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

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

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)
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

local __k = 'oUl56DoXGLhAr8I3KzWyZcRG'
local __p = 'Qng3bjym+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sVmFRZkTwiExisJN2Jkfw5adll6gdLTT3U1B31kJw0FbEg3RhZ4HXtwd1l6QwIrDjYJfFJkXmp2dF51RQ5xA3pIZ09uQ3I7T3U5fAxkIDo0JQwoE1YcWmtSDksRQwEkHTwcQRYGDjssfiogEVNgOUFad1l6Kx0JKgY4bBYKIAwODy1LUhhpE6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ77rTzIrV8trds6nu15vO47DT77f4tdTQ71JnbEhhIV07RS4IehApECciC3UHXFUvHHgEDSYPPWxpUS5aNRU1ADkiC3UKR1kpTywvKUgiHlEsXT9Udys1AT4oF3UPWVk3CitNbEhhUkwhVmsZOBc0BjEzBjoCFVcwTywvKUgvF0w+XDkRdxU7Gjc1QXUtW09kDDQuKQY1X0sgVy5adRg0FztqBDwPXhROT3hnbAcvHkFpWy4WJwp6FDoiAXUNFXorDDkrHwszG0g9EygbOxUpQx4oDDQAZVolFj01diMoEVNhGmuY1+16FDouDD1MQV4hZXhnbEgyF0o/VjldJFkbIHIjADAfFXgLO3gjI0ZLeBhpE2suPxx6CDskBCZMHXQFLHUfFDAZWxgqXCYfdx8oDD9nHDAeQ1M2QisuKA1hEF0hUj0TOAt6BzczCjYYXFkqQVJnbEhh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GzAlQVMpTXFNYUVhMVQoWiYJd1EpCjwgAzBBRl4rG3RnPwknFxFDXyQZNhV6MQ0EAzQFWHIlBjQ+bEhhUhhpE2taalkuESsBR3cvWVctAhwmJQQ4PlcuWiVYfnM2DDEmA3U+anUoDjEqDgc0HEwwE2tad1l6Q3J6TyEeTHBsTRsrLQEsMFc8XT8DdVBQDz0kDjlMZ2kHAzkuISE1F1VpE2tad1l6Q3JnUnUYR08CR3oEIAkoH3E9ViZYfnM2DDEmA3U+anUoDjEqDQooHlE9Smtad1l6Q3J6TyEeTHBsTRsrLQEsM1ogXyIOLis/FDM1CwUeWlE2Cis0bkFLHlcqUidaBSYIBjYiCjgvWlIhT3hnbEhhUhhpDmsOJQAcS3AVCjEJUFsHADwibkFLHlcqUidaBSYIBiMyCiYYZkYtAXhnbEhhUhhpDmsOJQAcS3AVCiQZUEUwPCguIkpoeFQmUCoWdysFMzczJjsfQVcqGxAmOAspUhhpE3ZaIwsjJXplPzAYRhkNASszLQY1Olk9UCNYfnM2DDEmA3U+amYhGxc3KQYTF1ktSmtad1l6Q3J6TyEeTHBsTQgiOBtuPUgsXRkfNh0jJjUgTXxmPxtpT7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco0FXelkPNxsLPF9BGBam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56hDXyQZNhV6NiYuAyZMCBY/ElIhOQYiBlEmXWsvIxA2EHwgCiEvXVc2R3FNbEhhUlQmUCoWdxp6XnILADYNWWYoDiEiPkYCGlk7UigOMgthQzshTzsDQRYnTywvKQZhAF09RjkUdxczD3IiATFmFRZkTzQoLwktUlBpDmsZbT8zDTYBBicfQXUsBjQjZEoJB1UoXSQTMys1DCYXDicYFx9OT3hnbAQuEVklEyZaalk5WRQuATEqXEQ3GxsvJQQlPV4KXyoJJFF4KycqDjsDXFJmRlJnbEhhG15pW2sbOR16DnIzBzACFUQhGy01IkgiXhghH2sXdxw0B1giATFmU0MqDCwuIwZhJ0wgXzhUMxguAhUiG30HGRYgRlJnbEhhHlcqUidaOBJ2QyRnUnUcVlcoA3AhOQYiBlEmXWNTdws/Fyc1AXUoVEIlVR8iOEAqWxgsXS9TXVl6Q3IuCXUDXhYlATxnOkg/TxgnWidaIxE/DXI1CiEZR1hkGXgiIgx6UkosRz4IOVk+aTcpC18KQFgnGzEoIkgUBlElQGUOMhU/Ez01G30cWkVtZXhnbEgtHVsoX2sle1kyESJnUnU5QV8oHHYgKRwCGlk7G2JBdxA8QzwoG3UER0ZkGzAiIkgzF0w8QSVaMRg2EDdnCjsIPxZkT3grIwsgHhgmQSIdPhd6XnIvHSVCZVk3BiwuIwZLUhhpEycVNBg2QyYmHTIJQRZ5TygoP0hqUm4sUD8VJUp0DTcwR2VAFQVoT2huRkhhUhglXCgbO1k+CiEzT3VMCBZsGzk1Kw01UhVpXDkTMBA0SnwKDjICXEIxCz1NbEhhUlEvEy8TJA16X29nLDoCU18jQQ8GACMeJmgWfwI3Hi16FzoiAV9MFRZkT3hnbAQuEVklEy0IOBR2QyYoT2hMXUQ0QRsBPgksFxRpcA0INhQ/TTwiGH0YVEQjCixuRkhhUhhpE2taMRYoQztnUnVdGRZ1XXgjI0gpAEhncA0INhQ/Q29nCScDWAwICio3ZBwuXhggHHpIfkJ6FzM0BHsbVF8wR2hpfFl3WxgsXS9wd1l6QzcrHDBmFRZkT3hnbEgtHVsoX2sJIxwqEHJ6TzgNQV5qDD0uIEAlG0s9E2RaFBY0BTsgQQIteX0bPAgCCSwePnEEeh9afVlpU3tNT3VMFRZkT3ghIxphGxh0E3pWdwouBiI0TzEDPxZkT3hnbEhhUhhpEycVNBg2Qw1rTz1MCBYRGzErP0YmF0wKWyoIf1BhQzshTzsDQRYsTywvKQZhAF09RjkUdx87DyEiTzACUTxkT3hnbEhhUhhpE2sSeTocETMqCnVRFXUCHTkqKUYvF09hXDkTMBA0WR4iHSVEQVc2CD0zYEgoXUs9VjsJflBQQ3JnT3VMFRZkT3hnOAkyGRY+UiIOf0h1UGJuZXVMFRZkT3hnKQYleBhpE2sfOR1QQ3JnTycJQUM2AXgzPh0keF0nV0EcIhc5FzsoAXU5QV8oHHY0OAk1WlZgOWtad1k2DDEmA3UARhZ5TxQoLwktIlQoSi4IbT8zDTYBBicfQXUsBjQjZEotF1ktVjkJIxguEHBuZXVMFRYtCXgrP0ggHFxpXzhAERA0BxQuHSYYdl4tAzxvIkFhBlAsXWsIMg0vETxnGzofQUQtAT9vIBsaHGVnZSoWIhxzQzcpC19MFRZkHT0zORovUhpkEUEfOR1QaX9qT7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3GJsXxgaZwouBHN3TnKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+shNIAciE1RpYD8bIwp6XnI8TzYNQFEsG2V3YEgyHVQtDntWdwo/ECEuADs/QVc2G2UzJQsqWhFlExQSPgouXik6TyhmU0MqDCwuIwZhIUwoRzhUJRwpBiZvRnU/QVcwHHYkLR0mGkxlYD8bIwp0ED0rC2hcGQZ/TwszLRwyXEssQDgTOBcJFzM1G2gYXFUvR3F8bDs1E0w6HRQSPgouXik6TzACUTwiGjYkOAEuHBgaRyoOJFcvEyYuAjBEHDxkT3hnIAciE1RpQGtHdxQ7FzppCTkDWkRsGzEkJ0BoUhVpYD8bIwp0EDc0HDwDW2UwDiozZWJhUhhpXyQZNhV6C3J6TzgNQV5qCTQoIxppARd6BXtKfkJ6EHJqUnUEHwVyX2hNbEhhUlQmUCoWdxR6XnIqDiEEG1AoADc1ZBtuRAhgCGsJd1RnQz9tWWVmFRZkTyoiOB0zHBhhEW5KZR1gRmJ1C29JBQQgTXF9KgczH1k9GyNWdxR2QyFuZTACUTwiGjYkOAEuHBgaRyoOJFc5Ez9vRl9MFRZkAzckLQRhHFc+H2scJRwpC3J6TyEFVl1sRnRnNxVLUhhpEy0VJVkFT3IzTzwCFV80DjE1P0ASBlk9QGUlPxApF3tnCzpMXFBkATcwYRx9Tw55Ez8SMhd6FzMlAzBCXFg3CiozZA4zF0shH2sOflk/DTZnCjsIPxZkT3gUOAk1ARYWWyIJI1lnQzQ1CiYEDhY2CiwyPgZhUV47VjgSXRw0B1ghGjsPQV8rAXgUOAk1ARYqUj8ZP1FzQwEzDiEfG1UlGj8vOEhqTxh4CGsONhs2BnwuASYJR0JsPCwmOBtvLVAgQD9Wdw0zADlvRnxMUFggZVI3LwktHhAvRiUZIxA1DXpuZXVMFRYtCXgBJRspG1YucCQUIws1Dz4iHXsqXEUsLDkyKwA1UlknV2s8PgoyCjwgLDoCQUQrAzQiPkYHG0shcCoPMBEuTREoATsJVkJkGzAiImJhUhhpE2tadz8zEDouATIvWlgwHTcrIA0zXH4gQCM5Ngw9CyZ9LDoCW1MnG3AUOAk1ARYqUj8ZP1BQQ3JnTzACUTwhATxuRmJsXxirptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sJNQnhMdGMQIHgBBTsJUhAHch8zATx6LBwLNnWOtaJkATdnLx0yBlckEygWPhoxQz4oACVFPxtpT7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco0EWOBo7D3IGGiEDc183B3h6bBNhIUwoRy5aalkhQzwmGzwaUBZ5Tz4mIBskUkVpTkFwMQw0ACYuADtMdEMwAB4uPwBvAUwoQT80Ng0zFTdvRl9MFRZkBj5nDR01HX4gQCNUBA07FzdpATQYXEAhTzc1bAYuBhgbbB4KMxguBhMyGzoqXEUsBjYgbBwpF1ZpQS4OIgs0QzcpC19MFRZkAzckLQRhHVNpDmsKNBg2D3ohGjsPQV8rAXBuRkhhUhhpE2taBSYPEzYmGzAtQEIrKTE0JAEvFQIAXT0VPBwJBiAxCidEQUQxCnFNbEhhUhhpE2sTMVk0DCZnOiEFWUVqCzkzLS8kBhBrcj4OOD8zEDouATI5RlMgTXRnKgktAV1gEyoUM1kIPB8mHT4tQEIrKTE0JAEvFRg9Wy4UXVl6Q3JnT3VMFRZkTygkLQQtWl48XSgOPhY0S3tnPQohVEQvLi0zIy4oAVAgXSxAHhcsDDkiPDAeQ1M2R3FnKQYlWzJpE2tad1l6QzcpC19MFRZkCjYjZWJhUhhpWi1aOBJ6FzoiAXUtQEIrKTE0JEYSBlk9VmUUNg0zFTdnUnUYR0MhTz0pKGIkHFxDVT4UNA0zDDxnLiAYWnAtHDBpPxwuAnYoRyIMMlFzaXJnT3UFUxYqACxnDR01HX4gQCNUBA07FzdpATQYXEAhTywvKQZhAF09RjkUdxw0B1hnT3VMRVUlAzRvKh0vEUwgXCVSflkIPAc3CzQYUHcxGzcBJRspG1YuCQIUIRYxBgEiHSMJRx4iDjQ0KUFhF1YtGkFad1l6IiczABMFRl5qPCwmOA1vHFk9Wj0fd0R6BTMrHDBmUFggZVJqYUij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwulQTn9nLgA4ehYCLgoKbEAyE14sEzgTOR42Bn80BzoYFUQhAjczKRthHVYlSmJwelR6gcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUZTQoLwktUnk8RyQ8Ngs3Q29nFF9MFRZkPCwmOA1hTxgyOWtad1l6Q3JnDiAYWmUhAzR6KgktAV1lEzgfOxUTDSYiHSMNWQt9X3RnPw0tHmwhQS4JPxY2B293Q3UfVFU2Bj4uLw18FFklQC5WXVl6Q3JnT3VMVEMwAB02OQExIFctDi0bOwo/T3I3HTAKUEQ2CjwVIwwIFgVrEWdwd1l6Q3JnT3UeVFIlHRcpcQ4gHkssH0Fad1l6Q3JnTzQZQVkCDi4oPgE1F2ooQS5HMRg2EDdrTzMNQ1k2BiwiHgkzG0wwZyMIMgoyDD4jUmBAPxZkT3hnbEhhE009XA4dMEQ8Aj40CnlMVEMwAAkyKRs1T14oXzgfe1k7FiYoLToZW0I9Uj4mIBskXhgoRj8VBAkzDW8hDjkfUBpOT3hnbBVteEVDXyQZNhV6BScpDCEFWlhkBjYxHwE7FxBgEzkfIwwoDXIEADsfQVcqGyt9Dwc0HEwAXT0fOQ01ESsUBi8JHXIlGzlubA0vFjJDHmZaFiwOLHIUKhkgP1orDDkrbDcyF1QlYT4Ud0R6BTMrHDBmU0MqDCwuIwZhM009XA0bJRR0ECYmHSE/UFooR3FNbEhhUlEvExQJMhU2MScpTyEEUFhkHT0zORovUl0nV3BaCAo/Dz4VGjtMCBYwHS0iRkhhUhg9UjgReQoqAiUpRzMZW1UwBjcpZEFLUhhpE2tad1ktCzsrCnUzRlMoAwoyIkggHFxpcj4OOD87ET9pPCENQVNqDi0zIzskHlRpVyRwd1l6Q3JnT3VMFRZkAzckLQRhBkogVCwfJVlnQyY1GjBmFRZkT3hnbEhhUhhpWi1aFgwuDBQmHThCZkIlGz1pPw0tHmwhQS4JPxY2B3J5T2VMQV4hAXgzPgEmFV07E3ZaPhcsMDs9Cn1FFQh5TxkyOAcHE0okHRgONg0/TSEiAzk4XUQhHDAoIAxhF1YtOWtad1l6Q3JnT3VMFV8iTyw1JQ8mF0ppRyMfOXN6Q3JnT3VMFRZkT3hnbEhhAlsoXydSMQw0ACYuADtEHDxkT3hnbEhhUhhpE2tad1l6Q3JnTzwKFXcxGzcBLRosXGs9Uj8feQo7ACAuCTwPUBYlATxnHjcSE1s7Wi0TNBwbDz5nGz0JWxYWMAsmLxooFFEqVgoWO0MTDSQoBDA/UEQyCipvZWJhUhhpE2tad1l6Q3JnT3VMFRZkTz0rPw0oFBgbbBgfOxUbDz5nGz0JWxYWMAsiIAQAHlRzeiUMOBI/MDc1GTAeHR9kCjYjRkhhUhhpE2tad1l6Q3JnT3UJW1JtZXhnbEhhUhhpE2tad1l6Q3IUGzQYRhg3ADQjbEN8UglDE2tad1l6Q3JnT3VMUFggZXhnbEhhUhhpE2tadw07EDlpGDQFQR4FGiwoCgkzHxYaRyoOMlcpBj4rJjsYUEQyDjRuRkhhUhhpE2taMhc+aXJnT3VMFRZkMCsiIAQTB1ZpDmscNhUpBlhnT3VMUFggRlIiIgxLFE0nUD8TOBd6IiczABMNR1tqHCwoPDskHlRhGmslJBw2DwAyAXVRFVAlAysibA0vFjIvRiUZIxA1DXIGGiEDc1c2AnY0KQQtPFc+G2Jwd1l6QyIkDjkAHVAxATszJQcvWhFDE2tad1l6Q3IuCXUtQEIrKTk1IUYSBlk9VmUJNhooCjQuDDBMVFggTwoYHwkiAFEvWigfFhU2QyYvCjtMZ2kXDjs1JQ4oEV0IXydAHhcsDDkiPDAeQ1M2R3FNbEhhUhhpE2sfOwo/CjRnPQo/UFooLjQrbBwpF1ZpYRQpMhU2Ij4rVRwCQ1kvCgsiPh4kABBgEy4UM3N6Q3JnCjsIHDxkT3hnHxwgBktnQCQWM1lxXnJ2ZTACUTxOQnVnDT0VPRgMYh4zB1kILBZNAzoPVFpkCS0pLxwoHVZpVSIUMzs/ECYVADFEHDxkT3hnIAciE1RpQSQeJFlnQwczBjkfG1IlGzkAKRxpUGomVzhYe1khHntNT3VMFVorDDkrbAokAUxlEykfJA0KDCUiHV9MFRZkCTc1bB00G1xlEzkVM1kzDXI3DjweRh42ADw0ZUglHTJpE2tad1l6Qz4oDDQAFV8gT2VnZBw4Al0mVWMIOB1zXm9lGzQOWVNmTzkpKEhpAFctHQIedxYoQyAoC3sFUR9tTzc1bBwuAUw7WiUdfws1B3tNT3VMFRZkT3grIwsgHhg5XDwfJVlnQ2JNT3VMFRZkT3guKkgIBl0kZj8TOxAuGnIzBzACPxZkT3hnbEhhUhhpEycVNBg2Qz0sQ3UIFQtkHzsmIARpFE0nUD8TOBdySnI1CiEZR1hkJiwiIT01G1QgRzJUEBwuKiYiAhENQVcCHTcqBRwkH2wwQy5SdT8zEDouATJMZ1kgHHprbAElWxgsXS9TXVl6Q3JnT3VMFRZkTzEhbAcqUlknV2sedxg0B3IjQRENQVdkGzAiIkgxHU8sQWtHdx10JzMzDns8WkEhHXgoPkhxUl0nV0Fad1l6Q3JnTzACUTxkT3hnbEhhUlEvEyUVI1k4BiEzTzoeFUYrGD01bFZhWlosQD8qOA4/EXIoHXVcHBYwBz0pbAokAUxlEykfJA0KDCUiHXVRFUMxBjxrbBguBV07Ey4UM3N6Q3JnCjsIPxZkT3g1KRw0AFZpUS4JI3M/DTZNCSACVkItADZnDR01HX4oQSZUMggvCiIFCiYYZ1kgR3FNbEhhUlQmUCoWdwwvCjZnUnUtQEIrKTk1IUYSBlk9VmUKJRw8BiA1CjE+WlINC3g5cUhjUBgoXS9aFgwuDBQmHThCZkIlGz1pPBokFF07QS4eBRY+KjZnACdMU18qCxoiPxwTHVxhGkFad1l6CjRnAToYFUMxBjxnIxphHFc9ExklEggvCiIOGzABFUIsCjZnPg01B0onEy0bOwo/QzcpC19MFRZkHzsmIARpFE0nUD8TOBdySnIVMBAdQF80JiwiIVIHG0osYC4IIRwoSycyBjFAFRQCBisvJQYmUmomVzhYflk/DTZuVHUeUEIxHTZnOBo0FzIsXS9wOxY5Aj5nMDAdZ0MqT2VnKgktAV1DVT4UNA0zDDxnLiAYWnAlHTVpPxwgAEwMQj4TJys1B3puZXVMFRYtCXgYKRkTB1ZpRyMfOVkoBiYyHTtMUFggVHgYKRkTB1ZpDmsOJQw/aXJnT3UYVEUvQSs3LR8vWl48XSgOPhY0S3tNT3VMFRZkT3gwJAEtFxgWVjooIhd6AjwjTxQZQVkCDioqYjs1E0wsHSoPIxYfEicuHwcDURYgAFJnbEhhUhhpE2tad1kzBXISGzwARhggDiwmCw01WhoMQj4TJwk/BwY+HzBOGRRmRng5cUhjNFE6WyIUMFkIDDY0TXUYXVMqTxkyOAcHE0okHS4LIhAqITc0GwcDUR5tTz0pKGJhUhhpE2tad1l6Q3IzDiYHG0ElBixveUFLUhhpE2tad1k/DTZNT3VMFRZkT3gYKRkTB1ZpDmscNhUpBlhnT3VMUFggRlIiIgxLFE0nUD8TOBd6IiczABMNR1tqHCwoPC0wB1E5YSQef1B6PDc2PSACFQtkCTkrPw1hF1YtOS0PORouCj0pTxQZQVkCDioqYhskBmooVyoIfw9zaXJnT3UtQEIrKTk1IUYSBlk9VmUINh07ER0pT2hMQzxkT3hnJQ5hIGccQy8bIxwIAjYmHXUYXVMqTygkLQQtWl48XSgOPhY0S3tnPQo5RVIlGz0VLQwgAAIAXT0VPBwJBiAxCidEQx9kCjYjZUgkHFxDViUeXXN3TnIGOgEjFWcRKgsTRgQuEVklExQLBQw0Q29nCTQARlNOCS0pLxwoHVZpcj4OOD87ET9pHCENR0IVGj00OEBoeBhpE2sTMVkFEgAyAXUYXVMqTyoiOB0zHBgsXS9BdyYrMScpT2hMQUQxClJnbEhhBlk6WGUJJxgtDXohGjsPQV8rAXBuRkhhUhhpE2taIBEzDzdnMCQ+QFhkDjYjbCk0BlcPUjkXeSouAiYiQTQZQVkVGj00OEglHTJpE2tad1l6Q3JnT3UcVlcoA3AhOQYiBlEmXWNTXVl6Q3JnT3VMFRZkT3hnbEgtHVsoX2sLIhwpFyFnUnU5QV8oHHYjLRwgNV09G2krIhwpFyFlQ3UXSB9OT3hnbEhhUhhpE2tad1l6QzshTyEVRVNsHi0iPxwyWxh0DmtYIxg4DzdlTzQCURYWMBsrLQEsO0wsXmsOPxw0aXJnT3VMFRZkT3hnbEhhUhhpE2taMRYoQyMuC3lMRBYtAXg3LQEzARA4Ri4JIwpzQzYoZXVMFRZkT3hnbEhhUhhpE2tad1l6Q3JnTzwKFUI9Hz1vPUFhTwVpET8bNRU/QXImATFMHUdqLDcqPAQkBl0tEyQId1ErTQI1ADIeUEU3TzkpKEgwXH8mUidaNhc+QyNpPycDUkQhHCtnclVhAxYOXCoWflB6FzoiAV9MFRZkT3hnbEhhUhhpE2tad1l6Q3JnT3VMFRZkHzsmIARpFE0nUD8TOBdySnIVMBYAVF8pJiwiIVIIHE4mWC4pMgssBiBvHjwIHBYhATxuRkhhUhhpE2tad1l6Q3JnT3VMFRZkT3hnbA0vFjJpE2tad1l6Q3JnT3VMFRZkT3hnbA0vFjJpE2tad1l6Q3JnT3VMFRZkCjYjRkhhUhhpE2tad1l6QzcpC3xmFRZkT3hnbEhhUhhpRyoJPFctAjszR2dcHDxkT3hnbEhhUl0nV0Fad1l6Q3JnTwodZ0MqT2VnKgktAV1DE2tadxw0B3tNCjsIP1AxATszJQcvUnk8RyQ8Ngs3TSEzACU9QFM3G3BubDcwIE0nE3ZaMRg2EDdnCjsIPzxpQngGGTwOUnoGZgUuDnM2DDEmA3UzV2QxAXh6bA4gHkssOS0PORouCj0pTxQZQVkCDioqYhs1E0o9cSQPOQ0jS3tNT3VMFV8iTwclHh0vUkwhViVaJRwuFiApTzACUQ1kMDoVOQZhTxg9QT4fXVl6Q3IzDiYHG0U0Di8pZA40HFs9WiQUf1BQQ3JnT3VMFRYzBzErKUgeEGo8XWsbOR16IiczABMNR1tqPCwmOA1vE009XAkVIhcuGnIjAF9MFRZkT3hnbEhhUhggVWsoCDo2AjsqLToZW0I9TywvKQZhAlsoXydSMQw0ACYuADtEHBYWMBsrLQEsMFc8XT8DbTA0FT0sCgYJR0AhHXBubA0vFhFpViUeXVl6Q3JnT3VMFRZkTywmPwNvBVkgR2NMZ1BQQ3JnT3VMFRYhATxNbEhhUhhpE2slNSsvDXJ6TzMNWUUhZXhnbEgkHFxgOS4UM3M8FjwkGzwDWxYFGiwoCgkzHxY6RyQKFRYvDSY+R3xMalQWGjZncUgnE1Q6VmsfOR1QaX9qTxQ5YXlkPAgOAmItHVsoX2slJAkIFjxnUnUKVFo3ClIhOQYiBlEmXWs7Ig01JTM1AnsfQVc2Gws3JQZpWzJpE2taPh96PCE3PSACFUIsCjZnPg01B0onEy4UM0J6PCE3PSACFQtkGyoyKWJhUhhpRyoJPFcpEzMwAX0KQFgnGzEoIkBoeBhpE2tad1l6FDouAzBMakU0PS0pbAkvFhgIRj8VERgoDnwUGzQYUBglGiwoHxgoHBgtXEFad1l6Q3JnT3VMFRYtCXgVEzokA00sQD8pJxA0QyYvCjtMRVUlAzRvKh0vEUwgXCVSflkIPAAiHiAJRkIXHzEpdiEvBFciVhgfJQ8/EXpuTzACUR9kCjYjRkhhUhhpE2tad1l6QyYmHD5CQlctG3B+fEFLUhhpE2tad1k/DTZNT3VMFRZkT3gYPxgTB1ZpDmscNhUpBlhnT3VMUFggRlIiIgxLFE0nUD8TOBd6IiczABMNR1tqHCwoPDsxG1ZhGmslJAkIFjxnUnUKVFo3CngiIgxLeBVkEwovAzZ6JhUAZTkDVlcoTwciKzo0HBh0Ey0bOwo/aTQyATYYXFkqTxkyOAcHE0okHSMbIxoyMTcmCyxEHDxkT3hnPAsgHlRhVT4UNA0zDDxvRl9MFRZkT3hnbAQuEVklEy4dMAp6XnISGzwARhggDiwmCw01WhoMVCwJdVV6GC9uZXVMFRZkT3hnJQ5hBkE5VmMfMB4pSnI5UnVOQVcmAz1lbBwpF1ZpQS4OIgs0QzcpC19MFRZkT3hnbA4uABg8RiIee1k/BDVnBjtMRVctHStvKQ8mARFpVyRwd1l6Q3JnT3VMFRZkBj5nOBExFxAsVCxTd0RnQ3AzDjcAUBRkDjYjbA0mFRYbVioeLlk7DTZnPQo8UEILHz0pHg0gFkFpRyMfOXN6Q3JnT3VMFRZkT3hnbEhhAlsoXydSMQw0ACYuADtEHBYWMAgiOCcxF1YbVioeLkMTDSQoBDA/UEQyCipvOR0oFhFpViUefnN6Q3JnT3VMFRZkT3giIgxLUhhpE2tad1k/DTZNT3VMFVMqC3FNKQYleF48XSgOPhY0QxMyGzoqVEQpQSszLRo1N18uG2Jwd1l6QzshTwoJUmQxAXgzJA0vUkosRz4IOVk/DTZ8TwoJUmQxAXh6bBwzB11DE2tadw07EDlpHCUNQlhsCS0pLxwoHVZhGkFad1l6Q3JnTyIEXFohTwciKzo0HBgoXS9aFgwuDBQmHThCZkIlGz1pLR01HX0uVGseOHN6Q3JnT3VMFRZkT3gGORwuNFk7XmUSNg05CwAiDjEVHR9OT3hnbEhhUhhpE2taIxgpCHwwDjwYHQdxRlJnbEhhUhhpEy4UM3N6Q3JnT3VMFWkhCAoyIkh8Ul4oXzgfXVl6Q3IiATFFP1MqC1IhOQYiBlEmXWs7Ig01JTM1AnsfQVk0Kj8gZEFhLV0uYT4Ud0R6BTMrHDBMUFggZVJqYUgAJ2wGEw07ATYIKgYCTwctZ3NOAzckLQRhLV4oRSQIMh16XnI8El8AWlUlA3gYKgk3IE0nE3ZaMRg2EDdNCSACVkItADZnDR01HX4oQSZUJA07ESYBDiMDR18wCnBuRkhhUhggVWslMRgsMScpTyEEUFhkHT0zORovUl0nV3BaCB87FQAyAXVRFUI2Gj1NbEhhUkwoQCBUJAk7FDxvCSACVkItADZvZWJhUhhpE2tadw4yCj4iTwoKVEAWGjZnLQYlUnk8RyQ8Ngs3TQEzDiEJG1cxGzcBLR4uAFE9VhkbJRx6Bz1NT3VMFRZkT3hnbEhhAlsoXydSMQw0ACYuADtEHDxkT3hnbEhhUhhpE2tad1l6Dz0kDjlMXEIhAitncUgUBlElQGUeNg07JDczR3clQVMpHHprbBM8WzJpE2tad1l6Q3JnT3VMFRZkBj5nOBExFxAgRy4XJFB6HW9nTSENV1ohTXgoPkgvHUxpYRQ8Ng81ETszChwYUFtkGzAiIkgzF0w8QSVaMhc+aXJnT3VMFRZkT3hnbEhhUhgvXDlaIgwzB35nBiFMXFhkHzkuPhtpG0wsXjhTdx01aXJnT3VMFRZkT3hnbEhhUhhpE2taPh96DT0zTwoKVEArHT0jFx00G1wUEyoUM1kuGiIiRzwYHBZ5UnhlOAkjHl1rEz8SMhdQQ3JnT3VMFRZkT3hnbEhhUhhpE2tad1l6Dz0kDjlMRxZ5TzEzYj4gAFEoXT9aOAt6CiZpIjoIXFAtCipnIxphQzJpE2tad1l6Q3JnT3VMFRZkT3hnbEhhUhggVWsOLgk/SyBuT2hRFRQqGjUlKRpjUlknV2sId0dnQxMyGzoqVEQpQQszLRwkXF4oRSQIPg0/MTM1BiEVYV42CisvIwQlUkwhViVwd1l6Q3JnT3VMFRZkT3hnbEhhUhhpE2tad1l6QyIkDjkAHVAxATszJQcvWhFpYRQ8Ng81ETszChwYUFt+KTE1KTskAE4sQWMPIhA+SnIiATFFPxZkT3hnbEhhUhhpE2tad1l6Q3JnT3VMFRZkT3gYKgk3HUosVxAPIhA+PnJ6TyEeQFNOT3hnbEhhUhhpE2tad1l6Q3JnT3VMFRZkCjYjRkhhUhhpE2tad1l6Q3JnT3VMFRZkCjYjRkhhUhhpE2tad1l6Q3JnT3UJW1JOT3hnbEhhUhhpE2taMhc+SlhnT3VMFRZkT3hnbEg1E0siHTwbPg1yUmJuZXVMFRZkT3hnKQYleBhpE2tad1l6PDQmGQcZWxZ5Tz4mIBskeBhpE2sfOR1zaTcpC18KQFgnGzEoIkgAB0wmdSoIOlcpFz03KTQaWkQtGz1vZUgeFFk/YT4Ud0R6BTMrHDBMUFggZVJqYUgCPXwMYEEcIhc5FzsoAXUtQEIrKTk1IUYzF1wsViZSOxApF3tNT3VMFV8iTzYoOEgTLWosVy4fOjo1BzdnGz0JWxY2CiwyPgZhQhgsXS9wd1l6Qz4oDDQAFVhkUnh3RkhhUhgvXDlaNBY+BnIuAXUYWkUwHTEpK0AtG0s9GnEdOhguADpvTQ4yGRM3MnNlZUglHTJpE2tad1l6Qz4oDDQAFVkvT2VnPAsgHlRhVT4UNA0zDDxvRnU+amQhCz0iISsuFl1zeiUMOBI/MDc1GTAeHVUrCz1ubA0vFhFDE2tad1l6Q3IuCXUDXhYwBz0pbAZhWQVpAmsfOR1QQ3JnT3VMFRYwDissYh8gG0xhAmJwd1l6QzcpC19MFRZkHT0zORovUlZDViUeXXN3TnKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+shNYUVhP3cfdgY/GS1QTn9njcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3XRgQuEVklEwYVIRw3BjwzT2hMTjxkT3hnHxwgBl1pDmsBdw47DzkUHzAJUQt1V3RnJh0sAmgmRC4IakxqT3IuATMmQFs0Uj4mIBskXhgnXCgWPglnBTMrHDBAFVAoFmUhLQQyFxRpVScDBAk/BjZ6V2VAFVcqGzEGCiN8Bko8VmdaPxAuAT0/UmdAFUUlGT0jHAcyT1YgX2sHe3N6Q3JnMDZMCBY/EnRNMWItHVsoX2scIhc5FzsoAXUNRUYoFhAyIUBoeBhpE2sWOBo7D3IYQ3UzGRYsT2VnGRwoHktnVC4OFBE7EXpuVHUFUxYqACxnJEg1Gl0nEzkfIwwoDXIiATFmFRZkTygkLQQtWl48XSgOPhY0S3tnB3s7VFovPCgiKQxhTxgEXD0fOhw0F3wUGzQYUBgzDjQsHxgkF1xpViUefnN6Q3JnHzYNWVpsCS0pLxwoHVZhGmsSeTMvDiIXACIJRxZ5TxUoOg0sF1Y9HRgONg0/TTgyAiU8WkEhHWNnJEYUAV0DRiYKBxYtBiBnUnUYR0MhTz0pKEFLF1YtOS0PORouCj0pTxgDQ1MpCjYzYhskBms5Vi4efw9zQx8oGTABUFgwQQszLRwkXE8oXyApJxw/B3J6TyEDW0MpDT01ZB5oUlc7E3pCbFk7EyIrFh0ZWB5tTz0pKGInB1YqRyIVOVkXDCQiAjACQRg3CiwNOQUxWk5gE2s3OA8/DjcpG3s/QVcwCnYtOQUxIlc+VjlaalkuDDwyAjcJRx4yRngoPkh0QgNpUjsKOwASFj9vRnUJW1JOCS0pLxwoHVZpfiQMMhQ/DSZpHDAYfFgiJS0qPEA3WzJpE2taGhYsBj8iASFCZkIlGz1pJQYnOE0kQ2tHdw9QQ3JnTzwKFUBkDjYjbAYuBhgEXD0fOhw0F3wYDHsFXxYwBz0pRkhhUhhpE2taGhYsBj8iASFCalVqBjJncUgUAV07eiUKIg0JBiAxBjYJG3wxAigVKRk0F0s9CQgVORc/ACZvCSACVkItADZvZWJhUhhpE2tad1l6Q3IuCXUCWkJkIjcxKQUkHExnYD8bIxx0CjwhJSABRRYwBz0pbBokBk07XWsfOR1QQ3JnT3VMFRZkT3hnIAciE1RpbGclexF6XnISGzwARhgjCiwEJAkzWhFyEyIcdxF6FzoiAXUED3UsDjYgKTs1E0wsGw4UIhR0KycqDjsDXFIXGzkzKTw4Al1neT4XJxA0BHtnCjsIPxZkT3hnbEhhF1YtGkFad1l6Bj40CjwKFVgrG3gxbAkvFhgEXD0fOhw0F3wYDHsFXxYwBz0pbCUuBF0kViUOeSY5TTstVREFRlUrATYiLxxpWwNpfiQMMhQ/DSZpMDZCXFxkUngpJQRhF1YtOS4UM3M8FjwkGzwDWxYJAC4iIQ0vBhY6Vj80OBo2CiJvGXxmFRZkTxUoOg0sF1Y9HRgONg0/TTwoDDkFRRZ5Ty5NbEhhUlEvEz1aNhc+QzwoG3UhWkAhAj0pOEYeERYnUGsOPxw0aXJnT3VMFRZkIjcxKQUkHExnbChUORp6XnIVGjs/UEQyBjsiYjs1F0g5Vi9AFBY0DTckG30KQFgnGzEoIkBoeBhpE2tad1l6Q3JnTzwKFVgrG3gKIx4kH10nR2UpIxguBnwpADYAXEZkGzAiIkgzF0w8QSVaMhc+aXJnT3VMFRZkT3hnbAQuEVklEyhaalkWDDEmAwUAVE8hHXYEJAkzE1s9VjlBdxA8QzwoG3UPFUIsCjZnPg01B0onEy4UM3N6Q3JnT3VMFRZkT3ghIxphLRQ5EyIUdxAqAjs1HH0PD3EhGxwiPwskHFwoXT8Jf1BzQzYoTzwKFUZ+JisGZEoDE0ssYyoII1tzQyYvCjtMRRgHDjYEIwQtG1wsDi0bOwo/QzcpC3UJW1JOT3hnbEhhUhgsXS9TXVl6Q3IiAyYJXFBkATczbB5hE1YtEwYVIRw3BjwzQQoPG1gnTywvKQZhP1c/ViYfOQ10PDFpATZWcV83DDcpIg0iBhBgCGs3OA8/DjcpG3szVhgqDHh6bAYoHhgsXS9wMhc+aT4oDDQAFVAxATszJQcvUks9UjkOERUjS3tNT3VMFVorDDkrbDdtUlA7Q2daPww3Q29nOiEFWUVqCD0zDwAgABBgCGsTMVk0DCZnByccFUIsCjZnPg01B0onEy4UM3N6Q3JnAzoPVFpkDS5ncUgIHEs9UiUZMlc0BiVvTRcDUU8SCjQoLwE1CxpgCGsYIVcXAioBACcPUBZ5Tw4iLxwuAAtnXS4Nf0g/Wn52CmxABFN9RmNnLh5vIlk7ViUOd0R6CyA3ZXVMFRYoADsmIEgjFRh0EwIUJA07DTEiQTsJQh5mLTcjNS84AFdrGnBad1l6QzAgQRgNTWIrHSkyKUh8Um4sUD8VJUp0DTcwR2QJDBp1CmFrfQ14WwNpUSxUB0RrBmZ8TzcLG2YlHT0pOFUpAEhDE2tadzQ1FTcqCjsYG2knQT4lOkh8Ulo/CGs3OA8/DjcpG3szVhgiDT9ncUgjFTJpE2taPh96CycqTyEEUFhkBy0qYjgtE0wvXDkXBA07DTZnUnUYR0MhTz0pKGJhUhhpfiQMMhQ/DSZpMDZCU0M0T2VnHh0vIV07RSIZMlcIBjwjCic/QVM0Hz0jdisuHFYsUD9SMQw0ACYuADtEHDxkT3hnbEhhUlEvEyUVI1kXDCQiAjACQRgXGzkzKUYnHkFpRyMfOVkoBiYyHTtMUFggZXhnbEhhUhhpXyQZNhV6ADMqT2hMQlk2BCs3LQskXHs8QTkfOQ0ZAj8iHTRXFVorDDkrbAVhTxgfVigOOAtpTTwiGH1FPxZkT3hnbEhhG15pZjgfJTA0EyczPDAeQ18nCmIOPyMkC3wmRCVSEhcvDnwMCiwvWlIhQQ9ubEhhUhhpE2sOPxw0Qz9nRGhMVlcpQRsBPgksFxYFXCQRARw5Fz01TzACUTxkT3hnbEhhUlEvEx4JMgsTDSIyGwYJR0AtDD19BRsKF0ENXDwUfzw0Fj9pJDAVdlkgCnYUZUhhUhhpE2taIxE/DXIqT3hRFVUlAnYEChogH11nfyQVPC8/ACYoHXUJW1JOT3hnbEhhUhggVWsvJBwoKjw3GiE/UEQyBjsidiEyOV0wdyQNOVEfDScqQR4JTHUrCz1pDUFhUhhpE2tadw0yBjxnAnVBCBYnDjVpDy4zE1UsHRkTMBEuNTckGzoeFVMqC1JnbEhhUhhpEyIcdywpBiAOASUZQWUhHS4uLw17O0sCVjI+OA40SxcpGjhCflM9LDcjKUYFWxhpE2tad1l6FzoiAXUBFR15TzsmIUYCNEooXi5UBRA9CyYRCjYYWkRkCjYjRkhhUhhpE2taPh96NiEiHRwCRUMwPD01OgEiFwIAQAAfLj01FDxvKjsZWBgPCiEEIwwkXGs5Uigffll6Q3IzBzACFVtkRGVnGg0iBlc7AGUUMg5yU352Q2VFFVMqC1JnbEhhUhhpEyIcdywpBiAOASUZQWUhHS4uLw17O0sCVjI+OA40SxcpGjhCflM9LDcjKUYNF149YCMTMQ1zFzoiAXUBFRt5Tw4iLxwuAAtnXS4Nf0l2Un53RnUJW1JOT3hnbEhhUhgrRWUsMhU1ADszFnVRFVtqIjkgIgE1B1wsE3VaZ1k7DTZnAns5W18wT3JnAQc3F1UsXT9UBA07FzdpCTkVZkYhCjxnIxphJF0qRyQIZFc0BiVvRl9MFRZkT3hnbAomXHsPQSoXMllnQzEmAnsvc0QlAj1NbEhhUl0nV2JwMhc+aT4oDDQAFVAxATszJQcvUks9XDs8OwBySlhnT3VMU1k2TwdrJ0goHBggQyoTJQpyGHAhGiVOGRQiDS5lYEonEF9rTmJaMxZQQ3JnT3VMFRYoADsmIEgiUgVpfiQMMhQ/DSZpMDY3XmtOT3hnbEhhUhggVWsZdw0yBjxNT3VMFRZkT3hnbEhhG15pRzIKMhY8SzFuT2hRFRQWLQAULxooAkwKXCUUMhouCj0pTXUYXVMqTzt9CAEyEVcnXS4ZI1FzQzcrHDBMRVUlAzRvKh0vEUwgXCVSflk5WRYiHCEeWk9sRngiIgxoUl0nV0Fad1l6Q3JnT3VMFRYJAC4iIQ0vBhYWUBARCllnQzwuA19MFRZkT3hnbA0vFjJpE2taMhc+aXJnT3UAWlUlA3gYYDdtGhh0Ex4OPhUpTTUiGxYEVERsRmNnJQ5hGhg9Wy4UdxF0Mz4mGzMDR1sXGzkpKEh8Ul4oXzgfdxw0B1giATFmU0MqDCwuIwZhP1c/ViYfOQ10EDczKTkVHUBtTxUoOg0sF1Y9HRgONg0/TTQrFnVRFUB/TzEhbB5hBlAsXWsJIxgoFxQrFn1FFVMoHD1nPxwuAn4lSmNTdxw0B3IiATFmU0MqDCwuIwZhP1c/ViYfOQ10EDczKTkVZkYhCjxvOkFhP1c/ViYfOQ10MCYmGzBCU1o9PCgiKQxhTxg9XCUPOhs/EXoxRnUDRxZ8X3giIgxLFE0nUD8TOBd6Lj0xCjgJW0JqHD0zBAE1EFcxGz1TXVl6Q3IKACMJWFMqG3YUOAk1FxYhWj8YOAF6XnIzADsZWFQhHXAxZUguABh7OWtad1k2DDEmA3UzGRYsHShncUgUBlElQGUdMg0ZCzM1R3xXFV8iTzA1PEg1Gl0nEzsZNhU2SzQyATYYXFkqR3FnJBoxXGsgSS5aalkMBjEzACdfG1ghGHAxYB5tBBFpViUeflk/DTZNCjsIP1AxATszJQcvUnUmRS4XMhcuTSEiGxQCQV8FKRNvOkFLUhhpEwYVIRw3BjwzQQYYVEIhQTkpOAEANHNpDmsMXVl6Q3IuCXUaFVcqC3gpIxxhP1c/ViYfOQ10PDFpDjMHFUIsCjZNbEhhUhhpE2s3OA8/DjcpG3szVhglCTNncUgNHVsoXxsWNgA/EXwOCzkJUQwHADYpKQs1Wl48XSgOPhY0S3tNT3VMFRZkT3hnbEhhG15pXSQOdzQ1FTcqCjsYG2UwDiwiYgkvBlEIdQBaIxE/DXI1CiEZR1hkCjYjRkhhUhhpE2tad1l6QyIkDjkAHVAxATszJQcvWhFpZSIIIww7Dwc0CidWdlc0Gy01KSsuHEw7XCcWMgtySmlnOTweQUMlAw00KRp7MVQgUCA4Ig0uDDx1RwMJVkIrHWppIg02WhFgEy4UM1BQQ3JnT3VMFRYhATxuRkhhUhgsXzgfPh96DT0zTyNMVFggTxUoOg0sF1Y9HRQZeRg8CHIzBzACFXsrGT0qKQY1XGcqHSocPEMeCiEkADsCUFUwR3F8bCUuBF0kViUOeSY5TTMhBHVRFVgtA3giIgxLF1YtOS0PORouCj0pTxgDQ1MpCjYzYhsgBF0ZXDhSflk2DDEmA3UzGRYsHShncUgUBlElQGUdMg0ZCzM1R3xXFV8iTzA1PEg1Gl0nEwYVIRw3BjwzQQYYVEIhQSsmOg0lIlc6E3ZaPwsqTQIoHDwYXFkqVHg1KRw0AFZpRzkPMlk/DTZnCjsIP1AxATszJQcvUnUmRS4XMhcuTSAiDDQAWWYrHHBubAEnUnUmRS4XMhcuTQEzDiEJG0UlGT0jHAcyUkwhViVaJRwuFiApTwAYXFo3QSwiIA0xHUo9GwYVIRw3BjwzQQYYVEIhQSsmOg0lIlc6GmsfOR16BjwjZV8gWlUlAwgrLREkABYKWyoINhouBiAGCzEJUQwHADYpKQs1Wl48XSgOPhY0S3tNT3VMFUIlHDNpOwkoBhB5HX1TbFk7EyIrFh0ZWB5tZXhnbEgoFBgEXD0fOhw0F3wUGzQYUBgiAyFnOAAkHBg6RyoIIz82GnpuTzACUTxkT3hnJQ5hP1c/ViYfOQ10MCYmGzBCXV8wDTc/bBZ8UgppRyMfOVkXDCQiAjACQRg3CiwPJRwjHUBhfiQMMhQ/DSZpPCENQVNqBzEzLgc5WxgsXS9wMhc+SlhNQnhM16PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3ReBVkEx8/GzwKLAATPF9BGBam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56hDXyQZNhV6BScpDCEFWlhkCTEpKDguARAnVi4eOxxzaXJnT3UCUFMgAz1ncUgvF10tXy5AOxYtBiBvRl9MFRZkAzckLQRhEF06R2daNQp6XnIpBjlAFQZOT3hnbA4uABgWH2sedxA0Qzs3DjweRh4TACosPxggEV1zdC4OExwpADcpCzQCQUVsRnFnKAdLUhhpE2tad1k2DDEmA3UCFQtkC3YJLQUkSFQmRC4If1BQQ3JnT3VMFRYtCXgpdg4oHFxhXS4fMxU/T3J2Q3UYR0MhRngzJA0veBhpE2tad1l6Q3JnTzkDVlcoTytncUhiHF0sVycfd1Z6DjMzB3sBVE5sXnRnbwxvPFkkVmJwd1l6Q3JnT3VMFRZkBj5nP0h/Ulo6Ez8SMhd6ASFrTzcJRkJkUng0YEglUl0nV0Fad1l6Q3JnTzACUTxkT3hnKQYleBhpE2sTMVk4BiEzTyEEUFhOT3hnbEhhUhggVWsYMgouWRs0Ln1Od1c3CggmPhxjWxg9Wy4Udws/Fyc1AXUOUEUwQQgoPwE1G1cnEy4UM3N6Q3JnT3VMFV8iTzoiPxx7O0sIG2k3OB0/D3BuTyEEUFhOT3hnbEhhUhhpE2taPh96ATc0G3s8R18pDio+HAkzBhg9Wy4Udws/Fyc1AXUOUEUwQQg1JQUgAEEZUjkOeSk1EDszBjoCFVMqC1JnbEhhUhhpE2tad1k2DDEmA3UcFQtkDT00OFIHG1YtdSIIJA0ZCzsrCwIEXFUsJisGZEoDE0ssYyoII1t2QyY1GjBFDhYtCXg3bBwpF1ZpQS4OIgs0QyJpPzofXEItADZnKQYleBhpE2tad1l6BjwjZXVMFRZkT3hnJQ5hEF06R3EzJDhyQRMzGzQPXVshASxlZUg1Gl0nEzkfIwwoDXIlCiYYG2ErHTQjHAcyG0wgXCVaMhc+aXJnT3VMFRZkBj5nLg0yBgIAQApSdSoqAiUpIzoPVEItADZlZUg1Gl0nEzkfIwwoDXIlCiYYG2YrHDEzJQcvUl0nV0Fad1l6BjwjZTACUTxOAzckLQRhJl0lVjsVJQ0pQ29nFChmYVMoCigoPhwyXF0nRzkTMgp6XnI8ZXVMFRY/TzYmIQ18UGs5UjwUdVV6Q3JnT3VMFRZkCD0zcQ40HFs9WiQUf1B6ETczGicCFVAtATwXIxtpUEs5UjwUdVB6DCBnOTAPQVk2XHYpKR9pQhR8H3tTdxw0B3I6Q19MFRZkFHgpLQUkTxoaVicWdzcKIHBrT3VMFRZkTz8iOFUnB1YqRyIVOVFzQyAiGyAeWxYiBjYjHAcyWho6VicWdVB6BjwjTyhAPxZkT3g8bAYgH110ERgSOAl6LQIETXlMFRZkT3hnKw01T148XSgOPhY0S3tnHTAYQEQqTz4uIgwRHUthETgSOAl4SnIiATFMSBpOT3hnbBNhHFkkVnZYFRgzF3IUBzocFxpkT3hnbEgmF0x0VT4UNA0zDDxvRnUeUEIxHTZnKgEvFmgmQGNYNRgzF3BuTzACURY5Q1JnbEhhCRgnUiYfalsYDDMzTxEDVl1mQ3hnbEhhUl8sR3YcIhc5FzsoAX1FFUQhGy01IkgnG1YtYyQJf1s4DDMzTXxMUFggTyVrRkhhUhgyEyUbOhxnQRM2GjQeXEMpTXRnbEhhUhhpVC4Oah8vDTEzBjoCHR9kHT0zORovUl4gXS8qOApyQTM2GjQeXEMpTXFnKQYlUkVlOWtad1khQzwmAjBRF3cwAzkpOAEyUnklRyoIdVV6BDczUjMZW1UwBjcpZEFhAF09RjkUdx8zDTYXACZEF1cwAzkpOAEyUBFpViUedwR2aXJnT3UXFVglAj16bisuAkgsQWs5NhcjDDxlQ3VMUlMwUj4yIgs1G1cnG2JaJRwuFiApTzMFW1IUACtvbgsuAkgsQWlTdxw0B3I6Q19MFRZkFHgpLQUkTxoPXDkdOA0uBjxnLDoaUBRoTz8iOFUnB1YqRyIVOVFzQyAiGyAeWxYiBjYjHAcyWhovXDkdOA0uBjxlRnUJW1JkEnRNbEhhUkNpXSoXMkR4NjwjCicbVEIhHXgEJRw4UBQuVj9HMQw0ACYuADtEHBY2CiwyPgZhFFEnVxsVJFF4FjwjCicbVEIhHXpubA0vFhg0H0Fad1l6GHIpDjgJCBQFATsuKQY1UnI8XSwWMlt2QzUiG2gKQFgnGzEoIkBoUkosRz4IOVk8CjwjPzofHRQuGjYgIA1jWxgsXS9aKlVQQ3JnTy5MW1cpCmVlCQ8mUnUoUCMTORx4T3JnT3ULUEJ5CS0pLxwoHVZhGmsIMg0vETxnCTwCUWYrHHBlKQ8mUBFpViUedwR2aXJnT3UXFVglAj16bi0vEVAoXT8TOR54T3JnT3VMUlMwUj4yIgs1G1cnG2JaJRwuFiApTzMFW1IUACtvbg0vEVAoXT9Yflk/DTZnEnlmFRZkTyNnIgksFwVrYDsTOVkNCzciA3dAFRZkT3ggKRx8FE0nUD8TOBdySnI1CiEZR1hkCTEpKDguARBrRCMfMhV4SnIiATFMSBpOElIhOQYiBlEmXWsuMhU/Ez01GyZCUllsATkqKUFLUhhpEy0VJVkFT3IiTzwCFV80DjE1P0AVF1QsQyQIIwp0BjwzHTwJRh9kCzdNbEhhUhhpE2sTMVk/TTwmAjBMCAtkATkqKUg1Gl0nEycVNBg2QyJnUnUJG1EhG3Bud0goFBg5Ez8SMhd6NiYuAyZCQVMoCigoPhxpAhFyEzkfIwwoDXIzHSAJFVMqC3giIgxLUhhpEy4UM3N6Q3JnHTAYQEQqTz4mIBskeF0nV0FwelR6gcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUZXVqbD4IIW0Ifxhafxc1QxcUP3UcWlooBjYgbIrB5hg9XCRaMxwuBjEzDjcAUB9OQnVnrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qXRU1ADMrTwMFRkMlAytncUg6Ums9Uj8fagI8Fj4rDScFUl4wUj4mIBskXhgnXA0VMEQ8Aj40CihAFWkmBGU8MUg8eFQmUCoWdx8vDTEzBjoCFVQlDDMyPEBoeBhpE2sTMVk0BiozRwMFRkMlAytpEwoqWxg9Wy4Udws/Fyc1AXUJW1JOT3hnbD4oAU0oXzhUCBsxQ29nFHUuR18jBywpKRsyT3QgVCMOPhc9TRA1BjIEQVghHCtrbCstHVsiZyIXMkQWCjUvGzwCUhgHAzckJzwoH11lEwwWOBs7DwEvDjEDQkV5IzEgJBwoHF9ndCcVNRg2MDomCzobRhpkKTcgCQYlT3QgVCMOPhc9TRQoCBACURpkKTcgHxwgAEx0fyIdPw0zDTVpKToLZkIlHSxnMWIkHFxDVT4UNA0zDDxnOTwfQFcoHHY0KRwHB1QlUTkTMBEuSyRuZXVMFRYSBisyLQQyXGs9Uj8feR8vDz4lHTwLXUJkUngxd0gjE1siRjtSfnN6Q3JnBjNMQxYwBz0pbCQoFVA9WiUdeTsoCjUvGzsJRkV5XGNnAAEmGkwgXSxUFBU1ADkTBjgJCAdwVHgLJQ8pBlEnVGU9OxY4Aj4UBzQIWkE3Uj4mIBskeBhpE2sfOwo/Qx4uCD0YXFgjQRo1JQ8pBlYsQDhHARApFjMrHHszV11qLSouKwA1HF06QGsVJVlrWHILBjIEQV8qCHYEIAciGWwgXi5HARApFjMrHHszV11qLDQoLwMVG1UsEyQId0huWHILBjIEQV8qCHYAIAcjE1QaWyoeOA4pXgQuHCANWUVqMDosYi8tHVooXxgSNh01FCFnEWhMU1coHD1nKQYleF0nV0EcIhc5FzsoAXU6XEUxDjQ0YhskBnYmdSQdfw9zaXJnT3U6XEUxDjQ0Yjs1E0wsHSUVERY9Q29nGW5MV1cnBC03ZEFLUhhpEyIcdw96FzoiAXUgXFEsGzEpK0YHHV8MXS9HZhxsWHILBjIEQV8qCHYBIw8SBlk7R3ZLMk9QQ3JnT3VMFRYoADsmIEggBlVpDms2Ph4yFzspCG8qXFggKTE1PxwCGlElVwQcFBU7ECFvTRQYWFk3HzAiPg1jWwNpWi1aNg03QyYvCjtMVEIpQRwiIhsoBkF0A2sfOR1QQ3JnTzAARlNkIzEgJBwoHF9ndSQdEhc+XgQuHCANWUVqMDosYi4uFX0nV2sVJVlrU2J3VHUgXFEsGzEpK0YHHV8aRyoII0QMCiEyDjkfG2kmBHYBIw8SBlk7R2sVJVlqQzcpC18JW1JOZXVqbIrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx3N3TnISJnWOtaJkADYrNUh0UkwoUThwelR6gcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUZSg1JQY1WhoSankxdzEvAQ9nIzoNUV8qCHgILhsoFlEoXR4TeVd0QXtNAzoPVFpkIzElPgkzCxRpZyMfOhwXAjwmCDAeGRYXDi4iAQkvE18sQUEWOBo7D3IyBhoHGRYxBh01Pkh8UkgqUicWfx8vDTEzBjoCHR9OT3hnbCQoEEooQTJad1l6Q3J6TzkDVFI3GyouIg9pFVkkVnEyIw0qJDczRxYDW1AtCHYSBTcTN2gGE2VUd1sWCjA1DicVG1oxDnpuZUBoeBhpE2suPxw3Bh8mATQLUERkUngrIwklAUw7WiUdfx47Djd9JyEYRXEhG3AEIwYnG19nZgIlBTwKLHJpQXVOVFIgADY0YzwpF1UsfioUNh4/EXwrGjROHB9sRlJnbEhhIVk/VgYbORg9BiBnT2hMWVklCyszPgEvFRAuUiYfbTEuFyIACiFEdlkqCTEgYj0ILWoMYwRaeVd6QTMjCzoCRhkXDi4iAQkvE18sQWUWIhh4SntvRl8JW1JtZTEhbAYuBhg8WgQRdxYoQzwoG3UgXFQ2Dio+bBwpF1ZDE2tadw47ETxvTQ41B31kJy0lEUgUOxgvUiIWMh1gQ3BnQXtMQVk3GyouIg9pB1EMQTlTfnN6Q3JnMBJCamYMKgIYBD0DUgVpXSIWbFkoBiYyHTtmUFggZVIrIwsgHhgGQz8TOBcpQ29nIzwOR1c2FnYIPBwoHVY6OScVNBg2QzQyATYYXFkqTxYoOAEnCxA9H2see1k/SnI3DDQAWR4iGjYkOAEuHBBgEwcTNQs7ESt9IToYXFA9RyNnGAE1Hl1pDmsfdxg0B3JvTbf2lRZmQXYzZUguABg9H2s+Mgo5ETs3GzwDWxZ5TzxnIxphUBplEx8TOhx6XnJzTyhFFVMqC3FnKQYleDIlXCgbO1kNCjwjACJMCBYIBjo1LRo4SHs7VioOMi4zDTYoGH0XPxZkT3gTJRwtFxhpDmtYB7rwADoiFXgAUBZlT3ilzMphUmF7eGsyIht6QyRlQXsvWlgiBj9pGi0TIXEGfWdwd1l6QxQoACEJRxZ5T3oefiNhIVs7WjsOdzs7ADl1LTQPXhRoZXhnbEgPHUwgVTIpPh0/XnAVBjIEQRRoTwsvIx8CB0s9XCY5IgspDCB6GycZUBpkLD0pOA0zT0w7Ri5WdzgvFz0UBzobCEI2Gj1rbDokAVEzUikWMkQuESciQ3UvWkQqCioVLQwoB0t0AntWXQRzaVgrADYNWRYQDjo0bFVhCTJpE2taGhgzDXJnT3VMCBYTBjYjIx97M1wtZyoYf1sXAjspTXlMFRZkT3o0LR4kUBFlOWtad1kbFiYoT3VMFRZ5Tw8uIgwuBQIIVy8uNhtyQRMyGzpOGRZkT3hnbgkiBlE/Wj8DdVB2aXJnT3U8WVc9CipnbEh8Um8gXS8VIEMbBzYTDjdEF2YoDiEiPkptUhhpET4JMgt4Sn5NT3VMFWUhGywuIg8yUgVpZCIUMxYtWRMjCwENVx5mPD0zOAEvFUtrH2tYJBwuFzspCCZOHBpOT3hnbCsuHF4gVDhad0R6NDspCzobD3cgCwwmLkBjMVcnVSIdJFt2Q3JlCzQYVFQlHD1lZURLDzJDHmZatezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD816PUjc3Xrv3RkK3Z0d7qtezKgcfXjcD8PxtpTwwGDkhwUtrJp2s3FjAUQ3JvKTwfXRZvTxQuOg1hIUwoRzhafFkJBiAxCidFPxtpT7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco0EWOBo7D3IKDjwCeRZ5TwwmLhtvP1kgXXE7Mx0WBjQzKCcDQEYmACBvbi4oAVAgXSxYe1spAiQiTXxmeFctARR9DQwlJlcuVCcff1sbFiYoKTwfXRRoTyNnGA05Bhh0E2k7Ig01QxQuHD1OGRYACj4mOQQ1UgVpVSoWJBx2aXJnT3U4WlkoGzE3bFVhUGwmVCwWMgp6NiIjDiEJdEMwAB4uPwAoHF8aRyoOMld6JDMqCnIfFVkzAXgrIwcxUlAoXS8WMgp6FzoiTycJRkJqTXRNbEhhUnsoXycYNhoxQ29nCSACVkItADZvOkFhG15pRWsOPxw0QxMyGzoqXEUsQSszLRo1PFk9Wj0ff1B6Bj40CnUtQEIrKTE0JEYyBlc5fSoOPg8/S3tnCjsIFVMqC3g6ZWIME1Enf3E7Mx0ODDUgAzBEF2QlCzk1bkRhCRgdVjMOd0R6QRQuHD0FW1FkPTkjLRpjXhgNVi0bIhUuQ29nCTQARlNoTxsmIAQjE1siE3ZaFgwuDBQmHThCRlMwPTkjLRphDxFDfioTOTVgIjYjKzwaXFIhHXBuRiUgG1YFCQoeMzsvFyYoAX0XFWIhFyxncUhjN0k8WjtaNRwpF3I1ADFMW1kzTXRnCh0vERh0Ey0PORouCj0pR3xMXFBkLi0zIy4gAFVnVjoPPgkYBiEzPToIHR9kGzAiIkgPHUwgVTJSdTwrFjs3TXlOcVkqCnZlZUgkHkssEwUVIxA8GnplKiQZXEZmQ3oJI0gzHVxrHz8IIhxzQzcpC3UJW1JkEnFNAQkoHHRzci8eFQwuFz0pRy5MYVM8G3h6bEoCE1YqVidaNAwoETcpG3UPVEUwTXRnCh0vERh0Ey0PORouCj0pR3xMRVUlAzRvKh0vEUwgXCVSflkcCiEvBjsLdlkqGyooIAQkAAIbVjoPMgouID4uCjsYZkIrHx4uPwAoHF9hGmsfOR1zWHIJACEFU09sTR4uPwBjXhoKUiUZMhU2BjZpTXxMUFggTyVuRmItHVsoX2s3NhA0MXJ6TwENV0VqIjkuIlIAFlwbWiwSIz4oDCc3DToUHRQIBi4ibDs1E0w6EWdYOhY0CiYoHXdFP1orDDkrbAQjHnsoRiwSI1l6XnIKDjwCZwwFCzwLLQokHhBrcCoPMBEuQ3JnT3VMFQxkX3puRgQuEVklEycYOzoKLnJnT3VMCBYJDjEpHlIAFlwFUikfO1F4IDMyCD0YGlstAXhnbFJhQhpgOScVNBg2Qz4lAwYDWVJkT3hncUgME1EnYXE7Mx0WAjAiA31OZlMoA3gkLQQtARhpE3FaZ1tzaT4oDDQAFVomAw03OAEsFxhpDms3NhA0MWgGCzEgVFQhA3BlGRg1G1UsE2tad1l6Q2hnX2VWBQZ+X2hlZWItHVsoX2sWNRUTDSQUBi8JFQtkIjkuIjp7M1wtfyoYMhVyQRspGTACQVk2FnhnbEh7UghmA2lTXRU1ADMrTzkOWXohGT0rbEhhTxgEUiIUBUMbBzYLDjcJWR5mIz0xKQRhUhhpE2tad0N6XHBuZTkDVlcoTzQlICsuG1Y6E2taalkXAjspPW8tUVIIDjoiIEBjMVcgXThad1l6Q3JnT29MChRtZTQoLwktUlQrXwUbIxAsBnJnUnUhVF8qPWIGKAwNE1osX2NYGRguCiQiT3VMFRZkT2JnAy4HUBFDfioTOStgIjYjKzwaXFIhHXBuRiUgG1YbCQoeMzsvFyYoAX0XFWIhFyxncUhjIF06Vj9aJA07FyFlQ3UqQFgnT2VnKh0vEUwgXCVSflkJFzMzHHseUEUhG3Bud0gPHUwgVTJSdSouAiY0TXlOZ1M3CixpbkFhF1YtEzZTXXM2DDEmA3UhVF8qI2pncUgVE1o6HQYbPhdgIjYjIzAKQXE2AC03Lgc5WhoaVjkMMgt4T3AwHTACVl5mRlIKLQEvPgpzci8eFQwuFz0pRy5MYVM8G3h6bEoTF1ImWiVaJBwoFTc1TXlMc0MqDHh6bA40HFs9WiQUf1B6NzcrCiUDR0IXCioxJQskSGwsXy4KOAsuSxEoATMFUhgUIxkECTcINhRpfyQZNhUKDzM+CidFFVMqC3g6ZWIME1Enf3lAFh0+ISczGzoCHU1kOz0/OEh8UhoaVjkMMgt6Cz03TycNW1IrAnprbC40HFtpDmscIhc5FzsoAX1FPxZkT3gJIxwoFEFhEQMVJ1t2QQEiDicPXV8qCLrH6kpoeBhpE2sONgoxTSE3DiICHVAxATszJQcvWhFDE2tad1l6Q3IrADYNWRYrBHRnPg0yUgVpQygbOxVyBScpDCEFWlhsRlJnbEhhUhhpE2tad1koBiYyHTtMUlcpCmIPOBwxNV09G2NYPw0uEyF9QHoLVFshHHY1IwotHUBnUCQXeA9rTDUmAjAfGhMgQCsiPh4kAEtmYz4YOxA5XCEoHSEjR1IhHWUGPwtnHlEkWj9HZklqQXt9CToeWFcwRxsoIg4oFRYZfwo5EiYTJ3tuZXVMFRZkT3hnKQYlWzJpE2tad1l6QzshTzsDQRYrBHgzJA0vUnYmRyIcLlF4Kz03TXlOfUIwHx8iOEgnE1ElVi9Yew0oFjduVHUeUEIxHTZnKQYleBhpE2tad1l6Dz0kDjlMWl12Q3gjLRwgUgVpQygbOxVyBScpDCEFWlhsRng1KRw0AFZpez8OJyo/ESQuDDBWf2ULIRwiLwclFxA7VjhTdxw0B3tNT3VMFRZkT3guKkgvHUxpXCBIdxYoQzwoG3UIVEIlTzc1bAYuBhgtUj8beR07FzNnGz0JWxYKACwuKhFpUHAmQ2lWdTs7B3I1CiYcWlg3CnprOBo0FxFyEzkfIwwoDXIiATFmFRZkT3hnbEgnHUppbGdaJFkzDXIuHzQFR0VsCzkzLUYlE0woGmseOHN6Q3JnT3VMFRZkT3guKkgyXEglUjITOR56AjwjTyZCWFc8PzQmNQ0zARgoXS9aJFcqDzM+BjsLFQpkHHYqLRARHlkwVjkJekh6AjwjTyZCXFJkEWVnKwksFxYDXCkzM1kuCzcpZXVMFRZkT3hnbEhhUhhpE2suMhU/Ez01GwYJR0AtDD19GA0tF0gmQT8uOCk2AjEiJjsfQVcqDD1vDwcvFFEuHRs2FjofPBsDQ3UfG18gQ3gLIwsgHmglUjIfJVBhQyAiGyAeWzxkT3hnbEhhUhhpE2sfOR1QQ3JnT3VMFRYhATxNbEhhUhhpE2s0OA0zBStvTR0DRRRoTRYobBskAE4sQWscOAw0B3BrGycZUB9OT3hnbA0vFhFDViUedwRzaVgrADYNWRYJDjEpHlphTxgdUikJeTQ7Cjx9LjEIZ18jBywAPgc0AlomS2NYEBg3BnIOATMDFxpmBjYhI0poeHUoWiUoZUMbBzYLDjcJWR5mKDkqKUhhUgJpEWVUFBY0BTsgQRIteHMbIRkKCUFLP1kgXRlIbTg+Bx4mDTAAHRQXDCouPBxhSBg/EWVUFBY0BTsgQQMpZ2UNIBZuRiUgG1YbAXE7Mx0eCiQuCzAeHR9OAzckLQRhHlolcCoPMBEuLwFnUnUhVF8qPWp9DQwlPlkrVidSdTo7FjUvG3VWFRtmRlIrIwsgHhglUScoNgs/ECYLPHVRFXslBjYVflIAFlwFUikfO1F4MTM1CiYYFQxkQnpuRmJsXxirptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sKl+sWOoKam+sil2fij56irptuYwum49sJNQnhMYXcGT2pnrujVUnkcZwRad1EpBj4rT35MUEcxBihnZ0giHlkgXjhafFkqBiY0T35MVlkgCituRkVsUtrco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU4trco6nvx5vP87DS/7f5pdTR/7rS3IrU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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
