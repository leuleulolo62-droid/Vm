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
local SPY_GUI = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true,
	["simplespy"] = true, ["hydroxide"] = true, ["remote spy"] = true,
}
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
				if SPY_GUI[string.lower(c.Name)] then return true, "GUI: " .. c.Name end
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

-- watchdog: scan on an interval, call onDetect(name, detail) on first hit -----
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	local body = function()
		local wait_ = (task and task.wait) or wait
		while ctx.alive do
			wait_(opts.interval or 3)
			if not ctx.alive then return end
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui,
				http = opts.http, namecall = opts.namecall,
				remote = opts.remote, dex = opts.dex, raw = ctx.raw,
			})
			if #hits > 0 then
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
			end
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

local __k = 's0t8JyWrLmurfsQcKE03uEie'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
