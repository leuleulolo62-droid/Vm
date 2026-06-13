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

local __k = 'jjP7dZBz9QQHG8puZ5dO6ddi'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
