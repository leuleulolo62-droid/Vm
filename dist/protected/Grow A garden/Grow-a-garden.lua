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

local __k = 'qut69QacjyyOOjTTvgASs5pe'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2 })
