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
				if o.halt then
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

local __k = '09sNdGh1HxCDqEMhYab0BC4z'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2 })
