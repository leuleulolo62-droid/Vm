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

local __k = '6SiUzXJsCbGfbaPIF3acxJ2c'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, antiSpy = { kick = true, halt = true } })
