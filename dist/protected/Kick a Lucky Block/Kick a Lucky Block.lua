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

local __k = 'WeFjcQ89l0LNnon88sq6VvPt'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2 })
