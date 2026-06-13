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

local __k = 'eHWicbDYAFw6s1Vqg9IkLhAa'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
