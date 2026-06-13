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

local __k = '46IwBpY9kWbxIXq5OoNRqCms'
local __p = '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MXhMFX9BeGVdY11dDAdpWm9QHEEIMg4ULDYFP29PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TUVo6EisWeVQEMwdYdGVRFwsKLTcfN01bAgZkT3JVcBtLIwodJ1JRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBY9FjAXPE0mPgxUaSwQRygKOh8QO01OFAZnQnJceQlFYVdYZHVRcj0KLyZ7Y01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2IVNUoOd09VaQoQWysAI1hRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRkfNhAfLCw8XCFDbiYQMQoWQHsoD2JNeQlFZVJUaWhfDHdlbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBYsGSZ6eRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLdwcUOj17FW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY00aUhYkGCYVeQRWd0AoLCoXUCwbbnpAc11WFBtpBSsDMkBCdUIMIT0fP29PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpVzYRK14OIy8RJ3RRQS4dKTcFDgwLFAtpR2xJbhVLZkxIaXVcFR8KPDQUIBl5FBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRkOOxEdID5RWCALK3JMfk1Rc1kmE2JYYQlGblddYHpRQScKIFhRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRkfNhAfLCw8XCFDbiYQMQoWQHsoD2JNeQlFb1NUaWhfDHlPY39RBhUQUVolEiwEUxlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRUCMcKzsXYwAcUFNpSn9Qe30ONAcWPXhZA39CdmJUak9TQF4sGUhQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW8bLyAWJhk+XVhlVzYRK14OIy8ZMXhMFX9BeGNdY11dAw9pWm9QHksONhZyaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnIULx4WFBtkVxARN10EOmhYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY00H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PXhMFWcMOyADJgMHZlkmA2wgNkoCIwsXJ3hcFTsOPDUUNz0cRx9nOiMXN1AfIgYdQ3hRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFF8vVyYZKk1La0JAaSwZUCFlbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLdwAKLDkaP29PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpVycePTNLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJcbk0hURsgBDEFPBkmOBQdHTdRXClPOj0eYwsSRhZhBScDPE0YdxYRJD0eQDtGRHJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeVANdwYROixRC29cfnIFKwgdPhZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW8HOz9LDgIFUWImXzYRK14OIzIXOnF7FW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpEiwUUxlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRUCELRHJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpAyMDMhccNgsMYWhfBmZlbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRYwgdUDxpV2JQeRlLd0JYaXhRFW9PbnJRY01TFBZpV2JQUxlLd0JYaXhRFW9PbnJRY01TFBZpV2JQeRlLd0JVZHgjUDwbISAUYwMcRlsoG2InOFUABBIdLDx7FW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbjoELkMkVVoiJDIVPF1LakJJf1JRFW9PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PRHJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnJRY01eGRYdEi4VKVYZI0IdMTkSQSMWbj0fNwJTX18qHGIAOF1LIw1YLi0QRy4BOjcUYw8GQEImGWIGMEoCNQsUICwIP29PbnJRY01TFBZpV2JQeRlLd0JYaXhRFW9PbnIDLAIHGnUPBSMdPBlWdyE+OzkcUGEBKyVZKAQQX2YoE2wgNkoCIwsXJ3haFRkKLSYeMV5dWlM+X3JceQpHd1JRYFJRFW9PbnJRY01T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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
