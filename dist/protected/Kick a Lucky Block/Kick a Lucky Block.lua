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

local __k = 'nwm1NTzIMknz5on2ZvHtMZCb'
local __p = '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7pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH2/n1AHG627sttSy01eykndXpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemOA+vVnHGN0mN3Zifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rMcCUiCA8WFSwIVXpLaA9HemNCTjYYRSEACCgkBU5aFU9OEnpWaEltPCIOHRJBO250WmkMHhoVfgYNWXpWaFRtemNCTldQESg1FjooR2RaFU9Ocy8CJyQhOyAHTldNEW50WmltVk4cVAMdV3Z8aFRtegIXGhg4QSkmGy0oKQIVVgQdEmdWLhUhKSZOZFdNEW4VDz0iOAsWWU9OEnpWaFRtemNfThEMXT0xVkNtS05adBoaXRgDMSMoMyQKGgRNEW50R2krCgIJUENkEnpWaDU4LiwgGw4+QSsxHmltS05aFVJOVDsaOxFhUGNCTlc5YRk1FiIIBQ8YWQoKEnpWaFRweiUDAgQIHUR0WmltPz4tVAMFYSoTLRBtemNCTldNDG5hSmVHS05aFSEBUTYfOFRtemNCTldNEW50WnRtDQ8WRgpCOHpWaFQENCUoGxodEW50WmltS05aFU9TEjwXJAcodklCTldNcCAgEwgLIE5aFU9OEnpWaFRtZ2MEDxseVGJeB0NHRkNa1/vi0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr6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GBIDRQA1FywQQkdaUQBkEnpWaFRtemNCTldNEW50WioiBQBAcwYcV3JfQlRtemNCTldNEW50WiwjD2RaFU9OEnpWaBEjPmpoTldNESs6HkNtS05aRQwPXjZeLgEjOTcLARlFGER0WmltS05aFQcPQD4BKQYoGS8LDRxFUzo6U0NtS05aUAEKG1ATJhBHUG5PTpX5vazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH27pX5sazA+qvZ64zutY36srjiyJbZ2qH2/n1AHG627sttSzszFTwrZg8maFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemOA+vVnHGN0mN3Zifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rUmN3Nifr61/vu0M72quDNuNfijOPt09rMcCUiCA8WFTgHXD4ZP1Rweg8LDAUMQzduOTsoChofYgYAVjUBYA8ZMzcOC0pPeic3EWksSyIPVgQXEhgaJxcmej9CN0UGE2IXHyc5DhxHQR0bV3Y3PQAiCSsNGUoZQzsxB2BHYUNXFTwPVD9WBhs5MyULDRYZWCE6Wj4/Ch4KUB1ORjVWOAYoLCYMGldPXS83ESAjDE4ZVB8PUDMaIQA0ehMOGxAEX2x0GTssGAYfRmUCXTkXJFQ/OzQsAQMEVzd0R2kBAgwIVB0XHBQZPB0rI0kuBxUfUDwtVAciHwccTE9TEjwDJhc5MywMRgQIXSh4WmdjRUdwFU9OEjYZKxUheiIQCQRNDG4vVGdjFmRaFU9OQjkXJBhlPDYMDQMEXiB8U0NtS05a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CE8ZZDsaQlRtemNCTldNEW50WmltS05aFU9OEnpWaBYoKTc2ARgBEXN0DkNtS05aFU9OEnpWaFRtemNCTldNESs6HkNtS05aFU9OEnpWaFRtemNCCxkJO250WmltS05aFU9OEj8YLH5temNCTldNEW50WmlHS05aFU9OEnpWaFRtMyVCDBYOWj41GSJtHwYfW2VOEnpWaFRtemNCTldNEW50HCY/SzFWFRtOWzRWIQQsMzERRhUMUiUkGyomUSkfQSwGWzYSOhEjcmpLThMCES08HyomPwEVWUcaG3oTJhBHemNCTldNEW50WmltDgAeP09OEnpWaFRtemNCTh4LES08GzttHwYfW2VOEnpWaFRtemNCTldNEW50HCY/SzFWFRtOWzRWIQQsMzERRhQFUDxuPSw5KAYTWQscVzReYV1tPixCDR8IUiUAFSYhQxpTFQoAVlBWaFRtemNCTldNEW4xFC1HS05aFU9OEnpWaFRtUGNCTldNEW50WmltS0NXFSofRzMGaBYoKTdCGhgCXW49HGkjBBpaVAMcVzsSMVQoKzYLHgcIVUR0WmltS05aFU9OEnofLlQvPzAWOhgCXW41FC1tCAYbR08aWj8YQlRtemNCTldNEW50WmltS04TU08MVykCHBsiNm0yDwUIXzp0BHRtCAYbR08aWj8YQlRtemNCTldNEW50WmltS05aFU9OXjUVKRhtMjYPTkpNUiY1CHMLAgAecwYcQS41IB0hPgwELRsMQj18WAE4Bg8UWgYKEHN8aFRtemNCTldNEW50WmltS05aFU8HVHoePRltLisHAH1NEW50WmltS05aFU9OEnpWaFRtemNCTlcFRCNuLycoGhsTRTsBXTYFYF1HemNCTldNEW50WmltS05aFU9OEnpWaFRtLiIRBVkaUCcgUnljWkdwFU9OEnpWaFRtemNCTldNEW50WmltS05aVwodRg4ZJxhjCiIQCxkZEXN0GSEsGWRaFU9OEnpWaFRtemNCTldNEW50WiwjD2RaFU9OEnpWaFRtemNCTldNVCAwcGltS05aFU9OEnpWaFRtemNoTldNEW50WmltS05aFU9OEndbaCA/OyoMQSQcRC8gW0NtS05aFU9OEnpWaFRtemNCAhgOUCJ0DjssAgApQAwNVykFaEltPCIOHRJnEW50WmltS05aFU9OEnpWaAQuOy8ORhEYXy0gEyYjQ0dwFU9OEnpWaFRtemNCTldNEW50WmkvDh0OYQABXmA3KwAkLCIWC19EO250WmltS05aFU9OEnpWaFRtemNCGgUMWCAHDyouDh0JFVJORigDLX5temNCTldNEW50WmltS05aUAEKG1BWaFRtemNCTldNEW50WmltYU5aFU9OEnpWaFRtemNCTlcEV24gCCgkBT0PVgwLQSlWPBwoNElCTldNEW50WmltS05aFU9OEnpWaAA/OyoMOR4DQm5pWj0/CgcUYgYAQXpdaEVHemNCTldNEW50WmltS05aFU9OEnoaJxcsNmMOBxoERR0gCGlwSyEKQQYBXClYHAYsMy0xCwQeWCE6VB8sBxsfFQAcEng/JhIkNCoWC1VnEW50WmltS05aFU9OEnpWaFRtemMLCFcBWCM9Dho5GU4ECE9MezQQIRokLiZATgMFVCBeWmltS05aFU9OEnpWaFRtemNCTldNEW50FiYuCgJaWQYDWy5WdVQ5NS0XAxUIQ2Y4EyQkHz0OR0ZkEnpWaFRtemNCTldNEW50WmltS05aFU9OWzxWJB0gMzdCDxkJETomGyAjPAcURk9QD3oaIRkkLmMWBhIDO250WmltS05aFU9OEnpWaFRtemNCTldNEW50WmkODQlUdBoaXQ4EKR0jen5CCBYBQiteWmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSx4ZVAMCGjwDJhc5MywMRl5NZSEzHSUoGEA7QBsBZigXIRp3CSYWOBYBRCt8HCghGAtTFQoAVnN8aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRteg8LDAUMQzduNCY5AggDHU06QDsfJlQ5OzEFCwNNQys1GSEoD05SF09AHHoaIRkkLmNMQFdPET0lDyg5GEdUFTwaXSoGLRBjeGpoTldNEW50WmltS05aFU9OEnpWaFRtemNCCxkJO250WmltS05aFU9OEnpWaFRtemNCCxkJO250WmltS05aFU9OEnpWaFQoNCdoTldNEW50WmltS05aUAEKOHpWaFRtemNCCxkJO250WmltS05aQQ4dWXQBKR05cnNMXV5nEW50WiwjD2QfWwtHOFBbZVQMLzcNTjQBWC0/WjF/SywVWxodEhYZJwRHd25COh8IESk1FyxtGB4bQgEdEjgZJgE+eiEXGgMCXz10UjF/R04CAENOSmtGYVQkNGMpBxQGZD4zCCgpDh1aUhoHEj4DOh0jPWMWHBYEXyc6HUNgRk4tUE8KVy4TKwBtOy0GThQBWC0/Wj0lDgNaVBoaXTcXPB0uOy8OF1cZXm43FigkBk4OXQpOXy8aPB09NioHHFcPXiAhCUM5Ch0RGxweUy0YYBI4NCAWBxgDGWdeWmltSxkSXAMLEi4EPRFtPixoTldNEW50WmkkDU45UwhAcy8CJzchMyAJNkVNRSYxFENtS05aFU9OEnpWaFQhNSADAlcGWC0/LzkqGQ8eUBxOD3o6JxcsNhMODw4IQ2AEFig0Dhw9QAZUdDMYLDIkKDAWLR8EXSp8WAIkCAUvRQgcUz4TO1ZkUGNCTldNEW50WmltSwccFQQHUTEjOBM/OycHHVcZWSs6cGltS05aFU9OEnpWaFRtemNPQ1chXiE/Wi8iGU4JRQ4ZXD8SaBYiNDYRThUYRTo7FDptQw0WWgELVnoQOhsgegENAAIeEToxFzkhChofHGVOEnpWaFRtemNCTldNEW50HCY/SzFWFQwGWzYSaB0jeioSDx4fQmY/EyomPh4dRw4KVylMDxE5HiYRDRIDVS86DjplQkdaUQBkEnpWaFRtemNCTldNEW50WmltS04TU08NWjMaLE4EKQJKTD4AUCkxODw5HwEUF0ZOUzQSaBclMy8GVD8MQho1HWFvKRsOQQAAEHNWPBwoNElCTldNEW50WmltS05aFU9OEnpWaFRtemNPQ1crXjs6HmksSwwVWxodEjgDPAAiNG9CDRsEUiV0Ez1sYU5aFU9OEnpWaFRtemNCTldNEW50WmltSx4ZVAMCGjwDJhc5MywMRl5nEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmRgSygTRwpOczkCIQIsLiYGTgQEViA1FmlmSw0WXAwFEiwfOgA4Oy8OF31NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50FiYuCgJaVgAAXHpLaBclMy8GQDYORSciGz0oD1Q5WgEAVzkCYBI4NCAWBxgDGWd0HycpQmRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OVDUEaCthejALCRkMXW49FGkkGw8TRxxGSXg3KwAkLCIWCxNPHW52NyY4GAs4QBsaXTRHCxgkOShAE15NVSFeWmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU8eUTsaJFwrLy0BGh4CX2Z9cGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaBclMy8GNQQEViA1FhR3LQcIUEdHOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCCxkJGER0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltDgAeP09OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoVJxojYAcLHRQCXyAxGT1lQmRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OH3dWCRg+NWMEBwUIETg9G2kbAhwOQA4CezQGPQAAOy0DCRIfES8gWis4HxoVW08eXSkfPB0iNElCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNXSE3GyVtCgwJZQAdEmdWKxwkNidMLxUeXiIhDiwdBB0TQQYBXFBWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtNiwBDxtNUCwnKSA3Dk5HFQwGWzYSZjUvKSwOGwMIYicuH0NtS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aWQANUzZWKxEjLiYQNldQES82CRkiGEAiFUROUzgFGx03P206TlhNA0R0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltBwEZVANOUT8YPBE/A2NfThYPQh47CWcUS0VaVA0dYTMMLVoUemxCXH1NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50LCA/HxsbWSYAQi8CBRUjOyQHHE0+VCAwNyY4GAs4QBsaXTQzPhEjLmsBCxkZVDwMVmkuDgAOUB03HnpGZFQ5KDYHQlcKUCMxVml9QmRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9ORjsFI1o6OyoWRkdDAXt9cGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS04sXB0aRzsaARo9LzcvDxkMVismQBooBQo3WhodVxgDPAAiNAYUCxkZGS0xFD0oGTZWFQwLXC4TOi1henNOThEMXT0xVmkqCgMfGU9eG1BWaFRtemNCTldNEW50WmltS05aFU9OEnoTJhBkUGNCTldNEW50WmltS05aFU9OEnpWLRopUGNCTldNEW50WmltS05aFU8LXD58aFRtemNCTldNEW50HycpYU5a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FU9OEnpWaFRtemNCTldNEW50WmltBwEZVANOUC8CPBsjen5CJiIpES86HmkFPipAcwYAVhwfOgc5GSsLAhNFEwU9GSIPHhoOWgFMG1BWaFRtemNCTldNEW50WmltS05aFU9OEnofLlQvLzcWARlNUCAwWis4HxoVW0E4WykfKhgoejcKCxlnEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50Wis5BTgTRgYMXj9WdVQ5KDYHZFdNEW50WmltS05aFU9OEnpWaFRtemNCThIBQiteWmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSxobRgRARTsfPFx9dHJLZFdNEW50WmltS05aFU9OEnpWaFRtemNCThIDVUR0WmltS05aFU9OEnpWaFRtemNCThIDVUR0WmltS05aFU9OEnpWaFRtemNCTn1NEW50WmltS05aFU9OEnpWaFRteioEThUZXxg9CSAvBwtaQQcLXFBWaFRtemNCTldNEW50WmltS05aFU9OEnpbZVR/dGM2HB4KVismWiIkCAVaVxZOUCMGKQc+My0FTgMFVG4fEyomKRsOQQAAEjsYLFQ+LiIQGh4DVm4gEixtBgcUXAgPXz9WLB0/PyAWAg5nEW50WmltS05aFU9OEnpWaFRtemNCTldNRTw9HS4oGSUTVgRGG1BWaFRtemNCTldNEW50WmltS05aFU9OEnp8aFRtemNCTldNEW50WmltS05aFU9OEnpWZVltaW1CORYERW4yFTttBgcUXAgPXz9WPBttKTcDHANnEW50WmltS05aFU9OEnpWaFRtemNCTldNXSE3GyVtGBobRxs6EmdWPB0uMWtLZFdNEW50WmltS05aFU9OEnpWaFRtemNCTgAFWCIxWiciH04xXAwFcTUYPAYiNi8HHFkkXwM9FCAqCgMfFQ4AVnoCIRcmcmpCQ1ceRS8mDh1tV05IFQ4AVno1LhNjGzYWATwEUiV0HiZHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFRsPQTFYPxUkLmtLZFdNEW50WmltS05aFU9OEnpWaFRtemNCThIDVUR0WmltS05aFU9OEnpWaFRtemNCTldNEW5eWmltS05aFU9OEnpWaFRtemNCTldNEW50Ey9tIAcZXiwBXC4EJxghPzFMJxkgWCA9HSggDk4OXQoAOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFQhNSADAlcAXioxWnRtJB4OXAAAQXQ9IRcmCiYQCBIORSc7FGcbCgIPUE8BQHpUDxsiPmNKVkdACHtxU2tHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFQMBUTsaaAAsKCQHGjoEX2J0Dig/DAsOeA4WOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRHemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTlpAEQoxDiw/BgcUUE8aWj9WPBU/PSYWTgQOUCIxWjssBQkfFQ0PQT8SaBsjejcKC1cAXioxWigjD04JQQ4KWy8baBE7Py0WZFdNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW44FSosB04TRjwaUz4fPRltZ2MEDxseVER0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltGw0bWQNGVC8YKwAkNS1KR31NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSwcJZhsPVjMDJVRwehQHDwMFVDwHHzs7Ag0faiwCWz8YPFoILCYMGgRDYjo1HiA4Bk4bWwtOZT8XPBwoKBAHHAEEUisLOSUkDgAOGyoYVzQCO1oeLiIGBwIAEXB0DSY/AB0KVAwLCB0TPCcoKDUHHCMEXCsaFT5lQmRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OVzQSYX5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCZFdNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW49HGkkGD0OVAsHRzdWPBwoNElCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WiArSwMVUQpOD2dWaiQoKCUHDQNNGX9kSmxtRk4IXBwFS3NUaAAlPy1oTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aQQ4cVT8CBR0jdmMWDwUKVDoZGzFtVk5KG1ddHnpGZk15em5PTicIQygxGT1HS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoTJAcoMyVCAxgJVG5pR2lvLAEVUU9GCmpbcUFoc2FCGh8IX0R0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoCKQYqPzcvBxlBETo1CC4oHyMbTU9TEmpYfkNhenNMVkZNHGN0PzEuDgIWUAEaOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCCxseVCcyWiQiDwtaCFJOEB4TKxEjLmNKWEdACX5xU2ttHwYfW2VOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTlcZUDwzHz0AAgBWFRsPQD0TPDksImNfTkdDBH54WnljXVtaGEJOdSgTKQBHemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW4xFjooS0NXFT0PXD4ZJX5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50Wmk5ChwdUBsjWzRaaAAsKCQHGjoMSW5pWnljWV5WFV9AC2J8aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTlcIXypeWmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSwsWRgpkEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMLCFcAXioxWnRwS0wqUB0IVzkCaFx8anNHTlpNQycnETBkSU4OXQoAOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNETo1CC4oHyMTW0NORjsELxE5FyIaTkpNAWBtTWVtWkBKFUJDEgoTOhIoOTdoTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmkoBx0fXAlOXzUSLVRwZ2NAKRgCVW58QnlgUltfHE1ORjITJn5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50Wmk5ChwdUBsjWzRaaAAsKCQHGjoMSW5pWnljU19WFV9AC2xWZVltHzsBCxsBVCAgcGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OVzYFLR0rei4NChJNDHN0WA0oCAsUQU9GBGpbcERoc2FCGh8IX0R0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoCKQYqPzcvBxlBETo1CC4oHyMbTU9TEmpYfkVhenNMWU5NHGN0PTsoChpwFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFQoNjAHTlpAERw1FC0iBmRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMWDwUKVDoZEydhSxobRwgLRhcXMFRwenNMXEdBEX56Q3BHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoTJhBHemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCThIDVUR0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltYU5aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9DH3ohKR05ejYMGh4BEQU9GSIOBAAORwACXj8EZicuOy8HThEMXSInWj4kHwYTW08aUygRLQAAMy1CDxkJETo1CC4oHyMbTWVOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWJBsuOy9CDRYdRTsmHy0eCA8WUE9TEjQfJH5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCAhgOUCJ0CSosBws5WgEAOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFQhNSADAlceUi84HxsoCg0SUAtOD3oQKRg+P0lCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNQi01FiwOBAAUFVJOYC8YGxE/LCoBC1k9QysGHycpDhxAdgAAXD8VPFwrLy0BGh4CX2Z9cGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OWzxWJhs5eggLDRwuXiAgCCYhBwsIGyYAfzMYIRMsNyZCGh8IX0R0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoFKxUhPwANABlXdScnGSYjBQsZQUdHOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNETwxDjw/BWRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaBEjPklCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WiUiCA8WFRwNUzYTaEltESoBBTQCXzomFSUhDhxUZgwPXj98aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTlcEV24nGSghDk5ECE8aUygRLQAAMy1CDxkJET03GyUoS1JHFRsPQD0TPDksImMWBhIDO250WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEikVKRgoCCYDDR8IVW5pWj0/HgtwFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCDRYdRTsmHy0eCA8WUE9TEikVKRgoUGNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSx0ZVAMLcTUYJk4JMzABARkDVC0gUmBHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoTJhBHemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCThIDVWdeWmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS2RaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OH3dWHxUkLmMXHlcZXm5lVHxtGAsZWgEKQXoQJwZtLisHTgQOUCIxWj0iSwYTQU8aWj9WPBU/PSYWTl8FVC8mDisoChpaUwAcEjcXMFQ+KiYHCl5nEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WiUiCA8WFQwGVzkdGwAsKDdCU1cZWC0/UmBHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFRgGWzYTaBoiLmMRDRYBVBwxGyolDgpaVAEKEhEfKx8ONS0WHBgBXSsmVAAjJgcUXAgPXz9WKRopejcLDRxFGG55WiolDg0RZhsPQC5WdFR8dHZCDxkJEQ0yHWcMHhoVfgYNWXoSJ35temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNERwhFBooGRgTVgpAej8XOgAvPyIWVCAMWDp8U0NtS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aUAEKOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFQkPGMRDRYBVA07FCdjKAEUWwoNRj8SaAAlPy1CHRQMXSsXFScjUSoTRgwBXDQTKwBlc2MHABNnEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WkNtS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aGEJOAXRWDRopejcKC1cAWCA9HSggDk4NXBsGEi4eLVQOGxM2OyUodW4nGSghDk4MVAMbV1BWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtLjELCRAIQws6HgIkCAVSVg4eRi8ELRAeOSIOC15nEW50WmltS05aFU9OEnpWaFRtemNCTldNVCAwcGltS05aFU9OEnpWaFRtemNCTldNEW50WkNtS05aFU9OEnpWaFRtemNCTldNEW50WmlgRk48WQ4JEi4eLVQ/PzcXHBlNfwEDWjoiSwMbXAFOXjUZOFQuOy1FGlcZVCIxCiY/H04eQB0HXD1WPxUkLmgWGRIIX0R0WmltS05aFU9OEnpWaFRtemNCTldNEW49CRsoHxsIWwYAVQ4ZAx0uMRMDCldQETomDyxHS05aFU9OEnpWaFRtemNCTldNEW50WmltYU5aFU9OEnpWaFRtemNCTldNEW50WmltS0NXFVtAEg0XIQBtPCwQTiQZUDohCWk5BE4YUAwBXz9WaiA+Ly0DAx5PEWY1HD0oGU4WVAEKWzQRaF9tODEDBxkfXjp0DjssBR0cWh0DG1BWaFRtemNCTldNEW50WmltS05aFU9OEnpbZVQZMioRThoIUCAnWj0lDk4dVAILEjIXO1Q9KCwBCwQeVCp0DiEoSwUTVgROUzQSaAc5OzEWCxNNRSYxWjsoHxsIW08dVysDLRouP0lCTldNEW50WmltS05aFU9OEnpWaFRtemMOARQMXW4gCTweHw8IQU9TEi4fKx9lc0lCTldNEW50WmltS05aFU9OEnpWaFRtemMVBh4BVG4TGyQoIw8UUQMLQHQlPBU5LzBCEEpNExonDycsBgdYFQ4AVnoCIRcmcmpCQ1cZQjsHDig/H05GFV5bEjsYLFQOPCRMLwIZXgU9GSJtDwFwFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEi4XOx9jLSILGl9dH3x9cGltS05aFU9OEnpWaFRtemNCTldNEW50WiwjD2RaFU9OEnpWaFRtemNCTldNEW50WmltS05wFU9OEnpWaFRtemNCTldNEW50WmltS05aGEJOfzUALVQ5NWMJBxQGET41Hmk4GAcUUk8mRzcXJhskPmMSBg4eWC0nWmE4BQ8UVgcBQD8SZFQ6OzUHTgcYQiYxCWkjChoPRw4CXiNfQlRtemNCTldNEW50WmltS05aFU9OEnpWaBgiOSIOThoCRysXEig/S1NaeQANUzYmJBU0PzFMLR8MQy83Diw/YU5aFU9OEnpWaFRtemNCTldNEW50WmltSwIVVg4CEigZJwBtZ2MPAQEIciY1CGksBQpaWAAYVxkeKQZjCjELAxYfSB41CD1HS05aFU9OEnpWaFRtemNCTldNEW50WmltBwEZVANOWi8baEltNywUCzQFUDx0GycpSwMVQwotWjsEcjIkNCckBwUeRQ08EyUpJAg5WQ4dQXJUAAEgOy0NBxNPGER0WmltS05aFU9OEnpWaFRtemNCTldNEW49HGk/BAEOFQ4AVnoePRltOy0GTjAMXCscGycpBwsIGzwaUy4DO1RwZ2NAOgQYXy85E2ttHwYfW2VOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWJBsuOy9CGhYfVisgKiY+S1NaXgYNWQoXLFodNTALGh4CX25/Wh8oCBoVR1xAXD8BYERhenBOTkdEO250WmltS05aFU9OEnpWaFRtemNCTldNEW50WmlHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFUJDEh4TPBE/NyoMC1caUDgxWjo9DgseFQkcXTdWKRc5MzUHTgAMRyt0EydtHAEIXhweUzkTQlRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMOARQMXW4jGz8oOB4fUAtOD3pHfUFHemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTgcOUCI4Ui84BQ0OXAAAGnN8aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTlcBXi01FmkaL05HFR0LQy8fOhFlCCYSAh4OUDoxHho5BBwbUgpAYTIXOhEpdAcDGhZDZi8iHw0sHw9TP09OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtPCwQTihBETk1DCxtAgBaXB8PWygFYAMiKCgRHhYOVGADGz8oGFQ9UBstWjMaLAYoNGtLR1cJXkR0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoaJxcsNmMGDwMMEXN0LQ1jPA8MUBw1RTsALVoDOy4HM31NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU8HVHoSKQAseiIMClcJUDo1VBo9DgseFRsGVzR8aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSxkbQwo9Qj8TLFRweicDGhZDYj4xHy1HS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCThUfVC8/cGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaBEjPklCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WiwjD2RaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OVzQSYX5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCZFdNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW55V2keDhpaRhoeVyhWIB0qMmM1DxsGYj4xHy1tHwFaWhoaQC8YaAAlP2MVDwEIO250WmltS05aFU9OEnpWaFRtemNCTldNEW50WmklHgNUYg4CWQkGLREpen5CGRYbVB0kHywpS0RaB0FbOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFQlLy5YLR8MXykxKT0sHwtScAEbX3Q+PRksNCwLCiQZUDoxLjA9DkAoQAEAWzQRYX5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCZFdNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW55V2kABBgfYQBORjUBKQYpeigLDRxNQS8wcGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS04SQAJUfzUALSAicjcDHBAIRR47CWBHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFWVOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWZVltDSILGlcYXzo9FmkuBwEJUE8aXXodIRcmejMDCn1NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50FiYuCgJaWAAYVwkCKQY5en5CGh4OWmZ9cGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS04NXQYCV3oCIRcmcmpCQ1cAXjgxKT0sGRpaCU9fB3oXJhBtGSUFQDYYRSEfEyomSwoVP09OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtNiwBDxtNUjsmCCwjHy0SVB1OD3o6JxcsNhMODw4IQ2AXEig/Cg0OUB1kEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMOARQMXW43Dzs/DgAOZwABRnpLaBc4KDEHAAMuWS8mWigjD04ZQB0cVzQCCxwsKG0yHB4AUDwtKig/H2RaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaB0reiAXHAUIXzoGFSY5SxoSUAFkEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNXSE3GyVtDwcJQU9TEnIVPQY/Py0WPBgCRWAEFTokHwcVW09DEi4XOhMoLhMNHV5DfC8zFCA5HgofP09OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTh4LESo9CT1tV05CFRsGVzR8aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSwwIUA4FOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNESs6HkNtS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRgd2MwC1oEQj0hH2kABBgfYQBOWzxWPBsieiUDHFdFQysnHz0+SxoTWAoBRy5fQlRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WiArSwoTRhtODHpFeFQ5MiYMZFdNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnoePRl3FywUCyMCGTo1CC4oHz4VRkZkEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNVCAwcGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OVzQSQlRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNRS8nEWc6CgcOHV9AAXN8aFRtemNCTldNEW50WmltS05aFU9OEnpWaFRteiYMCn1NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50cGltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05XGE88VykCJwYoei0NHBoMXW4DGyUmOB4fUAtkEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaBw4N201DxsGYj4xHy1tVk5LA2VOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWQlRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNPQ1c5VCIxCiY/H04fTQ4NRjYPaBsjLixCBR4OWm4kGy1tHwFaUhoPQDsYPBEoeiEXGgMCX24iEzokCQcWXBsXOHpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFQ/NSwWQDQrQy85H2lwSy08Rw4DV3QYLQNlMSoBBScMVWAEFTokHwcVW09FEgwTKwAiKHBMABIaGX54WnphS15THGVOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWQlRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNPQ1crXjw3H2k3BAAfFRoeVjsCLVQ+NWMpBxQGczsgDiYjSw8KRQoPQClWIRkgPycLDwMIXTdeWmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSx4ZVAMCGjwDJhc5MywMRl5nEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS04WWgwPXnosJxooGSwMGgUCXSIxCGlwSxwfRBoHQD9eGhE9NioBDwMIVR0gFTssDAtUeAAKRzYTO1oONS0WHBgBXSsmNiYsDwsIGzUBXD81Jxo5KCwOAhIfGER0WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFTUBXD81Jxo5KCwOAhIfCxskHig5DjQVWwpGG1BWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtPy0GR31NEW50WmltS05aFU9OEnpWaFRtemNCTlcIXypeWmltS05aFU9OEnpWaFRtemNCTldNEW50cGltS05aFU9OEnpWaFRtemNCTldNEW50WmRgSy8IRwYYVz5WKQBtMSoBBVcdUCp6WgAgBgseXA4aVzYPaAYoKTcDHANNUjc3FixjYU5aFU9OEnpWaFRtemNCTldNEW50WmltSx0fRhwHXTQhIRo+en5CHRIeQic7FB4kBR1aHk9fOHpWaFRtemNCTldNEW50WmltS05aFU9OElBWaFRtemNCTldNEW50WmltS05aFU9OEnpbZVQONiYDHFcLXS8zWjoiSwIVWh9OUTsYaAYoKTcDHANNWCM5Hy0kChofWRZkEnpWaFRtemNCTldNEW50WmltS05aFU9OWykkLQA4KC0LABA5XgU9GSIdCgpaCE8IUzYFLX5temNCTldNEW50WmltS05aFU9OEnpWaFQhOzAWJR4OWgs6HmlwSxoTVgRGG1BWaFRtemNCTldNEW50WmltS05aFU9OEnp8aFRtemNCTldNEW50WmltS05aFU9OEnpWZVltEiIMChsIESkxFCw/CgJaRgodQTMZJlQhMy4LGn1NEW50WmltS05aFU9OEnpWaFRtemNCTlcBXi01Fmk5ChwdUBs9RihWdVQCKjcLARkeHx0xCTokBAAuVB0JVy5YHhUhLyZCAQVNEwc6HCAjAhof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TldNXSE3GyVtHw8IUgoaEmdWBwQ5MywMHVk4QSkmGy0oPw8IUgoaHAwXJAEoeiwQTlUsXSJ2cGltS05aFU9OEnpWaFRtemNCTldNWCh0Dig/DAsOFVJTEng3JBhvejcKCxlnEW50WmltS05aFU9OEnpWaFRtemNCTldNVyEmWiBtVk5LGU9dAnoSJ35temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCBxFNXyEgWgorDEA7QBsBZyoROhUpPwEOARQGQm4gEiwjSwwIUA4FEj8YLH5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCAhgOUCJ0CWlwSx0WWhsdCBwfJhALMzERGjQFWCIwUmseBwEOF09AHHofYX5temNCTldNEW50WmltS05aFU9OEnpWaFRtemNCBxFNQm41FC1tGFQ8XAEKdDMEOwAOMioOCl9PYSI1GSwpOw8IQU1HEi4eLRpHemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW4kGSghB0YcQAENRjMZJlxkUGNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSyAfQRgBQDFYDh0/PxAHHAEIQ2Z2OBYYGwkIVAsLEHZWIV1HemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW4xFC1kYU5aFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWPBU+MW0VDx4ZGX56SGBHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFQoAVlBWaFRtemNCTldNEW50WmltS05aFU9OEnoTJhBHemNCTldNEW50WmltS05aFU9OEnoTJAcoUGNCTldNEW50WmltS05aFU9OEnpWaFRtei8NDRYBET04FT0DHgNaCE8aUygRLQB3NyIWDR9FEx04FT1tQ0seHkZMG1BWaFRtemNCTldNEW50WmltS05aFU9OEnofLlQ+NiwWIAIAETo8HydHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFQMBUTsaaBo4N2NfTgMCXzs5GCw/Qx0WWhsgRzdfQlRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMOARQMXW4nWnRtGAIVQRxUdDMYLDIkKDAWLR8EXSp8WBohBBpYFUFAEjQDJV1HemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTh4LET10GycpSx1AcwYAVhwfOgc5GSsLAhNFEx44GyooDz4bRxtMG3oCIBEjUGNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50FiYuCgJaVgcPQHpLaDgiOSIOPhsMSCsmVAolChwbVhsLQFBWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCThsCUi84WjsiBBpaCE8NWjsEaBUjPmMBBhYfCwg9FC0LAhwJQSwGWzYSYFYFLy4DABgEVRw7FT0dChwOF0ZkEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMLCFcfXiEgWj0lDgBwFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCHBgCRWAXPDssBgtaCE8dHBkwOhUgP2NJTiEIUjo7CHpjBQsNHV9CEmlaaERkUGNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltSxobRgRARTsfPFx9dHBLZFdNEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50WmltDgAeP09OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtKiADAhtFVzs6GT0kBABSHGVOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemNCTlcjVDojFTsmRSgTRwo9VygALQZleAE9OwcKQy8wH2thSwAPWEZkEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaFRtemMHABNEO250WmltS05aFU9OEnpWaFRtemNCTldNEW50WmkoBQpwFU9OEnpWaFRtemNCTldNEW50WmltS05aUAEKOHpWaFRtemNCTldNEW50WmltS05aUAEKOHpWaFRtemNCTldNEW50WmkoBQpwFU9OEnpWaFRtemNCCxkJO250WmltS05aUAEKOHpWaFRtemNCGhYeWmAjGyA5Q11TP09OEnoTJhBHPy0GR31nHGN0OCguAAkIWhoAVnoaJxs9ejcNThMUXy85EyosBwIDFRoeVjsCLVQJKCwSChgaXz10Uhw9DBwbUQpOQTYZPAdtOy0GTjgaXyswWj4oAgkSQRxHOC4XOx9jKTMDGRlFVzs6GT0kBABSHGVOEnpWPxwkNiZCGgUYVG4wFUNtS05aFU9OEndbaEVjehEH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GhhNUiYxGzkoGBpwFU9OEnpWaFRtemNCTldNESg7CGkkS1NaFhwBQC4TLCMoMyQKGgRBEX94WmR8SwoVP09OEnpWaFRtemNCTldNEW50WmltBwEZVANORXpLaAciKDcHCiAIWCk8DjoWAjNwFU9OEnpWaFRtemNCTldNEW50WmkkDU4UWhtORjsUJBFjPCoMCl86VCczEj0eDhwMXAwLcTYfLRo5dAwVABIJHW4jVCcsBgtTFRsGVzR8aFRtemNCTldNEW50WmltS05aFU9OEnpWJBsuOy9CDRgeRQE2EGlwSycUUwYAWy4TBRU5Mm0MCwBFRmA3FTo5QmRaFU9OEnpWaFRtemNCTldNEW50WmltS04TU08MUzYXJhcoen1fThQCQjobGCNtHwYfW2VOEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWOBcsNi9KCAIDUjo9FSdlQmRaFU9OEnpWaFRtemNCTldNEW50WmltS05aFU9OEnpWaDooLjQNHBxDdycmHxooGRgfR0dMYTIZOCsPLzpAQldPZis9HSE5OAYVRU1CEi1YJhUgP2poTldNEW50WmltS05aFU9OEnpWaFRtemNCTldNESs6HmBHS05aFU9OEnpWaFRtemNCTldNEW50WmltS05aFRsPQTFYPxUkLmtTR31NEW50WmltS05aFU9OEnpWaFRtemNCTldNEW50GDsoCgVaGEJOcC8PaBsjNjpCGh8IESwxCT1tCggcWh0KUzgaLVQ6PyoFBgNNWCB0DiEkGE4OXAwFOHpWaFRtemNCTldNEW50WmltS05aFU9OEj8YLH5temNCTldNEW50WmltS05aFU9OEj8YLH5temNCTldNEW50WmltS05aUAEKOHpWaFRtemNCTldNESs6HkNtS05aFU9OEj8YLH5temNCTldNETo1CSJjHA8TQUddG1BWaFRtPy0GZBIDVWdecGRgSy8PQQBOcC8PaCc9PyYGTiIdVjw1Hiw+YRobRgRAQSoXPxplPDYMDQMEXiB8U0NtS05aQgcHXj9WPAY4P2MGAX1NEW50WmltSwccFSwIVXQ3PQAiGDYbPQcIVCp0DiEoBWRaFU9OEnpWaFRtemMSDRYBXWYyDycuHwcVW0dHOHpWaFRtemNCTldNEW50WmkeGwsfUTwLQCwfKxEONioHAANXYyslDyw+HzsK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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2 })
