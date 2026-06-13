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

local __k = 'SE1g93ACm08XkSJdkNLWE32L'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2 })
