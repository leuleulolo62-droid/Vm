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

local __k = 'F5mtQXSTqYUIlVgPe32gZCDL'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
