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

local __k = 'VaQYxe838XSQnuZVz97uK7xI'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2 })
