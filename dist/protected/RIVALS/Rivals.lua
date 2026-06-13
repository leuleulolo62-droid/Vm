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

local __k = 'dL1yAOW41mhZMS04wIxCeQyk'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
