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

local __k = 'QbOlFkvFRyGEmyqC83h62zOl'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2 })
