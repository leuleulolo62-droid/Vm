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

local __k = 'NFnssCgImSEgzrDc2oQOZdT1'
local __p = 'Y2tOkebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9sdD3mOfUgaf/s9rKhsGhrNP+kebThdz9WWhKWlIXBl4DcS56KDFcIShOOwYhRzVNJXRJSnhpThJPBAZ6XnR+LDUHFxoiCRwkc20+SBlkMFEdOD8uRBZQLS1cMRIgDGBnfmhHWjUlDldPa28JAThdbidOPxYuCCdNfGUxHxwgEVdPNSopRDdYOjQBHQBjG2k9PyQEHzsgQwVWY3liV20CfnFcR0d3bWRAc6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR89D6wa3P9Lak3qT745HW96v4w6fy6pDR8zhlOCl6CjtFbiEPHhZ5LjohPCQDHxZsShIbOSo0RDNQIyNAPxwiAywJaRIGEwZsShIKPytQbnkcbqT6/5HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5Lal3kxDXlOh88tNcwolKTsAKnMhcRoTRHQRbmZOU1NjR2lNc2VHWlJkQxJPcW96RHQRbmZOU1NjR2lNc2VHWlJkQxJPcW96RHTT2sRkXl5jhd35sdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefbbSUCMCQLWgAhE11PbG94DCBFPjVUXFwxBj5DNCwTEgcmFkEKIyw1CiBUIDJAEBwuSBBfOBYECBs0F3AOMiRoJjVSJWkhEQAqAyAMPRAOVR8lClxAc0VQCDtSLypOFQYtBD0EPCtHFh0lB2cmeTooCH07bmZOUx8sBCgBczcGDVJ5Q1UOPCpgLCBFPgELB1s2FSVEWWVHWlItBRIbKD8/TCZQOW9OTk5jRS8YPSYTEx0qQRIbOSo0bnQRbmZOU1NjCyYOMilHFRloQ0AKIjo2EHQMbjYNEh8vTy8YPSYTEx0qSxtPIyouESZfbjQPBFskBiQIf2USCB5tQ1cBNWZQRHQRbmZOU1MqAWkCOGUGFBZkF0sfNGcoASdEIjJHUw1+R2sLJisEDhsrDRBPJSc/CnRDKzIbAR1jFSweJikTWhcqBzhPcW96RHQRbi8IUxwoRygDN2UTAwIhS0AKIjo2EH0Rc3tOURU2CSoZOioJWFIwC1cBW296RHQRbmZOU1NjR2RAcxEPH1I2BkEaPTt6DSBCKyoIUx4qACEZcycCWhNkFEAOIT8/FngROygZARIzRyAZWWVHWlJkQxJPcW96RDheLScCUxA2FTsIPTFHR1I2BkEaPTtQRHQRbmZOU1NjR2lNNSoVWi1kXhJefW9vRDBeRGZOU1NjR2lNc2VHWlJkQxIGN28uHSRUZiUbAQEmCT1EcztaWlAiFlwMJSY1CnYROi4LHVMxAj0YIStHGQc2EVcBJW8/CjA7bmZOU1NjR2lNc2VHWlJkQ14AMi42RDtafGpOHRY7ExsIIDALDlJ5Q0IMMCM2TDJEICUaGhwtT2BNISATDwAqQ1EaIz0/CiAZKScDFl9jEjsBemUCFBZtaRJPcW96RHQRbmZOU1NjR2kENWUJFQZkDFldcTsyAToRLDQLEhhjAicJWWVHWlJkQxJPcW96RHQRbmYNBgExAicZc3hHFBc8F2AKIjo2EF4RbmZOU1NjR2lNc2UCFBZOQxJPcW96RHQRbmZOGhVjEzAdNm0EDwA2BlwbeG8kWXQTKDMAEAcqCCdPczEPHxxkEVcbJD00RDdEPDQLHQdjAicJWWVHWlJkQxJPNCE+bnQRbmZOU1NjSmRNFSQLFhAlAFlVcTsoHXRQPWYdBwEqCS5nc2VHWlJkQxIDPiw7CHRXIGpOLFN+RyUCMiEUDgAtDVVHJSApECZYICFGARI0TmBnc2VHWlJkQxIGN288CnRFJiMAUwEmEzwfPWUBFFojAl8KeG8/CjA7bmZOUxYvFCxnc2VHWlJkQxIdNDsvFjoRIikPFwA3FSADNG0VGwVtSxtlcW96RDFfKkxOU1NjFSwZJjcJWhwtDzgKPytQbjheLScCUz8qBTsMITxHWlJkQxJScSM1BTBkB24cFgMsR2dDc2crExA2AkAWfyMvBXYYRCoBEBIvRx0FNigCNxMqAlUKI29nRDheLyI7OlsxAjkCc2tJWlAlB1YAPzx1MDxUIyMjEh0iACwffSkSG1BtaV4AMi42RAdQOCMjEh0iACwfc2VaWh4rAlY6GGcoASRebmhAU1EiAy0CPTZIKRMyBn8OPy49ASYfIjMPUVpJbSUCMCQLWj00F1sAPzx6RHQRbmZTUz8qBTsMITxJNQIwCl0BIkU2CzdQImY6HBQkCywec2VHWlJkXhIjOC0oBSZIYBIBFBQvAjpnWWhKWpDQ79D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz6nhpThKNxc16RAd0HBAnMDYQR2lNc2VHWlJkQxJPcW96RHQRbmZOU1NjR2lNc2VHWlJkQxJPcW96RHQRbmZOU1NjR2lNc2WF7vBOTh9Ps9vOhsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgab3WyM1BzVdbhYCEgomFTpNc2VHWlJkQxJPcXJ6AzVcK3wpFgcQAjsbOiYCUlAUD1MWND0pRn07IikNEh9jNTwDACAVDBsnBhJPcW96RHQRc2YJEh4mXQ4IJxYCCAQtAFdHcx0vCgdUPDAHEBZhTkMBPCYGFlIWBkIDOCw7EDFVHTIBARIkAmlQcyIGFxd+JFcbAiooEj1SK25MIRYzCyAOMjECHiEwDEAONip4TV5dISUPH1MUCDsGIDUGGRdkQxJPcW96RHQMbiEPHhZ5ICwZACAVDBsnBhpNBiAoDydBLyULUVpJCyYOMilHLwEhEXsBITouNzFDOC8NFlNjWmkKMigCQDUhF2EKIzkzBzEZbBMdFgEKCTkYJxYCCAQtAFdNeEVQCDtSLypOPxwgBiU9PyQeHwBkXhI/PS4jASZCYAoBEBIvNyUMKiAVcB4rAFMDcQw7CTFDL2ZOU1NjR3RNBCoVEQE0AlEKfwwvFiZUIDItEh4mFShnWWhKWpDQ79D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz6nhpThKNxc16RBd+AAAnNFNjR2lNc2VHWlJkQxJPcW96RHQRbmZOU1NjR2lNc2VHWlJkQxJPcW96RHQRbmZOU1NjR2lNc2WF7vBOTh9Ps9vOhsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgab3WyM1BzVdbgUIFFN+RzJnc2VHWjMxF10sPSY5DxhUIykAU05jASgBICBLcFJkQxIuJDs1MSRWPCcKFlNjR2lQcyMGFgEhTzhPcW96JSFFIRMeFAEiAyw5MjcAHwZkXhJNECM2Rng7bmZOUzI2EyY9OyoJHz0iBVcdcXJ6AjVdPSNCeVNjR2ksJjEIORM3C3YdPj96RHQMbiAPHwAmS0NNc2VHOwcwDGAKMyYoEDwRbmZOTlMlBiUeNmltWlJkQ3MaJSAfEjtdOCNOU1NjR3RNNSQLCRdoaRJPcW8bESBeDzUNFh0nR2lNc2VaWhQlD0EKfUV6RHQRDzMaHCMsECwfHyARHx5kXhIJMCMpAXg7bmZOUzI2EyY4IyIVGxYhM10YND16WXRXLyodFl9JR2lNcwQSDh0QCl8KEi4pDHQRbntOFRIvFCxBWWVHWlIFFkYAFC4oCjFDDCkBAAdjWmkLMikUH15OQxJPcQ4vEDt1ITMMHxYMAS8BOisCWk9kBVMDIip2bnQRbmYvBgcsKiADOiIGFxcWAlEKcXJ6AjVdPSNCeVNjR2ksJjEINxsqClUOPCoOFjVVK2ZTUxUiCzoIf09HWlJkIkcbPgwyBTpWKwoPERYvR3RNNSQLCRdoaRJPcW8bESBeDS4PHRQmJCYBPDcUWk9kBVMDIip2bnQRbmYrICMTCygUNjcUWlJkQxJScSk7CCdUYkxOU1NjIho9ECQUEjY2DEJPcW96WXRXLyodFl9JR2lNcwA0KiY9AF0AP296RHQRbntOFRIvFCxBWWVHWlITAl4EAj8/ATARbmZOU1N+R3hbf09HWlJkKUcCIR81EzFDbmZOU1NjWmlYY2ltWlJkQ3UdMDkzEC0RbmZOU1NjR3RNYnxRVEBoaRJPcW8cCC10ICcMHxYnR2lNc2VaWhQlD0EKfUV6RHQRCCoXIAMmAi1Nc2VHWlJkXhJaYWNQRHQRbggBEB8qF2lNc2VHWlJkQw9PNy42FzEdRGZOU1MKCS8nJigXWlJkQxJPcW9nRDJQIjULX3ljR2lNBjUACBMgBnYKPS4jRHQRc2ZeXUZvbWlNc2U3CBc3F1sINAs/CDVIbmZTU0JzS0NNc2VHOB0rEEYrNCM7HXQRbmZOTlNwV2Vnc2VHWjMqF1suFwR6RHQRbmZOU05jASgBICBLcA9OaR9Cca3O6LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D70a3O5LalzqT685HX56v506fz+pDQ49D7wUV3SXTT2sROUyc6BCYCPWUvHx40BkAccW96RHQRbmZOU1NjR2lNc2VHWlJkQxJPcW96RHQRbmZOU1NjR2lNc2VHWlJkQxKNxc1QSXkRrNL6kefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCxrNLukefDhd3tsdHnmObEgabvs9vahsCpRCoBEBIvRy8YPSYTEx0qQ1UKJRsjBzteIG5HeVNjR2kLPDdHJV5kDFAFcSY0RD1BLy8cAFsUCDsGIDUGGRd+JFcbEiczCDBDKyhGWlpjAyZnc2VHWlJkQxIGN29yCzZbdA8dMlthISYBNyAVWFtkDEBPPi0wXh1CD25MPhwnAiVPemUICFIrAVhVGDwbTHZyISgIGhQ2FSgZOioJWFttQ1MBNW81Bj4fACcDFkklDicJe2czAxErDFxNeG8uDDFfRGZOU1NjR2lNc2VHWh4rAFMDcSAtCjFDbntOHBEpXQ8EPSEhEwA3F3EHOCM+THZ+OSgLAVFqbWlNc2VHWlJkQxJPcSY8RDtGICMcUxItA2kCJCsCCEgNEHNHcwA4DjFSOhAPHwYmRWBNMisDWh0zDVcdfxk7CCFUbntTUz8sBCgBAykGAxc2Q0YHNCFQRHQRbmZOU1NjR2lNc2VHWgAhF0cdP281Bj47bmZOU1NjR2lNc2VHHxwgaRJPcW96RHQRKygKeVNjR2kIPSFtWlJkQ0AKJTooCnRf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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
