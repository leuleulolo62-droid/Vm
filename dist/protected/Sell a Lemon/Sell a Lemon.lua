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

local __k = 's3rB328w7cfYQ34RxM5JudUU'
local __p = 'Xh5SoKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKnaUt0cRNnNxQhFStVKDA4HF1SCkZQGAsXFVd3YTkZf1htYANVXnUaEUAbJlpTViJ+Q04AY1gUARs/XDoBRBc0EFhAAFJRU149Tkt5cXRVPx1tD2omATk5U1JSDlZfVxkXTEYPNF1QIB1tUS8GRDY8B0EdLEASRFdnDwc6NHpQck90B3xNV2xmQwRAdgcGMloaQ4TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwprYpajg9LfA49Hn0tGnqJWi84TMwdGhwnJHXCxVCjohU1QTL1YIcQR7DAc9NFcce1g5XS8bRDI0HlZcDlxTXBJTWTE4OEcce1goWy5/bnh4U9HmztGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB89HmwtGmuJWj44TN0dGg0prZtajh5LfB4zlfbxPQrPUXQykbAnpwGzkDFR88RHV1UxNSYhMSGFcXQ0Z5cRMUclhtFWpVRHV1UxNSYhMSGFcXQ0Z5cRMUclhtFWpVRHW357F4bx4S2uOjgfLZs6e0sOzN1971hsHVkafyoKey2uO3gfLZ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xKPWx+ivoNqX8cW35qOQ16PQrefV9va7xKPWx+ivoNqX8cW35qOQ16PQrefV9va7xKPWx+ivoNqX8cW35qOQ16PQrefV9va7xKPWx+ivoNqX8cW35qOQ16PQrefV9va7xKPWx+ivoNqX8cW35qOQ16PQrefV9va7xKPWx+ivoNqX8cW35qOQ16PQrefV9va7xKM+f1VtFRw8NwAUPxMmA3E4FVoXgfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6akWBQiVisZRAM8AH9SfxNmWRVETTAwIkZVPkIMUS45ATMhNEEdN0NQVw8fQSMKAREYcB00UGhcbl8DGkA+eHJWXCNYBAE1NBsWFysdZSYUHTAnABFeOTkSGFcXNwMhJQ4WFysdFRoZBSwwAUBQbjkSGFcXJwM/MEZYJkUrVCYGAXlfUxNSYnBTVBtVAgUybFVBPBs5XCUbTCN8U3AUJR13aydnDwcgNEFHbw5tUCQRSF8oWjl4FFpBdE12BwINPlRTPh1lFw8mNBY0AFs2MFxCGltMaUZ5cRNgNwA5CGgwNwV1MFIBKhN2ShhHQUpTcRMUcjwoUysACCFoFVIeMVYeMlcXQ0YaMF9YMBkuXncTETs2B1odLBtEEVd0BQF3FGBkERk+XQ4HCyVoBRMXLFceMgoeaWwPOEB4aDkpUR4aAzI5FhtQB2BibA5UDAk3cx9PWFhtFWohAS0hThE3EWMSdQ4XNx86PlxacFRHFWpVRBEwFVIHLkcPXhZbEAN1WxMUclgOVCYZBjQ2GA4UN11RTB5YDU4veBN3NB9jcBklMCw2HFwcf0USXRlTT2wkeDk+f1Vt19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDFkabioKai2uKngfPJs6aksO3d19/lhsDF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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2 })
