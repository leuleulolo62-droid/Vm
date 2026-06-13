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

local __k = '8HRdgcabdIw79hpukJ2JXYSN'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true } })
