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

local __k = 'Ashmxm3gHxbR92d6KyMx9rTL'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
