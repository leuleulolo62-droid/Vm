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

local __k = 'kAevt4fd4NlMvGf8qfqBA6Mc'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
