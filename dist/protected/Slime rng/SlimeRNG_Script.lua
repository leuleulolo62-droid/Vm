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

local __k = 'NuCxh8zHPsJrs7itH1rMUqGQ'
local __p = 'Y1gYI2IYWmhwICYbHlJJJgZ2UgUgE2d8bixxE0hrGTo5Az54UxdJVBhdEy4wOCNrbkxxTFkOTnphRnhASgFZfmgRUm0AOH1xARcwEQxRGyZwWxNAGBc8PWE7LxBfey43bhImDA9dFD54WmQhH14EERp/NQE6ECM0KlU3EA1WWjo1Bz8AHRcMGiw7FSghFiI/OF1qVjtUEyU1IQQ1P1gIEC1VUnB1BTUkK39JVUUXVWgDNhgkOnQsJ0JdHS40HWcBIhQ6HRpLWnVwFCsfFg0uETxiFz8jGCQ0ZlcTFAlBHzojUWN4H1gKFSQRICglHS4yLwEmHDtMFToxFC9SThcOFSVUSAowBRQ0PAMqGw0QWBo1AyYbEFYdESxiBiInECA0bFxJFAdbGyRwIT8cIFIbAiFSF21oUSAwIxB5Pw1MKS0iBSMRFh9LJj1fISgnBy4yK1dqcgRXGSk8Ux0dAVwaBClSF21oUSAwIxB5Pw1MKS0iBSMRFh9LIydDGT4lECQ0bFxJFAdbGyRwPyUREls5GClIFz91TGcBIhQ6HRpLVAQ/ECseI1sIDS1DeEd4XGh+biAKWCRxOBoRIRN4H1gKFSQRACglHmdsblcrDBxICXJ/XDgTBBkOHTxZBy8gAiIjLRotDA1WDmYzHCddKgUCJytDGz0hMyYyJUcBGQtTVQcyACMWGlYHISEeHyw8H2hzRBksGwlUWgQ5ETgTAU5JSWhdHSwxAjMjJxskUA9ZFy1qOz4GA3AMAGBDFz06UWl/blcPEQpKGzopXSYHEhVAXWAYeCE6EiY9biErHQVdNyk+Ei0XARdUVCReEykmBTU4IBJrHwlVH3IYBz4CNFIdXDpUAiJ1X2lxbBQnHAdWCWcEGy8fFnoIGilWFz97HTIwbFxqUEEyFiczEiZSIFYfEQVQHCwyFDVxc1UvFwlcCTwiGiQVW1AIGS0LOjkhAQA0Ol0xHRhXWmZ+U2gTF1MGGjseISwjFAowIBQkHRoWFj0xUWNbWx5jfiReESw5URA4IBEsD0gFWgQ5ETgTAU5TNzpUEzkwJi4/Kho0UBMyWmhwUx4bB1sMVHURUBRnGmcZOxdjBEhrFiE9FmogPXBLWEIRUm11MiI/OhAxWFUYDjolFmZ4UxdJVAlEBiIGGSgmbkhjDBpNH2RaU2pSU2MIFhhQFik8HyBxc1V7VGIYWmhwPi8cBnEIEC1lGyAwUXpxfltxchURcEJ9XmVdU2MoNhs7HiI2ECtxGhQhC0gFWjNaU2pSU3oIHSYRT20CGCk1IQJ5OQxcLikyW2g/El4HVmQRUD00EiwwKRBhUUQyWmhwUx8CFEUIEC1CUnB1Ji4/Kho0QilcHhwxEWJQJkcOBilVFz53XWdzPR0qHQRcWGF8eWpSUxc6AClFAW1oURA4IBEsD1J5HiwEEihaUWQdFTxCUGF1UyMwOhQhGRtdWGF8eWpSUxc9ESRUAiInBWdsbiIqFgxXDXIRFy4mElVBVhxUHiglHjUlbFljWgVXDC19FyMTFFgHFSQcQG98XU1xblVjNQdOHyU1HT5SThc+HSZVHTpvMCM1GhQhUEp1FT41Hi8cBxVFVGpQETk8By4lN1dqVGIYWmhwIC8GB14HEzsRT20CGCk1IQJ5OQxcLikyW2ghFkMdHSZWAW95UWUiKwE3EQZfCWp5X0APeT1EWWceUgoUPAJxAzoHLSR9KUI8HCkTHxcPASZSBiQ6H2ciLxMmKg1JDyEiFmJcXRlAfmgRUm05HiQwIlUiCg9LWnVwCGRcXUpjVGgRUiE6EiY9bhooVEhKHzslHz5SThcZFyldHmUzBCkyOhwsFkARcGhwU2pSUxdJGCdSEyF1HiU7bkhjKg1IFiEzEj4XF2QdGzpQFShfUWdxblVjWEheFTpwLGZSAxcAGmhYAiw8AzR5LwckC0EYHidaU2pSUxdJVGgRUm11HiU7bkhjFwpSQB8xGj40HEUqHCFdFmUlXWdiZ39jWEgYWmhwU2pSUxcAEmhfHTl1HiU7bgErHQYYHzoiHDhaUXkGAGhXHTg7FX1xbFttCEEYHyY0eWpSUxdJVGgRFyMxe2dxblVjWEgYCC0kBjgcU0UMBT1YACh9HiU7Z39jWEgYHyY0WkBSUxdJBi1FBz87USg6bhQtHEhKHzslHz5SHEVJGiFdeCg7FU1bIhogGQQYPikkEhkXAUEAFy0RUm11UWdxblVjWEgFWjsxFS8gFkYcHTpUWm8FECQ6LxImC0oUWmoUEj4TIFIbAiFSF298eys+LRQvWDpXFiQDFjgEGlQMNyRYFyMhUWdxblVjRUhLGy41IS8DBl4bEWATISIgAyQ0bFljWi5dGzwlAS8BURtJVhpeHiF3XWdzHBovFDtdCD45EC8xH14MGjwTW0c5HiQwIlUKFh5dFDw/ATMhFkUfHStUMSE8FCklbkhjCwleHxo1Aj8bAVJBVhteBz82FGV9blcFHQlMDzo1AGheUxUgGj5UHDk6Az5zYlVhMQZOHyYkHDgLIFIbAiFSFw45GCI/OldqcgRXGSk8Ux8CFEUIEC1iFz8jGCQ0DRkqHQZMWmhwTmoBElEMJi1AByQnFG9zHRo2CgtdWGRwUQwXEkMcBi1CUGF1UxIhKQciHA1LWGRwUR8CFEUIEC1iFz8jGCQ0DRkqHQZMWGFaHyUREltJJi1TGz8hGRQ0PAMqGw17FiE1HT5SUxdUVDtQFCgHFDYkJwcmUEprFT0iEC9QXxdLMi1QBjgnFDRzYlVhKg1aEzokG2heUxU7ESpYADk9IiIjOBwgHStUEy0+B2hbeVsGFyldUh8wEy4jOh0QHRpOEys1Jj4bH0RJVGgRT20mECE0HBAyDQFKH2ByICUHAVQMVmQRUAswEDMkPBAwWkQYWBo1ESMAB19LWGgTICg3GDUlJiYmCh5RGS0FByMeABVAfiReESw5UQs+IQEQHRpOEys1MCYbFlkdVGgRUm11TGciLxMmKg1JDyEiFmJQIFgcBitUUGF1UwE0LwE2Cg1LWGRwUQYdHENLWGgTPiI6BRQ0PAMqGw17FiE1HT5QWj0FGytQHm0xAgQ9JxAtDEgFWgwxByshFkUfHStUUiw7FWcVLwEiKw1KDCEzFmQRH14MGjwRHT91Hy49RH9uVUcXWgAVPxo3IWRjGCdSEyF1FzI/LQEqFwYYHS0kNysGEh9AfmgRUm08F2c/IQFjHBt7FiE1HT5SB18MGmhDFzkgAylxNQhjHQZccGhwU2oeHFQIGGheGWF1ByY9bkhjCAtZFiR4FT8cEEMAGyYZW20nFDMkPBtjHBt7FiE1HT5IFFIdXGERFyMxWE1xblVjCg1MDzo+U2IdGBcIGiwRBjQlFG8nLxlqWFUFWmokEigeFhVAVClfFm0jECtxIQdjAxUyHyY0eUAeHFQIGGhXByM2BS4+IFUlFxpVGzweBidaHR5jVGgRUiN1TGclIRs2FQpdCGA+WmodARdZfmgRUm08F2c/bkt+WFldS3pwByIXHRcbETxEACN1AjMjJxskVg5XCCUxB2JQVhlbEhwTXm07XnY0f0dqckgYWmg1HzkXGlFJGmgPT21kFH5xbgErHQYYCC0kBjgcU0QdBiFfFWMzHjU8LwFrWk0WSC4SUWZSHRhYEXEYeG11UWc0IgYmEQ4YFGhuTmpDFgFJVDxZFyN1AyIlOwctWBtMCCE+FGQUHEUEFTwZUGh7QyEcbFljFkcJH355eWpSUxcMGDtUGyt1H2dvc1VyHVsYWjw4FiRSAVIdATpfUj4hAy4/KVslFxpVGzx4UW9cQlEiVmQRHGJkFHR4RFVjWEhdFjs1UzgXB0IbGmhFHT4hAy4/KV0uGRxQVC48HCUAW1lAXWhUHClfFCk1RH8vFwtZFmg2BiQRB14GGmhFEy85FAs0IF03UWIYWmhwGixSB04ZEWBFW20rTGdzOhQhFA0aWjw4FiRSAVIdATpfUn11FCk1RFVjWEhUFSsxH2ocUwpJREIRUm11FygjbipjEQYYCik5ATlaBx5JECcRHG1oUSlxZVVyWA1WHkJwU2pSAVIdATpfUiNfFCk1RH8vFwtZFmg2BiQRB14GGmhQAj05CBQhKxAnUB4RcGhwU2oCEFYFGGBXByM2BS4+IF1qckgYWmhwU2pSGlFJOCdSEyEFHSYoKwdtOwBZCCkzBy8AU0MBESY7Um11UWdxblVjWEgYFiczEiZSGxdUVAReESw5ISswNxAxVitQGzoxED4XAQ0vHSZVNCQnAjMSJhwvHCdeOSQxADlaUX8cGSlfHSQxU25bblVjWEgYWmhwU2pSGlFJHGhFGig7US9/GRQvEztIHy00U3dSBRcMGiw7Um11UWdxblUmFgwyWmhwUy8cFx5jESZVeEc5HiQwIlUlDQZbDiE/HWoTA0cFDQJEHz19B25bblVjWBhbGyQ8WywHHVQdHSdfWmRfUWdxblVjWEhRHGgcHCkTH2cFFTFUAGMWGSYjLxY3HRoYDiA1HUBSUxdJVGgRUm11UWc9IRYiFEhQWnVwPyUREls5GClIFz97Mi8wPBQgDA1KQA45HS40GkUaAAtZGyExPiESIhQwC0AaMj09EiQdGlNLXUIRUm11UWdxblVjWEhRHGg4Uz4aFllJHGZ7ByAlISgmKwdjRUhOWi0+F0BSUxdJVGgRUig7FU1xblVjHQZcU0I1HS54eVsGFyldUisgHyQlJxotWBxdFi0gHDgGJ1hBBCdCW0d1UWdxPhYiFAQQHD0+ED4bHFlBXUIRUm11UWdxbhksGwlUWis4EjhSThclGytQHh05ED40PFsAEAlKGyskFjh4UxdJVGgRUm08F2cyJhQxWAlWHmgzGysASXEAGix3Gz8mBQQ5JxknUEpwDyUxHSUbF2UGGzxhEz8hU25xOh0mFmIYWmhwU2pSUxdJVGhSGiwnXw8kIxQtFwFcKCc/BxoTAUNHNw5DEyAwUXpxDTMxGQVdVCY1BGICHERAfmgRUm11UWdxKxsnckgYWmg1HS5beVIHEEI7X2B6XmcLATsGWDh3KQEEOgU8ID0FGytQHm0PPgkUESUMK0gFWjNaU2pSU2xYKWgRT20DFCQlIQdwVgZdDWBiSnteUxdbRGQRX3xnWGtxbi5xJUgYR2gGFikGHEVaWiZUBWVgRXF9blVxSEQYV3liWmZ4UxdJVBMCL211TGcHKxY3FxoLVCY1BGJKQwVFVGgDQmF1XHZjZ1ljWDMMJ2hwTmokFlQdGzoCXCMwBm9gfkd2VEgKSmRwXntAWhtjVGgRUhZgLGdxc1UVHQtMFTpjXSQXBB9YR3gCXm1nQWtxY0RxUUQYWhNmLmpSThc/EStFHT9mXyk0OV1yTVsPVmhiQ2ZSXgZbXWQ7Um11URxmE1VjRUhuHyskHDhBXVkMA2AARX5jXWdjflljVVkKU2RwUxFKLhdJSWhnFy4hHjViYBsmD0AJQ35mX2pAQxtJWXkDW2FfUWdxbi56JUgYR2gGFikGHEVaWiZUBWVnQHFhYlVxSEQYV3liWmZSU2xYRBURT20DFCQlIQdwVgZdDWBiQH1AXxdbRGQRX3xnWGtbblVjWDMJSxVwTmokFlQdGzoCXCMwBm9jeEVyVEgKSmRwXntAWhtJVBMAQBB1TGcHKxY3FxoLVCY1BGJASwZaWGgDQmF1XHZjZ1lJWEgYWhNhQBdSThc/EStFHT9mXyk0OV1wSFsJVmhiQ2ZSXgZbXWQRUhZkRRpxc1UVHQtMFTpjXSQXBB9aRX0FXm1kRGtxY0RwUUQyWmhwUxFDRmpJSWhnFy4hHjViYBsmD0ALTnhkX2pDRhtJWXoHW2F1URxgeChjRUhuHyskHDhBXVkMA2ACRHhlXWdge1ljVVkIU2RaU2pSU2xYQxURT20DFCQlIQdwVgZdDWBjS3NDXxdYQWQRX3xlWGtxbi5yQDUYR2gGFikGHEVaWiZUBWVhQ3NiYlVxSEQYV3liWmZ4UxdJVBMASxB1TGcHKxY3FxoLVCY1BGJGQA9RWGgAR2F1XHJ4YlVjWDMKShVwTmokFlQdGzoCXCMwBm9leEZ3VEgJT2RwXntKWhtjVGgRUhZnQBpxc1UVHQtMFTpjXSQXBB9dTX8BXm1nQWtxY0RxUUQYWhNiQRdSThc/EStFHT9mXyk0OV12SVkMVmhhRmZSXgZZXWQ7Um11URxjfShjRUhuHyskHDhBXVkMA2AEQXttXWdge1ljVVkIU2RwUxFAR2pJSWhnFy4hHjViYBsmD0ANTHlnX2pDRhtJWXkBW2FfUWdxbi5xTTUYR2gGFikGHEVaWiZUBWVgSXFmYlVyTUQYV3lgWmZSU2xbQhURT20DFCQlIQdwVgZdDWBmQntAXxdYQWQRX3p8XU1xblVjI1oPJ2htUxwXEEMGBnsfHCgiWXFie0NvWFkNVmh9RGNeUxdJL3oJL21oURE0LQEsClsWFC0nW3xEQwFFVHkEXm14QHV4Yn9jWEgYIXppLmpPU2EMFzxeAH57HyImZkN7TVEUWnllX2pfRB5FVGgRKX5lLGdsbiMmGxxXCHt+HS8FWwBYRX0dUnxgXWd8eVxvckgYWmgLQHsvUwpJIi1SBiInQmk/KwJrT1sNQ2RwQn9eUxpYRGEdUm0OQnUMbkhjLg1bDiciQGQcFkBBQ30ISmF1QHJ9blh7UUQyWmhwUxFBQGpJSWhnFy4hHjViYBsmD0APQnxjX2pDRhtJWXkDW2F1URxieihjRUhuHyskHDhBXVkMA2AJQnVjXWdge1ljVVkIU2RaU2pSU2xaQRURT20DFCQlIQdwVgZdDWBoQHlBXxdYQWQRX3xlWGtxbi5wTjUYR2gGFikGHEVaWiZUBWVtRH9nYlVyTUQYV3lgWmZ4UxdJVBMCRRB1TGcHKxY3FxoLVCY1BGJKSwNbWGgAR2F1XHZhZ1ljWDMLQhVwTmokFlQdGzoCXCMwBm9ofkx7VEgJT2RwXntCWhtjVGgRUhZmSBpxc1UVHQtMFTpjXSQXBB9QR30FXm1kRGtxY0RzUUQYWhNkQxdSThc/EStFHT9mXyk0OV16TlkIVmhhRmZSXgZZXWQ7D0dfXGp+YVUQLClsP0I8HCkTHxcvGClWAW1oUTxbblVjWAlNDicCHCYeUxdJVGgRUm11TGc3LxkwHUQyWmhwUysHB1g7ESpYADk9UWdxblVjRUheGyQjFmZ4UxdJVClEBiIWHis9KxY3WEgYWmhwTmoUElsaEWQ7Um11USYkOhoGCR1RCgo1AD5SUxdJSWhXEyEmFGtbblVjWABRHiw1HRgdH1tJVGgRUm11TGc3LxkwHUQyWmhwUzgdH1stESRQC211UWdxblVjRUgIVHhlX0BSUxdJAyldGR4lFCI1blVjWEgYWmhtU3hAXz1JVGgRGDg4ARc+ORAxWEgYWmhwU2pPUwJZWEIRUm11EDIlITc2ASRNGSNwU2pSUxdUVC5QHj4wXU1xblVjGR1MFQolChkeHEMaVGgRUm1oUSEwIgYmVGIYWmhwEj8GHHUcDRpeHiEGASI0KlV+WA5ZFjs1X0BSUxdJFT1FHQ8gCAowKRsmDEgYWmhtUywTH0QMWEIRUm11EDIlITc2AStXEyZwU2pSUxdUVC5QHj4wXU1xblVjGR1MFQolCg0dHEdJVGgRUm1oUSEwIgYmVGIYWmhwEj8GHHUcDQZUCjkPHik0blV+WA5ZFjs1X0BSUxdJBy1dFy4hFCMEPhIxGQxdWmhtU2geBlQCVmQ7Um11UTQ0IhAgDA1cICc+FmpSUxdJSWgAXkd1UWdxIBoAFAFIWmhwU2pSUxdJVGgMUis0HTQ0Yn9jWEgYCSQ5Hi83IGdJVGgRUm11UWdsbhMiFBtdVkJwU2pSA1sIDS1DNx4FUWdxblVjWEgFWi4xHzkXXz0UfkJdHS40HWciKwYwEQdWKCc8HzlSThdZfiReESw5URI/IhoiHA1cWnVwFSseAFJjGCdSEyF1Mig/IBAgDAFXFDtwTmoJDj1jGCdSEyF1MAsdESATPzp5Pg0DU3dSCD1JVGgRUCEgEixzYlcwFAdMCWp8UTgdH1s6BC1UFm95UyQ+JxsKFgtXFy1yX2gFElsCJzhUFyl3XWU8LxItHRxqGyw5BjlQXz1JVGgRUCg7FCooDRo2FhwaVmozHyUEFkU7GyRdAW95UyU+IAAwKgdUFjtyX2gXC0MbFRpeHiEWGSY/LRBhVEpfFScgNzgdA2UIAC0TXkd1UWdxbBEsDQpUHw8/HDpQXxUGAi1DGSQ5HWV9bBMxEQ1WHgQlECFQXxUPBiFUHCkZBCQ6DBosCxwaVmojHyMfFnAcGgxQHywyFGV9RFVjWEgaCSQ5Hi81BlkvHTpUICwhFGV9bAYvEQVdPT0+ISscFFJLWGpUHCg4CBQhLwItKxhdHyxyX2gBH14EERxQACowBRUwIBImWkQyWmhwU2gdFVEFHSZUPiI6BQY8IQAtDEoUWCo5FA8cFloQNyBQHC4wU2tzPR0qFhF9FC09CgkaElkKEWodUCUgFiIUIBAuAStQGyYzFmheeRdJVGgTGyMjFDUlKxEGFg1VAws4EiQRFhVFVipYFR45GCo0PVdvWgBNHS0DHyMfFkRLWGpCGiQ7CBQ9JxgmC0oUWCE+BS8AB1INJyRYHygmU2tbblVjWEpfFScgUWZQEkIdGxpeHiF3XU0sRH9uVUcXWhscOgc3U3I6JEJdHS40HWciIhwuHSBRHSA8Gi0aB0RJSWhKD0dfHSgyLxljHh1WGTw5HCRSGkQ6GCFcF2U6Ey14RFVjWEhUFSsxH2ocEloMVHURHS8/XwkwIxB5FAdPHzp4WkBSUxdJGCdSEyF1GDQBLwc3WFUYFSo6SQMBMh9LNilCFx00AzNzZ1UsCkhXGCJqOjkzWxUkETtZIiwnBWV4RFVjWEhUFSsxH2obAHoGEC1dUnB1HiU7dDwwOUAaNyc0FiZQWj1jVGgRUiQzUS4iHhQxDEhMEi0+eWpSUxdJVGgRGyt1HyY8K08lEQZcUmojHyMfFhVAVDxZFyN1AyIlOwctWBxKDy18UyUQGRcMGiw7Um11UWdxblUqHkhWGyU1SSwbHVNBVi1fFyAsU25xOh0mFkhKHzwlASRSB0UcEWQRHS8/USI/Kn9jWEgYWmhwUyMUU1kIGS0LFCQ7FW9zKRosCEoRWjw4FiRSAVIdATpfUjknBCJ9bhohEkhdFCxaU2pSUxdJVGhYFG07ECo0dBMqFgwQWCo8HChQWhcdHC1fUj8wBTIjIFU3Ch1dVmg/ESBSFlkNfmgRUm11UWdxJxNjFwpSVBgxAS8cBxcIGiwRHS8/XxcwPBAtDEZ2GyU1SSYdBFIbXGELFCQ7FW9zPRkqFQ0aU2gkGy8cU0UMAD1DHG0hAzI0YlUsGgIYHyY0eWpSUxcMGiw7eG11UWc4KFUqCyVXHi08Uz4aFlljVGgRUm11UWc4KFUtGQVdQC45HS5aUUQFHSVUUGR1BS80IFUxHRxNCCZwBzgHFhtJGypbUig7FU1xblVjWEgYWiE2UyQTHlJTEiFfFmV3FCk0IwxhUUhMEi0+UzgXB0IbGmhFADgwXWc+LB9jHQZccGhwU2pSUxdJHS4RHCw4FH03JxsnUEpfFScgUWNSB18MGmhDFzkgAylxOgc2HUQYFSo6Uy8cFz1JVGgRUm11US43bhsiFQ0CHCE+F2JQEVsGFmoYUjk9FClxPBA3DRpWWjwiBi9eU1gLHmhUHClfUWdxblVjWEhRHGg/ESBINV4HEA5YAD4hMi84IhFrWjtUEyU1IysABxVAVDxZFyN1AyIlOwctWBxKDy18UyUQGRcMGiw7Um11UWdxblUqHkhXGCJqNSMcF3EABjtFMSU8HSN5bCYvEQVdWGFwByIXHRcbETxEACN1BTUkK1ljFwpSWi0+F0BSUxdJVGgRUiQzUSgzJE8FEQZcPCEiAD4xG14FEB9ZGy49ODQQZlcBGRtdKikiB2hbU1YHEGhfEyAwSyE4IBFrWhtIGz8+UWNSB18MGmhDFzkgAylxOgc2HUQYFSo6Uy8cFz1JVGgRFyMxe01xblVjCg1MDzo+UywTH0QMWGhfGyFfFCk1RH8vFwtZFmg2BiQRB14GGmhWFzkGHS48KzQnFxpWHy14HCgYWj1JVGgRGyt1HiU7dDwwOUAaOCkjFhoTAUNLXWheAG06Ey1rBwYCUEp1Hzs4IysABxVAVDxZFyNfUWdxblVjWEhKHzwlASRSHFUDfmgRUm0wHyNbblVjWAFeWicyGXA7AHZBVgVeFig5U25xOh0mFmIYWmhwU2pSU0UMAD1DHG06Ey1rCBwtHC5RCDskMCIbH1M+HCFSGgQmMG9zDBQwHThZCDxyX2oGAUIMXWheAG06Ey1bblVjWA1WHkJwU2pSAVIdATpfUiI3G000IBFJcgRXGSk8UywHHVQdHSdfUi4nFCYlKyYvEQVdPxsAWzkeGloMXUIRUm11HSgyLxljFwMUWjwxAS0XBxdUVCFCISE8HCJ5PRkqFQ0RcGhwU2obFRcHGzwRHSZ1BS80IFUxHRxNCCZwFiQWeRdJVGhYFG0mHS48Kz0qHwBUEy84BzkpAFsAGS1sUjk9FClxPBA3DRpWWi0+F0B4UxdJVCReESw5USY1IQctHQ0YR2g3Fj4hH14EEQlVHT87FCJ5OhQxHw1MU0JwU2pSH1gKFSQRAiwnBWdsbhQnFxpWHy1qOjkzWxUrFTtUIiwnBWV4bhQtHEhZHiciHS8XU1gbVDtdGyAwSwE4IBEFERpLDgs4GiYWJF8AFyB4AQx9UwUwPRATGRpMWGRwBzgHFh5jVGgRUiQzUSk+OlUzGRpMWjw4FiRSAVIdATpfUig7FU1bblVjWARXGSk8UyIeUwpJPSZCBiw7EiJ/IBA0UEpwEy84HyMVG0NLXUIRUm11GSt/ABQuHUgFWmoDHyMfFnI6JBd5Pm9fUWdxbh0vVi5RFiQTHCYdARdUVAteHiInQmk3PBouKi96Unh8U3hHRhtJRXgBW0d1UWdxJhltNx1MFiE+FgkdH1gbVHURMSI5HjViYBMxFwVqPQp4Q2ZSQgdZWGgEQmRfUWdxbh0vVi5RFiQEASscAEcIBi1fETR1TGdhYEFJWEgYWiA8XQUHB1sAGi1lACw7AjcwPBAtGxEYR2hgeWpSUxcBGGZ1Fz0hGQo+KhBjRUh9FD09XQIbFF8FHS9ZBgkwATM5AxonHUZ5Fj8xCjk9HWMGBEIRUm11GSt/DxEsCgZdH2htUysWHEUHES07Um11US89YCUiCg1WDmhtUzkeGloMfkIRUm11HSgyLxljGgFUFmhtUwMcAEMIGitUXCMwBm9zDBwvFApXGzo0ND8bUR5jVGgRUi88HSt/ABQuHUgFWmoDHyMfFnI6JBdzGyE5U01xblVjGgFUFmYRFyUAHVIMVHURAiwnBU1xblVjGgFUFmYDGjAXUwpJIQxYH397HyImZkVvWF4IVmhgX2pARx5jVGgRUi88HSt/Dxk0GRFLNSYEHDpSThcdBj1UeG11UWczJxkvVjtMDywjPCwUAFIdVHURJCg2BSgjfVstHR8QSmRwQGZSQx5jfmgRUm05HiQwIlUvGgQYR2gZHTkGElkKEWZfFzp9UxM0NgEPGQpdFmp8UygbH1tAfmgRUm05Eyt/HRw5HUgFWh0UGidAXVkMA2AAXm1lXWdgYlVzUWIYWmhwHygeXWMMDDwRT20mHS48K1sNGQVdcGhwU2oeEVtHNilSGSonHjI/KiExGQZLCikiFiQRChdUVHk7Um11USszIlsXHRBMOSc8HDhBUwpJNyddHT9mXyEjIRgRPyoQSmRwQX9HXxdYRHgYeG11UWc9LBltLA1ADhskASUZFmMbFSZCAiwnFCkyN1V+WFgyWmhwUyYQHxk9ETBFIS40HSI1bkhjDBpNH0JwU2pSH1UFWg5eHDl1TGcUIAAuVi5XFDx+NCUGG1YENiddFkdfUWdxbhcqFAQWKikiFiQGUwpJByRYHyhfUWdxbgYvEQVdMiE3GyYbFF8dBxNCHiQ4FBpxc1U4EAQYR2g4H2ZSEV4FGGgMUi88HSssRH9jWEgYCSQ5Hi9cMlkKETtFADQWGSY/KRAnQitXFCY1ED5aFUIHFzxYHSN9LmtxPhQxHQZMU0JwU2pSUxdJVCFXUiM6BWchLwcmFhwYGyY0UzkeGloMPCFWGiE8Fi8lPS4wFAFVHxVwByIXHT1JVGgRUm11UWdxblUwFAFVHwA5FCIeGlABADtqASE8HCIMYB0vQixdCTwiHDNaWj1JVGgRUm11UWdxblUwFAFVHwA5FCIeGlABADtqASE8HCIMYBcqFAQCPi0jBzgdCh9AfmgRUm11UWdxblVjWBtUEyU1OyMVG1sAEyBFARYmHS48KyhjRUhWEyRaU2pSUxdJVGhUHClfUWdxbhAtHEEyHyY0eUAeHFQIGGhXByM2BS4+IFUxHQVXDC0DHyMfFnI6JGBCHiQ4FG5bblVjWAFeWjs8GicXO14OHCRYFSUhAhwiIhwuHTUYDiA1HUBSUxdJVGgRUj45GCo0BhwkEARRHSAkABEBH14EERUfGiFvNSIiOgcsAUARcGhwU2pSUxdJByRYHygdGCA5IhwkEBxLITs8GicXLhkLHSRdSAkwAjMjIQxrUWIYWmhwU2pSU0QFHSVUOiQyGSs4KR03CzNLFiE9FhdSThcHHSQ7Um11USI/Kn8mFgwycCQ/ECseU1EcGitFGyI7UTIhKhQ3HTtUEyU1NhkiWx5jVGgRUiQzUSk+OlUFFAlfCWYjHyMfFnI6JGhFGig7e2dxblVjWEgYHCciUzkeGloMWGhHGz4gECsibhwtWBhZEzojWzkeGloMPCFWGiE8Fi8lPVxjHAcyWmhwU2pSUxdJVGgRACg4HjE0HRkqFQ19KRh4ACYbHlJAfmgRUm11UWdxKxsnckgYWmhwU2pSAVIdATpfeG11UWc0IBFJckgYWmg8HCkTHxcaGCFcFws6HSM0PAZjRUhDcGhwU2pSUxdJIydDGT4lECQ0dDMqFgx+EzojBwkaGlsNXGp0HCg4GCIibFxvckgYWmhwU2pSJFgbHztBEy4wSwE4IBEFERpLDgs4GiYWWxU6GCFcFz53WGtbblVjWEgYWmgHHDgZAEcIFy0LNCQ7FQE4PAY3OwBRFix4UQQiMERLXWQ7Um11UWdxblUUFxpTCTgxEC9INV4HEA5YAD4hMi84IhFrWjtUEyU1IDoTBFkaVmEdeG11UWdxblVjLwdKETsgEikXSXEAGix3Gz8mBQQ5JxknUEprFiE9FhkCEkAHBwVeFig5AmV4Yn9jWEgYWmhwUx0dAVwaBClSF3cTGCk1CBwxCxx7EiE8F2JQIEcIAyZUFgg7FCo4KwZhUUQyWmhwU2pSUxc+GzpaAT00EiJrCBwtHC5RCDskMCIbH1NBVglSBiQjFBQ9JxgmC0oRVkJwU2pSDj1jVGgRUiE6EiY9bhYsDQZMWnVwQ0BSUxdJEidDUhJ5USE+IhEmCkhRFGg5AysbAURBByRYHygTHis1KwcwUUhcFUJwU2pSUxdJVCFXUis6HSM0PFU3EA1WcGhwU2pSUxdJVGgRUis6A2cOYlUsGgIYEyZwGjoTGkUaXC5eHikwA30WKwEHHRtbHyY0EiQGAB9AXWhVHUd1UWdxblVjWEgYWmhwU2pSH1gKFSQRHSZ1TGc4PSYvEQVdUicyGWN4UxdJVGgRUm11UWdxblVjWAFeWic7Uz4aFlljVGgRUm11UWdxblVjWEgYWmhwU2oRAVIIAC1iHiQ4FAICHl0sGgIRcGhwU2pSUxdJVGgRUm11UWdxblVjGwdNFDxwTmoRHEIHAGgaUnxfUWdxblVjWEgYWmhwU2pSU1IHEEIRUm11UWdxblVjWEhdFCxaU2pSUxdJVGhUHClfUWdxbhAtHGIyWmhwU2dfU3EIGCRTEy4+S2ciLRQtWB9XCCMjAysRFhcAEmhfHW0mASIyJxMqG0heFSQ0FjgBU1EGASZVUiI3GyIyOgZJWEgYWiE2UykdBlkdVHUMUn11BS80IH9jWEgYWmhwUywdARc2WGheECd1GClxJwUiERpLUh8/ASEBA1YKEXJ2FzkRFDQyKxsnGQZMCWB5WmoWHD1JVGgRUm11UWdxblUvFwtZFmg/GGpPU14aJyRYHyh9HiU7Z39jWEgYWmhwU2pSUxcAEmheGW0hGSI/RFVjWEgYWmhwU2pSUxdJVGhSACg0BSICIhwuHS1rKmA/ESBbeRdJVGgRUm11UWdxblVjWEhbFT0+B2pPU1QGASZFUmZ1QE1xblVjWEgYWmhwU2oXHVNjVGgRUm11UWc0IBFJWEgYWi0+F0AXHVNjfjxQECEwXy4/PRAxDEB7FSY+FikGGlgHB2QRJSInGjQhLxYmVixdCSs1HS4THUMoECxUFncWHik/KxY3UA5NFCskGiUcW1MMBysYeG11UWc4KFUWFgRXGyw1F2oGG1IHVDpUBjgnH2c0IBFJWEgYWiE2UwweElAaWjtdGyAwNBQBbhQtHEhRCRs8GicXW1MMBysYUjk9FClbblVjWEgYWmgkEjkZXUAIHTwZQmNkWE1xblVjWEgYWisiFisGFmQFHSVUNx4FWSM0PRZqckgYWmg1HS54FlkNXWE7eGB4XmhxHjkCIS1qWg0DI0AeHFQIGGhBHiwsFDUZJxIrFAFfEjwjU3dSCEpjfiReESw5USEkIBY3EQdWWisiFisGFmcFFTFUAAgGIW8hIhQ6HRoRcGhwU2obFRcZGClIFz91THpxAhogGQRoFikpFjhSB18MGmhDFzkgAylxKxsnckgYWmg8HCkTHxcKHClDUnB1ASswNxAxVitQGzoxED4XAT1JVGgRGyt1HyglbhYrGRoYDiA1HWoAFkMcBiYRFyMxe2dxblUvFwtZFmg4ATpSThcKHClDSAs8HyMXJwcwDCtQEyQ0W2g6BloIGidYFh86HjMBLwc3WkEyWmhwUyMUU1kGAGhZAD11BS80IFUxHRxNCCZwFiQWeRdJVGhYFG0lHSYoKwcLEQ9QFiE3Gz4BKEcFFTFUABB1BS80IFUxHRxNCCZwFiQWeT1JVGgRHiI2ECtxJhljRUhxFDskEiQRFhkHET8ZUAU8Fi89JxIrDEoRcGhwU2oaHxknFSVUUnB1Uxc9LwwmCi1rKhcYP2h4UxdJVCBdXAs8HSsSIRksCkgFWgs/HyUAQBkPBidcIAoXWXd9bkR0SEQYSH1lWkBSUxdJHCQfPTghHS4/KzYsFAdKWnVwMCUeHEVaWi5DHSAHNgV5flljQFgUWnllQ2N4UxdJVCBdXAs8HSsFPBQtCxhZCC0+EDNSThdZWnw7Um11US89YDo2DARRFC0EASscAEcIBi1fETR1TGdhRFVjWEhQFmYUFjoGG3oGEC0RT20QHzI8YD0qHwBUEy84Bw4XA0MBOSdVF2MUHTAwNwYMFjxXCkJwU2pSG1tHNSxeACMwFGdsbhYrGRoyWmhwUyIeXWcIBi1fBm1oUSQ5LwdJckgYWmg8HCkTHxcLHSRdUnB1OCkiOhQtGw0WFC0nW2gwGlsFFidQACkSBC5zZ39jWEgYGCE8H2Q8EloMVHURUB05ED40PDAQKDd6EyQ8UUBSUxdJFiFdHmMUFSgjIBAmWFUYEjogeWpSUxcLHSRdXB48CyJxc1UWPAFVSGY+Fj1aQxtJTHgdUn15UXRhZ39jWEgYGCE8H2QzH0AIDTt+HBk6AWdsbgExDQ0yWmhwUygbH1tHJzxEFj4aFyEiKwFjRUhuHyskHDhBXVkMA2ABXm1mX3J9bkVqcmIYWmhwHyUREltJGCpdUnB1OCkiOhQtGw0WFC0nW2gmFk8dOClTFyF3XWczJxkvUWIYWmhwHygeXWQADi0RT20ANS48fFstHR8QS2RwQ2ZSQhtJRGE7Um11USszIlsXHRBMWnVwAyYTClIbWgZQHyhfUWdxbhkhFEZ6Gys7FDgdBlkNIDpQHD4lEDU0IBY6WFUYS0JwU2pSH1UFWhxUCjkWHis+PEZjRUh7FSQ/AXlcFUUGGRp2MGVlXWdjfkVvWFoNT2FaU2pSU1sLGGZlFzUhIjMjIR4mLBpZFDsgEjgXHVQQVHURQkd1UWdxIhcvVjxdAjwDECseFlNJSWhFADgwe2dxblUvGgQWPCc+B2pPU3IHASUfNCI7BWkWIQErGQV6FSQ0eUBSUxdJFiFdHmMFEDU0IAFjRUhbEikieWpSUxcZGClIFz8dGCA5IhwkEBxLITg8EjMXAWpJSWhKGiF1TGc5IlljGgFUFmhtUygbH1tFVCRQECg5UXpxIhcvBWIyWmhwUzoeEk4MBmZyGiwnECQlKwcRHQVXDCE+FHAxHFkHEStFWisgHyQlJxotUEEyWmhwU2pSUxcAEmhBHiwsFDUZJxIrFAFfEjwjKDoeEk4MBhURBiUwH01xblVjWEgYWmhwU2oCH1YQETp5Gyo9HS42JgEwIxhUGzE1ARdcG1tTMC1CBj86CG94RFVjWEgYWmhwU2pSU0cFFTFUAAU8Fi89JxIrDBtjCiQxCi8ALhkLHSRdSAkwAjMjIQxrUWIYWmhwU2pSUxdJVGhBHiwsFDUZJxIrFAFfEjwjKDoeEk4MBhURT207GCtbblVjWEgYWmg1HS54UxdJVC1fFmRfFCk1RH8vFwtZFmg2BiQRB14GGmhDFyA6ByIBIhQ6HRp9KRh4AyYTClIbXUIRUm11GCFxPhkiAQ1KMiE3GyYbFF8dBxNBHiwsFDUMbgErHQYyWmhwU2pSUxcZGClIFz8dGCA5IhwkEBxLITg8EjMXAWpHHCQLNigmBTU+N11qckgYWmhwU2pSA1sIDS1DOiQyGSs4KR03CzNIFikpFjgvXVUAGCQLNigmBTU+N11qckgYWmhwU2pSA1sIDS1DOiQyGSs4KR03CzNIFikpFjgvUwpJGiFdeG11UWc0IBFJHQZccEI8HCkTHxcPASZSBiQ6H2ckPhEiDA1oFikpFjg3IGdBXUIRUm11GCFxIBo3WC5UGy8jXToeEk4MBg1iIm0hGSI/RFVjWEgYWmhwFSUAU0cFFTFUAGF1Lmc4IFUzGQFKCWAgHysLFkUhHS9ZHiQyGTMiZ1UnF2IYWmhwU2pSUxdJVGhDFyA6ByIBIhQ6HRp9KRh4AyYTClIbXUIRUm11UWdxbhAtHGIYWmhwU2pSU0UMAD1DHEd1UWdxKxsnckgYWmg2HDhSLBtJBCRQCygnUS4/bhwzGQFKCWAAHysLFkUaTg9UBh05ED40PAZrUUEYHidaU2pSUxdJVGhYFG0lHSYoKwdjBlUYNiczEiYiH1YQEToRBiUwH01xblVjWEgYWmhwU2oRAVIIAC1hHiwsFDUUHSVrCARZAy0iWkBSUxdJVGgRUig7FU1xblVjHQZccC0+F0B4B1YLGC0fGyMmFDUlZjYsFgZdGTw5HCQBXxc5GClIFz8mXxc9LwwmCilcHi00SQkdHVkMFzwZFDg7EjM4IRtrCARZAy0iWkBSUxdJHS4RJyM5HiY1KxFjDABdFGgiFj4HAVlJESZVeG11UWc4KFUFFAlfCWYgHysLFkUsJxgRBiUwH01xblVjWEgYWisiFisGFmcFFTFUAAgGIW8hIhQ6HRoRcGhwU2oXHVNjESZVW2RfezMwLBkmVgFWCS0iB2IxHFkHEStFGyI7AmtxHhkiAQ1KCWYAHysLFkU7ESVeBCQ7Fn0SIRstHQtMUi4lHSkGGlgHXDhdEzQwA25bblVjWBpdFycmFhoeEk4MBg1iImUlHSYoKwdqcg1WHmF5eUBfXhhGVB14SG0YMA4fbiECOmJUFSsxH2o/PxdUVBxQED57PCY4IE8CHAx0Hy4kNDgdBkcLGzAZUB86HSs4IBJhUWJUFSsxH2o/IRdUVBxQED57PCY4IE8CHAxqEy84Bw0AHEIZFidJWm8ZHiglblNjKg1aEzokG2hbeVsGFyldUgAcUXpxGhQhC0Z1GyE+SQsWF3sMEjx2ACIgASU+Nl1hMQZOHyYkHDgLUR5jGCdSEyF1PAICHlV+WDxZGDt+PisbHQ0oECxjGyo9BQAjIQAzGgdAUmoGGjkHElsaVmE7eAAZSwY1KiEsHw9UH2ByMj8GHGUGGCQTXm0uJSIpOlV+WEp5Dzw/UxgdH1tLWGh1Fys0BCslbkhjHglUCS18UwkTH1sLFStaUnB1FzI/LQEqFwYQDGFaU2pSU3EFFS9CXCwgBSgDIRkvWFUYDEJwU2pSGlFJJiddHh4wAzE4LRAAFAFdFDxwByIXHT1JVGgRUm11UTcyLxkvUA5NFCskGiUcWx5JJiddHh4wAzE4LRAAFAFdFDxqAC8GMkIdGxpeHiEQHyYzIhAnUB4RWi0+F2N4UxdJVC1fFkcwHyMsZ39JNSQCOyw0JyUVFFsMXGp5GykxFCkDIRkvWkQYARw1Cz5SThdLPCFVFig7URU+IhljUAZXWik+GicTB14GGmETXm0RFCEwOxk3WFUYHCk8AC9eU3QIGCRTEy4+UXpxKAAtGxxRFSZ4BWN4UxdJVA5dEyomXy84KhEmFjpXFiRwTmoEeRdJVGhYFG0HHis9HRAxDgFbHws8Gi8cBxcdHC1feG11UWdxblVjCAtZFiR4FT8cEEMAGyYZW20HHis9HRAxDgFbHws8Gi8cBw0aETx5GykxFCkDIRkvPQZZGCQ1F2IEWhcMGiwYeG11UWc0IBFJHQZcB2FaeQc+SXYNEBtdGykwA29zHBovFCxdFikpUWZSCGMMDDwRT213Iyg9IlUHHQRZA2h4AGNQXxckHSYRT21lXWccLw1jRUgNVmgUFiwTBlsdVHURQmNlRGtxHBo2FgxRFC9wTmpAXxcqFSRdECw2GmdsbhM2FgtMEyc+WzxbeRdJVGh3HiwyAmkjIRkvPA1UGzFwTmofEkMBWiVQCmVlX3dgYlU1UWJdFCwtWkB4PntTNSxVMDghBSg/Zg4XHRBMWnVwURgdH1tJOidGUGF1NzI/LVV+WA5NFCskGiUcWx5jVGgRUiQzURU+IhkQHRpOEys1MCYbFlkdVDxZFyNfUWdxblVjWEhIGSk8H2IUBlkKACFeHGV8URU+IhkQHRpOEys1MCYbFlkdTjpeHiF9WGc0IBFqckgYWmhwU2pSAFIaByFeHB86HSsibkhjCw1LCSE/HRgdH1saVGMRQ0d1UWdxKxsncg1WHjV5eUA/IQ0oECxlHSoyHSJ5bDQ2DAd7FSQ8FikGURtJDxxUCjl1TGdzDwA3F0h7FSQ8FikGU3sGGzwTXm0RFCEwOxk3WFUYHCk8AC9eU3QIGCRTEy4+UXpxKAAtGxxRFSZ4BWN4UxdJVA5dEyomXyYkOhoAFwRUHyskU3dSBT0MGixMW0dfPBVrDxEnOh1MDic+WzEmFk8dVHURUA46HSs0LQFjOQRUWgY/BGheU3EcGisRT20zBCkyOhwsFkARcGhwU2obFRclGydFISgnBy4yKzYvEQ1WDmgkGy8ceRdJVGgRUm11ASQwIhlrHh1WGTw5HCRaWj1JVGgRUm11UWdxblUvFwtZFmg8HCUGMU4gEGgMUgE6HjMCKwc1EQtdOSQ5FiQGXVsGGzxzCwQxe2dxblVjWEgYWmhwUyMUU1sGGzxzCwQxUTM5KxtJWEgYWmhwU2pSUxdJVGgRUis6A2c4KlUqFkhIGyEiAGIeHFgdNjF4FmR1FShbblVjWEgYWmhwU2pSUxdJVGgRUm0lEiY9Il0lDQZbDiE/HWJbU3sGGzxiFz8jGCQ0DRkqHQZMQDo1Aj8XAEMqGyRdFy4hWS41Z1UmFgwRcGhwU2pSUxdJVGgRUm11UWc0IBFJWEgYWmhwU2pSUxdJESZVeG11UWdxblVjHQZcU0JwU2pSFlkNfi1fFjB8e00cHE8CHAxsFS83Hy9aUXYcACdjFy88AzM5bFljAzxdAjxwTmpQMkIdG2hjFy88AzM5bFljPA1eGz08B2pPU1EIGDtUXm0WECs9LBQgE0gFWi4lHSkGGlgHXD4YeG11UWcXIhQkC0ZZDzw/IS8QGkUdHGgMUjtfFCk1M1xJciVqQAk0Fx4dFFAFEWATMzghHgUkNzsmABxiFSY1UWZSCGMMDDwRT213MDIlIVUBDREYNC0oB2ooHFkMVmQRNigzEDI9OlV+WA5ZFjs1X2oxElsFFilSGW1oUSEkIBY3EQdWUj55eWpSUxcvGClWAWM0BDM+DAA6Ng1ADhI/HS9SThcffi1fFjB8e00cHE8CHAx6DzwkHCRaCGMMDDwRT213IyIzJwc3EEh2FT9yX2o0BlkKVHURFDg7EjM4IRtrUWIYWmhwGixSIVILHTpFGh4wAzE4LRAAFAFdFDxwByIXHT1JVGgRUm11USs+LRQvWAdTWnVwAykTH1tBEj1fETk8Hil5Z1URHQpRCDw4IC8ABV4KEQtdGyg7BX0wOgEmFRhMKC0yGjgGGx9AVC1fFmRfUWdxblVjWEhRHGg/GGoGG1IHVARYED80Az5rABo3EQ5BUmoCFigbAUMBVDtEES4wAjQ3OxliWkQYSWFwFiQWeRdJVGhUHClfFCk1M1xJciVxQAk0Fx4dFFAFEWATMzghHgIgOxwzOg1LDmp8UzEmFk8dVHURUAwgBShxCwQ2ERgYOC0jB2ohH14EETsTXm0RFCEwOxk3WFUYHCk8AC9eU3QIGCRTEy4+UXpxKAAtGxxRFSZ4BWN4UxdJVA5dEyomXyYkOhoGCR1RCgo1AD5SThcffi1fFjB8e00cB08CHAx6DzwkHCRaCGMMDDwRT213NDYkJwVjOg1LDmgeHD1QXxcvASZSUnB1FzI/LQEqFwYQU0JwU2pSGlFJPSZHFyMhHjUoHRAxDgFbHws8Gi8cBxcdHC1feG11UWdxblVjCAtZFiR4FT8cEEMAGyYZW20cHzE0IAEsChFrHzomGikXMFsAESZFSCgkBC4hDBAwDEARWi0+F2N4UxdJVC1fFkcwHyMsZ39JVUUXVWgFOnBSJmcuJgl1Nx51JQYTRBksGwlUWh0cU3dSJ1YLB2ZkAionECM0PU8CHAx0Hy4kNDgdBkcLGzAZUA8gCGcEPhIxGQxdCWp5eSYdEFYFVB1jUnB1JSYzPVsWCA9KGyw1AHAzF1M7HS9ZBgonHjIhLBo7UEp5Dzw/UwgHChVAfkJkPncUFSMVPBozHAdPFGByIC8eFlQdESxkAionECM0bFljAzxdAjxwTmpQJkcOBilVF20hHmcTOwxhVEhuGyQlFjlSThcoOARuJx0SIwYVCyZvWCxdHCklHz5SThdLGD1SGW95UQQwIhkhGQtTWnVwFT8cEEMAGyYZBGRfUWdxbjMvGQ9LVDs1Hy8RB1INIThWACwxFGdsbgNJHQZcB2FaeR8+SXYNEApEBjk6H28qGhA7DEgFWmoSBjNSIFIFEStFFyl1JDc2PBQnHUoUWg4lHSlSThcPASZSBiQ6H294RFVjWEhRHGgFAy0AElMMJy1DBCQ2FAQ9JxAtDEhMEi0+eWpSUxdJVGgRAi40HSt5KAAtGxxRFSZ4WmonA1AbFSxUISgnBy4yKzYvEQ1WDnIlHSYdEFw8BC9DEykwWQE9LxIwVhtdFi0zBy8WJkcOBilVF2R1FCk1Z39jWEgYWmhwUwYbEUUIBjELPCIhGCEoZlcBFx1fEjxqU2hSXRlJACdCBj88HyB5CBkiHxsWCS08FikGFlM8BC9DEykwWGtxfVxJWEgYWi0+F0AXHVMUXUI7JwFvMCM1DAA3DAdWUjMEFjIGUwpJVgpEC20UPQtxGwUkCglcHztyX2o0BlkKVHURFDg7EjM4IRtrUWIYWmhwGixSHVgdVB1BFT80FSICKwc1EQtdOSQ5FiQGU0MBESYRACghBDU/bhAtHGIYWmhwBysBGBkaBClGHGUzBCkyOhwsFkARcGhwU2pSUxdJEidDUhJ5US41bhwtWAFIGyEiAGIzP3s2IRh2IAwRNBR4bhEsckgYWmhwU2pSUxdJVDhSEyE5WSEkIBY3EQdWUmFwJjoVAVYNERtUADs8EiISIhwmFhwCDyY8HCkZJkcOBilVF2U8FW5xKxsnUWIYWmhwU2pSUxdJVGhFEz4+XzAwJwFrSEYITWFaU2pSUxdJVGhUHClfUWdxblVjWEh0EyoiEjgLSXkGACFXC2V3MCs9bgAzHxpZHi0jUzoHAVQBFTtUFmx3XWdiZ39jWEgYHyY0WkAXHVMUXUI7Jx9vMCM1GhokHwRdUmoRBj4dMUIQOD1SGW95UTwFKw03WFUYWAklByVSMUIQVAREESZ3XWcVKxMiDQRMWnVwFSseAFJFVAtQHiE3ECQ6bkhjHh1WGTw5HCRaBR5JMiRQFT57EDIlITc2ASRNGSNwTmoEU1IHEDUYeBgHSwY1KiEsHw9UH2ByMj8GHHUcDRtdHTkmU2txNSEmABwYR2hyMj8GHBcrATERISE6BTRzYlUHHQ5ZDyQkU3dSFVYFBy0dUg40HSszLxYoWFUYHD0+ED4bHFlBAmERNCE0FjR/LwA3FypNAxs8HD4BUwpJAmhUHCkoWE0EHE8CHAxsFS83Hy9aUXYcACdzBzQHHis9HQUmHQwaVmgrJy8KBxdUVGpwBzk6UQUkN1URFwRUWhsgFi8WURtJMC1XEzg5BWdsbhMiFBtdVmgTEiYeEVYKH2gMUisgHyQlJxotUB4RWg48Ei0BXVYcACdzBzQHHis9HQUmHQwYR2gmUy8cF0pAfh1jSAwxFRM+KRIvHUAaOz0kHAgHCnoIEyZUBm95UTwFKw03WFUYWAklByVSMUIQVAVQFSMwBWcDLxEqDRsaVmgUFiwTBlsdVHURFCw5AiJ9bjYiFARaGys7U3dSFUIHFzxYHSN9B25xCBkiHxsWGz0kHAgHCnoIEyZUBm1oUTFxKxsnBUEyLxpqMi4WJ1gOEyRUWm8UBDM+DAA6OwdRFGp8UzEmFk8dVHURUAwgBShxDAA6WCtXEyZwOiQRHFoMVmQRNigzEDI9OlV+WA5ZFjs1X2oxElsFFilSGW1oUSEkIBY3EQdWUj55UwweElAaWilEBiIXBD4SIRwtWFUYDGg1HS4PWj08JnJwFikBHiA2IhBrWilNDicSBjM1HFgZVmQRCRkwCTNxc1VhOR1MFWgSBjNSNFgGBGh1ACIlURUwOhBhVEh8Hy4xBiYGUwpJEildASh5UQQwIhkhGQtTWnVwFT8cEEMAGyYZBGR1NyswKQZtGR1MFQolCg0dHEdJSWhHUig7FTp4RH9uVUcXWh0ZSWohJ3Y9J2hlMw9fHSgyLxljKyQYR2gEEigBXWQdFTxCSAwxFQs0KAEECgdNCio/C2JQI0UGEiFdF298eys+LRQvWDtqWnVwJysQABk6AClFAXcUFSMDJxIrDC9KFT0gESUKWxU7GyRdAW1zURU0LBwxDAAaU0JaHyUREltJGCpdMSI8HzRxblVjRUhrNnIRFy4+ElUMGGATMSI8HzRrbhksGQxRFC9+XWRQWj0FGytQHm05EysWIRozWEgYWmhtUxk+SXYNEARQECg5WWUWIRozQkhUFSk0GiQVXRlHVmE7HiI2ECtxIhcvIgdWH2hwU2pSThc6OHJwFikZECU0Il1hIgdWH3JwHyUTF14HE2YfXG98eys+LRQvWARaFgUxCxAdHVJJVHURIQFvMCM1AhQhHQQQWAUxC2ooHFkMTmhdHSwxGCk2YFttWkEyFiczEiZSH1UFJi1TGz8hGTRxc1UQNFJ5HiwcEigXHx9LJi1TGz8hGTRrbhksGQxRFC9+XWRQWj0FGytQHm05EysEPhIxGQxdCWhtUxk+SXYNEARQECg5WWUEPhIxGQxdCXJwHyUTF14HE2YfXG98eys+LRQvWARaFg0hBiMCA1INVHURIQFvMCM1AhQhHQQQWA0hBiMCA1INTmhdHSwxGCk2YFttWkEyFiczEiZSH1UFJiddHg4gA2dxc1UQNFJ5HiwcEigXHx9LJiddHm0WBDUjKxsgAVIYFicxFyMcFBlHWmoYeEc5HiQwIlUvGgRsFTwxHxgdH1saVGgRT20GI30QKhEPGQpdFmByJyUGEltJJiddHj5vUSs+LxEqFg8WVGZyWkAeHFQIGGhdECEGFDQiJxotKgdUFjtwTmohIQ0oECx9Ey8wHW9zHRAwCwFXFGgCHCYeAA1JRGoYeCE6EiY9bhkhFC9XFiw1HWpSUxdJVGgMUh4HSwY1KjkiGg1UUmoXHCYWFllTVCReEyk8HyB/YFthUWJUFSsxH2oeEVstHSlcHSMxUWdxblVjRUhrKHIRFy4+ElUMGGATNiQ0HCg/Kk9jFAdZHiE+FGRcXRVAfiReESw5USszIiMsEQwYWmhwU2pSUxdUVBtjSAwxFQswLBAvUEpuFSE0SWoeHFYNHSZWXGN7U25bIhogGQQYFio8NCseEk8QVGgRUm11UXpxHSd5OQxcNikyFiZaUXAIGClJC3d1HSgwKhwtH0YWVGp5eSYdEFYFVCRTHh80AyIiOlVjWEgYWmhtUxkgSXYNEARQECg5WWUDLwcmCxwYKCc8H3BSH1gIECFfFWN7X2V4RBksGwlUWiQyHxgXEV4bACByHT4hUWdsbiYRQilcHgQxES8eWxU7ESpYADk9UQQ+PQF5WARXGyw5HS1cXRlLXUJdHS40HWc9LBkPDQtTNz08B2pSUxdJSWhiIHcUFSMdLxcmFEAaNj0zGGo/BlsdHThdGygnS2c9IRQnEQZfVGZ+UWN4H1gKFSQRHi85IyIzJwc3EDpdGywpU3dSIGVTNSxVPiw3FCt5bCcmGgFKDiBwIS8TF05TVCReEyk8HyB/YFthUWIyV2V/XGonOg1JIA19Nx0aIxNxGjQBcgRXGSk8Ux4+UwpJIClTAWMBFCs0PhoxDFJ5HiwcFiwGNEUGAThTHTV9Ux0+IBAwWkEyFiczEiZSJ2VJSWhlEy8mXxM0IhAzFxpMQAk0FxgbFF8dMzpeBz03Hj95bDksGwlMEyc+AGpUU2cFFTFUAD53WE1bGjl5OQxcKSQ5Fy8AWxU6ESRUETkwFR0+IBBhVEhDLi0oB2pPUxU6ESRUETl1Kyg/K1dvWCVRFGhtU3teU3oIDGgMUnllXWcVKxMiDQRMWnVwQmZSIVgcGixYHCp1TGdhYlUAGQRUGCkzGGpPU1EcGitFGyI7WTF4RFVjWEh+Fik3AGQBFlsMFzxUFhc6HyJxc1UuGRxQVC48HCUAW0FAfi1fFjB8e00FAk8CHAx6DzwkHCRaCGMMDDwRT213JSI9KwUsChwYDidwIC8eFlQdESwRKCI7FGV9bjM2FgsYR2g2BiQRB14GGmAYeG11UWc9IRYiFEhIFTtwTmooPHksKxh+IRYTHSY2PVswHQRdGTw1FxAdHVI0fmgRUm08F2chIQZjDABdFEJwU2pSUxdJVDxUHiglHjUlGhprCAdLU0JwU2pSUxdJVARYED80Az5rABo3EQ5BUmoEFiYXA1gbAC1VUjk6UR0+IBBjWkgWVGgWHysVABkaESRUETkwFR0+IBBvWFsRcGhwU2oXHVNjESZVD2RfexMddDQnHCpNDjw/HWIJJ1IRAGgMUm8PHik0bkRjUDtMGzokWmheU3EcGisRT20zBCkyOhwsFkARWjw1Hy8CHEUdICcZKAIbNBgBASYYSTURWi0+FzdbeWMlTglVFg8gBTM+IF04LA1ADmhtU2goHFkMVHkBUGF1NzI/LVV+WA5NFCskGiUcWx5JAC1dFz06AzMFIV0ZNyZ9JRgfIBFDQ2pAVC1fFjB8exMddDQnHCpNDjw/HWIJJ1IRAGgMUm8PHik0bkdzWkQYPD0+EGpPU1EcGitFGyI7WW5xOhAvHRhXCDwEHGIoPHksKxh+IRZnQRp4bhAtHBURcBwcSQsWF3UcADxeHGUuJSIpOlV+WEpiFSY1U3lCURtJMj1fEW1oUSEkIBY3EQdWUmFwBy8eFkcGBjxlHWUPPgkUESUMKzMLShV5Uy8cF0pAfhx9SAwxFQUkOgEsFkBDLi0oB2pPUxUzGyZUUnllUW8cLw1qWkQYPD0+EGpPU1EcGitFGyI7WW5xOhAvHRhXCDwEHGIoPHksKxh+IRZhQRp4bhAtHBURcEIEIXAzF1MrATxFHSN9ChM0NgFjRUgaMj0yU2VSIEcIAyYTXm0TBCkybkhjHh1WGTw5HCRaWhcdESRUAiInBRM+ZiMmGxxXCHt+HS8FWwZFVHkEXm14Q3R4Z1UmFgxFU0IEIXAzF1MrATxFHSN9ChM0NgFjRUgaNi0xFy8AEVgIBixCUmB1IyYjKwY3WDpXFiRyX2o0BlkKVHURFDg7EjM4IRtrUUhMHyQ1AyUAB2MGXB5UETk6A3R/IBA0UFkPVmhhRmZSXgVeXWERFyMxDG5bGid5OQxcOD0kByUcW0w9ETBFUnB1Uws0LxEmCgpXGzo0AGpfU3MIHSRIUh80AyIiOldvWC5NFCtwTmoUBlkKACFeHGV8UTM0IhAzFxpMLid4JS8RB1gbR2ZfFzp9Q359bkR2VEgVTn15WmoXHVMUXUJlIHcUFSMTOwE3FwYQARw1Cz5SThdLOC1QFignEygwPBEwWEUYNycjB2ogHFsFB2odUgsgHyRxc1UlDQZbDiE/HWJbU0MMGC1BHT8hJSh5GBAgDAdKSWY+Fj1aQgBFVHkEXm14Qm54bhAtHBURcBwCSQsWF3UcADxeHGUuJSIpOlV+WEp0Hyk0FjgQHFYbEDsRX20HFCU4PAErC0oUWg4lHSlSThcPASZSBiQ6H294bgEmFA1IFTokJyVaJVIKACdDQWM7FDB5fExvWFkNVmhhRGNbU1IHEDUYeEcBI30QKhEBDRxMFSZ4CB4XC0NJSWgTJig5FDc+PAFjDAcYKCk+FyUfU2cFFTFUAG95UQEkIBZjRUheDyYzByMdHR9AfmgRUm05HiQwIlUsDABdCDtwTmoJDj1JVGgRFCInURh9bgVjEQYYEzgxGjgBW2cFFTFUAD5vNiIlHhkiAQ1KCWB5WmoWHD1JVGgRUm11US43bgVjBlUYNiczEiYiH1YQEToREyMxUTd/DR0iCglbDi0iUyscFxcZWgtZEz80EjM0PE8FEQZcPCEiAD4xG14FEGATOjg4ECk+JxERFwdMKikiB2hbU0MBESY7Um11UWdxblVjWEgYDikyHy9cGlkaETpFWiIhGSIjPVljCEEyWmhwU2pSUxcMGiw7Um11USI/Kn9jWEgYEy5wUCUGG1IbB2gPUn11BS80IH9jWEgYWmhwUyYdEFYFVDxQACowBWdsbho3EA1KCRM9Ej4aXUUIGixeH2VkXWdyIQErHRpLUxVaU2pSUxdJVGhFFyEwASgjOiEsUBxZCC81B2QxG1YbFStFFz97OTI8LxssEQxqFSckIysABxk5GztYBiQ6H2d6biMmGxxXCHt+HS8FWwdFVH0dUn18WE1xblVjWEgYWgQ5ETgTAU5TOidFGyssWWUFKxkmCAdKDi00Uz4dSRdLVGYfUjk0AyA0OlsNGQVdVmhjWkBSUxdJESRCF0d1UWdxblVjWCRRGDoxATNIPVgdHS5IWm8bHmc+Oh0mCkhIFikpFjgBU1EGASZVXG95UXR4RFVjWEhdFCxaFiQWDh5jfmUcXWJ1JA5rbjgMLi11PwYEUx4zMT0FGytQHm0YJ2dsbiEiGhsWNycmFicXHUNTNSxVPigzBQAjIQAzGgdAUmodHDwXHlIHAGoYeCE6EiY9bjgVSkgFWhwxETlcPlgfESVUHDlvMCM1HBwkEBx/CCclAygdCx9LJCBIASQ2AmV4RH8OLlJ5HiwDHyMWFkVBVh9QHiYGASI0KldvWBNsHzAkU3dSUWAIGCMRIT0wFCNzYlUOEQYYR2hhRWZSPlYRVHURR31lXWcVKxMiDQRMWnVwQXheU2UGASZVGyMyUXpxflljOwlUFioxECFSThcPASZSBiQ6H28nZ39jWEgYPCQxFDlcBFYFHxtBFygxUXpxOH9jWEgYGzggHzMhA1IMEGBHW0cwHyMsZ39JNT4COyw0ICYbF1IbXGp7ByAlISgmKwdhVEhDLi0oB2pPUxUjASVBUh06BiIjbFljNQFWWnVwQnpeU3oIDGgMUnhlQWtxChAlGR1UDmhtU39CXxc7Gz1fFiQ7FmdsbkVvWCtZFiQyEikZUwpJEj1fETk8Hil5OFxJWEgYWg48Ei0BXV0cGThhHTowA2dsbgNJWEgYWikgAyYLOUIEBGBHW0cwHyMsZ39JNT4COyw0MT8GB1gHXDNlFzUhUXpxbCcmCw1MWgU/BS8fFlkdVmQRNDg7EmdsbhM2FgtMEyc+W2N4UxdJVA5dEyomXzAwIh4QCA1dHmhtU3hAeRdJVGh3HiwyAmk7OxgzKAdPHzpwTmpHQz1JVGgREz0lHT4CPhAmHEAKSGFaU2pSU1YZBCRIODg4AW9kflxJWEgYWgQ5ETgTAU5TOidFGyssWWUcIQMmFQ1WDmgiFjkXBxcdG2hVFys0BCslbFljS0EyHyY0DmN4eXo/RnJwFikBHiA2IhBrWiZXOSQ5A2heU0w9ETBFUnB1Uwk+bjYvERgaVmgUFiwTBlsdVHURFCw5AiJ9bjYiFARaGys7U3dSFUIHFzxYHSN9B25bblVjWC5UGy8jXSQdMFsABGgMUjtfFCk1M1xJciV9KRhqMi4WJ1gOEyRUWm8GHS48KzAQKEoUWjMEFjIGUwpJVhtdGyAwUQICHldvWCxdHCklHz5SThcPFSRCF2F1MiY9IhciGwMYR2g2BiQRB14GGmBHW0d1UWdxCBkiHxsWCSQ5Hi83IGdJSWhHeG11UWckPhEiDA1rFiE9Fg8hIx9Afi1fFjB8e00cCyYTQilcHhw/FC0eFh9LJCRQCygnNBQBbFljAzxdAjxwTmpQI1sIDS1DUggGIWV9bjEmHglNFjxwTmoUElsaEWQRMSw5HSUwLR5jRUheDyYzByMdHR8fXUIRUm11NyswKQZtCARZAy0iNhkiUwpJAkIRUm11BDc1LwEmKARZAy0iNhkiWx5jESZVD2Rfe2p8YVpjLSECWhsVJx47PXA6VBxwMEc5HiQwIlUQPTxqWnVwJysQABk6ETxFGyMyAn0QKhEREQ9QDg8iHD8CEVgRXGpiET88ATNzZ39JKy1sKHIRFy4wBkMdGyYZCRkwCTNxc1VhLQZUFSk0UwcXHUJLWGh3ByM2UXpxKAAtGxxRFSZ4WkBSUxdJISZdHSwxFCNxc1U3Ch1dcGhwU2oUHEVJK2QRESI7H2c4IFUqCAlRCDt4MCUcHVIKACFeHD58USM+RFVjWEgYWmhwGixSEFgHGmhQHCl1Eig/IFsAFwZWHyskFi5SB18MGmhBESw5HW83OxsgDAFXFGB5UykdHVlTMCFCESI7HyIyOl1qWA1WHmFwFiQWeRdJVGhUHClfUWdxbhMsCkhLFiE9FmZSLBcAGmhBEyQnAm8iIhwuHSBRHSA8Gi0aB0RAVCxeeG11UWdxblVjCg1VFT41ICYbHlIsJxgZASE8HCJ4RFVjWEhdFCxaU2pSU1EGBmhBHiwsFDV9bipjEQYYCik5ATlaA1sIDS1DOiQyGSs4KR03C0EYHidaU2pSUxdJVGhDFyA6ByIBIhQ6HRp9KRh4AyYTClIbXUIRUm11FCk1RFVjWEhZCjg8ChkCFlINXHkHW0d1UWdxLwUzFBFyDyUgW39CWj1JVGgRAi40HSt5KAAtGxxRFSZ4Wmo+GlUbFTpISBg7HSgwKl1qWA1WHmFaU2pSU1AMAC9UHDt9WGkCIhwuHTp2PQQ/Ei4XFxdUVCZYHkcwHyMsZ39JVUUYPxsAUz8CF1YdEWhdHSIlezMwPR5tCxhZDSZ4FT8cEEMAGyYZW0d1UWdxOR0qFA0YDikjGGQFEl4dXHoYUik6e2dxblVjWEgYEy5wJiQeHFYNESwRBiUwH2cjKwE2CgYYHyY0eWpSUxdJVGgRBz0xEDM0HRkqFQ19KRh4WkBSUxdJVGgRUjglFSYlKyUvGRFdCA0DI2JbeRdJVGhUHClfFCk1Z39JVUUXVWgEOw8/NhdPVBtwJAhfJS80IxAOGQZZHS0iSRkXB3sAFjpQADR9PS4zPBQxAUEyKSkmFgcTHVYOEToLISghPS4zPBQxAUB0EyoiEjgLWj09HC1cFwA0HyY2Kwd5Kw1MPCc8Fy8AWxUwRiN5By96Iis4IxARNi8aU0IDEjwXPlYHFS9UAHcGFDMXIRknHRoQWBFiGAIHERg6GCFcFx8bNmgyIRslEQ9LWGFaJyIXHlIkFSZQFSgnSwYhPhk6LAdsGyp4JysQABk6ETxFGyMyAm5bHRQ1HSVZFCk3FjhIMUIAGCxyHSMzGCACKxY3EQdWUhwxETlcIFIdACFfFT58exQwOBAOGQZZHS0iSQYdElMoATxeHiI0FQQ+IBMqH0ARcEJ9XmVdU3Y8IAd8MxkcPglxAjoMKDsycGV9UwsHB1hJJiddHkchEDQ6YAYzGR9WUi4lHSkGGlgHXGE7Um11UTA5JxkmWBxZCSN+BCsbBx8EFTxZXCA0CW9hYEVyVEh+Fik3AGQAHFsFMC1dEzR8WGc1IX9jWEgYWmhwUyMUU2IHGCdQFigxUTM5KxtjCg1MDzo+Uy8cFz1JVGgRUm11US43bjMvGQ9LVCklByUgHFsFVClfFm0HHis9HRAxDgFbHws8Gi8cBxcdHC1feG11UWdxblVjWEgYWjgzEiYeW1EcGitFGyI7WW5xHBovFDtdCD45EC8xH14MGjwLACI5HW94bhAtHEEyWmhwU2pSUxdJVGgRASgmAi4+ICcsFARLWnVwAC8BAF4GGhpeHiEmUWxxf39jWEgYWmhwUy8cFz1JVGgRFyMxeyI/KlxJckUVWgklByVSMFgFGC1SBkchEDQ6YAYzGR9WUi4lHSkGGlgHXGE7Um11UTA5JxkmWBxZCSN+BCsbBx9ZWn0YUik6e2dxblVjWEgYEy5wJiQeHFYNESwRBiUwH2cjKwE2CgYYHyY0eWpSUxdJVGgRGyt1NyswKQZtGR1MFQs/HyYXEENJFSZVUgE6HjMCKwc1EQtdOSQ5FiQGU0MBESY7Um11UWdxblVjWEgYCisxHyZaFUIHFzxYHSN9WE1xblVjWEgYWmhwU2pSUxdJGCdSEyF1HSVxc1UPFwdMKS0iBSMRFnQFHS1fBmM5HiglDAwKHGIYWmhwU2pSUxdJVGgRUm11GCFxIhdjDABdFEJwU2pSUxdJVGgRUm11UWdxblVjWA5XCGg5F2obHRcZFSFDAWU5E25xKhpJWEgYWmhwU2pSUxdJVGgRUm11UWdxblVjCAtZFiR4FT8cEEMAGyYZW20ZHiglHRAxDgFbHws8Gi8cBw0bETlEFz4hMig9IhAgDEBRHmFwFiQWWj1JVGgRUm11UWdxblVjWEgYWmhwUy8cFz1JVGgRUm11UWdxblVjWEgYHyY0eWpSUxdJVGgRUm11USI/KlxJWEgYWmhwU2oXHVNjVGgRUig7FU00IBFqcmIVV2gRBj4dU2UMFiFDBiVfBSYiJVswCAlPFGA2BiQRB14GGmAYeG11UWcmJhwvHUhMGzs7XT0TGkNBRmERFiJfUWdxblVjWEhRHGgFHSYdElMMEGhFGig7UTU0OgAxFkhdFCxaU2pSUxdJVGhYFG0THSY2PVsiDRxXKC0yGjgGGxcIGiwRICg3GDUlJiYmCh5RGS0THyMXHUNJFSZVUh8wEy4jOh0QHRpOEys1Jj4bH0RJACBUHEd1UWdxblVjWEgYWmggECseHx8PASZSBiQ6H294RFVjWEgYWmhwU2pSUxdJVGhdHS40HWc1LwEiWFUYHS0kNysGEh9AfmgRUm11UWdxblVjWEgYWmg8HCkTHxcOGydBUnB1BSg/OxghHRoQHikkEmQVHFgZXWheAG1le2dxblVjWEgYWmhwU2pSUxcFGytQHm0nFCU4PAErC0gFWjw/HT8fEVIbXCxQBix7AyIzJwc3EBsRWiciU3p4UxdJVGgRUm11UWdxblVjWARXGSk8UykdAENJSWhjFy88AzM5HRAxDgFbHx0kGiYBXVAMAAteATl9AyIzJwc3EBsRcGhwU2pSUxdJVGgRUm11UWc4KFUgFxtMWik+F2oVHFgZVHYMUi46AjNxOh0mFmIYWmhwU2pSUxdJVGgRUm11UWdxbicmGgFKDiADFjgEGlQMNyRYFyMhSyYlOhAuCBxqHyo5AT4aWx5jVGgRUm11UWdxblVjWEgYWi0+F0BSUxdJVGgRUm11UWc0IBFqckgYWmhwU2pSFlkNfmgRUm0wHyNbKxsnUWIyV2VwMj8GHBcsBT1YAm0XFDQlRAEiCwMWCTgxBCRaFUIHFzxYHSN9WE1xblVjDwBRFi1wBysBGBkeFSFFWnh8USM+RFVjWEgYWmhwGixSJlkFGylVFyl1BS80IFUxHRxNCCZwFiQWeRdJVGgRUm11GCFxCBkiHxsWGz0kHA8DBl4ZNi1CBm00HyNxBxs1HQZMFTopIC8ABV4KEQtdGyg7BWclJhAtckgYWmhwU2pSUxdJVDhSEyE5WSEkIBY3EQdWUmFwOiQEFlkdGzpIISgnBy4yKzYvEQ1WDnI1Aj8bA3UMBzwZW20wHyN4RFVjWEgYWmhwFiQWeRdJVGhUHClfFCk1Z39JVUUYOz0kHGowBk5JIThWACwxFDRbOhQwE0ZLCiknHWIUBlkKACFeHGV8e2dxblU0EAFUH2gkEjkZXUAIHTwZQmNmWGc1IX9jWEgYWmhwUyMUU2IHGCdQFigxUTM5KxtjCg1MDzo+Uy8cFz1JVGgRUm11US43bhssDEhtCi8iEi4XIFIbAiFSFw45GCI/OlU3EA1WWis/HT4bHUIMVC1fFkd1UWdxblVjWAFeWg48Ei0BXVYcACdzBzQZBCQ6blVjWEgYDiA1HWoCEFYFGGBXByM2BS4+IF1qWD1IHToxFy8hFkUfHStUMSE8FCkldAAtFAdbER0gFDgTF1JBViREESZ3WGc0IBFqWA1WHkJwU2pSUxdJVCFXUgs5ECAiYBQ2DAd6DzEDHyUGABdJVGgRBiUwH2chLRQvFEBeDyYzByMdHR9AVB1BFT80FSICKwc1EQtdOSQ5FiQGSUIHGCdSGRglFjUwKhBrWhtUFTwjUWNSFlkNXWhUHClfUWdxblVjWEhRHGgWHysVABkIATxeMDgsIyg9IiYzHQ1cWjw4FiRSA1QIGCQZFDg7EjM4IRtrUUhtCi8iEi4XIFIbAiFSFw45GCI/Ok82FgRXGSMFAy0AElMMXGpDHSE5Ijc0KxFhUUhdFCx5Uy8cFz1JVGgRUm11US43bjMvGQ9LVCklByUwBk4kFS9fFzl1UWdxOh0mFkhIGSk8H2IUBlkKACFeHGV8URIhKQciHA1rHzomGikXMFsAESZFSDg7HSgyJSAzHxpZHi14UScTFFkMABpQFiQgAmV4bhAtHEEYHyY0eWpSUxdJVGgRGyt1NyswKQZtGR1MFQolCgkdGllJVGgRUm0hGSI/bgUgGQRUUi4lHSkGGlgHXGERJz0yAyY1KyYmCh5RGS0THyMXHUNTASZdHS4+JDc2PBQnHUAaGSc5HQMcEFgEEWoYUig7FW5xKxsnckgYWmhwU2pSGlFJMiRQFT57EDIlITc2AS9XFThwU2pSUxcdHC1fUj02ECs9ZhM2FgtMEyc+W2NSJkcOBilVFx4wAzE4LRAAFAFdFDxqBiQeHFQCIThWACwxFG9zKRosCCxKFTgCEj4XUR5JESZVW20wHyNbblVjWA1WHkI1HS5beT1EWWhwBzk6UQUkN1UNHRBMWhI/HS94H1gKFSQRKCI7FDQCKwc1EQtdOSQ5FiQGUwpJBylXFx8wADI4PBBrWjtXDzozFmheUxUvESlFBz8wAmV9blcZFwZdCWp8U2goHFkMBxtUADs8EiISIhwmFhwaU0IkEjkZXUQZFT9fWisgHyQlJxotUEEyWmhwUz0aGlsMVDxQASZ7BiY4Ol1wUUhcFUJwU2pSUxdJVCFXUhg7HSgwKhAnWBxQHyZwAS8GBkUHVC1fFkd1UWdxblVjWAFeWg48Ei0BXVYcACdzBzQbFD8lFBotHUhZFCxwKSUcFkQ6ETpHGy4wMis4Kxs3WBxQHyZaU2pSUxdJVGgRUm11ASQwIhlrHh1WGTw5HCRaWj1JVGgRUm11UWdxblVjWEgYFiczEiZSFUIbACBUATl1TGcLIRsmCztdCD45EC8xH14MGjwLFSghNzIjOh0mCxxiFSY1W2N4UxdJVGgRUm11UWdxblVjWARXGSk8UyQXC0MzGyZUUnB1WSEkPAErHRtMWiciU3pbUxxJRUIRUm11UWdxblVjWEgYWmhwGixSHVIRABJeHCh1TXpxekVjDABdFEJwU2pSUxdJVGgRUm11UWdxblVjWDJXFC0jIC8ABV4KEQtdGyg7BX0hOwcgEAlLHxI/HS9aHVIRABJeHCh8e2dxblVjWEgYWmhwU2pSUxcMGiw7Um11UWdxblVjWEgYHyY0WkBSUxdJVGgRUig7FU1xblVjHQZccC0+F2N4eRpEVAZeMSE8AWc9IRozchxZGCQ1XSMcAFIbAGByHSM7FCQlJxotC0QYKD0+IC8ABV4KEWZiBiglASI1dDYsFgZdGTx4FT8cEEMAGyYZW0d1UWdxJxNjLQZUFSk0Fi5SB18MGmhDFzkgAylxKxsnckgYWmg5FWo0H1YOB2ZfHQ45GDdxLxsnWCRXGSk8IyYTClIbWgtZEz80EjM0PFU3EA1WcGhwU2pSUxdJEidDUhJ5UTcwPAFjEQYYEzgxGjgBW3sGFyldIiE0CCIjYDYrGRpZGTw1AXA1FkMtETtSFyMxECklPV1qUUhcFUJwU2pSUxdJVGgRUm08F2chLwc3QiFLO2ByMSsBFmcIBjwTW20hGSI/RFVjWEgYWmhwU2pSUxdJVGhBEz8hXwQwIDYsFARRHi1wTmoUElsaEUIRUm11UWdxblVjWEhdFCxaU2pSUxdJVGhUHClfUWdxbhAtHGJdFCx5WkB4XhpJJC1DASQmBWciPhAmHEdSDyUgUyUcU0UMBzhQBSNfBSYzIhBtEQZLHzokWwkdHVkMFzxYHSMmXWcdIRYiFDhUGzE1AWQxG1YbFStFFz8UFSM0Kk8AFwZWHyskWywHHVQdHSdfWi49EDV4RFVjWEhMGzs7XT0TGkNBRGYEW0d1UWdxIhogGQQYEj09U3dSEF8IBnJ3GyMxNy4jPQEAEAFUHgc2MCYTAERBVgBEHyw7Hi41bFxJWEgYWiE2UyIHHhcdHC1feG11UWdxblVjEQ4YPCQxFDlcBFYFHxtBFygxUTlsbkdxWBxQHyZwGz8fXWAIGCNiAigwFWdsbjMvGQ9LVD8xHyEhA1IMEGhUHClfUWdxblVjWEhRHGgWHysVABkDASVBIiIiFDVxMEhjTVgYDiA1HWoaBlpHPj1cAh06BiIjbkhjPgRZHTt+GT8fA2cGAy1DUig7FU1xblVjHQZccC0+F2NbeT1EWWceUgEcJwJxHSECLDsYNgcfI0AGEkQCWjtBEzo7WSEkIBY3EQdWUmFaU2pSU0ABHSRUUjk0Aix/ORQqDEAJVH15Uy4deRdJVGgRUm11GCFxGxsvFwlcHyxwByIXHRcbETxEACN1FCk1RFVjWEgYWmhwAykTH1tBEj1fETk8Hil5Z39jWEgYWmhwU2pSUxcFGytQHm0xUXpxKRA3PAlMG2B5eWpSUxdJVGgRUm11USs+LRQvWAtXEyYjU2pSUwpJACdfByA3FDV5KlsgFwFWCWFwHDhSQz1JVGgRUm11UWdxblUvFwtZFmg3HCUCUxdJVGgMUjk6HzI8LBAxUAwWHSc/A2NSHEVJREIRUm11UWdxblVjWEhUFSsxH2oIHFkMVGgRUm1oUTM+IAAuGg1KUix+CSUcFh5JGzoRQ0d1UWdxblVjWEgYWmg8HCkTHxcEFTBrHSMwUWdsbgEsFh1VGC0iWy5cHlYRLidfF2R1HjVxf39jWEgYWmhwU2pSUxcFGytQHm0nFCU4PAErC0gFWjw/HT8fEVIbXCwfACg3GDUlJgZqWAdKWnhaU2pSUxdJVGgRUm11HSgyLxljCgdUFgslAWpSThcdGyZEHy8wA281YAcsFAR7DzoiFiQRCh5JGzoRQkd1UWdxblVjWEgYWmg8HCkTHxccBC9DEykwAmdsbgE6CA0QHmYlAy0AElMMB2ERT3B1UzMwLBkmWkhZFCxwF2QHA1AbFSxUAW06A2cqM39jWEgYWmhwU2pSUxcFGytQHm0wADI4PgUmHEgFWjwpAy9aFxkMBT1YAj0wFW5xc0hjWhxZGCQ1UWoTHVNJEGZUAzg8ATc0KlUsCkhDB0JwU2pSUxdJVGgRUm05HiQwIlUwDAlMCWhwU2pPU0MQBC0ZFmMmBSYlPVxjRVUYWDwxESYXURcIGiwRFmMmBSYlPVUsCkhDB0JwU2pSUxdJVGgRUm05HiQwIlUwChgYWmhwU2pPU0MQBC0ZFmMmASIyJxQvKgdUFhgiHC0AFkQaHSdfW21oTGdzOhQhFA0aWik+F2oWXUQZEStYEyEHHis9HgcsHxpdCTs5HCRSHEVJDzU7eG11UWdxblVjWEgYWiQyHwkdGlkaThtUBhkwCTN5bDYsEQZLQGhyU2RcU1EGBiVQBgMgHG8yIRwtC0ERcGhwU2pSUxdJVGgRUiE3HQA+IQV5Kw1MLi0oB2JQNFgGBHIRUG17X2c3IQcuGRx2DyV4FCUdAx5AfmgRUm11UWdxblVjWARaFhI/HS9IIFIdIC1JBmV3MjIjPBAtDEhiFSY1SWpQUxlHVDJeHCh8e2dxblVjWEgYWmhwUyYQH3oIDBJeHChvIiIlGhA7DEAaNykoUxAdHVJTVGoRXGN1HCYpFBotHUEyWmhwU2pSUxdJVGgRHi85IyIzJwc3EBsCKS0kJy8KBx9LJi1TGz8hGTRrbldjVkYYCC0yGjgGG0RAfmgRUm11UWdxblVjWARaFh0gFDgTF1IaThtUBhkwCTN5bCAzHxpZHi0jUyUFHVINTmgTUmN7UTMwLBkmNA1WUj0gFDgTF1IaXWE7Um11UWdxblVjWEgYFio8NjsHGkcZESwLISghJSIpOl1hKwRRFy0jUy8DBl4ZBC1VSG13UWl/bgEiGgRdNi0+Wy8DBl4ZBC1VW2RfUWdxblVjWEgYWmhwHygeIVgFGAtEAHcGFDMFKw03UEpqFSQ8UwkHAUUMGitISG13UWl/bgcsFAR7Dzp5eUBSUxdJVGgRUm11UWc9LBkXFxxZFho/HyYBSWQMABxUCjl9UxM+OhQvWDpXFiQjSWpQUxlHVC5eACA0BQkkI10wDAlMCWYiHCYeABcGBmgBW2RfUWdxblVjWEgYWmhwHygeIFIaByFeHB86HSsidCYmDDxdAjx4URkXAEQAGyYRICI5HTRrbldjVkYYHCciHisGPUIEXDtUAT48HikDIRkvC0ERcEJwU2pSUxdJVGgRUm05HiQwIlUlDQZbDiE/HWoUHkM6BC1SGyw5WSw0N1ljFAlaHyR5eWpSUxdJVGgRUm11UWdxblUvFwtZFmg1HT4AChdUVDtDAhY+FD4MRFVjWEgYWmhwU2pSUxdJVGhYFG0hCDc0ZhAtDBpBU2htTmpQB1YLGC0TUjk9FClbblVjWEgYWmhwU2pSUxdJVGgRUm05HiQwIlU2FhxRFhdwTmoXHUMbDWZDHSE5AhI/OhwvNg1ADmg/AWoXHUMbDWZDHSE5AhI/OhwvWAdKWmpvUUBSUxdJVGgRUm11UWdxblVjWEgYWjo1Bz8AHRcFFSpUHm17X2dzbhwtQkgaWmZ+Uz4dAEMbHSZWWjg7BS49EVxjVkYYWGgiHCYeABVjVGgRUm11UWdxblVjWEgYWi0+F0BSUxdJVGgRUm11UWdxblVjCg1MDzo+UyYTEVIFVGYfUm91GClrblhuWmIYWmhwU2pSUxdJVGhUHClfe2dxblVjWEgYWmhwUyYQH3AGGCxUHHcGFDMFKw03UA5VDhsgFikbEltBVi9eHikwH2V9blcEFwRcHyZyWmN4UxdJVGgRUm11UWdxIhcvPAFZFyc+F3AhFkM9ETBFWis4BRQhKxYqGQQQWCw5EicdHVNLWGgTNiQ0HCg/KldqUWIYWmhwU2pSUxdJVGhdECEDHi41dCYmDDxdAjx4FScGIEcMFyFQHmV3Byg4KldvWEpuFSE0UWNbeRdJVGgRUm11UWdxbhkhFC9ZFikoCnAhFkM9ETBFWis4BRQhKxYqGQQQWC8xHysKChVFVGp2EyE0CT5zZ1xJckgYWmhwU2pSUxdJVCFXUj4hEDMiYAciCg1LDho/HyZSElkNVDtFEzkmXzUwPBAwDDpXFiR+ACYbHlItFTxQUjk9FClbblVjWEgYWmhwU2pSUxdJVCReESw5US41blVjRUhLDikkAGQAEkUMBzxjHSE5XzQ9JxgmPAlMG2Y5F2odARdLS2o7Um11UWdxblVjWEgYWmhwUyYdEFYFVCdVFj51TGciOhQ3C0ZKGzo1AD4gHFsFWidVFj51HjVxf39jWEgYWmhwU2pSUxdJVGgRHi85IyYjKwY3QjtdDhw1Cz5aUWUIBi1CBm0HHis9dFVhWEYWWiE0U2RcUxVJXHkeUG17X2clIQY3CgFWHWA/Fy4BWhdHWmgTW298e2dxblVjWEgYWmhwUy8cFz1jVGgRUm11UWdxblVjEQ4YKC0yGjgGG2QMBj5YESgABS49PVU3EA1WcGhwU2pSUxdJVGgRUm11UWc9IRYiFEhbFTskU3dSIVILHTpFGh4wAzE4LRAWDAFUCWY3Fj4xHEQdXDpUECQnBS8iZ1UsCkgIcGhwU2pSUxdJVGgRUm11UWc9IRYiFEhUDys7Pj8eUwpJJi1TGz8hGRQ0PAMqGw1tDiE8AGQVFkMlAStaPzg5BS4hIhwmCkBKHyo5AT4aAB5JGzoRQ0d1UWdxblVjWEgYWmhwU2pSH1UFJi1TGz8hGQQ+PQF5Kw1MLi0oB2JQIVILHTpFGm0WHjQldFVhWEYWWi4/AScTB3kcGWBSHT4hWGd/YFVhWA9XFThyWkBSUxdJVGgRUm11UWdxblVjFApUNj0zGAcHH0NTJy1FJigtBW9zAgAgE0h1DyQkGjoeGlIbTmhJUG17X2ciOgcqFg8WHCciHisGWxVMWnpXUGF1HTIyJTg2FEERcGhwU2pSUxdJVGgRUm11UWc9LBkRHQpRCDw4IS8TF05TJy1FJigtBW9zHBAhERpMEmgCFisWCg1JVmgfXG19Fig+PlV9RUhbFTskUyscFxdLLQ1iUG06A2dzADpjUAZdHyxwUWpcXRcPGzpcEzkbBCp5IxQ3EEZVGzB4Q2ZSEFgaAGgcUio6Hjd4Z1VtVkgaU2p5WkBSUxdJVGgRUm11UWc0IBFJWEgYWmhwU2oXHVNAfmgRUm0wHyNbKxsnUWIyNiEyASsACg0nGzxYFDR9UxQ9JxgmWDp2PWgDEDgbA0NJGCdQFigxUGcBPBAwC0hqEy84BwkGAVtJEidDUhgcX2V9bkBqcg=='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2 })
