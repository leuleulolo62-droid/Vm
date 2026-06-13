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

local __k = '83MgSPNntq6aVEUrZRE16617'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2 })
