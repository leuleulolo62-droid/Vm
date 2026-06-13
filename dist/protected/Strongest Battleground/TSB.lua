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

local __k = 'dh6gZHIh5ynAfSIwTMKrZus8'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2 })
