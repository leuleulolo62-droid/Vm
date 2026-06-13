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

local __k = 'U5RQKsbBI2l1uiamEQof5GQX'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
