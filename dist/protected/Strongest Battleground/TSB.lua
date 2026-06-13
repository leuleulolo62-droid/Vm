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

local __k = 'Do1f0m4KNPaeCiUobMngxXKH'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2 })
