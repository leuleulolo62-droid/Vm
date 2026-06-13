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

local __k = 'wlbZLLegsyjpKo8O9gih7HY0'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, antiSpy = { kick = true, halt = true, remote = false, dex = false } })
