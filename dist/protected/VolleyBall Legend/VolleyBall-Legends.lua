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

local __k = 'PKexHUoxTcrOtK5rogcEFO5m'
local __p = 'fWY+I0K3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxdtvWGh1Ty4bLz4KLQl0PiNHLwABCnspA2tFmsjBT1gNUTlvPB53Uk8RUmt2YQVNcGtFWGh1T1h0Q1JvVGsVUk9HSzYvIVIBNWYDESQwTxohCh4rXUEVUk9HMjAnI1wZKWYKHmU5Bh4xQxo6FmtTHR1HMyknLFAkNGtSTH5sXk5sUkJ8TXkCQU9PNSoqI1AUMioJFGgSDhUxQzU9Gz5FW2VHQ2VmGnxXcGtFWAc3HBEwChMhISIVWjZVKGUVLEcEID9FOik2BEoWAhEkXUEVUk9HMDE/I1BXcAUAFyZ1NkofT1I8GSRaBgdHFzIjKlsefGsDDSQ5Tws1FRdgACNQHwpHEDA2P1ofJEFvWGh1TykBKjEEVBhhMz0zQ6fG2xUdMTgRHWg8AQw7QxMhDWtnHQ0LDD1mKk0IMz4RFzp1DhYwQwA6GmU/eE9HQ2USLlceakFFWGh1T1i249BvNipZHk9HQ2VmbxWP0N9FLDo0BR03Fx09DWtFAAoDCiYyJloDfGsJGSYxBhYzQx8uBiBQAENHAjAyIBgdPzgMDCE6AXJ0Q1JvVGvX8s1HMyknNlAfcGtFWGi37+x0MAIqES8aOBoKE2oOJkEPPzNKPiQsQDk6FxtiNQ1+eE9HQ2Vmb9ft8msgKxh1T1h0Q1JvVKm15k83DyQ/KkcecGMRHSk4Qhs7Dx09ES8cXk8FAikqYxUOPz4XDGgvABYxEHhvVGsVUk+F4+dmAlweM2tFWGh1T1i24+ZvOCJDF08UFyQyPBlNIy4XDi0nTwoxCR0mGmRdHR9LQwMJGRUYPicKGyNfT1h0Q1JvlsuXUiwIDSMvKEZNcGtFmsjBTys1FRcCFSVUFQoVQzU0KkYIJGsWFCchHHJ0Q1JvVGvX8s1HMCAyO1wDNzhFWGi37+x0NjtvBDlQFBxHSGUnLEEEPyVFECchBB0tEFJkVD9dFwICQzUvLF4IIkFFWGh1T1i249BvNzlQFgYTEGVmbxWP0N9FOSo6Ggx0SFI7FSkVFRoOByBMRRVNcGuH4uh1OxA9EFIoFSZQUhoUBjZmFXQ9cCUADD86HRM9DRVvXDhQAAYGDyw8KlFNICocFCc0Cwt0Fxo9Gz5SGk9VQzcjIloZNThMVkJ1T1h0Q1JvICNQUhwEESw2OxULPygQCy0mTxc6QxEjHS5bBkIUCiEjb2QCHGsKFiQsT5rU91IhG2tTEwQCQyQlO1wCPjhFGTowTwsxDQZhfqmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB83gSKUE/GwlHPAJoFgcmDx0qNAQQNiccNjAQOAR0NiojQzEuKltncGtFWD80HRZ8QSkWRgAVOhoFPmUHI0cIMS8cWCQ6DhwxB1Kt9N8VEQ4LD2UKJlcfMTkcQh07Axc1B1pmVC1cABwTTWdvRRVNcGsXHTwgHRZeBhwrfhRyXDZVKBoQAHkhFRI6MB0XMDQbIjYKMGsIUhsVFiBMRVkCMyoJWBg5DgExEQFvVGsVUk9HQ2VmchUKMSYAQg8wGysxEQQmFy4dUD8LAjwjPUZPeUEJFys0A1gGBgIjHShUBgoDMDEpPVQKNXZFHyk4CkITBgYcETlDGwwCS2cUKkUBOSgEDC0xPAw7ERMoEWkceAMIACQqb2cYPhgACj48DB10Q1JvVGsVT08AAigjdXIIJBgACj48DB18QSA6GhhQABkOACBkZj8BPygEFGgCAAo/EAIuFy4VUk9HQ2VmbwhNNyoIHXISCgwHBgA5HShQWk0wDDctPEUMMy5HUUI5ABs1D1IaBy5HOwEXFjEVKkcbOSgAWHV1CBk5BkgIET9mFx0RCiYjZxc4Iy4XMSYlGgwHBgA5HShQUEZtDyolLllNHCICEDw8AR90Q1JvVGsVUk9aQyInIlBXFy4RKy0nGRE3BlptOCJSGhsODSJkZj8BPygEFGgDBgogFhMjIThQAE9HQ2VmbwhNNyoIHXISCgwHBgA5HShQWk0xCjcyOlQBBTgACmp8ZRQ7ABMjVAdaEQ4LMyknNlAfcGtFWGh1UlgEDxM2ETlGXCMIACQqH1kMKS4XckI8CVg6DAZvEypYF1UuEAkpLlEINGNMWDw9ChZ0BBMiEWV5HQ4DBiF8GFQEJGNMWC07C3JeTl9vlt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWRRhAcHpLWAsaIT4dJHhiWWvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qVnPCQGGSR1LBc6BRsoVHYVCRJtICooKVwKfgwkNQ0KITkZJlJvSWsXJAALDyA/LVQBPGspHS8wARwnQXgMGyVTGwhJMwkHDHAyGQ9FWGhoT09gVUt+QnMEQlxeUXJ1RXYCPi0MH2YWPT0VNz0dVGsVUlJHQRMpI1kIKSkEFCR1KBk5BlIIBiRAAk1tICooKVwKfhgmKgEFOycCJiBvSWsXQ0FXTXVkRXYCPi0MH2YAJicGJiIAVGsVUlJHQS0yO0UeamRKCikiQR89Fxo6Fj5GFx0EDCsyKlsZfigKFWcMXRMHAAAmBD93EwwMUQcnLF5CHykWESw8DhYBCl0iFSJbXU1tICooKVwKfhgkLg0KPTcbN1JvSWsXJAALDyA/LVQBPAcAHy07Cwt2aTEgGi1cFUE0IhMDEHYrFxhFWHV1TS47Dx4qDSlUHgMrBiIjIVEefygKFi48CAt2aTEgGi1cFUEzLAIBA3AyGw48WHV1TSo9BBo7NyRbBh0ID2dMDFoDNiICVgkWLD0aN1JvVGsVT08kDCkpPQZDNjkKFRoSLVBkT1J9RXsZUl1VWmxMRRhAcAwXGT48GwF0FgEqEGtTHR1HDyQoK1wDN2sVCi0xBhsgCh0hWkEYX0+F+eVmGVoBPC4cGik5A1gYBhUqGi9GUhoUBjZmDGA+BAQoWCo0AxR0BAAuAiJBC09PHXRxb0YZJS8WVzuX3Vg7AQEqBj1QFkZHBSo0RRhAcCpFHiQ6DgwtQxQqEScVkO/zQwsJGxU/PykJFzB1Cx0yAgcjAGsES1lJUWtmC1ALMT4JDGghAFg1QwAqFThaHA4FDyBmIlwJNCcAWCk7C3J5TlIqDDtaAQpHAmU1I1wJNTlFCyd1GgsxEQFvFypbUhsSDSBmJkFNNjkKFWghBx10NjthfghaHAkOBGsBHXQ7GR88WGh1T0V0VkJFfmYYUo3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wEFIVWhnQVgBNzsDJ0EYX0+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxdtvFCc2DhR0NgYmGDgVT08cHk9MKUADMz8MFyZ1Ogw9DwFhEy5BMQcGEW1vRRVNcGsJFys0A1g3CxM9VHYVPgAEAikWI1QUNTlLOyA0HRk3Fxc9fmsVUk8OBWUoIEFNMyMECmghBx06QwAqAD5HHE8JCilmKlsJWmtFWGg5ABs1D1InBjsVT08ECyQ0dXMEPi8jETomGzs8Ch4rXGl9BwIGDSovK2cCPz81GTohTVFeQ1JvVCdaEQ4LQy0zIhVQcCgNGTpvKRE6BzQmBjhBMQcODyEJKXYBMTgWUGodGhU1DR0mEGkceE9HQ2UvKRUFIjtFGSYxTxAhDlI7HC5bUh0CFzA0IRUOOCoXVGg9HQh4Qxo6GWtQHAttBisiRT8LJSUGDCE6AVgBFxsjB2VBFwMCEyo0Ox0dPzhMcmh1T1g4DBEuGGtqXk8PETVmchU4JCIJC2YyCgwXCxM9XGI/Uk9HQywgb10fIGsEFix1HxcnQwYnESUVGh0XTQYAPVQANWtYWAsTHRk5BlwhETwdAgAUSn5mPVAZJTkLWDwnGh10BhwrfmsVUk8VBjEzPVtNNioJCy1fChYwaXgpASVWBgYIDWUTO1wBI2UJFyclRx8xFzshAC5HBA4LT2U0OlsDOSUCVGgzAVFeQ1JvVD9UAQRJEDUnOFtFNj4LGzw8ABZ8SnhvVGsVUk9HQzIuJlkIcDkQFiY8AR98SlIrG0EVUk9HQ2VmbxVNcGsJFys0A1g7CF5vETlHUlJHEyYnI1lFNiVMcmh1T1h0Q1JvVGsVUgYBQyspOxUCO2sREC07Tw81ERxnVhBsQCQ6QykpIEVXcGlFVmZ1GxcnFwAmGiwdFx0VSmxmKlsJWmtFWGh1T1h0Q1JvVCdaEQ4LQyEybwhNJDIVHWAyCgwdDQYqBj1UHkZHXnhmbVMYPigRESc7TVg1DRZvEy5BOwETBjcwLllFeWsKCmgyCgwdDQYqBj1UHmVHQ2VmbxVNcGtFWGghDgs/TQUuHT8dFhtOaWVmbxVNcGtFHSYxZVh0Q1IqGi8ceAoJB09MKUADMz8MFyZ1Ogw9DwFhECJGBg4JACBuLhlNMmJFCi0hGgo6Q1ouVGYVEEZJLiQhIVwZJS8AWC07C3JeTl9vlt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWRRhAcHhLWAoUIzR0gfLbVC1cHAtHDywwKhUPMScJVGglHR0wChE7VCdUHAsODSJMYhhNst71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3EaV9iVAJ4IiA1NwQIGw9NJCMAWCo0AxR0CgFvFSVWGgAVBiFmIFtNJCMAWCs5Bh06F1JnBy5HBAoVQwYAPVQANWYWASY2HFg9F1tjVDhaeEJKQwQ1PFAAMiccNCE7ChkmNRcjGyhcBhZHCjZmLlkaMTIWWHh7Ty8xQxEgGTtABgpHFSAqIFYEJDJFGjF1HBk5Ex4mGiwVAgAUCjEvIFsefkEJFys0A1gWAh4jVHYVCWVHQ2VmEFkMIz81Fzt1T1h0Q09vGiJZXmVHQ2VmEFkMIz8xESs+T1h0Q09vRGc/Uk9HQxowKlkCMyIRAWh1T1hpQyQqFz9aAFxJDSAxZxxBWmtFWGh4QlgXAhEnES8VAAoBBjcjIVYII2uH+Nx1Dg47ChZvByhUHAEODSJmGFofOzgVGSswTx0iBgA2VANQEx0TASAnOxVFZnum72cmRnJ0Q1JvKyhUEQcCBwgpK1ABcHZFFiE5Q3J0Q1JvKyhUEQcCBxUnPUFNcHZFFiE5Q3IpaXhiWWt5GxwTBitmKVofcCkEFCR1HAg1FBxgEC5GAg4QDWU1IBUaNWsBFyZyG1gkDB4jVBxaAAQUEyQlKhUIJi4XAWgzHRk5BlxFGCRWEwNHBTAoLEEEPyVFETsXDhQ4Lh0rEScdGwEUF2xMbxVNcDkADD0nAVg9DQE7TgJGM0dFLioiKllPeWsEFix1HAwmChwoWi1cHAtPCis1OxsjMSYAVGh3LDQdJjwbKwl0PiNFT2V3YxUZIj4AUUIwARxeaSUgBiBGAg4EBmsFJ1wBNAoBHC0xVTs7DRwqFz8dFBoJADEvIFtFM2JvWGh1TxEyQxs8NipZHiIIByAqZ1ZEcD8NHSZfT1h0Q1JvVGtZHQwGD2U2LkcZcHZFG3ITBhYwJRs9Bz92GgYLBxIuJlYFGTgkUGoXDgsxMxM9AGkZUhsVFiBvRRVNcGtFWGh1Bh50DR07VDtUABtHFy0jIT9NcGtFWGh1T1h0Q1JiWWtiEwYTQyc0JlALPDJFHicnTxs8Ch4rVDtUABsUQzEpb0cIICcMGykhCnJ0Q1JvVGsVUk9HQ2U2LkcZcHZFG2YWBxE4BzMrEC5RSDgGCjFuZj9NcGtFWGh1T1h0Q1ImEmtFEx0TQyQoKxUDPz9FCCknG0IdEDNnVglUAQo3AjcybRxNJCMAFkJ1T1h0Q1JvVGsVUk9HQ2VmP1QfJGtYWCtvKRE6BzQmBjhBMQcODyERJ1wOOAIWOWB3LRknBiIuBj8XXk8TETAjZj9NcGtFWGh1T1h0Q1IqGi8/Uk9HQ2VmbxUIPi9vWGh1T1h0Q1ImEmtFEx0TQzEuKltncGtFWGh1T1h0Q1JvNipZHkE4ACQlJ1AJHSQBHSR1Ulg3aVJvVGsVUk9HQ2Vmb3cMPCdLJys0DBAxByIuBj8VUlJHEyQ0Oz9NcGtFWGh1Tx06B3hvVGsVFwEDaSAoKxxnByQXEzslDhsxTTEnHSdRIAoKDDMjKw8uPyULHSshRx4hDRE7HSRbWgxOaWVmbxUENmsGWHVoTzo1Dx5hKyhUEQcCBwgpK1ABcD8NHSZfT1h0Q1JvVGt3EwMLTRolLlYFNS8oFywwA1hpQxwmGHAVMA4LD2sZLFQOOC4BKCknG1hpQxwmGEEVUk9HQ2Vmb3cMPCdLJyQ0HAwEDAFvSWtbGwNcQwcnI1lDDz0AFCc2BgwtQ09vIi5WBgAVUGsoKkJFeUFFWGh1ChYwaRchEGI/eEJKQxcjO0AfPmsGGSs9Chx0ERcpETlQHAwCEGUxJ1ADcDsKCzs8DRQxTVIAGidMUhwEAitmOF0IPmsGGSs9Clg9EFIqGTtBC0FtBTAoLEEEPyVFOik5A1YyChwrXGI/Uk9HQ2hrb3MMIz9FCCkhB0J0ABMsHC4VGgYTaWVmbxUENmsnGSQ5QSc3AhEnES94HQsCD2UnIVFNEioJFGYKDBk3CxcrOSRRFwNJMyQ0KlsZWmtFWGh1T1h0AhwrVAlUHgNJPCYnLF0INBsECjx1Txk6B1INFSdZXDAEAiYuKlE9MTkRVhg0HR06F1I7HC5beE9HQ2VmbxVNIi4RDTo7Tzo1Dx5hKyhUEQcCBwgpK1ABfGsnGSQ5QSc3AhEnES9lEx0TaWVmbxUIPi9vWGh1T1V5QyEjGzwVAg4TC39mPFYMPmsRFzh4Ax0iBh5vGyVZC09PBCQrKhUeICoSFjt1DRk4D1IuAGtCHR0MEDUnLFBNIiQKDGFfT1h0QxQgBmtqXk8EQywob1wdMSIXC2ACAAo/EAIuFy4PNQoTIC0vI1EfNSVNUWF1CxdeQ1JvVGsVUk8OBWUvPHcMPCcoFywwA1A3SlI7HC5beE9HQ2VmbxVNcGtFWCQ6DBk4QwIuBj8VT08EWQMvIVErOTkWDAs9BhQwNBomFyN8AS5PQQcnPFA9MTkRWmR1GwohBltFVGsVUk9HQ2VmbxVNOS1FCCknG1ggCxchfmsVUk9HQ2VmbxVNcGtFWGgXDhQ4TS0sFShdFwsqDCEjIxVQcChvWGh1T1h0Q1JvVGsVUk9HQwcnI1lDDygEGyAwCyg1EQZvVHYVAg4VF09mbxVNcGtFWGh1T1h0Q1JvBi5BBx0JQyZqb0UMIj9vWGh1T1h0Q1JvVGsVFwEDaWVmbxVNcGtFHSYxZVh0Q1IqGi8/Uk9HQzcjO0AfPmsLESRfChYwaXgpASVWBgYIDWUELlkBfjsKCyEhBhc6S1tFVGsVUgMIACQqb2pBcDsECjx1UlgWAh4jWi1cHAtPSk9mbxVNIi4RDTo7Twg1EQZvFSVRUh8GETFoH1oeOT8MFyZfChYwaXhiWWtnFxsSESs1b0EFNWsTHSQ6DBEgGlI5EShBHR1JQxcjLFoAID4RHSx1CQo7DlI8FSZFHgoDQzUpPFwZOSQLC2gwGR0mGlIpBipYF2VKTmVuK0cEJi4LWCosTww8BlI5ESdaEQYTGmUyPVQOOy4XWCQ6AAh0ARcjGzwcXE8hAikqPBUPMSgOWDw6TzknEBciFidMPgYJBiQ0GVABPygMDDFfQlV0ChRvACNQUh8GETFmJ1QdIC4LC2ghAFg1AAY6FSdZC08PAjMjb0UFKTgMGzt7ZR4hDRE7HSRbUi0GDyloOVABPygMDDF9RnJ0Q1JvGCRWEwNHPGlmP1QfJGtYWAo0AxR6BRshEGMceE9HQ2UvKRUDPz9FCCknG1ggCxchVDlQBhoVDWUQKlYZPzlWViYwGFB9QxchEEEVUk9HDyolLllNMSgRDSk5T0V0ExM9AGV0ARwCDicqNnkEPi4ECh4wAxc3CgY2fmsVUk8OBWUnLEEYMSdLNSkyAREgFhYqVHUVQkFWQzEuKltNIi4RDTo7Txk3FwcuGGtQHAttQ2Vmb0cIJD4XFmgXDhQ4TS05ESdaEQYTGk8jIVFnWmZIWAkgGxd5Bxc7EShBFwtHBDcnOVwZKWtNCyU6AAw8BhZmWmtiGgoJQwQzO1pANC4RHSshTxEnQx0hWGt2HQEBCiJoCGcsBgIxIUJ4Qlg9EFI9ETtZEwwCB2UkNhUZOCIWWCc7Tx0iBgA2VDtHFwsOADEvIFtDWgkEFCR7MBwxFxcsAC5RNR0GFSwyNhVQcCUMFEJfQlV0KxcuBj9XFw4TQzYnIkUBNTlLWAc7AwF0Bx0qB2tCHR0MQzIuKltNJCMAWCo0AxR0AhE7ASpZHhZHBj0vPEEefkFIVWgCBx06QwYnEWtXEwMLQyw1b1ICPi5JWCEhTwoxFwc9GjgVGwEUFyQoO1kUcGMGGSs9Clg3CxcsH2tcAU8oS3RvZhtnNj4LGzw8ABZ0IRMjGGVGBg4VFxMjI1oOOT8cLDo0DBMxEVpmfmsVUk8OBWUELlkBfhQRCik2BB0mMAYuBj9QFk8TCyAob0cIJD4XFmgwARxeQ1JvVAlUHgNJPDE0LlYGNTk2DCknGx0wQ09vADlAF2VHQ2VmI1oOMSdFFCkmGy4taVJvVGtnBwE0BjcwJlYIfgMAGTohDR01F0gMGyVbFwwTSyMzIVYZOSQLUCwhRnJ0Q1JvVGsVUkJKQwMnPEFAIyAMCGgiBx06QxwgVClUHgNHgcXSb1YMMyMAWCs9Chs/Qxs8VCFAARtHFzIpbxs9MTkAFjx1HR01BwFFVGsVUk9HQ2UvKRUDPz9FUAo0AxR6PBEuFyNQFiIIByAqb1QDNGsnGSQ5QSc3AhEnES94HQsCD2sWLkcIPj9vWGh1T1h0Q1JvVGsVEwEDQwcnI1lDDygEGyAwCyg1EQZvFSVRUi0GDyloEFYMMyMAHBg0HQx6MxM9ESVBW08TCyAoRRVNcGtFWGh1T1h0Q19iVBlQAQoTQzYyLkEIcDgKWDw9Clg6Bgo7VClUHgNHEDEnPUEecC0XHTs9ZVh0Q1JvVGsVUk9HQywgb3cMPCdLJyQ0HAwEDAFvACNQHGVHQ2VmbxVNcGtFWGh1T1h0IRMjGGVqHg4UFxUpPBVQcCUMFEJ1T1h0Q1JvVGsVUk9HQ2VmDVQBPGU6Di05ABs9FwtvSWtjFwwTDDd1YVsIJ2NMcmh1T1h0Q1JvVGsVUk9HQ2UqLkYZBjJFRWg7BhReQ1JvVGsVUk9HQ2VmKlsJWmtFWGh1T1h0Q1JvVDlQBhoVDU9mbxVNcGtFWC07C3J0Q1JvVGsVUgMIACQqb0UMIj9FRWgXDhQ4TS0sFShdFws3AjcyRRVNcGtFWGh1Axc3Ah5vGiRCUlJHEyQ0Oxs9PzgMDCE6AXJ0Q1JvVGsVUgMIACQqb0FNbWsRESs+R1FeQ1JvVGsVUk8OBWUELlkBfhQJGTshPxcnQxMhEGt3EwMLTRoqLkYZBCIGE2hrT0h0FxoqGkEVUk9HQ2VmbxVNcGsJFys0A1gxDxM/By5RUlJHF2Vrb3cMPCdLJyQ0HAwAChEkfmsVUk9HQ2VmbxVNcCIDWC05DggnBhZvSmsFUg4JB2UjI1QdIy4BWHR1X1ZhQwYnESU/Uk9HQ2VmbxVNcGtFWGh1TxQ7ABMjVD0VT09PDSoxbxhNEioJFGYKAxknFyIgB2IVXU8CDyQ2PFAJWmtFWGh1T1h0Q1JvVGsVUk8lAikqYWobNScKGyEhFlhpQzAuGCcbLRkCDyolJkEUagcACjh9GVR0U1x5XUEVUk9HQ2VmbxVNcGtFWGh1Bh50DxM8AB1MUhsPBitMbxVNcGtFWGh1T1h0Q1JvVGsVUk8LDCYnIxUMMygAFGhoT1AiTStvWWtZExwTNTxvbxpNNScECDswC3J0Q1JvVGsVUk9HQ2VmbxVNcGtFWCQ6DBk4QxVvSWsYEwwEBilMbxVNcGtFWGh1T1h0Q1JvVGsVUk8OBWUhbwtNZWsEFix1CFhoQ0F/RGtUHAtHFWsLLlIDOT8QHC11UVhhQwYnESU/Uk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVMA4LD2sZK1AZNSgRHSwSHRkiCgY2VHYVMA4LD2sZK1AZNSgRHSwSHRkiCgY2fmsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUk8GDSFmZ3cMPCdLJywwGx03FxcrMzlUBAYTGmVsbwVDaXlFU2gyT1J0U1x/TGI/Uk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUk9HQyo0b1JncGtFWGh1T1h0Q1JvVGsVUk9HQ2UjIVFncGtFWGh1T1h0Q1JvVGsVUgoJB09mbxVNcGtFWGh1T1h0Q1JvGCpGBjkeQ3hmORs0WmtFWGh1T1h0Q1JvVC5bFmVHQ2VmbxVNcC4LHEJ1T1h0Q1JvVAlUHgNJPCknPEE9PzhFRWg7AA9eQ1JvVGsVUk8lAikqYWoBMTgRLCE2BFhpQwZFVGsVUgoJB2xMKlsJWkFIVWgFHR0wChE7VDxdFx0CQzEuKhUPMScJWD88AxR0DxMhEGtUBk8eQ3hmO1QfNy4RIWggHBE6BFI/HDJGGwwUWU9rYhVNcDJNDGF1UlgtU1JkVD1MWBtHTmUhZUGv4mRXWGh1T1h8BAAuAiJBC08GADE1b1ECJyUSGToxRnJ5TlIdESpHAA4JBCAib1MCImsREC11Hg01BwAuACJWUgkIESgzI1RXWmZIWGh1Rx97UVtlAImHUkRHS2gwNhxHJGtOWGAhDgozBgYWVGYVC19OQ3hmfz9AfWs3HTwgHRYnQwYnEWtZEwEDCishb0UCIyIRESc7Txk6B1I7HSZQXxsITiknIVFNeDgAGyc7Cwt9TXgpASVWBgYIDWUELlkBfjsXHSw8DAwYAhwrHSVSWhsGESIjO2xEWmtFWGg5ABs1D1IQWGtFEx0TQ3hmDVQBPGUDESYxR1FeQ1JvVCJTUgEIF2U2LkcZcD8NHSZ1HR0gFgAhVCVcHk8CDSFMbxVNcCcKGyk5Twh0XlI/FTlBXD8IECwyJloDWmtFWGg5ABs1D1I5VHYVMA4LD2swKlkCMyIRAWB8ZVh0Q1ImEmtDXCIGBCsvO0AJNWtZWHh7XlggCxchVDlQBhoVDWUoJllNNSUBWGV4Txo1Dx5vHTgVExtHESA1Oz9NcGtFDCknCB0gOlJyVD9UAAgCFxxmIEdNIGU8WGV1Xk1eQ1JvVGYYUjoUBmUnOkECfS8ADC02Gx0wQxU9FT1cBhZHCiNmLkMMOScEGiQwTxk6B1I7HC4VBxwCEWUjIVQPPC4BWCEhZVh0Q1IjGyhUHk8AQ3hmZ3cMPCdLJz0mCjkhFx0IBipDGxseQyQoKxUvMScJVhcxCgwxAAYqEAxHExkOFzxvb1ofcAgKFi48CFYTMTMZPR9seE9HQ2UqIFYMPGsEWHV1CFh7Q0BFVGsVUgMIACQqb1dNbWtIDmYMZVh0Q1IjGyhUHk8EQ3hmO1QfNy4RIWh4Twh6OlJvVGsVX0JHgdnDb1YCIjkAGzx1HBEzDXhvVGsVHgAEAilmK1weM2tYWCp1RVg2Q19vQGsfUg5HSWUlRRVNcGsMHmgxBgs3Q05vRGtBGgoJQzcjO0AfPmsLESR1ChYwaVJvVGtZHQwGD2U1PhVQcCYEDCB7HAkmF1orHThWW2VHQ2VmI1oOMSdFDHl1Ulh8ThBvX2tGA0ZHTGVufRVHcCpMcmh1T1g4DBEuGGtBQE9aQ21rLRVAcDgUUWh6T1BmQ1hvFWI/Uk9HQykpLFQBcD9FRWg4Dgw8TRo6Ey4/Uk9HQywgb0FccHVFSGghBx06QwZvSWtYExsPTSgvIR0ZfGsRSWF1ChYwaVJvVGtcFE8TUWV4bwVNJCMAFmghT0V0DhM7HGVYGwFPF2lmOwdEcC4LHEJ1T1h0ChRvAGsIT08KAjEuYV0YNy5FFzp1G1hoXlJ/VD9dFwFHESAyOkcDcCUMFGgwARxeQ1JvVCdaEQ4LQyknIVE1cHZFCGYNT1N0FVwXVGEVBmVHQ2VmI1oOMSdFFCk7CyJ0XlI/WhEVWU8RTR9mZRUZWmtFWGgnCgwhERxvIi5WBgAVUGsoKkJFPCoLHBB5Tww1ERUqABIZUgMGDSEcZhlNJEEAFixfZVV5Qyc8EWtBGgpHBCQrKhIecCQSFmgXDhQ4MBouECRCOwEDCiYnO1ofcCIDWCEhTx0sCgE7B2sdAQcIFDZmI1QDNCILH2gmHxcgSngpASVWBgYIDWUELlkBfjgNGSw6GCg7EFpmfmsVUk8LDCYnIxUecHZFLycnBAskAhEqTg1cHAshCjc1O3YFOScBUGoXDhQ4MBouECRCOwEDCiYnO1ofcmJvWGh1TxEyQwFvFSVRUhxdKjYHZxcvMTgAKCknG1p9QwYnESUVAAoTFjcob0ZDACQWETw8ABZ0Bhwrfi5bFmVtTmhmraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3FZVV5Q0ZhVBhhMzs0Q201KkYeOSQLWCs6GhYgBgA8XUEYX0+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxdtvFCc2DhR0MAYuADgVT08cQzUpPFwZOSQLHSx1UlhkT1I8EThGGwAJMDEnPUFNbWsRESs+R1F0HngpASVWBgYIDWUVO1QZI2UXHTswG1B9QyE7FT9GXB8IECwyJloDNS9FRWhlVFgHFxM7B2VGFxwUCiooHEEMIj9FRWghBhs/S1tvESVReAkSDSYyJloDcBgRGTwmQQ0kFxsiEWMceE9HQ2UqIFYMPGsWWHV1AhkgC1wpGCRaAEcTCiYtZxxNfWs2DCkhHFYnBgE8HSRbIRsGETFvRRVNcGsJFys0A1g8Q09vGSpBGkEBDyopPR0ecGRFS35lX1FvQwFvSWtGUkJHC2VsbwZbYHtvWGh1TxQ7ABMjVCYVT08KAjEuYVMBPyQXUDt1QFhiU1t0VGsVAU9aQzZmYhUAcGFFTnhfT1h0QwAqAD5HHE8UFzcvIVJDNiQXFSkhR1pxU0ArTm4FQAtdRnV0KxdBcCNJWCV5Twt9aRchEEE/X0JHgdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71cmV4T016QzMaIAQVIiA0KhEPAHtNssvxWCU6GR0nQwsgAWtBHU8TCyBmP0cINCIGDC0xTxQ1DRYmGiwVAR8IF09rYhWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+uheDx0sFScVMxoTDBUpPBVQcDBFKzw0Gx10XlI0fmsVUk8VFisoJlsKcGtFWGhoTx41DwEqWEEVUk9HDioiKhVNcGtFWGh1Ulh2NxcjETtaABtFT2VrYhVPBC4JHTg6HQx2Qw5vVhxUHgRFaWVmbxUEPj8ACj40A1h0Q1JyVHsbQ0NtQ2Vmb1oDPDIqDyYGBhwxQ09vADlAF0NHQ2VmbxVNcGZIWCc7AwF0Agc7G2ZFHRwOFywpIRUaOC4LWCo0AxR0DxMhEDgVHQFHDDA0b0YENC5vWGh1TxcyBQEqABIVUk9HQ3hmfxlNcGtFWGh1T1h0Q19iVD1QABsOACQqb1oLNjgADGh9ClYzTV5vACQVGBoKE2g1P1wGNWJvWGh1TwwmChUoETlmAgoCB3hmehlNcGtFWGh1T1h0Q19iVCRbHhZHESAnLEFNJyMAFmg3DhQ4QwQqGCRWGxseQyA+LFAINDhFDCA8HHIpHnhFGCRWEwNHBTAoLEEEPyVFFi0hPBEwBlpmfmsVUk9KTmUSJ1BNPi4RWCkhTwJ0gfvHVGYEQVpRQ20kKkEaNS4LWAs6GgogPDM9ESoHQ08GF2VrfgZcZGsEFix1LBchEQYQNTlQE15XQyQybxhcZHlXUWZfT1h0Q19iVBxQUg4UEDArKhVPPz4XWDs8Cx12Qxs8VDxdGwwPBjMjPRUeOS8AWCcgHVg3CxM9FShBFx1HCjZmIFtDWmtFWGg5ABs1D1IQWGtdAB9HXmUTO1wBI2UCHTwWBxkmS1tFVGsVUgYBQyspOxUFIjtFDCAwAVgmBgY6BiUVHAYLQyAoKz9NcGtFCi0hGgo6Qxo9BGVlHRwOFywpIRs3Wi4LHEJfCQ06AAYmGyUVMxoTDBUpPBseJCoXDGB8ZVh0Q1ImEmt0BxsIMyo1YWYZMT8AVjogARY9DRVvACNQHE8VBjEzPVtNNSUBcmh1T1gVFgYgJCRGXDwTAjEjYUcYPiUMFi91UlggEQcqfmsVUk8yFywqPBsBPyQVUC4gARsgCh0hXGIVAAoTFjcob3QYJCQ1Fzt7PAw1FxdhHSVBFx0RAilmKlsJfEFFWGh1T1h0QxQ6GihBGwAJS2xmPVAZJTkLWAkgGxcEDAFhJz9UBgpJETAoIVwDN2sAFix5Tx4hDRE7HSRbWkZtQ2VmbxVNcGtFWGh1Axc3Ah5vK2cVGh0XQ3hmGkEEPDhLHy0hLBA1EVpmfmsVUk9HQ2VmbxVNcCIDWCY6G1g8EQJvACNQHE8VBjEzPVtNNSUBcmh1T1h0Q1JvVGsVUgMIACQqb2pBcDsECjx1UlgWAh4jWi1cHAtPSk9mbxVNcGtFWGh1T1g9BVIhGz8VAg4VF2UyJ1ADcDkADD0nAVgxDRZFVGsVUk9HQ2VmbxVNPCQGGSR1GR04Q09vNipZHkERBikpLFwZKWNMcmh1T1h0Q1JvVGsVUgYBQzMjIxsgMSwLETwgCx10X1IOAT9aIgAUTRYyLkEIfj8XES8yCgoHExcqEGtBGgoJQzcjO0AfPmsAFixfT1h0Q1JvVGsVUk9HDyolLllNNicKFzoMT0V0CwA/WhtaAQYTCiooYWxNfWtXVn1fT1h0Q1JvVGsVUk9HDyolLllNPCoLHGR1G1hpQzAuGCcbAh0CBywlO3kMPi8MFi99CRQ7DAAWXUEVUk9HQ2VmbxVNcGsMHmg7AAx0DxMhEGtBGgoJQzcjO0AfPmsAFixfT1h0Q1JvVGsVUk9HTmhmHFQANWYWESwwTxs8BhEkfmsVUk9HQ2VmbxVNcCIDWAkgGxcEDAFhJz9UBgpJDCsqNnoaPhgMHC11GxAxDXhvVGsVUk9HQ2VmbxVNcGtFFCc2DhR0DgsVVHYVGh0XTRUpPFwZOSQLVhJfT1h0Q1JvVGsVUk9HQ2Vmb1kCMyoJWCYwGyJ0XlJiRXgARE9HTmhmLkUdIiQdESU0Gx1eQ1JvVGsVUk9HQ2VmbxVNcCIDWGA4FiJ0X1IhET9vW08ZXmVuI1QDNGU/WHR1AR0gOVtvACNQHE8VBjEzPVtNNSUBcmh1T1h0Q1JvVGsVUgoJB09mbxVNcGtFWGh1T1g4DBEuGGtBEx0ABjFmchUBMSUBWGN1OR03Fx09R2VbFxhPU2lmDkAZPxsKC2YGGxkgBlwgEi1GFxs+T2V2Zj9NcGtFWGh1T1h0Q1ImEmt0BxsIMyo1YWYZMT8AViU6Cx10Xk9vVh9QHgoXDDcybRUZOC4Lcmh1T1h0Q1JvVGsVUk9HQ2UuPUVDEw0XGSUwT0V0IDQ9FSZQXAECFG0yLkcKNT9Mcmh1T1h0Q1JvVGsVUgoLECBMbxVNcGtFWGh1T1h0Q1JvVGYYUo39w2UOOlgMPiQMHBo6AAwEAgA7VCJGUg5HMyQ0OxWP0N9FETx1BxknQzwAVHF4HRkCNypmIlAZOCQBVkJ1T1h0Q1JvVGsVUk9HQ2VmYhhNBTgAWDw9ClgcFh8uGiRcFk9PDDdmAloJNSdMWCE7HAwxAhZhfmsVUk9HQ2VmbxVNcGtFWGg5ABs1D1InASYVT08PETVoH1QfNSURWCk7C1g8EQJhJCpHFwETWQMvIVErOTkWDAs9BhQwLBQMGCpGAUdFKzArLlsCOS9HUUJ1T1h0Q1JvVGsVUk9HQ2VmJlNNOD4IWDw9ChZeQ1JvVGsVUk9HQ2VmbxVNcGtFWGg9GhVuLh05ER9aWhsGESIjOxxncGtFWGh1T1h0Q1JvVGsVUgoLECBMbxVNcGtFWGh1T1h0Q1JvVGsVUk9KTmUALlkBMioGE3J1HBY1E1ImEmtbHU8PFignIVoENEFFWGh1T1h0Q1JvVGsVUk9HQ2Vmb10fIGUmPjo0Ah10XlIMMjlUHwpJDSAxZ0EMIiwADGFfT1h0Q1JvVGsVUk9HQ2Vmb1ADNEFFWGh1T1h0Q1JvVGtQHAttQ2VmbxVNcGtFWGh1PAw1FwFhBCRGGxsODCsjKxVQcBgRGTwmQQg7EBs7HSRbFwtHSGV3RRVNcGtFWGh1ChYwSngqGi8/FBoJADEvIFtNET4RFxg6HFYnFx0/XGIVMxoTDBUpPBs+JCoRHWYnGhY6ChwoVHYVFA4LECBmKlsJWkFIVWi3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4ds/X0JHVmtzb3Q4BARFLQQBT5rU91IrET9QERtHFC0jIRU+IC4GESk5TxEnQxEnFTlSFwtHAisib0EfOSwCHTp1BgxeTl9vlt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWRRhAcB8NHWgyDhUxRAFvVhhFFwwOAilkbx0YPD9MWCEmTxo7FhwrVD9aUg4JQyQlO1wCPmsTESl1LBc6Fxc3AApWBgYIDRYjPUMEMy5LcmV4Tyw8BlIrES1UBwMTQy4jNhUEI2sRATg8DBk4DwtvJWsdAQAKBmUlJ1QfMSgRHTomTw0nBlIuVC9cFAkCESAoOxUGNTJMVkJ4QlgDBkhFWWYVUk9WTWUUKlQJcD8NHWg2BxkmBBdvGC5DFwNHBTcpIhU9PCocHToSGhF6Khw7ETlTEwwCTQInIlBDBScRESU0Gx0XCxM9Ey4bIR8CACwnI3YFMTkCHWYTBhQ4aV9iVGsVUk9HSzEuKhUrOScJWC4nDhUxRAFvJyJPF08UACQqKkZNJyIREGg2BxkmBBdvlsuhUjwOGSBoFxs+MyoJHWgyAB0nQ0Jvls2nUl5OaWhrbxVNYmVFLyAwAVg3CxM9Ey4VkObCQzEuPVAeOCQJHGR1HBE5Fh4uAC4VBgcCQyYpIVMENz4XHSx1BB0tQwI9EThGeAMIACQqb3QYJCQwFDx1UlgvQyE7FT9QUlJHGE9mbxVNIj4LFiE7CFh0Q09vEipZAQpLaWVmbxUZODkACyA6Axx0XlJ+WnsZUk9HQ2hrbwVNJCRFSWi37+x0BRs9EWtCGgoJQyYuLkcKNWsXHSk2Bx0nQwYnHTg/Uk9HQy4jNhVNcGtFWGhoT1oFQV5vVGsVX0JHCCA/LVoMIi9FEy0sTww7QwI9EThGeE9HQ2UlIFoBNCQSFmh1UlhkTUdjVGsVUkJKQzYjLFoDNDhFGi0hGB0xDVI/Bi5GAQoUQ20nOVoENGsWCCk4AhE6BFtFVGsVUgECBiE1DVQBPAgKFjw0DAx0XlIpFSdGF0NHTmhmIFsBKWsDETowTw88BhxvAyJBGgYJQx1mPEEYNDhFFy51DRk4D3hvVGsVEQAJFyQlO2cMPiwAWHV1Xkp4aQ9jVBRZExwTJSw0KhVQcHtFBUJfQlV0NBMjH2tlHg4eBjcBOlxNJCRFHiE7C1ggCxdvJztQEQYGDwYuLkcKNWsjESQ5Tx4mAh8qWmtnFxsSESs1b1sEPGsMHmg7AAx0Dx0uEC5RXGULDCYnIxULJSUGDCE6AVgyChwrNyNUAAgCJSwqIx1EWmtFWGg8CVgVFgYgISdBXDAEAiYuKlErOScJWCk7C1gVFgYgISdBXDAEAiYuKlErOScJVhg0HR06F1I7HC5bUh0CFzA0IRUsJT8KLSQhQSc3AhEnES9zGwMLQyAoKz9NcGtFFCc2DhR0ExVvSWt5HQwGDxUqLkwIInEjESYxKREmEAYMHCJZFkdFMyknNlAfFz4MWmFfT1h0QxspVCVaBk8XBGUyJ1ADcDkADD0nAVg6Ch5vESVReE9HQ2VrYhU9MT8NQmgcAQwxERQuFy4bNQ4KBmsTI0EEPSoRHQs9DgozBlwcBC5WGw4LIC0nPVIIfg0MFCRfT1h0Q19iVBxUHgRHECQgKlkUWmtFWGgzAAp0PF5vEC5GEU8ODWUvP1QEIjhNCC9vKB0gJxc8Fy5bFg4JFzZuZhxNNCRvWGh1T1h0Q1ImEmtRFxwETQsnIlBNbXZFWhslChs9Ah4MHCpHFQpFQyQoKxUJNTgGQgEmLlB2JQAuGS4XW08TCyAoRRVNcGtFWGh1T1h0Qx4gFypZUgkODylmchUJNTgGQg48ARwSCgA8AAhdGwMDS2cAJlkBcmdFDDogClFeQ1JvVGsVUk9HQ2VmJlNNNiIJFGg0ARx0BRsjGHF8AS5PQQM0LlgIcmJFDCAwAXJ0Q1JvVGsVUk9HQ2VmbxVNET4RFx05G1YLABMsHC5RNAYLD2V7b1MEPCdvWGh1T1h0Q1JvVGsVUk9HQzcjO0AfPmsDESQ5ZVh0Q1JvVGsVUk9HQyAoKz9NcGtFWGh1Tx06B3hvVGsVFwEDaSAoKz9nfWZFKi00C1ggCxdvFz5HAAoJF2UlJ1QfNy5FGTt1DlgiAh46EWtcHE88U2lmfmhnNj4LGzw8ABZ0Igc7Gx5ZBkEABjEFJ1QfNy5NUUJ1T1h0Dx0sFScVFAYLD2V7b1MEPi8mECknCB0SCh4jXGI/Uk9HQywgb1sCJGsDESQ5Tww8BhxvBi5BBx0JQ3VmKlsJWmtFWGh4QlgACxdvMiJZHk8BESQrKhIecBgMAi17N1YHABMjEWtcAU8TCyBmLF0MIiwAWDgwHRsxDQYuEy4/Uk9HQzcjO0AfPmsIGTw9QRs4Ah8/XC1cHgNJMCw8Khs1fhgGGSQwQ1hkT1J+XUFQHAttaWhrb2UfNTgWWDw9Clg3DBwpHSxAAAoDQy4jNhUCPigAciQ6DBk4QxQ6GihBGwAJQzU0KkYeGy4cUGFfT1h0Qx4gFypZUgwIByBmchUoPj4IVgMwFjs7BxcUNT5BHToLF2sVO1QZNWUOHTEIZVh0Q1ImEmtbHRtHACoiKhUZOC4LWDowGw0mDVIqGi8/Uk9HQzUlLlkBeC0QFishBhc6S1tFVGsVUk9HQ2UQJkcZJSoJLTswHUIXAgI7ATlQMQAJFzcpI1kIImNMcmh1T1h0Q1JvIiJHBhoGDxA1KkdXAy4RMy0sKxcjDVoOAT9aJwMTTRYyLkEIfiAAAWFfT1h0Q1JvVGtBExwMTTInJkFFYGVVTmFfT1h0Q1JvVGtjGx0TFiQqGkYIInE2HTweCgEBE1oOAT9aJwMTTRYyLkEIfiAAAWFfT1h0QxchEGI/FwEDaU8gOlsOJCIKFmgUGgw7Nh47WjhBEx0TS2xMbxVNcCIDWAkgGxcBDwZhJz9UBgpJETAoIVwDN2sREC07TwoxFwc9GmtQHAttQ2Vmb3QYJCQwFDx7PAw1FxdhBj5bHAYJBGV7b0EfJS5vWGh1Tww1EBlhBztUBQFPBTAoLEEEPyVNUUJ1T1h0Q1JvVDxdGwMCQwQzO1o4PD9LKzw0Gx16EQchGiJbFU8DDE9mbxVNcGtFWGh1T1ggAgEkWjxUGxtPU2t0Zj9NcGtFWGh1T1h0Q1IjGyhUHk8ECyQ0KFBNbWskDTw6OhQgTRUqAAhdEx0ABm1vRRVNcGtFWGh1T1h0QxspVChdEx0ABmV4chUsJT8KLSQhQSsgAgYqWj9dAAoUCyoqKxUZOC4Lcmh1T1h0Q1JvVGsVUk9HQ2UvKRUZOSgOUGF1QlgVFgYgISdBXDALAjYyCVwfNWtbRWgUGgw7Nh47WhhBExsCTSYpIFkJPzwLWDw9ChZeQ1JvVGsVUk9HQ2VmbxVNcGtFWGh4QlgbEwYmGyVUHk8FAikqYlYCPj8EGzx1CBkgBnhvVGsVUk9HQ2VmbxVNcGtFWGh1TxEyQzM6ACRgHhtJMDEnO1BDPi4AHDsXDhQ4IB0hACpWBk8TCyAoRRVNcGtFWGh1T1h0Q1JvVGsVUk9HQ2Vmb1kCMyoJWBd5Twg1EQZvSWt3EwMLTSMvIVFFeUFFWGh1T1h0Q1JvVGsVUk9HQ2VmbxVNcGsJFys0A1gLT1InBjsVT08yFywqPBsKNT8mECknR1FeQ1JvVGsVUk9HQ2VmbxVNcGtFWGh1T1h0ChRvGiRBUkcXAjcyb1QDNGsNCjh8Tww8BhxvFyRbBgYJFiBmKlsJWmtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxVNcCIDWGAlDgogTSIgByJBGwAJQ2hmJ0cdfhsKCyEhBhc6SlwCFSxbGxsSByBmcRUsJT8KLSQhQSsgAgYqWihaHBsGADEULlsKNWsREC07ZVh0Q1JvVGsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1IsGyVBGwESBk9mbxVNcGtFWGh1T1h0Q1JvVGsVUk9HQ2UjIVFncGtFWGh1T1h0Q1JvVGsVUk9HQ2UjIVFncGtFWGh1T1h0Q1JvVGsVUk9HQ2U2PVAeIwAAAWB8ZVh0Q1JvVGsVUk9HQ2VmbxVNcGtFOT0hAC04F1wQGCpGBikOESBmchUZOSgOUGFfT1h0Q1JvVGsVUk9HQ2Vmb1ADNEFFWGh1T1h0Q1JvVGtQHAttQ2VmbxVNcGsAFixfT1h0QxchEGI/FwEDaSMzIVYZOSQLWAkgGxcBDwZhBz9aAkdOQwQzO1o4PD9LKzw0Gx16EQchGiJbFU9aQyMnI0YIcC4LHEJfQlV0gefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3aWhrbwNDcAYqLg0YKjYAaV9iVKmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT3z8BPygEFGgYAA4xDhchAGsIUhRHMDEnO1BNbWsecmh1T1gjAh4kJztQFwtHXmV0fBlNOj4ICBg6GB0mQ09vQXsZUgYJBQ8zIkVNbWsDGSQmClR0DR0sGCJFUlJHBSQqPFBBWmtFWGgzAwF0XlIpFSdGF0NHBSk/HEUINS9FRWhtX1R0Ahw7HQpzOU9aQzE0OlBBcCMMDCo6F1hpQ0BjfmsVUk8UAjMjK2UCI2tYWCY8A1R0BR05VHYVRV9LaThqb2oOPyULWHV1FAV0HnhFGCRWEwNHBTAoLEEEPyVFGTglAwEcFh8uGiRcFkdOaWVmbxUBPygEFGgKQ1gLT1InASYVT08yFywqPBsKNT8mECknR1FvQxspVCVaBk8PFihmO10IPmsXHTwgHRZ0BhwrfmsVUk8PFihoGFQBOxgVHS0xT0V0Lh05ESZQHBtJMDEnO1BDJyoJExslCh0waVJvVGtFEQ4LD20gOlsOJCIKFmB8TxAhDlwFASZFIgAQBjdmchUgPz0AFS07G1YHFxM7EWVfBwIXMyoxKkdNNSUBUUJ1T1h0ExEuGCcdFBoJADEvIFtFeWsNDSV7OgsxKQciBBtaBQoVQ3hmO0cYNWsAFix8ZR06B3gpASVWBgYIDWULIEMIPS4LDGYmCgwDAh4kJztQFwtPFWxmAlobNSYAFjx7PAw1FxdhAypZGTwXBiAibwhNJCQLDSU3Cgp8FVtvGzkVQFxcQyQ2P1kUGD4IGSY6Bhx8SlIqGi8/FBoJADEvIFtNHSQTHSUwAQx6EBc7Pj5YAj8IFCA0Z0NEcAYKDi04ChYgTSE7FT9QXAUSDjUWIEIIImtYWDw6AQ05ARc9XD0cUgAVQ3B2dBUMIDsJAQAgAhk6DBsrXGIVFwEDaSMzIVYZOSQLWAU6GR05Bhw7WjhQBicOFycpNx0beUFFWGh1IhciBh8qGj8bIRsGFyBoJ1wZMiQdWHV1Gxc6Fh8tETkdBEZHDDdmfT9NcGtFFCc2DhR0PF5vHDlFUlJHNjEvI0ZDNy4ROyA0HVB9aVJvVGtcFE8PETVmO10IPmsNCjh7PBEuBlJyVB1QERsIEXZoIVAaeD1JWD55Tw59QxchEEFQHAttBTAoLEEEPyVFNScjChUxDQZhBy5BOwEBKTArPx0beUFFWGh1IhciBh8qGj8bIRsGFyBoJlsLGj4ICGhoTw5eQ1JvVCJTUhlHAisib1sCJGsoFz4wAh06F1wQFyRbHEEODSMMOlgdcD8NHSZfT1h0Q1JvVGt4HRkCDiAoOxsyMyQLFmY8AR4eFh8/VHYVJxwCEQwoP0AZAy4XDiE2ClYeFh8/Ji5EBwoUF38FIFsDNSgRUC4gARsgCh0hXGI/Uk9HQ2VmbxVNcGtFES51ARcgQz8gAi5YFwETTRYyLkEIfiILHgIgAgh0FxoqGmtHFxsSEStmKlsJWmtFWGh1T1h0Q1JvVCdaEQ4LQxpqb2pBcCMQFWhoTy0gCh48WixQBiwPAjduZj9NcGtFWGh1T1h0Q1ImEmtdBwJHFy0jIRUFJSZfOyA0AR8xMAYuAC4dNwESDmsOOlgMPiQMHBshDgwxNws/EWV/BwIXCishZhUIPi9vWGh1T1h0Q1IqGi8ceE9HQ2UjI0YIOS1FFichTw50AhwrVAZaBAoKBisyYWoOPyULViE7CTIhDgJvACNQHGVHQ2VmbxVNcAYKDi04ChYgTS0sGyVbXAYJBQ8zIkVXFCIWGyc7AR03F1pmT2t4HRkCDiAoOxsyMyQLFmY8AR4eFh8/VHYVHAYLaWVmbxUIPi9vHSYxZR4hDRE7HSRbUiIIFSArKlsZfjgADAY6DBQ9E1o5XUEVUk9HLiowKlgIPj9LKzw0Gx16DR0sGCJFUlJHFU9mbxVNOS1FDmg0ARx0DR07VAZaBAoKBisyYWoOPyULViY6DBQ9E1I7HC5beE9HQ2VmbxVNHSQTHSUwAQx6PBEgGiUbHAAEDyw2bwhNAj4LKy0nGRE3BlwcAC5FAgoDWQYpIVsIMz9NHj07DAw9DBxnXUEVUk9HQ2VmbxVNcGsMHmg7AAx0Lh05ESZQHBtJMDEnO1BDPiQGFCElTww8BhxvBi5BBx0JQyAoKz9NcGtFWGh1T1h0Q1IjGyhUHk8ECyQ0bwhNHCQGGSQFAxktBgBhNyNUAA4EFyA0dBUENmsLFzx1DBA1EVI7HC5bUh0CFzA0IRUIPi9vWGh1T1h0Q1JvVGsVFAAVQxpqb0VNOSVFETg0BgonSxEnFTkPNQoTJyA1LFADNCoLDDt9RlF0Bx1FVGsVUk9HQ2VmbxVNcGtFWCEzTwhuKgEOXGl3ExwCMyQ0OxdEcCoLHGglQTs1DTEgGCdcFgpHFy0jIRUdfggEFgs6AxQ9BxdvSWtTEwMUBmUjIVFncGtFWGh1T1h0Q1JvESVReE9HQ2VmbxVNNSUBUUJ1T1h0Bh48ESJTUgEIF2Uwb1QDNGsoFz4wAh06F1wQFyRbHEEJDCYqJkVNJCMAFkJ1T1h0Q1JvVAZaBAoKBisyYWoOPyULViY6DBQ9E0gLHThWHQEJBiYyZxxWcAYKDi04ChYgTS0sGyVbXAEIACkvPxVQcCUMFEJ1T1h0Bhwrfi5bFmULDCYnIxULJSUGDCE6AVgnFxM9AA1ZC0dOaWVmbxUBPygEFGgKQ1g8EQJjVCNAH09aQxAyJlkefiwADAs9Dgp8SklvHS0VHAATQy00PxUCImsLFzx1Bw05QwYnESUVAAoTFjcob1ADNEFFWGh1Axc3Ah5vFj0VT08uDTYyLlsONWULHT99TTo7BwsZESdaEQYTGmdvdBUPJmUoGTATAAo3BlJyVB1QERsIEXZoIVAaeHoAQWRkCkF4Uhd2XXAVEBlJNSAqIFYEJDJFRWgDChsgDAB8WiVQBUdOWGUkORs9MTkAFjx1Ulg8EQJFVGsVUgMIACQqb1cKcHZFMSYmGxk6ABdhGi5CWk0lDCE/CEwfP2lMQ2g3CFYZAgobGzlEBwpHXmUQKlYZPzlWViYwGFBlBktjRS4MXl4CWmx9b1cKfhtFRWhkCkxvQxAoWhtUAAoJF2V7b10fIEFFWGh1IhciBh8qGj8bLQwIDStoKVkUEh1JWAU6GR05Bhw7WhRWHQEJTSMqNncqcHZFGj55TxozaVJvVGtdBwJJMyknO1MCIiY2DCk7C1hpQwY9AS4/Uk9HQwgpOVAANSURVhc2ABY6TRQjDR5FFg4TBmV7b2cYPhgACj48DB16MRchEC5HIRsCEzUjKw8uPyULHSshRx4hDRE7HSRbWkZtQ2VmbxVNcGsMHmg7AAx0Lh05ESZQHBtJMDEnO1BDNiccWDw9ChZ0ERc7ATlbUgoJB09mbxVNcGtFWCQ6DBk4QxEuGWsIUhgIES41P1QONWUmDTonChYgIBMiETlUeE9HQ2VmbxVNPCQGGSR1AlhpQyQqFz9aAFxJDSAxZxxncGtFWGh1T1g9BVIaBy5HOwEXFjEVKkcbOSgAQgEmJB0tJx04GmNwHBoKTQ4jNnYCNC5LL2F1T1h0Q1JvVGtBGgoJQyhmchUAcGBFGyk4QTsSERMiEWV5HQAMNSAlO1ofcC4LHEJ1T1h0Q1JvVCJTUjoUBjcPIUUYJBgACj48DB1uKgEEETJxHRgJSwAoOlhDGy4cOycxClYHSlJvVGsVUk9HQzEuKltNPWtYWCV1Qlg3Ah9hNw1HEwICTQkpIF47NSgRFzp1ChYwaVJvVGsVUk9HCiNmGkYIIgILCD0hPB0mFRssEXF8ASQCGgEpOFtFFSUQFWYeCgEXDBYqWgocUk9HQ2VmbxVNJCMAFmg4T0V0DlJiVChUH0EkJTcnIlBDAiICEDwDChsgDABvESVReE9HQ2VmbxVNOS1FLTswHTE6Ewc7Jy5HBAYEBn8PPH4IKQ8KDyZ9KhYhDlwEETJ2HQsCTQFvbxVNcGtFWGh1GxAxDVIiVHYVH09MQyYnIhsuFjkEFS17PREzCwYZEShBHR1HBisiRRVNcGtFWGh1Bh50NgEqBgJbAhoTMCA0OVwONXEsCwMwFjw7FBxnMSVAH0EsBjwFIFEIfhgVGSswRlh0Q1JvACNQHE8KQ3hmIhVGcB0AGzw6HUt6DRc4XHsZUl5LQ3Vvb1ADNEFFWGh1T1h0QxspVB5GFx0uDTUzO2YIIj0MGy1vJgsfBgsLGzxbWioJFihoBFAUEyQBHWYZCh4gMBomEj8cUhsPBitmIhVQcCZFVWgDChsgDAB8WiVQBUdXT2V3YxVdeWsAFixfT1h0Q1JvVGtcFE8KTQgnKFsEJD4BHWhrT0h0FxoqGmtYUlJHDmsTIVwZcGFFNScjChUxDQZhJz9UBgpJBSk/HEUINS9FHSYxZVh0Q1JvVGsVEBlJNSAqIFYEJDJFRWg4ZVh0Q1JvVGsVEAhJIAM0LlgIcHZFGyk4QTsSERMiEUEVUk9HBisiZj8IPi9vFCc2DhR0BQchFz9cHQFHEDEpP3MBKWNMcmh1T1gyDABvK2cVGU8ODWUvP1QEIjhNA2ozAwEBExYuAC4XXk0BDzwEGRdBci0JAQoSTQV9QxYgfmsVUk9HQ2VmI1oOMSdFG2hoTzU7FRciESVBXDAEDCsoFF4wWmtFWGh1T1h0ChRvF2tBGgoJaWVmbxVNcGtFWGh1TxEyQwY2BC5aFEcESmV7chVPAgk9KysnBgggIB0hGi5WBgYIDWdmO10IPmsGQgw8HBs7DRwqFz8dW08CDzYjb1ZXFC4WDDo6FlB9QxchEEEVUk9HQ2VmbxVNcGsoFz4wAh06F1wQFyRbHDQMPmV7b1sEPEFFWGh1T1h0QxchEEEVUk9HBisiRRVNcGsJFys0A1gLT1IQWGtdBwJHXmUTO1wBI2UCHTwWBxkmS1tFVGsVUgYBQy0zIhUZOC4LWCAgAlYEDxM7EiRHHzwTAisibwhNNioJCy11ChYwaRchEEFTBwEEFywpIRUgPz0AFS07G1YnBgYJGDIdBEZHLiowKlgIPj9LKzw0Gx16BR42VHYVBFRHCiNmORUZOC4LWDshDgogJR42XGIVFwMUBmU1O1odFiccUGF1ChYwQxchEEFTBwEEFywpIRUgPz0AFS07G1YnBgYJGDJmAgoCB20wZhUgPz0AFS07G1YHFxM7EWVTHhY0EyAjKxVQcD8KFj04DR0mSwRmVCRHUldXQyAoKz8LJSUGDCE6AVgZDAQqGS5bBkEUBjEHIUEEEQ0uUD58ZVh0Q1ICGz1QHwoJF2sVO1QZNWUEFjw8Lj4fQ09vAkEVUk9HCiNmORUMPi9FFichTzU7FRciESVBXDAEDCsoYVQDJCIkPgN1GxAxDXhvVGsVUk9HQwgpOVAANSURVhc2ABY6TRMhACJ0NCRHXmUKIFYMPBsJGTEwHVYdBx4qEHF2HQEJBiYyZ1MYPigRESc7R1FeQ1JvVGsVUk9HQ2VmJlNNPiQRWAU6GR05Bhw7WhhBExsCTSQoO1wsFgBFDCAwAVgmBgY6BiUVFwEDaWVmbxVNcGtFWGh1Twg3Ah4jXC1AHAwTCiooZxxNBiIXDD00Ay0nBgB1NypFBhoVBgYpIUEfPycJHTp9RkN0NRs9AD5UHjoUBjd8DFkEMyAnDTwhABZmSyQqFz9aAF1JDSAxZxxEcC4LHGFfT1h0Q1JvVGtQHAtOaWVmbxUIPDgAES51ARcgQwRvFSVRUiIIFSArKlsZfhQGFyY7QRk6FxsOMgAVBgcCDU9mbxVNcGtFWAU6GR05Bhw7WhRWHQEJTSQoO1wsFgBfPCEmDBc6DRcsAGMcSU8qDDMjIlADJGU6Gyc7AVY1DQYmNQ1+UlJHDSwqRRVNcGsAFixfChYwaRQ6GihBGwAJQwgpOVAANSURVjswGz4bNVo5XUEVUk9HLiowKlgIPj9LKzw0Gx16BR05VHYVBGVHQ2VmI1oOMSdFGyk4T0V0FB09HzhFEwwCTQYzPUcIPj8mGSUwHRleQ1JvVCJTUgwGDmUyJ1ADcCgEFWYTBh04Bz0pIiJQBU9aQzNmKlsJWi4LHEIzGhY3FxsgGmt4HRkCDiAoOxseMT0AKCcmR1FeQ1JvVCdaEQ4LQxpqb10fIGtYWB0hBhQnTRUqAAhdEx1PSk9mbxVNOS1FEDolTww8BhxvOSRDFwICDTFoHEEMJC5LCykjChwEDAFvSWtdAB9JMyo1JkEEPyVeWDowGw0mDVI7Bj5QUgoJB08jIVFnNj4LGzw8ABZ0Lh05ESZQHBtJESAlLlkBACQWUGFfT1h0QxspVAZaBAoKBisyYWYZMT8AVjs0GR0wMx08VD9dFwFHNjEvI0ZDJC4JHTg6HQx8Lh05ESZQHBtJMDEnO1BDIyoTHSwFAAt9WFI9ET9AAAFHFzczKhUIPi9vHSYxZXIYDBEuGBtZExYCEWsFJ1QfMSgRHToUCxwxB0gMGyVbFwwTSyMzIVYZOSQLUGFfT1h0QwYuByAbBQ4OF212YQNEa2sECDg5FjAhDhMhGyJRWkZtQ2Vmb1wLcAYKDi04ChYgTSE7FT9QXAkLGmUyJ1ADcDgRGTohKRQtS1tvESVReE9HQ2UvKRUgPz0AFS07G1YHFxM7EWVdGxsFDD1mMQhNYmsREC07TzU7FRciESVBXBwCFw0vO1cCKGMoFz4wAh06F1wcACpBF0EPCjEkIE1EcC4LHEIwARx9aXhiWWvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qVnfWZFT2Z1KisEQ5DP4Gt3EwMLT2U2I1QUNTkWWGAhChk5ThEgGCRHFwtOT2UlIEAfJGsfFyYwHHJ5TlKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tVMI1oOMSdFPRsFT0V0GFIcACpBF09aQz5MbxVNcCkEFCR1UlgyAh48EWcVEA4LDxE0LlwBcHZFHik5HB14Qx4uGi9cHAgqAjctKkdNbWsDGSQmClReQ1JvVDtZExYCETZmchULMScWHWR1FRc6BgFvSWtTEwMUBmlMbxVNcCkEFCQWABQ7EVJvVGsIUiwIDyo0fBsLIiQIKg8XR0phVl5vRnkFXk9RU2xqRRVNcGsVFCksCgoXDB4gBmsVT08kDCkpPQZDNjkKFRoSLVBkT1J9RXsZUl1VWmxqRRVNcGsAFi04Fjs7Dx09VGsVT08kDCkpPQZDNjkKFRoSLVBmVkdjVHMFXk9fU2xqRRVNcGsfFyYwLBc4DABvVGsVT08kDCkpPQZDNjkKFRoSLVBlUUJjVHkHQkNHUnd2ZhlncGtFWDs9AA8QCgE7FSVWF09aQzE0OlBBWjZJWBc3DTo1Dx5vSWtbGwNLQxokLWUBMTIACjt1UlgvHl5vKylXKAAJBjZmchUWLWdFJyQ0ARw9DRUCFTleFx1HXmUoJllBcBQGFyY7T0V0GA9vCUE/HgAEAilmKUADMz8MFyZ1Ahk/BjANXCpRHR0JBiBqb0EIKD9JWCs6AxcmT1InESJSGhtLQyogKUYIJBJMcmh1T1g4DBEuGGtXEE9aQwwoPEEMPigAViYwGFB2IRsjGClaEx0DJDAvbRxncGtFWCo3QTY1DhdvSWsXK10sPAAVHxdncGtFWCo3QTkwDAAhES4VT08GByo0IVAIWmtFWGg3DVYHCggqVHYVJysODndoIVAaeHtJWHplX1R0U15vHC5cFQcTQyo0bwZfeUFFWGh1DRp6MAY6EDh6FAkUBjFmchU7NSgRFzpmQRYxFFp/WGtaFAkUBjEfb1ofcHhJWHh8ZVh0Q1ItFmV0HhgGGjYJIWECIGtYWDwnGh1eQ1JvVClXXCIGGwEvPEEMPigAWHV1Xk1kU3hvVGsVHgAEAilmI1QPNSdFRWgcAQsgAhwsEWVbFxhPQREjN0EhMSkAFGp8ZVh0Q1IjFSlQHkElAiYtKEcCJSUBLDo0AQskAgAqGihMUlJHU2tyRRVNcGsJGSowA1YWAhEkEzlaBwEDICoqIEdecHZFOyc5AApnTRQ9GyZnNS1PUnVqbwRdfGtXSGFfT1h0Qx4uFi5ZXC0IESEjPWYEKi41ETAwA1hpQ0JFVGsVUgMGASAqYWYEKi5FRWgAKxE5UVwpBiRYIQwGDyBufhlNYWJvWGh1TxQ1ARcjWg1aHBtHXmUDIUAAfg0KFjx7JQ0mAnhvVGsVHg4FBiloG1AVJBgMAi11UlhlV3hvVGsVHg4FBiloG1AVJAgKFCcnXFhpQxEgGCRHeE9HQ2UqLlcIPGUxHTAhT0V0Fxc3AEEVUk9HDyQkKllDACoXHSYhT0V0ARBFVGsVUgMIACQqb0YZIiQOHWhoTzE6EAYuGihQXAECFG1kGnw+JDkKEy13RnJ0Q1JvBz9HHQQCTQYpI1ofcHZFGyc5AApvQwE7BiReF0EzCywlJFsIIzhFRWhkQU1vQwE7BiReF0E3AjcjIUFNbWsJGSowA3J0Q1JvFikbIg4VBisybwhNMS8KCiYwCnJ0Q1JvBi5BBx0JQyckYxUBMSkAFEIwARxeaR4gFypZUgkSDSYyJloDcCYEEy0ZDhYwChwoOSpHGQoVS2xMbxVNcCIDWA0GP1YLDxMhECJbFSIGES4jPRUMPi9FPRsFQSc4AhwrHSVSPw4VCCA0YWUMIi4LDGghBx06QwAqAD5HHE8iMBVoEFkMPi8MFi8YDgo/BgBvESVReE9HQ2UqIFYMPGsVWHV1JhYnFxMhFy4bHAoQS2cWLkcZcmJvWGh1Twh6LRMiEWsIUk0+UQ4ZA1QDNCILHwU0HRMxEVBFVGsVUh9JMCw8KhVQcB0AGzw6HUt6DRc4XH8ZUl9JUWlmexxncGtFWDh7LhY3Cx09ES8VT08TETAjRRVNcGsVVgs0ATs7Dx4mEC4VT08BAik1Kj9NcGtFCGYYDgwxERsuGGsIUioJFihoAlQZNTkMGSR7IR07DXhvVGsVAkEzESQoPEUMIi4LGzF1UlhkTUFFVGsVUh9JICoqIEdNbWsgKxh7PAw1FxdhFipZHiwIDyo0RRVNcGsVVhg0HR06F1JyVBxaAAQUEyQlKj9NcGtFFCc2DhR0EBVvSWt8HBwTAislKhsDNTxNWhsgHR41ABcIASIXW2VHQ2VmPFJDFioGHWhoTz06Fh9hOiRHHw4LKiFoG1odWmtFWGgmCFYEAgAqGj8VT08XaWVmbxUeN2U1ETAwAwsEBgAcAD5RUlJHVnVMbxVNcCcKGyk5Twx0XlIGGjhBEwEEBmsoKkJFch8AADwZDhoxD1BmfmsVUk8TTQcnLF4KIiQQFiwBHRk6EAIuBi5bERZHXmV3RRVNcGsRVhs8FR10XlIaMCJYQEEBESorHFYMPC5NSWR1XlFeQ1JvVD8bNAAJF2V7b3ADJSZLPic7G1YeFgAufmsVUk8TTREjN0E+MyoJHSx1UlggEQcqfmsVUk8TTREjN0EuPycKCnt1UlgXDB4gBngbFB0IDhcBDR1fZX5JWHpgWlR0UUd6XUEVUk9HF2sSKk0ZcHZFWgQUITx2aVJvVGtBXD8GESAoOxVQcDgCcmh1T1gRMCJhKydUHAsODSILLkcGNTlFRWglZVh0Q1I9ET9AAAFHE08jIVFnWi0QFishBhc6QzccJGVGFxslAikqZ0NEWmtFWGgQPCh6MAYuAC4bEA4LD2V7b0NncGtFWCEzTxY7F1I5VCpbFk8iMBVoEFcPEioJFGghBx06QzccJGVqEA0lAikqdXEIIz8XFzF9RkN0JiEfWhRXEC0GDylmchUDOSdFHSYxZR06B3hFEj5bERsODCtmCmY9fjgADAQ0ARw9DRUCFTleFx1PFWxMbxVNcA42KGYGGxkgBlwjFSVRGwEALiQ0JFAfcHZFDkJ1T1h0ChRvGiRBUhlHAisib3A+AGU6FCk7CxE6BD8uBiBQAE8TCyAob3A+AGU6FCk7CxE6BD8uBiBQAFUjBjYyPVoUeGJeWA0GP1YLDxMhECJbFSIGES4jPRVQcCUMFGgwARxeBhwrfkFTBwEEFywpIRUoAxtLCy0hPxQ1Ghc9B2NDW2VHQ2VmCmY9fhgRGTwwQQg4AgsqBjgVT08RaWVmbxUENmsLFzx1GVggCxchfmsVUk9HQ2VmKVofcBRJWCo3TxE6QwIuHTlGWio0M2sZLVc9PCocHTomRlgwDFImEmtXEE8GDSFmLVdDACoXHSYhTww8BhxvFikPNgoUFzcpNh1EcC4LHGgwARxeQ1JvVGsVUk8iMBVoEFcPACcEAS0nHFhpQwkyfmsVUk8CDSFMKlsJWkEDDSY2GxE7DVIKJxsbAQoTOSooKkZFJmJvWGh1Tz0HM1wcACpBF0EdDCsjPBVQcD1vWGh1TxEyQxwgAGtDUhsPBitMbxVNcGtFWGgzAAp0PF5vFikVGwFHEyQvPUZFFRg1Vhc3DSI7DRc8XWtRHU8OBWUkLRUMPi9FGip7PxkmBhw7VD9dFwFHASd8C1AeJDkKAWB8Tx06B1IqGi8/Uk9HQ2VmbxUoAxtLJyo3NRc6BgFvSWtOD2VHQ2VmKlsJWi4LHEJfCQ06AAYmGyUVNzw3TTYyLkcZeGJvWGh1TxEyQzccJGVqEQAJDWsrLlwDcD8NHSZ1HR0gFgAhVC5bFmVHQ2VmCmY9fhQGFyY7QRU1ChxvSWtnBwE0BjcwJlYIfgMAGTohDR01F0gMGyVbFwwTSyMzIVYZOSQLUGFfT1h0Q1JvVGsYX08iAjcqNhgeOyIVWCEzTxY7FxomGiwVFwEGASkjKxVFIyoTHTt1LCgBQwUnESUVAQwVCjUyb1wecCIBFC18ZVh0Q1JvVGsVGwlHDSoybx0oAxtLKzw0Gx16ARMjGGtaAE8iMBVoHEEMJC5LFCk7CxE6BD8uBiBQAGVHQ2VmbxVNcGtFWGg6HVgRMCJhJz9UBgpJEyknNlAfI2sKCmgQPCh6MAYuAC4bCAAJBjZvb0EFNSVvWGh1T1h0Q1JvVGsVAAoTFjcoRRVNcGtFWGh1ChYwaVJvVGsVUk9HTmhmDVQBPGsgKxhfT1h0Q1JvVGtcFE8iMBVoHEEMJC5LGik5A1ggCxchfmsVUk9HQ2VmbxVNcCcKGyk5TxU7BxcjWGtFEx0TQ3hmDVQBPGUDESYxR1FeQ1JvVGsVUk9HQ2VmJlNNICoXDGghBx06aVJvVGsVUk9HQ2VmbxVNcGsMHmg7AAx0JiEfWhRXEC0GDylmIEdNFRg1Vhc3DTo1Dx5hNS9aAAECBmU4chUdMTkRWDw9ChZeQ1JvVGsVUk9HQ2VmbxVNcGtFWGg8CVgRMCJhKylXMA4LD2UyJ1ADcA42KGYKDRoWAh4jTg9QARsVDDxuZhUIPi9vWGh1T1h0Q1JvVGsVUk9HQ2VmbxUoAxtLJyo3LRk4D1JyVCZUGQolIW02LkcZfGtHiNfa/1gWIj4DVmcVNzw3TRYyLkEIfikEFCQWABQ7EV5vR3kZUl1OaWVmbxVNcGtFWGh1T1h0Q1IqGi8/Uk9HQ2VmbxVNcGtFWGh1TxQ7ABMjVCdUEAoLQ3hmCmY9fhQHGgo0AxRuJRshEA1cABwTIC0vI1E6OCIGEAEmLlB2Nxc3AAdUEAoLQWxMbxVNcGtFWGh1T1h0Q1JvVCJTUgMGASAqb0EFNSVvWGh1T1h0Q1JvVGsVUk9HQ2VmbxUBPygEFGgjT0V0IRMjGGVDFwMIACwyNh1EWmtFWGh1T1h0Q1JvVGsVUk9HQ2VmI1oOMSdFCzgwChx0XlI5WgZUFQEOFzAiKj9NcGtFWGh1T1h0Q1JvVGsVUk9HQykpLFQBcBRJWCAnH1hpQyc7HSdGXAgCFwYuLkdFeUFFWGh1T1h0Q1JvVGsVUk9HQ2Vmb1kCMyoJWCw8HAx0XlInBjsVEwEDQxAyJlkefi8MCzw0ARsxSxo9BGVlHRwOFywpIRlNICoXDGYFAAs9FxsgGmIVHR1HU09mbxVNcGtFWGh1T1h0Q1JvVGsVUgMGASAqYWEIKD9FRWh9TYjL7OJvUS9GBk9HH2VmalFNJmlMQi46HRU1F1oiFT9dXAkLDCo0Z1EEIz9MVGg4Dgw8TRQjGyRHWhwXBiAiZhxncGtFWGh1T1h0Q1JvVGsVUgoJB09mbxVNcGtFWGh1T1gxDwEqHS0VNzw3TRokLXcMPCdFDCAwAXJ0Q1JvVGsVUk9HQ2VmbxVNFRg1Vhc3DTo1Dx51MC5GBh0IGm1vdBUoAxtLJyo3LRk4D1JyVCVcHmVHQ2VmbxVNcGtFWGgwARxeQ1JvVGsVUk8CDSFMRRVNcGtFWGh1QlV0LxMhECJbFU8KAjctKkdncGtFWGh1T1g9BVIKJxsbIRsGFyBoI1QDNCILHwU0HRMxEVI7HC5beE9HQ2VmbxVNcGtFWCQ6DBk4Qy1jVCNHAk9aQxAyJlkefiwADAs9Dgp8SnhvVGsVUk9HQ2VmbxUBPygEFGg2AA0mF1JyVBxaAAQUEyQlKg8rOSUBPiEnHAwXCxsjEGMXPw4XQWxmLlsJcBwKCiMmHxk3BlwCFTsPNAYJBwMvPUYZEyMMFCx9TTs7FgA7VmI/Uk9HQ2VmbxVNcGtFFCc2DhR0BR4gGzlsUlJHACozPUFNMSUBWCs6GgogTSIgByJBGwAJTRxmZBUOPz4XDGYGBgIxTStvW2sHUkRHU2tzRRVNcGtFWGh1T1h0Q1JvVGtaAE9PCzc2b1QDNGsNCjh7PxcnCgYmGyUbK09KQ3doehxNPzlFSEJ1T1h0Q1JvVGsVUk8LDCYnIxUBMSUBVGghT0V0IRMjGGVFAAoDCiYyA1QDNCILH2AzAxc7EStmfmsVUk9HQ2VmbxVNcCIDWCQ0ARx0FxoqGkEVUk9HQ2VmbxVNcGtFWGh1Axc3Ah5vGSpHGQoVQ3hmIlQGNQcEFiw8AR8ZAgAkETkdW2VHQ2VmbxVNcGtFWGh1T1h0DhM9Hy5HXD8IECwyJloDcHZFFCk7C3J0Q1JvVGsVUk9HQ2VmbxVNPSoXEy0nQTs7Dx09VHYVNzw3TRYyLkEIfikEFCQWABQ7EXhvVGsVUk9HQ2VmbxVNcGtFFCc2DhR0EBVvSWtYEx0MBjd8CVwDNA0MCjshLBA9DxYYHCJWGiYUIm1kHEAfNioGHQ8gBlp9aVJvVGsVUk9HQ2VmbxVNcGsJFys0A1ggD1JyVDhSUg4JB2U1KA8rOSUBPiEnHAwXCxsjEBxdGwwPKjYHZxc5NTMRNCk3ChR2SnhvVGsVUk9HQ2VmbxVNcGtFES51GxR0AhwrVD8VBgcCDWUyIxs5NTMRWHV1R1oYIjwLVCJbUkpJUiM1bRxXNiQXFSkhRwx9QxchEEEVUk9HQ2VmbxVNcGsAFDswBh50JiEfWhRZEwEDCishAlQfOy4XWDw9ChZeQ1JvVGsVUk9HQ2VmbxVNcA42KGYKAxk6BxshEwZUAAQCEWsWIEYEJCIKFmhoTy4xAAYgBngbHAoQS3VqbxhcYHtVVGhlRnJ0Q1JvVGsVUk9HQ2UjIVFncGtFWGh1T1gxDRZFfmsVUk9HQ2VmYhhNACcEAS0nTz0HM3hvVGsVUk9HQywgb3A+AGU2DCkhClYkDxM2ETlGUhsPBitMbxVNcGtFWGh1T1h0Dx0sFScVAQoCDWV7b04QWmtFWGh1T1h0Q1JvVC1aAE84T2U2I0dNOSVFETg0BgonSyIjFTJQABxdJCAyH1kMKS4XC2B8RlgwDHhvVGsVUk9HQ2VmbxVNcGtFES51HxQmQwxyVAdaEQ4LMyknNlAfcCoLHGglAwp6IBouBipWBgoVQzEuKltncGtFWGh1T1h0Q1JvVGsVUk9HQ2UqIFYMPGsNHSkxT0V0Ex49WghdEx0GADEjPQ8rOSUBPiEnHAwXCxsjEGMXOgoGB2dvRRVNcGtFWGh1T1h0Q1JvVGsVUk9HDyolLllNOD4IWHV1HxQmTTEnFTlUERsCEX8AJlsJFiIXCzwWBxE4Bz0pNydUARxPQQ0zIlQDPyIBWmFfT1h0Q1JvVGsVUk9HQ2VmbxVNcGsMHmg9ChkwQxMhEGtdBwJHFy0jIT9NcGtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxUeNS4LIzg5HSV0XlI7Bj5QeE9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUgMIACQqb1cPcHZFPRsFQSc2ASIjFTJQABw8Eyk0Ej9NcGtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxUENmsLFzx1DRp0DABvFikbMwsIESsjKhUTbWsNHSkxTww8BhxFVGsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUgYBQyckb0EFNSVFGipvKx0nFwAgDWMcUgoJB09mbxVNcGtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxVNPCQGGSR1DBc4DABvSWtwIT9JMDEnO1BDICcEAS0nLBc4DABFVGsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUgYBQzUqPRs5NSoIWCk7C1gYDBEuGBtZExYCEWsSKlQAcCoLHGglAwp6NxcuGWtLT08rDCYnI2UBMTIACmYBChk5QwYnESU/Uk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxUOPycKCmhoTz0HM1wcACpBF0ECDSArNnYCPCQXcmh1T1h0Q1JvVGsVUk9HQ2VmbxVNcGtFWGh1T1gxDRZFVGsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUg0FQ3hmIlQGNQknUCAwDhx4QwIjBmV7EwICT2UlIFkCImdFS3p5T0t9aVJvVGsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGtwIT9JPCckH1kMKS4XCxMlAwoJQ09vFik/Uk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVFwEDaWVmbxVNcGtFWGh1T1h0Q1JvVGsVUk9HQykpLFQBcCcEGi05T0V0ARB1MiJbFikOETYyDF0EPC8yECE2BzEnIlptIC5NBiMGASAqbRxncGtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxVNOS1FFCk3ChR0FxoqGkEVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUk9HDyolLllND2dFEDolT0V0NgYmGDgbFQoTIC0nPR1EWmtFWGh1T1h0Q1JvVGsVUk9HQ2VmbxVNcGtFWGg5ABs1D1IrHThBUlJHCzc2b1QDNGsNHSkxTxk6B1IaACJZAUEDCjYyLlsONWMNCjh7PxcnCgYmGyUZUgcCAiFoH1oeOT8MFyZ8TxcmQ0JFVGsVUk9HQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUgMGASAqYWEIKD9FRWh9TZrD7FJqB2sVVwsPE2VmFBAJIz84WmFvCRcmDhM7XDtZAEEpAigjYxUAMT8NVi45ABcmSxo6GWV9Fw4LFy1vYxUAMT8NVi45ABcmSxYmBz8cW2VHQ2VmbxVNcGtFWGh1T1h0Q1JvVGsVUk8CDSFMbxVNcGtFWGh1T1h0Q1JvVGsVUk8CDSFMbxVNcGtFWGh1T1h0Q1JvVC5bFmVHQ2VmbxVNcGtFWGgwARxeQ1JvVGsVUk9HQ2VmKVofcDsJCmR1DRp0ChxvBCpcABxPJhYWYWoPMhsJGTEwHQt9QxYgfmsVUk9HQ2VmbxVNcGtFWGg8CVg6DAZvBy5QHDQXDzcbb1QDNGsHGmghBx06QxAtTg9QARsVDDxuZg5NFRg1Vhc3DSg4AgsqBjhuAgMVPmV7b1sEPGsAFixfT1h0Q1JvVGsVUk9HBisiRRVNcGtFWGh1ChYwaXhvVGsVUk9HQ2hrb28CPi5FPRsFT1A3DAc9AGtUAAoGQyknLVABI2JvWGh1T1h0Q1ImEmtwIT9JMDEnO1BDKiQLHTt1GxAxDXhvVGsVUk9HQ2VmbxUBPygEFGgvABYxEFJyVBxaAAQUEyQlKg8rOSUBPiEnHAwXCxsjEGMXPw4XQWxmLlsJcBwKCiMmHxk3BlwCFTsPNAYJBwMvPUYZEyMMFCx9TSI7DRc8VmI/Uk9HQ2VmbxVNcGtFES51FRc6BgFvACNQHGVHQ2VmbxVNcGtFWGh1T1h0BR09VBQZUhVHCitmJkUMOTkWUDI6AR0nWTUqAAhdGwMDESAoZxxEcC8Kcmh1T1h0Q1JvVGsVUk9HQ2VmbxVNOS1FAnIcHDl8QTAuBy5lEx0TQWxmLlsJcCUKDGgQPCh6PBAtLiRbFxw8GRhmO10IPkFFWGh1T1h0Q1JvVGsVUk9HQ2VmbxVNcGsgKxh7MBo2OR0hEThuCDJHXmUrLl4IEglNAmR1FVYaAh8qWGtwIT9JMDEnO1BDKiQLHQs6AxcmT1J9TGcVQkFSSk9mbxVNcGtFWGh1T1h0Q1JvVGsVUgoJB09mbxVNcGtFWGh1T1h0Q1JvESVReE9HQ2VmbxVNcGtFWC07C3J0Q1JvVGsVUgoJB09mbxVNNSUBUUIwARxeaV9iVKmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT39f4wKnw6KrA/5rB85Da5Kmg4o3y86fT3z9AfWtdVmgDJisBIj4cVGNZGwgPFywoKBUCPiccUUJ4Qli29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/9tDyolLllNBiIWDSk5HFhpQwlvJz9UBgpHXmU9b1MYPCcHCiEyBwx0XlIpFSdGF08aT2UZLVQOOz4VWHV1FAV0HngpASVWBgYIDWUQJkYYMScWVjswGz4hDx4tBiJSGhtPFWxMbxVNcB0MCz00Awt6MAYuAC4bFBoLDyc0JlIFJGtYWD5fT1h0QxspVCVaBk8JBj0yZ2MEIz4EFDt7MBo1ABk6BGIVBgcCDU9mbxVNcGtFWB48HA01DwFhKylUEQQSE2sEPVwKOD8LHTsmT0V0LxsoHD9cHAhJITcvKF0ZPi4WC0J1T1h0Q1JvVB1cARoGDzZoEFcMMyAQCGYWAxc3CCYmGS4VUlJHLywhJ0EEPixLOyQ6DBMACh8qfmsVUk9HQ2VmGVweJSoJC2YKDRk3CAc/WgxZHQ0GDxYuLlECJzhFRWgZBh88FxshE2VyHgAFAikVJ1QJPzwWcmh1T1gxDRZFVGsVUgYBQzNmO10IPkFFWGh1T1h0Qz4mEyNBGwEATQc0JlIFJCUACzt1UlhnWFIDHSxdBgYJBGsFI1oOOx8MFS11UlhlV0lvOCJSGhsODSJoCFkCMioJKyA0CxcjEFJyVC1UHhwCaWVmbxUIPDgAcmh1T1h0Q1JvOCJSGhsODSJoDUcENyMRFi0mHFhpQyQmBz5UHhxJPCcnLF4YIGUnCiEyBww6BgE8VCRHUl5tQ2VmbxVNcGspES89GxE6BFwMGCRWGTsODiBmchU7OTgQGSQmQSc2AhEkATsbMQMIAC4SJlgIcCQXWHlhZVh0Q1JvVGsVPgYACzEvIVJDFycKGik5PBA1Bx04B2sIUjkOEDAnI0ZDDykEGyMgH1YTDx0tFSdmGg4DDDI1b0tQcC0EFDswZVh0Q1IqGi8/FwEDaU9rYhWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+ui29uKt4dvX5/+F9tWk2qWPxduH7di3+uheTl9vTWUVJyZtTmhmraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3Fje3Egefflt6lkPr3gdDWraD9st71mt3FZQgmChw7XGMXKTZVKBhmA1oMNCILH2gaDQs9BxsuGh5cUgkIEWVjPBVDfmVHUXIzAAo5AgZnNyRbFAYATQIHAnAyHgooPWF8ZXI4DBEuGGt5Gw0VAjc/YxU5OC4IHQU0ARkzBgBjVBhUBAoqAisnKFAfWicKGyk5Txc/NjtvSWtFEQ4LD20gOlsOJCIKFmB8ZVh0Q1IDHSlHEx0eQ2VmbxVNbWsJFykxHAwmChwoXCxUHwpdKzEyP3IIJGMmFyYzBh96NjsQJg5lPU9JTWVkA1wPIioXAWY5Ghl2SltnXUEVUk9HNy0jIlAgMSUEHy0nT0V0Dx0uEDhBAAYJBG0hLlgIagMRDDgSCgx8IB0hEiJSXDouPBcDH3pNfmVFWikxCxc6EF0bHC5YFyIGDSQhKkdDPD4EWmF8R1FeQ1JvVBhUBAoqAisnKFAfcGtYWCQ6DhwnFwAmGiwdFQ4KBn8OO0EdFy4RUAs6AR49BFwaPRRnNz8oQ2tobxcMNC8KFjt6PBkiBj8uGipSFx1JDzAnbRxEeGJvHSYxRnI9BVIhGz8VHQQyKmUpPRUDPz9FNCE3HRkmGlI7HC5beE9HQ2UxLkcDeGk+IXoeTzAhAS9vMipcHgoDQzEpb1kCMS9FNyomBhw9AhwaHWUVMw0IETEvIVJDcmJvWGh1TycTTSt9PxRjPSMrJhwZB2AvDwcqOQwQK1hpQxwmGHAVAAoTFjcoRVADNEFvFCc2DhR0LAI7HSRbAUNHNyohKFkII2tYWAQ8DQo1EQthOztBGwAJEGlmA1wPIioXAWYBAB8zDxc8fgdcEB0GETxoCVofMy4mEC02BBo7G1JyVC1UHhwCaU8qIFYMPGsDDSY2GxE7DVIBGz9cFBZPFywyI1BBcC8ACyt5Tx0mEVtFVGsVUiMOATcnPUxXHiQRES4sRwN0Nxs7GC4VT08CETdmLlsJcGNHPTonAAp0gfLtVGkVXEFHFywyI1BEcCQXWDw8GxQxT1ILEThWAAYXFywpIRVQcC8ACyt1AAp0QVBjVB9cHwpHXmVyb0hEWi4LHEJfAxc3Ah5vIyJbFgAQQ3hmA1wPIioXAXIWHR01FxcYHSVRHRhPGE9mbxVNBCIRFC11T1h0Q1JvVGsVUk9aQ2cQIFkBNTIHGSQ5TzQxBBchEDgVUo3nwWVmFgcmcAMQGmh1GVp0TVxvNyRbFAYATRYFHXw9BBQzPRp5ZVh0Q1IJGyRBFx1HQ2VmbxVNcGtFWHV1TSFmKFIcFzlcAhtHISQlJAcvMSgOWGi379p0Q1BvWmUVMQAJBSwhYXIsHQ46NgkYKlReQ1JvVAVaBgYBGhYvK1BNcGtFWGh1Ulh2MRsoHD8XXmVHQ2VmHF0CJwgQCzw6AjshEQEgBmsIUhsVFiBqRRVNcGsmHSYhCgp0Q1JvVGsVUk9HQ3hmO0cYNWdvWGh1TzkhFx0cHCRCUk9HQ2VmbxVNbWsRCj0wQ3J0Q1JvJi5GGxUGASkjbxVNcGtFWGhoTwwmFhdjfmsVUk8kDDcoKkc/MS8MDTt1T1h0Q09vRXsZeBJOaU8qIFYMPGsxGSomT0V0GHhvVGsVMA4LD2VmbxVNbWsyESYxAA9uIhYrICpXWk0lAikqbRlNcGtFWGh3DAo7EAEnFSJHUEZLaWVmbxU9PCocHTp1T1hpQyUmGi9aBVUmByESLldFchsJGTEwHVp4Q1JvVGlAAQoVQWxqRRVNcGsgKxh1T1h0Q1JyVBxcHAsIFH8HK1E5MSlNWg0GP1p4Q1JvVGsVUk0CGiBkZhlncGtFWAU8HBt0Q1JvVHYVJQYJByoxdXQJNB8EGmB3IhEnAFBjVGsVUk9HQSwoKVpPeWdvWGh1Tzs7DRQmEzgVUlJHNCwoK1oaagoBHBw0DVB2IB0hEiJSAU1LQ2VmbVEMJCoHGTswTVF4aVJvVGtmFxsTCishPBVQcBwMFiw6GEIVBxYbFSkdUDwCFzEvIVIecmdFWGomCgwgChwoB2kcXmVHQ2VmDEcINCIRC2h1UlgDChwrGzwPMwsDNyQkZxcuIi4BETwmTVR0Q1JtHC5UABtFSmlMMj9nfWZFmtzVjezUgebPVB90ME9WQ6fG2xUvEQcpWKrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA43gjGyhUHk8lAikqG1cVHGtYWBw0DQt6IRMjGHF0FgsrBiMyG1QPMiQdUGFfAxc3Ah5vJDlQFjsGAWVmchUvMScJLCotI0IVBxYbFSkdUD8VBiEvLEEEPyVHUUI5ABs1D1IOAT9aJg4FQ2V7b3cMPCcxGjAZVTkwByYuFmMXMxoTDGUWIEYEJCIKFmp8ZRQ7ABMjVB5ZBjsGAWVmbwhNEioJFBw3FzRuIhYrICpXWk0mFjEpb2ABJGlMckIFHR0wNxMtTgpRFiMGASAqZ05NBC4dDGhoT1oCCgE6FScVEwYDEGWkz6FNPCoLHCE7CFg5AgAkETkZUg0GDylmPEEMJDhFFz4wHRQ1Gl5vBipbFQpHFypmLVQBPGVHVGgRAB0nNAAuBGsIUhsVFiBmMhxnADkAHBw0DUIVBxYLHT1cFgoVS2xMH0cINB8EGnIUCxwADBUoGC4dUCMGDSEvIVIgMTkOHTp3Q1gvQyYqDD8VT09FLyQoK1wDN2sIGTo+Cgp0SxwqGyUVAg4DSmdqRRVNcGsxFyc5GxEkQ09vVhhFExgJEGUnb1IBPzwMFi91HxkwQwUnETlQUhsPBmUkLlkBcDwMFCR1Axk6B1xvITtRExsCEGUqJkMIfmlJcmh1T1gQBhQuASdBUlJHBSQqPFBBcAgEFCQ3Dhs/Q09vMRhlXBwCFwknIVEEPiwoGTo+Cgp0HltFJDlQFjsGAX8HK1E5PywCFC19TTo1Dx4KJxsXXk8cQxEjN0FNbWtHOik5A1g9DRQgVCRDFx0LAjxkYz9NcGtFLCc6Aww9E1JyVGlzHgAGFywoKBUBMSkAFGg6AVggCxdvFipZHk8UCyoxJlsKcC8MCzw0ARsxQ1lvAi5ZHQwOFzxobRlncGtFWAwwCRkhDwZvSWtTEwMUBmlmDFQBPCkEGyN1UlgRMCJhBy5BMA4LD2U7Zj89Ii4BLCk3VTkwBzYmAiJRFx1PSk8WPVAJBCoHQgkxCys4ChYqBmMXNR0GFSwyNhdBcDBFLC0tG1hpQ1ANFSdZUggVAjMvO0xNeCYEFj00A1F2T1ILES1UBwMTQ3hmegVBcAYMFmhoT014Qz8uDGsIUl1SU2lmHVoYPi8MFi91UlhkT1IcAS1TGxdHXmVkb0YZfzinymp5ZVh0Q1IbGyRZBgYXQ3hmbX0ENyMACmhoTxo1Dx5vEipZHhxHBSQ1O1AffmsxDSYwTw06FxsjVD9dF08KAjctKkdNPSoRGyAwHFgmBhMjHT9MXE8jBiMnOlkZcH5VWD86HRMnQxQgBmtTHgAGFzxmOVoBPC4cGik5A1Z2T3hvVGsVMQ4LDycnLF5NbWsDDSY2GxE7DVo5XWt2HQEBCiJoCGcsBgIxIWhoTw50BhwrVDYceD8VBiESLldXES8BLCcyCBQxS1AOAT9aNR0GFSwyNhdBcDBFLC0tG1hpQ1AOAT9aXwsCFyAlOxUKIioTETwsTx4mDB9vBypYAgMCEGdqRRVNcGsxFyc5GxEkQ09vVhxUBgwPBjZmO10IcCkEFCR1DhYwQxEgGTtABgoUQzEuKhUKMSYAXzt1DhsgFhMjVCxHExkOFzxob3obNTkXESwwHFggCxdvBydcFgoVTWdqRRVNcGshHS40GhQgQ09vADlAF0NtQ2Vmb3YMPCcHGSs+T0V0BQchFz9cHQFPFWxmDVQBPGU6DTswLg0gDDU9FT1cBhZHXmUwb1ADNGsYUUIXDhQ4TS06By50BxsIJDcnOVwZKWtYWDwnGh1eaTM6ACRhEw1dIiEiA1QPNSdNA2gBCgAgQ09vVgpABgBKEyo1JkEEPyUWWDE6Ggp0ABouBipWBgoVQyQyb0EFNWsVCi0xBhsgBhZvGCpbFgYJBGU1P1oZfms/ORh4CQo9BhwrGDIVkO/zQzUzPVABKWsGFCEwAQx0Dh05ESZQHBtJQWlmC1oIIxwXGTh1UlggEQcqVDYceC4SFyoSLldXES8BPCEjBhwxEVpmfgpABgAzAid8DlEJBCQCHyQwR1oVFgYgJCRGUENHGGUSKk0ZcHZFWgkgGxd0Mx08HT9cHQFFT2UCKlMMJScRWHV1CRk4EBdjfmsVUk8zDCoqO1wdcHZFWgs6AQw9DQcgAThZC08KDDMjPBUUPz5FDCd1GBAxERdvACNQUg0GDylmOFwBPGsJGSYxQVp4aVJvVGt2EwMLASQlJBVQcC0QFishBhc6SwRmVCJTUhlHFy0jIRUsJT8KKCcmQQsgAgA7XGIVFwMUBmUHOkECACQWVjshAAh8SlIqGi8VFwEDQzhvRXQYJCQxGSpvLhwwJwAgBC9aBQFPQQQzO1o9PzgoFywwTVR0GFIbETNBUlJHQQgpK1BPfGszGSQgCgt0XlI0VGlhFwMCEyo0OxdBcGkyGSQ+TVgpT1ILES1UBwMTQ3hmbWEIPC4VFzohTVReQ1JvVB9aHQMTCjVmchVPBC4JHTg6HQx0XlI8GipFXE8wAiktbwhNJTgAWCAgAhk6DBsrTgZaBAozDGVuIlofNWsLGTwgHRk4T1IjEThGUh0CDywnLVkIeWVHVEJ1T1h0IBMjGClUEQRHXmUgOlsOJCIKFmAjRlgVFgYgJCRGXDwTAjEjYVgCNC5FRWgjTx06B1IyXUF0BxsINyQkdXQJNBgJESwwHVB2Igc7GxtaASYJFyA0OVQBcmdFA2gBCgAgQ09vVghdFwwMQywoO1AfJioJWmR1Kx0yAgcjAGsIUl9JUmlmAlwDcHZFSGZlWlR0LhM3VHYVQENHMSozIVEEPixFRWhnQ1gHFhQpHTMVT09FQzZkYz9NcGtFOyk5Axo1ABlvSWtTBwEEFywpIR0beWskDTw6PxcnTSE7FT9QXAYJFyA0OVQBcHZFDmgwARx0HltFNT5BHTsGAX8HK1E+PCIBHTp9TTkhFx0fGzhhAAYABCA0bRlNK2sxHTAhT0V0QTAuGCcVAR8CBiFmO10fNTgNFyQxTVR0JxcpFT5ZBk9aQ3Bqb3gEPmtYWHh5TzU1G1JyVHoFQkNHMSozIVEEPixFRWhlQ3J0Q1JvICRaHhsOE2V7bxciPiccWDowDhsgQwUnESUVEA4LD2UwKlkCMyIRAWgwFxsxBhY8VD9dGxxJQ3VmchUMPDwEATt1HR01AAZhVmc/Uk9HQwYnI1kPMSgOWHV1CQ06AAYmGyUdBEZHIjAyIGUCI2U2DCkhClYgERsoEy5HIR8CBiFmchUbcC4LHGgoRnIVFgYgICpXSC4DBxYqJlEIImNHOT0hACg7ECttWGtOUjsCGzFmchVPBi4XDCE2DhR0DBQpBy5BUENHJyAgLkABJGtYWHh5TzU9DVJyVGYEQkNHLiQ+bwhNY3tJWBo6GhYwChwoVHYVQ0NHMDAgKVwVcHZFWmgmG1p4aVJvVGthHQALFyw2bwhNchsKCyEhBg4xQx4mEj9GUhYIFmUzPxVFJTgAHj05Tx47EVIlASZFXxwXCi4jPBxDcmdvWGh1Tzs1Dx4tFSheUlJHBTAoLEEEPyVNDmF1Lg0gDCIgB2VmBg4TBmspKVMeNT88WHV1GVgxDRZvCWI/MxoTDBEnLQ8sNC8xFy8yAx18QT04GhhcFgooDSk/bRlNK2sxHTAhT0V0QT0hGDIVAAoGADFmIFtNPzwLWDs8Cx12T1ILES1UBwMTQ3hmO0cYNWdvWGh1Tyw7DB47HTsVT09FMC4vPxUaOC4LWCo0AxR0CgFvHC5UFgYJBGUyIBUZOC5FFzglABYxDQZoB2tGGwsCTWdqRRVNcGsmGSQ5DRk3CFJyVC1AHAwTCiooZ0NEcAoQDCcFAAt6MAYuAC4bHQELGgoxIWYENC5FRWgjTx06B1IyXUE/X0JHIjAyIBU4PD9FCz03Qgw1AXgaGD9hEw1dIiEiA1QPNSdNA2gBCgAgQ09vVgpABgBKBSw0KkZNKSQQCmgGHx03ChMjVGNAHhtOQzIuKltNMyMECi8wTwoxAhEnETgVBgcCQzEuPVAeOCQJHGZ1PR01BwFvFyNUAAgCQykvOVBNNjkKFWghBx10NjthVmcVNgACEBI0LkVNbWsRCj0wTwV9aScjAB9UEFUmByECJkMENC4XUGFfOhQgNxMtTgpRFjsIBCIqKh1PET4RFx05G1p4QwlvIC5NBk9aQ2cHOkECcB4JDGp5TzwxBRM6GD8VT08BAik1KhlncGtFWBw6ABQgCgJvSWsXIQYKFiknO1AecCpFEy0sTwgmBgE8VDxdFwFHMDUjLFwMPGsMC2g2BxkmBBcrWmkZeE9HQ2UFLlkBMioGE2hoTx4hDRE7HSRbWhlOQywgb0NNJCMAFmgUGgw7Nh47WjhBEx0TS2xmKlkeNWskDTw6OhQgTQE7GzsdW08CDSFmKlsJcDZMch05Gyw1AUgOEC9mHgYDBjdubWABJB8NCi0mBxc4B1BjVDAVJgofF2V7bxcrOTkAWCkhTxs8AgAoEWvX+8pFT2UCKlMMJScRWHV1XlZkT1ICHSUVT09XTXRqb3gMKGtYWHl7X1R0MR06Gi9cHAhHXmV0Yz9NcGtFLCc6Aww9E1JyVGkEXF9HXmUxLlwZcC0KCmgzGhQ4QxEnFTlSF0FHU2t+bwhNNiIXHWgwDgo4GlJnByRYF08ECyQ0PBUJPyVCDGg7Ch0wQxQ6GCccXE1LaWVmbxUuMScJGik2BFhpQxQ6GihBGwAJSzNvb3QYJCQwFDx7PAw1FxdhACNHFxwPDCkibwhNJmsAFix1ElFeNh47ICpXSC4DBwwoP0AZeGkwFDweCgF2T1I0VB9QChtHXmVkGlkZcCAAAWh9HBE6BB4qVCdQBhsCEWxkYxUpNS0EDSQhT0V0QSNtWEEVUk9HMyknLFAFPycBHTp1Ulh2MlJgVA4VXU81Q2pmCRVCcAxHVEJ1T1h0Nx0gGD9cAk9aQ2cSJ1BNOy4cWDE6Ggp0MAIqFyJUHk8OEGUkIEADNGsRF2Z1LBA1DRUqVCJbXwgGDiBmHFAZJCILHzt1jf7GQzEgGj9HHQMUQywgb0ADIz4XHWZ3Q3J0Q1JvNypZHg0GAC5mchULJSUGDCE6AVAiSnhvVGsVUk9HQywgb0EUIC5NDmF1UkV0QQE7BiJbFU1HAisibxYbcHVYWHl1GxAxDXhvVGsVUk9HQ2VmbxUsJT8KLSQhQSsgAgYqWiBQC09aQzN8PEAPeHpJSWFvGggkBgBnXUEVUk9HQ2Vmb1ADNEFFWGh1ChYwQw9mfh5ZBjsGAX8HK1E+PCIBHTp9TS04FzEgGydRHRgJQWlmNBU5NTMRWHV1TTs7DB4rGzxbUg0CFzIjKltNNiIXHTt3Q1gQBhQuASdBUlJHU2tzYxUgOSVFRWhlQUl4Qz8uDGsIUlpLQxcpOlsJOSUCWHV1XVR0MAcpEiJNUlJHQWU1bRlncGtFWBw6ABQgCgJvSWsXMxkICiE1b10MPSYACiE7CFggCxdvHy5MUgYBQyYuLkcKNWsWDCksHFg1F1I7HDlQAQcIDyFobRlncGtFWAs0AxQ2AhEkVHYVFBoJADEvIFtFJmJFOT0hAC04F1wcACpBF0EEDCoqK1oaPmtYWD51ChYwQw9mfh5ZBjsGAX8HK1EpOT0MHC0nR1FeNh47ICpXSC4DBxEpKFIBNWNHLSQhIR0xBwENFSdZUENHGGUSKk0ZcHZFWgc7AwF0BRs9EWtCGgoJQysjLkdNMioJFGp5TzwxBRM6GD8VT08BAik1KhlncGtFWBw6ABQgCgJvSWsXIQQOE2UyJ1BNJScRWD07Ax0nEFI7HC4VEA4LD2UvPBUaOT8NESZ1HRk6BBdvlsuhUhwGFSA1b1YFMTkCHWgzAAp0EAImHy5GXE1LaWVmbxUuMScJGik2BFhpQxQ6GihBGwAJSzNvb3QYJCQwFDx7PAw1FxdhGi5QFhwlAikqDFoDJCoGDGhoTw50BhwrVDYceDoLFxEnLQ8sNC82FCExCgp8QScjAAhaHBsGADEULlsKNWlJWDN1Ox0sF1JyVGl3EwMLQyYpIUEMMz9FCik7CB12T1ILES1UBwMTQ3hmfgdBcAYMFmhoT0x4Qz8uDGsIUlpXT2UUIEADNCILH2hoT0h4QyE6Ei1cCk9aQ2dmPEFPfEFFWGh1LBk4DxAuFyAVT08BFislO1wCPmMTUWgUGgw7Nh47WhhBExsCTSYpIUEMMz83GSYyClhpQwRvESVRUhJOaU8qIFYMPGsnGSQ5PVhpQyYuFjgbMA4LD38HK1E/OSwNDA8nAA0kAR03XGl5GxkCQycnI1lNOSUDF2p5T1o9DRQgVmI/MA4LDxd8DlEJHCoHHSR9FFgABgo7VHYVUD0CAilrO1wANWsBGTw0Txc6QwYnEWtUERsOFSBmLVQBPGVHVGgRAB0nNAAuBGsIUhsVFiBmMhxnEioJFBpvLhwwJxs5HS9QAEdOaSkpLFQBcCcHFAo0AxQEDAFvSWt3EwMLMX8HK1EhMSkAFGB3LRk4D1I/GzgPUkJFSk8qIFYMPGsJGiQXDhQ4NRcjVHYVMA4LDxd8DlEJHCoHHSR9TS4xDx0sHT9MSE9KQWxMI1oOMSdFFCo5LRk4DzYmBz8VT08lAikqHQ8sNC8pGSowA1B2Jxs8ACpbEQpdQ2hkZj8BPygEFGg5DRQWAh4jMR90Uk9aQwcnI1k/agoBHAQ0DR04S1ADFSVRUiozIn9mYhdEWicKGyk5TxQ2DzU9FT1cBhZHQ3hmDVQBPBlfOSwxIxk2Bh5nVgxHExkOFzxmbw9NfWlMciQ6DBk4Qx4tGB5ZBiwPAjchKghNEioJFBpvLhwwLxMtEScdUDoLF2UlJ1QfNy5fWGV3RnIWAh4jJnF0FgsjCjMvK1AfeGJvOik5AypuIhYrNj5BBgAJSz5mG1AVJGtYWGoBChQxEx09AGthPU8FAikqbRlNFj4LG2hoTx4hDRE7HSRbWkZtQ2Vmb1kCMyoJWDh1UlgWAh4jWjtaAQYTCiooZxxncGtFWCEzTwh0FxoqGmtgBgYLEGsyKlkIICQXDGAlT1N0NRcsACRHQUEJBjJufxlcfHtMUXN1IRcgChQ2XGl3EwMLQWlmbdfrwmsHGSQ5TVF0Bh48EWt7HRsOBTxubXcMPCdHVGh3IRd0ARMjGGtTHRoJB2dqb0EfJS5MWC07C3IxDRZvCWI/MA4LDxd8DlEJEj4RDCc7RwN0Nxc3AGsIUk0zBikjP1ofJGsRF2gZLjYQKjwIVmcVNBoJAGV7b1MYPigRESc7R1FeQ1JvVCdaEQ4LQxpqb10fIGtYWB0hBhQnTRUqAAhdEx1PSk9mbxVNPCQGGSR1CRQ7DAAWVHYVGh0XQyQoKxVFODkVVhg6HBEgCh0hWhIVX09VTXBvb1ofcHtvWGh1TxQ7ABMjVCdUHAtHXmUELlkBfjsXHSw8DAwYAhwrHSVSWgkLDCo0FhxncGtFWCEzTxQ1DRZvACNQHE8yFywqPBsZNScACCcnG1A4AhwrXXAVPAATCiM/ZxcvMScJWmR1TZrS8VIjFSVRGwEAQWxmKlkeNWsrFzw8CQF8QTAuGCcXXk9FLSpmP0cINCIGDCE6AVp4QwY9AS4cUgoJB08jIVFNLWJvcmV4T5rA45Db9Kmh8k8zIgdmfRWP0N9FKAQUNj0GQ5Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA43gjGyhUHk83DzcKbwhNBCoHC2YFAxktBgB1NS9RPgoBFwI0IEAdMiQdUGoYAA4xDhchAGkZUk0SECA0bRxnACcXNHIUCxwYAhAqGGNOUjsCGzFmchVPAzsAHSx5TxIhDgJjVC1ZC0NHDSolI1wdfms3HWU0Hwg4Chc8VCRbUh0CEDUnOFtDcmdFPCcwHC8mAgJvSWtBABoCQzhvRWUBIgdfOSwxKxEiChYqBmMceD8LEQl8DlEJAycMHC0nR1oDAh4kJztQFwtFT2U9b2EIKD9FRWh3OBk4CFIcBC5QFk1LQwEjKVQYPD9FRWhnXFR0LhshVHYVQ1lLQwgnNxVQcHpVSGR1PRchDRYmGiwVT09XT2UVOlMLOTNFRWh3TwsgFhY8WzgXXmVHQ2VmG1oCPD8MCGhoT1oTAh8qVC9QFA4SDzFmJkZNYnhLWmR1LBk4DxAuFyAVT08qDDMjIlADJGUWHTwCDhQ/MAIqES8VD0ZtMyk0Aw8sNC82FCExCgp8QTg6GTtlHRgCEWdqb05NBC4dDGhoT1oeFh8/VBtaBQoVQWlmC1ALMT4JDGhoT01kT1ICHSUVT09SU2lmAlQVcHZFSn1lQ1gGDAchECJbFU9aQ3VqRRVNcGsmGSQ5DRk3CFJyVAZaBAoKBisyYUYIJAEQFTgFAA8xEVIyXUFlHh0rWQQiK2ECNywJHWB3JhYyKQciBGkZUhRHNyA+OxVQcGksFi48AREgBlIFASZFUENHJyAgLkABJGtYWC40AwsxT1IMFSdZEA4ECGV7b3gCJi4IHSYhQQsxFzshEgFAHx9HHmxMH1kfHHEkHCwBAB8zDxdnVgVaEQMOE2dqbxUWcB8AADx1Ulh2LR0sGCJFUENHQ2VmbxVNcA8AHikgAwx0XlIpFSdGF0NHICQqI1cMMyBFRWgYAA4xDhchAGVGFxspDCYqJkVNLWJvKCQnI0IVBxYLHT1cFgoVS2xMH1kfHHEkHCwGAxEwBgBnVgNcBg0IG2dqb05NBC4dDGhoT1ocCgYtGzMVAQYdBmdqb3EINioQFDx1UlhmT1ICHSUVT09VT2ULLk1NbWtUTWR1PRchDRYmGiwVT09XT2UVOlMLOTNFRWh3TwsgFhY8Vmc/Uk9HQxEpIFkZOTtFRWh3LREzBBc9VDlaHRtHEyQ0OxVQcC4ECyEwHVg2Ah4jVChaHBsGADFobRlNEyoJFCo0DBN0XlICGz1QHwoJF2s1KkElOT8HFzB1ElFeaR4gFypZUj8LERdmchU5MSkWVhg5DgExEUgOEC9nGwgPFwI0IEAdMiQdUGoUCw41DREqEGkZUk0QESAoLF1PeUE1FDoHVTkwBz4uFi5ZWhRHNyA+OxVQcGkjFDF5Tz4bNVI6GidaEQRLQyQoO1xAEQ0uVGgmDg4xTAAqFypZHk8XDDYvO1wCPmVHVGgRAB0nNAAuBGsIUhsVFiBmMhxnACcXKnIUCxwQCgQmEC5HWkZtMyk0HQ8sNC8xFy8yAx18QTQjDWkZUhRHNyA+OxVQcGkjFDF3Q1gQBhQuASdBUlJHBSQqPFBBcB8KFyQhBgh0XlJtIwpmNk9MQxY2LlYIfwc2ECEzG1p4QzEuGCdXEwwMQ3hmAlobNSYAFjx7HB0gJR42VDYceD8LERd8DlEJAycMHC0nR1oSDwscBC5QFk1LQz5mG1AVJGtYWGoTAwF0EAIqES8XXk8jBiMnOlkZcHZFQHh5TzU9DVJyVHoFXk8qAj1mchVfZXtJWBo6GhYwChwoVHYVQkNtQ2Vmb3YMPCcHGSs+T0V0Lh05ESZQHBtJECAyCVkUAzsAHSx1ElFeMx49JnF0FgsjCjMvK1AfeGJvKCQnPUIVBxYcGCJRFx1PQQMJGRdBcDBFLC0tG1hpQ1AJHS5ZFk8IBWUQJlAacmdFPC0zDg04F1JyVHwFXk8qCitmchVZYGdFNSktT0V0UkB/WGtnHRoJBywoKBVQcHtJcmh1T1gADB0jACJFUlJHQQ0vKF0IImtYWDswClg5DAAqVCpHHRoJB2U/IEBDcB4WHS4gA1gyDABvADlUEQQODSJmO10IcCkEFCR7TVReQ1JvVAhUHgMFAiYtbwhNHSQTHSUwAQx6EBc7MgRjUhJOaRUqPWdXES8BPCEjBhwxEVpmfhtZAD1dIiEiG1oKNycAUGoUAQw9IjQEVmcVCU8zBj0ybwhNcgoLDCF4Lj4fQV5vMC5TExoLF2V7b0EfJS5Jcmh1T1gADB0jACJFUlJHQQcqIFYGI2sREC11XUh5DhshAT9QUgYDDyBmJFwOO2VHVGgWDhQ4ARMsH2sIUiIIFSArKlsZfjgADAk7GxEVJTlvCWI/PwARBigjIUFDIy4ROSYhBjkSKFo7Bj5QW2U3DzcUdXQJNA8MDiExCgp8SngfGDlnSC4DBwczO0ECPmMeWBwwFwx0XlJtJypDF08EFjc0KlsZcDsKCyEhBhc6QV5vMj5bEU9aQyMzIVYZOSQLUGF1Bh50Lh05ESZQHBtJECQwKmUCI2NMWDw9ChZ0LR07HS1MWk03DDZkYxc+MT0AHGZ3RlgxDRZvESVRUhJOaRUqPWdXES8BOj0hGxc6SwlvIC5NBk9aQ2cUKlYMPCdFCykjChx0Ex08HT9cHQFFT2UAOlsOcHZFHj07DAw9DBxnXWtcFE8qDDMjIlADJGUXHSs0AxQEDAFnXWtBGgoJQwspO1wLKWNHKCcmTVR2MRcsFSdZFwtJQWxmKlsJcC4LHGgoRnJeTl9vlt+1kPvngdHGb2EsEmtWWKrV+1gRMCJvlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGraHtst/lmtzVjezUgebPlt+1kPvngdHGRVkCMyoJWA0mHzR0XlIbFSlGXCo0M38HK1EhNS0RPzo6Ggg2DApnVhtZExYCEWUDHGVPfGtHHTEwTVFeJgE/OHF0FgsrAicjIx0WcB8AADx1Ulh2KxsoHCdcFQcTEGUpO10IImsVFCksCgonQwUmACMVBgoGDmglIFkCIi4BWCQ0DR04EFxtWGtxHQoUNDcnPxVQcD8XDS11ElFeJgE/OHF0FgsjCjMvK1AfeGJvPTslI0IVBxYbGyxSHgpPQQAVH2UBMTIACjt3Q1gvQyYqDD8VT09FMyknNlAfcA42KGp5TzwxBRM6GD8VT08BAik1KhlNEyoJFCo0DBN0XlIKJxsbAQoTMyknNlAfI2sYUUIQHAgYWTMrEAdUEAoLS2cSKlQAPSoRHWg2ABQ7EVBmTgpRFiwIDyo0H1wOOy4XUGoQPCgEDxM2ETl2HQMIEWdqb05ncGtFWAwwCRkhDwZvSWtwIT9JMDEnO1BDICcEAS0nLBc4DABjVB9cBgMCQ3hmbWEIMSYIGTwwTxs7Dx09Vmc/Uk9HQwYnI1kPMSgOWHV1CQ06AAYmGyUdEUZHJhYWYWYZMT8AVjg5DgExETEgGCRHUlJHAGUjIVFNLWJvPTslI0IVBxYDFSlQHkdFJisjIkxNMyQJFzp3RkIVBxYMGydaAD8OAC4jPR1PFRg1PSYwAgEXDB4gBmkZUhRtQ2Vmb3EINioQFDx1UlgRMCJhJz9UBgpJBisjIkwuPycKCmR1OxEgDxdvSWsXNwECDjxmLFoBPzlHVEJ1T1h0IBMjGClUEQRHXmUgOlsOJCIKFmA2RlgRMCJhJz9UBgpJBisjIkwuPycKCmhoTxt0BhwrVDYceGULDCYnIxUoIzs3WHV1Oxk2EFwKJxsPMwsDMSwhJ0EqIiQQCCo6F1B2IB06Bj8VNzw3QWlmbVgMIGlMcg0mHypuIhYrOCpXFwNPGGUSKk0ZcHZFWgQ0DR04EFIqFShdUgwIFjcyb08CPi5FUAs6GgogPDM9ESoEQkJUU2xmrbX5cD4WHS4gA1gyDABvGC5UAAEODSJmPFAfJi4WVmp5Tzw7BgEYBipFUlJHFzczKhUQeUEgCzgHVTkwBzYmAiJRFx1PSk8DPEU/agoBHBw6CB84BlptMRhlKAAJBjZkYxUWcB8AADx1Ulh2IB06Bj8VKAAJBmUqLlcIPDhHVGgRCh41Fh47VHYVFA4LECBqb3YMPCcHGSs+T0V0JiEfWjhQBjUIDSA1b0hEWg4WCBpvLhwwLxMtEScdUDUIDSBmLFoBPzlHUXIUCxwXDB4gBhtcEQQCEW1kCmY9CiQLHQs6AxcmQV5vD0EVUk9HJyAgLkABJGtYWA0GP1YHFxM7EWVPHQECICoqIEdBcB8MDCQwT0V0QSggGi4VEQALDDdkYz9NcGtFOyk5Axo1ABlvSWtTBwEEFywpIR0OeWsgKxh7PAw1FxdhDiRbFywIDyo0bwhNM2sAFix1ElFeJgE/JnF0FgsjCjMvK1AfeGJvPTslPUIVBxYbGyxSHgpPQQMzI1kPIiICEDx3Q1gvQyYqDD8VT09FJTAqI1cfOSwNDGp5TzwxBRM6GD8VT08BAik1KhlNEyoJFCo0DBN0XlIZHThAEwMUTTYjO3MYPCcHCiEyBwx0HltFfmYYUo3z46fSz9f50GsxOQp1W1i24+ZvOQJmMU+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27VnPCQGGSR1IhEnAD5vSWthEw0UTQgvPFZXES8BNC0zGz8mDAc/FiRNWk0gAigjb1wDNiRHVGh3BhYyDFBmfgZcAQwrWQQiK3kMMi4JUGB3PxQ1ABd1VG5GUEZdBSo0IlQZeAgKFi48CFYTIj8KKwV0PypOSk8LJkYOHHEkHCwZDhoxD1pnVhtZEwwCQwwCdRVINGlMQi46HRU1F1oMGyVTGwhJMwkHDHAyGQ9MUUIYBgs3L0gOEC95Ew0CD21ubXYfNSoRFzpvT10nQVt1EiRHHw4TSwYpIVMEN2UmKg0UOzcGSltFOSJGESNdIiEiC1wbOS8ACmB8ZRQ7ABMjVCdXHjoXFywrKhVQcAYMCysZVTkwBz4uFi5ZWk0yEzEvIlBNcGtFQmhlX0JkU0h/RGkceAMIACQqb1kPPBsKCws6GhYgQ09vOSJGESNdIiEiA1QPNSdNWgkgGxd5Ex08VGsPUl9FSk8LJkYOHHEkHCwRBg49Bxc9XGI/PwYUAAl8DlEJEj4RDCc7RwN0Nxc3AGsIUk01BjYjOxUeJCoRC2p5Tz4hDRFvSWtTBwEEFywpIR1EcBgRGTwmQQoxEBc7XGIOUiEIFywgNh1PAz8EDDt3Q1oGBgEqAGUXW08CDSFmMhxnWicKGyk5TzU9EBEdVHYVJg4FEGsLJkYOagoBHBo8CBAgJAAgATtXHRdPQRYjPUMIImlJWGoiHR06ABptXUF4GxwEMX8HK1EhMSkAFGAuTywxGwZvSWsXIAoNDCwob1ofcCMKCGghAFg1QxQ9EThdUhwCETMjPRtPfGshFy0mOAo1E1JyVD9HBwpHHmxMAlweMxlfOSwxKxEiChYqBmMceCIOECYUdXQJNAkQDDw6AVAvQyYqDD8VT09FMSAsIFwDcD8NETt1HB0mFRc9Vmc/Uk9HQwMzIVZNbWsDDSY2GxE7DVpmVCxUHwpdJCAyHFAfJiIGHWB3Ox04BgIgBj9mFx0RCiYjbRxXBC4JHTg6HQx8IB0hEiJSXD8rIgYDEHwpfGspFys0Ayg4AgsqBmIVFwEDQzhvRXgEIyg3QgkxCzohFwYgGmNOUjsCGzFmchVPAy4XDi0nTxA7E1JnBipbFgAKSmdqRRVNcGsjDSY2T0V0BQchFz9cHQFPSk9mbxVNcGtFWAY6GxEyGlptPCRFUENHQRYjLkcOOCILH2Z7QVp9aVJvVGsVUk9HFyQ1JBseICoSFmAzGhY3FxsgGmMceE9HQ2VmbxVNcGtFWCQ6DBk4QyYcVHYVFQ4KBn8BKkE+NTkTESswR1oABh4qBCRHBjwCETMvLFBPeUFFWGh1T1h0Q1JvVGtZHQwGD2UOO0EdAy4XDiE2ClhpQxUuGS4PNQoTMCA0OVwONWNHMDwhHysxEQQmFy4XW2VHQ2VmbxVNcGtFWGg5ABs1D1IgH2cVAAoUQ3hmP1YMPCdNHj07DAw9DBxnXUEVUk9HQ2VmbxVNcGtFWGh1HR0gFgAhVCxUHwpdKzEyP3IIJGNNWiAhGwgnWV1gEypYFxxJESokI1oVfigKFWcjXlczAh8qB2QQFkAUBjcwKkcefxsQGiQ8DEcnDAA7OzlRFx1aIjYlaVkEPSIRRXllX1p9WRQgBiZUBkckDCsgJlJDAAckOw0KJjx9SnhvVGsVUk9HQ2VmbxUIPi9Mcmh1T1h0Q1JvVGsVUgYBQyspOxUCO2sREC07TzY7FxspDWMXOgAXQWlkB0EZIAwADGgzDhE4BhZhVmdBABoCSn5mPVAZJTkLWC07C3J0Q1JvVGsVUk9HQ2UqIFYMPGsKE3p5Txw1FxNvSWtFEQ4LD20gOlsOJCIKFmB8TwoxFwc9Gmt9BhsXMCA0OVwONXEvKwcbKx03DBYqXDlQAUZHBisiZj9NcGtFWGh1T1h0Q1ImEmtbHRtHDC50b1ofcCUKDGgxDgw1Qx09VCVaBk8DAjEnYVEMJCpFDCAwAVgaDAYmEjIdUCcIE2dqbXcMNGsXHTslABYnBlxtWD9HBwpOWGU0KkEYIiVFHSYxZVh0Q1JvVGsVUk9HQyMpPRUyfGsWCj51BhZ0CgIuHTlGWgsGFyRoK1QZMWJFHCdfT1h0Q1JvVGsVUk9HQ2Vmb1wLcDgXDmYlAxktChwoVCpbFk8UETNoIlQVACcEAS0nHFg1DRZvBzlDXB8LAjwvIVJNbGsWCj57AhksMx4uDS5HAU9KQ3RmLlsJcDgXDmY8C1gqXlIoFSZQXCUIAQwib0EFNSVvWGh1T1h0Q1JvVGsVUk9HQ2VmbxU5A3ExHSQwHxcmFyYgJCdUEQouDTYyLlsONWMmFyYzBh96Mz4ONw5qOytLQzY0ORsENGdFNCc2DhQEDxM2ETkcSU8VBjEzPVtncGtFWGh1T1h0Q1JvVGsVUgoJB09mbxVNcGtFWGh1T1gxDRZFVGsVUk9HQ2VmbxVNHiQRES4sR1ocDAJtWGl7HU8UBjcwKkdNNiQQFix7TVQgEQcqXUEVUk9HQ2Vmb1ADNGJvWGh1Tx06B1IyXUE/X0JHLywwKhUYIC8EDC11Axc7E1JnBydaBQoVQzIuKltNPiRFGik5A1i24+ZvRjgVGwEUFyAnKxUCNmtVVn0mQ1gnAgQqB2tCHR0MSk8yLkYGfjgVGT87Rx4hDRE7HSRbWkZtQ2Vmb0IFOScAWDwnGh10Bx1FVGsVUk9HQ2VrYhUkNmsHGSQ5TwgmBgEqGj8VkOn1Q3VoekZNIi4DCi0mB1R0ChRvGiRBUo3h8WV0PBUfNS0XHTs9ZVh0Q1JvVGsVBg4UCGsxLlwZeAkEFCR7MBs1ABoqEBtUABtHAisibwVDZWsKCmhnQUh9aVJvVGsVUk9HEyYnI1lFNj4LGzw8ABZ8SnhvVGsVUk9HQ2VmbxUBPygEFGgKQ1gkAgA7VHYVMA4LD2sgJlsJeGJvWGh1T1h0Q1JvVGsVHgAEAilmEBlNODkVWHV1Ogw9DwFhEy5BMQcGEW1vRRVNcGtFWGh1T1h0QxspVDtUABtHAisib1kPPAkEFCQFAAt0AhwrVCdXHi0GDykWIEZDAy4RLC0tG1ggCxchfmsVUk9HQ2VmbxVNcGtFWGg5ABs1D1I/VHYVAg4VF2sWIEYEJCIKFkJ1T1h0Q1JvVGsVUk9HQ2VmI1oOMSdFDmhoTzo1Dx5hAi5ZHQwOFzxuZj9NcGtFWGh1T1h0Q1JvVGsVHg0LISQqI2UCI3E2HTwBCgAgSwE7BiJbFUEBDDcrLkFFcgkEFCR1HxcnWVJqEGcVVwtLQ2AibRlNIGU9VGglQSF4QwJhLmIceE9HQ2VmbxVNcGtFWGh1T1g4AR4NFSdZJAoLWRYjO2EIKD9NCzwnBhYzTRQgBiZUBkdFNSAqIFYEJDJfWG17Xx50EAY6EDgaAU1LQzNoAlQKPiIRDSwwRlFeQ1JvVGsVUk9HQ2VmbxVNcCIDWCAnH1ggCxchfmsVUk9HQ2VmbxVNcGtFWGh1T1h0DxAjNipZHisOEDF8HFAZBC4dDGAmGwo9DRVhEiRHHw4TS2cCJkYZMSUGHXJ1SlZkBVI8AD5RAU1LQ20uPUVDACQWETw8ABZ0TlI/XWV4EwgJCjEzK1BEeUFFWGh1T1h0Q1JvVGsVUk9HBisiRRVNcGtFWGh1T1h0Q1JvVGtZHQwGD2UZYxUZcHZFOik5A1YkERcrHShBPg4JBywoKB0FIjtFGSYxT1A8EQJhJCRGGxsODCtoFhVAcHlLTWF8ZVh0Q1JvVGsVUk9HQ2VmbxUENmsRWDw9ChZ0DxAjNipZHiozIn8VKkE5NTMRUDshHRE6BFwpGzlYExtPQQknIVFNFR8kQmhwQUoyQwFtWGtBW0ZtQ2VmbxVNcGtFWGh1T1h0QxcjBy4VHg0LISQqI3A5EXE2HTwBCgAgS1ADFSVRUiozIn9mYhdEcC4LHEJ1T1h0Q1JvVGsVUk8CDzYjJlNNPCkJOik5Ayg7EFI7HC5beE9HQ2VmbxVNcGtFWGh1T1g4AR4NFSdZIgAUWRYjO2EIKD9NWgo0AxR0Ex08TmsYUEZtQ2VmbxVNcGtFWGh1T1h0Qx4tGAlUHgMxBil8HFAZBC4dDGB3OR04DBEmADIPUkJFSk9mbxVNcGtFWGh1T1h0Q1JvGClZMA4LDwEvPEFXAy4RLC0tG1B2Jxs8ACpbEQpdQ2hkZj9NcGtFWGh1T1h0Q1JvVGsVHg0LISQqI3A5EXE2HTwBCgAgS1ADFSVRUiozIn9mYhdEWmtFWGh1T1h0Q1JvVC5bFmVHQ2VmbxVNcGtFWGg8CVg4AR4aBD9cHwpHAisib1kPPB4VDCE4ClYHBgYbETNBUhsPBitmI1cBBTsRESUwVSsxFyYqDD8dUDoXFywrKhVNcGtfWGp1QVZ0MAYuADgbBx8TCigjZxxEcC4LHEJ1T1h0Q1JvVGsVUk8OBWUqLVk9PzgmFz07G1g1DRZvGClZIgAUICozIUFDAy4RLC0tG1ggCxchVCdXHj8IEAYpOlsZahgADBwwFwx8QTM6ACQYAgAUQ2V8bxdNfmVFKzw0Gwt6Ex08HT9cHQECB2xmKlsJWmtFWGh1T1h0Q1JvVCJTUgMFDwI0LkMEJDJFGSYxTxQ2DzU9FT1cBhZJMCAyG1AVJGsREC07ZVh0Q1JvVGsVUk9HQ2VmbxUBPygEFGgyT0V0SzAuGCcbLRoUBgQzO1oqIioTETwsTxk6B1INFSdZXDADBjEjLEEINAwXGT48GwF9Qx09VAhaHAkOBGsBHXQ7GR88cmh1T1h0Q1JvVGsVUk9HQ2UqIFYMPGsWCit1Ulh8IRMjGGVqBxwCIjAyIHIfMT0MDDF1DhYwQzAuGCcbLQsCFyAlO1AJFzkEDiEhFlF0AhwrVGlUBxsIQWUpPRVPPSoLDSk5TXJ0Q1JvVGsVUk9HQ2VmbxVNPCkJPzo0GREgGkgcET9hFxcTSzYyPVwDN2UDFzo4Dgx8QTU9FT1cBhZHQ39mahtcNmsWDGcmrcp0S1c8XWkZUghLQzY0LBxEWmtFWGh1T1h0Q1JvVC5bFmVHQ2VmbxVNcGtFWGg8CVg4AR4aGD92Gg4VBCBmLlsJcCcHFB05Gzs8AgAoEWVmFxszBj0yb0EFNSVvWGh1T1h0Q1JvVGsVUk9HQykpLFQBcDsGDGhoTzkhFx0aGD8bFQoTIC0nPVIIeGJFUmhkX0heQ1JvVGsVUk9HQ2VmbxVNcCcHFB05Gzs8AgAoEXFmFxszBj0yZ0YZIiILH2YzAAo5AgZnVh5ZBk8ECyQ0KFBXcG4BXW13Q1g5AgYnWi1ZHQAVSzUlOxxEeUFFWGh1T1h0Q1JvVGtQHAttQ2VmbxVNcGsAFix8ZVh0Q1IqGi8/FwEDSk9MYhhNst/lmtzVjezUQyYONmsCUo3n92UFHXApGR82WKrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50Knx+KrB75rA45Db9Kmh8o3z46fSz9f50EEJFys0A1gXET5vSWthEw0UTQY0KlEEJDhfOSwxIx0yFzU9Gz5FEAAfS2cHLVoYJGsRECEmTzAhAVBjVGlcHAkIQWxMDEchagoBHAQ0DR04SwlvIC5NBk9aQ2cQIFkBNTIHGSQ5TzQxBBchEDgVkO/zQxx0BBUlJSlHVGgRAB0nNAAuBGsIUhsVFiBmMhxnEzkpQgkxCzQ1ARcjXDAVJgofF2V7bxc5IioPHSshAAotQwI9ES9cERsODCtmZBUMJT8KVTg6HBEgCh0hVGAVHwARBigjIUFNASQpVmgFGgoxQxEjHS5bBkIUCiEjYxUDP2sDGSMwC1g1AAYmGyVGXE1LQwEpKkY6IioVWHV1GwohBlIyXUF2ACNdIiEiC1wbOS8ACmB8ZTsmL0gOEC95Ew0CD21ubWYOIiIVDGgjCgonCh0hVHEVVxxFSn8gIEcAMT9NOyc7CREzTSEMJgJlJjAxJhdvZj8uIgdfOSwxIxk2Bh5nVh58UgMOATcnPUxNcGtFWHJ1IBonChYmFSVgG01OaQY0Aw8sNC8pGSowA1B8QSEuAi4VFAALByA0bxVNcHFFXTt3RkIyDAAiFT8dMQAJBSwhYWYsBg46KgcaO1F9aXgjGyhUHk8kERdmchU5MSkWVgsnChw9FwF1NS9RIAYACzEBPVoYICkKAGB3Oxk2QzU6HS9QUENHQSgpIVwZPzlHUUIWHSpuIhYrOCpXFwNPGGUSKk0ZcHZFWh89Dgx0BhMsHGtBEw1HByojPA9PfGshFy0mOAo1E1JyVD9HBwpHHmxMDEc/agoBHAw8GREwBgBnXUF2AD1dIiEiA1QPNSdNA2gBCgAgQ09vVqm10E8lAikqb9ftxGspGSYxBhYzQx8uBiBQAENHAjAyIBgdPzgMDCE6AVR0ARMjGGtcHAkITWdqb3ECNTgyCiklT0V0FwA6EWtIW2UkERd8DlEJHCoHHSR9FFgABgo7VHYVUI3nwWUWI1QUNTlFmsjBTyskBhcrWGtfBwIXT2UuJkEPPzNJWC45FlR0JT0ZWmkZUisIBjYRPVQdcHZFDDogClgpSngMBhkPMwsDLyQkKllFK2sxHTAhT0V0QZDP1mtwIT9HgcXSb2UBMTIACjt1RwwxAh9iFyRZHR0CB2xqb1YCJTkRWDI6AR0nTVBjVA9aFxwwESQ2bwhNJDkQHWgoRnIXESB1NS9RPg4FBiluNBU5NTMRWHV1TZrUwVICHThWUo3n92UVKkcbNTlFGSshBhc6EF5vBz9UBhxJQWlmC1oIIxwXGTh1UlggEQcqVDYceCwVMX8HK1EhMSkAFGAuTywxGwZvSWsXkO/FQwYpIVMENzhFmsjBTys1FRdgGCRUFk8XESA1KkFNIDkKHiE5Cgt6QV5vMCRQATgVAjVmchUZIj4AWDV8ZTsmMUgOEC95Ew0CD209b2EIKD9FRWh3jfj2QyEqAD9cHAgUQ6fG2xU4GWsVCi0zHFR0AhE7HSRbUgcIFy4jNkZBcD8NHSUwQVp4QzYgEThiAA4XQ3hmO0cYNWsYUUJfQlV0gebPlt+1kPvnQxEHDRVbcKnl7GgGKiwAKjwIJ2vX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/heDx0sFScVIQoTL2V7b2EMMjhLKy0hGxE6BAF1NS9RPgoBFwI0IEAdMiQdUGocAQwxERQuFy4XXk9FDiooJkECImlMchswGzRuIhYrOCpXFwNPGGUSKk0ZcHZFWh48HA01D1I/Bi5TFx0CDSYjPBULPzlFDCAwTxUxDQdhVmcVNgACEBI0LkVNbWsRCj0wTwV9aSEqAAcPMwsDJywwJlEIImNMchswGzRuIhYrICRSFQMCS2cVJ1oaEz4WDCc4LA0mEB09VmcVCU8zBj0ybwhNcggQCzw6AlgXFgA8GzkXXk8jBiMnOlkZcHZFDDogClReQ1JvVAhUHgMFAiYtbwhNNj4LGzw8ABZ8FVtvOCJXAA4VGmsVJ1oaEz4WDCc4LA0mEB09VHYVBE8CDSFmMhxnAy4RNHIUCxwYAhAqGGMXMRoVECo0b3YCPCQXWmFvLhwwIB0jGzllGwwMBjdubXYYIjgKCgs6AxcmQV5vD0EVUk9HJyAgLkABJGtYWAs6AR49BFwONwhwPDtLQxEvO1kIcHZFWgsgHQs7EVIMGydaAE1LaWVmbxUuMScJGik2BFhpQxQ6GihBGwAJSyZvb3kEMjkECjFvPB0gIAc9ByRHMQALDDduLBxNNSUBWDV8ZSsxFz51NS9RNh0IEyEpOFtFcgUKDCEzFis9BxdtWGtOUjkGDzAjPBVQcDBFWgQwCQx2T1JtJiJSGhtFQzhqb3EINioQFDx1Ulh2MRsoHD8XXk8zBj0ybwhNcgUKDCEzBhs1FxsgGmtGGwsCQWlMbxVNcAgEFCQ3Dhs/Q09vEj5bERsODCtuORxNHCIHCiknFkIHBgYBGz9cFBY0CiEjZ0NEcC4LHGgoRnIHBgYDTgpRFisVDDUiIEIDeGkwMRs2DhQxQV5vD2tjEwMSBjZmchUWcGlSTW13Q1plU0JqVmcXQ11SRmdqbQRYYG5HWDV5TzwxBRM6GD8VT09FUnV2ahdBcB8AADx1Ulh2NjtvJyhUHgpFT09mbxVNEyoJFCo0DBN0XlIpASVWBgYIDW0wZhUhOSkXGTosVSsxFzYfPRhWEwMCSzEpIUAAMi4XUD5vCAshAVptUW4XXk1FSmxvb1ADNGsYUUIGCgwYWTMrEA9cBAYDBjduZj8+NT8pQgkxCzQ1ARcjXGl4FwESQw4jNlcEPi9HUXIUCxwfBgsfHSheFx1PQQgjIUAmNTIHESYxTVR0GHhvVGsVNgoBAjAqOxVQcAgKFi48CFYALDUIOA5qOSo+T2UIIGAkcHZFDDogClR0Nxc3AGsIUk0zDCIhI1BNHS4LDWp5ZQV9aSEqAAcPMwsDJywwJlEIImNMchswGzRuIhYrNj5BBgAJSz5mG1AVJGtYWGoAARQ7AhZvPD5XUENHJyozLVkIEycMGyN1UlggEQcqWEEVUk9HJTAoLBVQcC0QFishBhc6S1tFVGsVUk9HQ2UDHGVDIy4ROik5A1AyAh48EWIOUio0M2s1KkE9PCocHTomRx41DwEqXXAVNzw3TTYjO28CPi4WUC40AwsxSklvMRhlXBwCFwknIVEEPiwoGTo+Cgp8BRMjBy4ceE9HQ2VmbxVNOS1FPRsFQSc3DBwhWiZUGwFHFy0jIRUoAxtLJys6ARZ6DhMmGnFxGxwEDCsoKlYZeGJFHSYxZVh0Q1JvVGsVPwARBigjIUFDIy4RPiQsRx41DwEqXXAVPwARBigjIUFDIy4RNic2AxEkSxQuGDhQW1RHLiowKlgIPj9LCy0hJhYyKQciBGNTEwMUBmxMbxVNcGtFWGgUGgw7Mx08WjhBHR9PSn5mDkAZPx4JDGYmGxckS1tFVGsVUk9HQ2UZCBs0YgA6LgcZIz0NPDoaNhR5PS4jJgFmchUDOSdvWGh1T1h0Q1IDHSlHEx0eWRAoI1oMNGNMcmh1T1gxDRZvCWI/eAMIACQqb2YIJBlFRWgBDhonTSEqAD9cHAgUWQQiK2cENyMRPzo6Ggg2DApnVgpWBgYIDWUOIEEGNTIWWmR1TRMxGlBmfhhQBj1dIiEiA1QPNSdNA2gBCgAgQ09vVhpAGwwMQy4jNkZNNiQXWCc7ClUnCx07VCpWBgYIDTZobRlNFCQACx8nDgh0XlI7Bj5QUhJOaRYjO2dXES8BPCEjBhwxEVpmfhhQBj1dIiEiA1QPNSdNWhwwAx0kDAA7VB96Ug0GDylkZg8sNC8uHTEFBhs/BgBnVgNaBgQCGgcnI1lPfGsecmh1T1gQBhQuASdBUlJHQQJkYxUgPy8AWHV1TSw7BBUjEWkZUjsCGzFmchVPEioJFGp5ZVh0Q1IMFSdZEA4ECGV7b1MYPigRESc7Rxk3Fxs5EWI/Uk9HQ2VmbxUENmsEGzw8GR10FxoqGmtZHQwGD2U2bwhNEioJFGYlAAs9FxsgGmMcSU8OBWU2b0EFNSVFLTw8Awt6FxcjETtaABtPE2Vtb2MIMz8KCnt7AR0jS0JjRWcFW0ZcQwspO1wLKWNHMCchBB0tQV5tls2nUg0GDylkZhUIPi9FHSYxZVh0Q1IqGi8VD0ZtMCAyHQ8sNC8pGSowA1B2NxcjETtaABtHFypmA3QjFAIrP2p8VTkwBzkqDRtcEQQCEW1kB1oZOy4cNCk7CxE6BFBjVDA/Uk9HQwEjKVQYPD9FRWh3J1p4Qz8gEC4VT09FNyohKFkIcmdFLC0tG1hpQ1ADFSVRGwEAQWlMbxVNcAgEFCQ3Dhs/Q09vEj5bERsODCtuLlYZOT0AUUJ1T1h0Q1JvVCJTUg4EFywwKhUZOC4Lcmh1T1h0Q1JvVGsVUgMIACQqb2pBcCMXCGhoTy0gCh48WixQBiwPAjduZj9NcGtFWGh1T1h0Q1IjGyhUHk8BDyopPWxNbWsNCjh1DhYwQ1onBjsbIgAUCjEvIFtDCWtIWHp7WlF0DABvREEVUk9HQ2VmbxVNcGsJFys0A1g4AhwrVHYVMA4LD2s2PVAJOSgRNCk7CxE6BFopGCRaADZOaWVmbxVNcGtFWGh1TxEyQx4uGi8VBgcCDWUTO1wBI2URHSQwHxcmF1ojFSVRW1RHLSoyJlMUeGktFzw+CgF2T1Ct8tkVHg4JBywoKBdEcC4LHEJ1T1h0Q1JvVC5bFmVHQ2VmKlsJcDZMchswGypuIhYrOCpXFwNPQREpKFIBNWskDTw6Tyg7EBs7HSRbUEZdIiEiBFAUACIGEy0nR1ocDAYkETJ0BxsIMyo1bRlNK0FFWGh1Kx0yAgcjAGsIUk0tQWlmAloJNWtYWGoBAB8zDxdtWGthFxcTQ3hmbXQYJCQ1Fzt3Q3J0Q1JvNypZHg0GAC5mchULJSUGDCE6AVA1AAYmAi4ceE9HQ2VmbxVNOS1FGSshBg4xQwYnESU/Uk9HQ2VmbxVNcGtFES51Lg0gDCIgB2VmBg4TBms0OlsDOSUCWDw9ChZ0Igc7GxtaAUEUFyo2ZxxWcAUKDCEzFlB2Kx07Hy5MUENFIjAyIGUCI2sqPg53RnJ0Q1JvVGsVUk9HQ2UjI0YIcAoQDCcFAAt6EAYuBj8dW1RHLSoyJlMUeGktFzw+CgF2T1AOAT9aIgAUQwoIbRxNNSUBcmh1T1h0Q1JvESVReE9HQ2UjIVFNLWJvKy0hPUIVBxYDFSlQHkdFMSAlLlkBcDsKC2p8VTkwBzkqDRtcEQQCEW1kB1oZOy4cKi02DhQ4QV5vD0EVUk9HJyAgLkABJGtYWGoHTVR0Lh0rEWsIUk0zDCIhI1BPfGsxHTAhT0V0QSAqFypZHk1LaWVmbxUuMScJGik2BFhpQxQ6GihBGwAJSyQlO1wbNWJFES51DhsgCgQqVD9dFwFHLiowKlgIPj9LCi02DhQ4Mx08XGIVFwEDQyAoKxUQeUE2HTwHVTkwBz4uFi5ZWk0zDCIhI1BNET4RF2gAAwx2SkgOEC9+FxY3CiYtKkdFcgMKDCMwFi04F1BjVDA/Uk9HQwEjKVQYPD9FRWh3Olp4Qz8gEC4VT09FNyohKFkIcmdFLC0tG1hpQ1AOAT9aJwMTQWlMbxVNcAgEFCQ3Dhs/Q09vEj5bERsODCtuLlYZOT0AUUJ1T1h0Q1JvVCJTUg4EFywwKhUZOC4Lcmh1T1h0Q1JvVGsVUgYBQwQzO1o4PD9LKzw0Gx16EQchGiJbFU8TCyAob3QYJCQwFDx7HAw7E1pmT2t7HRsOBTxubX0CJCAAAWp5TTkhFx0aGD8VPSkhQWxMbxVNcGtFWGh1T1h0Bh48EWt0BxsINikyYUYZMTkRUGFuTzY7FxspDWMXOgATCCA/bRlPET4RFx05G1gbLVBmVC5bFmVHQ2VmbxVNcC4LHEJ1T1h0BhwrVDYceGUrCic0LkcUfh8KHy85CjMxGhAmGi8VT08oEzEvIFsefgYAFj0eCgE2ChwrfkEYX0+F98Wk27WPxMtFLCAwAh10SFIcFT1QUg4DByooPBWPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/i29/Kt4MvX5u+F98Wk27WPxMuH7Mi3+/heChRvICNQHwoqAisnKFAfcCoLHGgGDg4xLhMhFSxQAE8TCyAoRRVNcGsxEC04CjU1DRMoETkPIQoTLywkPVQfKWMpESonDgotSnhvVGsVIQ4RBggnIVQKNTlfKy0hIxE2ERM9DWN5Gw0VAjc/Zj9NcGtFKykjCjU1DRMoETkPOwgJDDcjG10IPS42HTwhBhYzEFpmfmsVUk80AjMjAlQDMSwACnIGCgwdBBwgBi58HAsCGyA1Z05NcgYAFj0eCgE2ChwrVmtIW2VHQ2VmG10IPS4oGSY0CB0mWSEqAA1aHgsCEW0FIFsLOSxLKwkDKicGLD0bXUEVUk9HMCQwKngMPioCHTpvPB0gJR0jEC5HWiwIDSMvKBs+ER0gJwsTKCt9aVJvVGtmExkCLiQoLlIIInEnDSE5Czs7DRQmExhQERsODCtuG1QPI2UmFyYzBh8nSnhvVGsVJgcCDiALLlsMNy4XQgklHxQtNx0bFSkdJg4FEGsVKkEZOSUCC2FfT1h0QwIsFSdZWgkSDSYyJloDeGJFKykjCjU1DRMoETkPPgAGBwQzO1oBPyoBOyc7CREzS1tvESVRW2UCDSFMRXA+AGUWDCknG1B9aTAuGCcbARsGETEQKlkCMyIRARwnDhs/BgBnXWsVX0JHADcvO1wOMSdfWCo0AxR0CgFvFSVWGgAVBiFmPFpNJy5FCyk4HxQxQwIgByJBGwAJEE9MAVoZOS0cUGoMXTN0KwctVmcVUCMIAiEjKxULPzlFWmh7QVgXDBwpHSwbNS4qJhoIDngocGVLWGp7TygmBgE8VBlcFQcTIDE0IxUZP2sRFy8yAx16QVtFBDlcHBtPS2cdFgcmDWspFykxChx0BR09VG5GUkc3DyQlKnwJcG4BUWZ3RkIyDAAiFT8dMQAJBSwhYXIsHQ46NgkYKlR0IB0hEiJSXD8rIgYDEHwpeWJv'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, antiSpy = { kick = true, halt = true } })
