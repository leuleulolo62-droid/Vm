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

	mt.__metatable = "locked"  -- getmetatable returns this string, hiding mt

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store
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
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envMT)
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
			local okE = Integrity.checkEnv(ctx.env, ctx.envMT)
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
	local env, envMT = Environment.build(proxies, realG)

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

local __k = 'OmuHYy5YouD8ysgfhVFWQx7Z'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2 })
