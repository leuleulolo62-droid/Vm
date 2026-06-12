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

local __k = 'AwrACNNmcZbahRDzIvlefyy8'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2 })
