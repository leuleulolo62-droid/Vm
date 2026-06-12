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

local __k = 'P8PFaWMZsPMtFk90C5FDmkJc'
local __p = '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0NrExoPDzbjn0K/gxomtsKGhxqb566j30NrExoPDzbjn0K/gxomtsKGhxqb566j30NrExoPDzbjn0K/gxomtsKGhxqb566j3wDJ9a0G12dhTcA47CC1wd2MVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2qBxLpaa0x3r87nstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXPRzYcMywYZihfV2MIZj9nS2pDcHklMg4DPzsaPm1UZksZEGMVZnlNDSsPI118TEF3bXoyJTkbDQJaW2MVZmRNS2pDcBhtZgc2ISkWfEdUZksZcTZBKRQBCikGcBhwZkF3bXpTbW0SJwdKVW8/ZmRNSwsWJFcFNgYlLD4WEiEbJQBKEH4VICUBGC9PWhhwZkEWOC4cAygYKksZEGMVZmRNS2pecF4xKhIyYVBTcG1UBx5NXwFAPxMIAi0LJEtwZkF3cHoVMSEHI0czEGMVZgUYHyUhJUEDNgQyKXpTcG1UZlYZViJZNSFBYWpDcBgEFjY2ITE2PiwWKg5dEGMVZmRQSywCPEs1amt3bXpTBB0jJwdSYzNQIyBNS2pDcBhwe0FifXZ5cG1UZiVWUy9cNmRNS2pDcBhwZkF3bWdTNiwYNQ4VOmMVZmQkBSwpJVUgZkF3bXpTcG1UZksEECVUKjcIR0BDcBhwBw8jJBs1G21UZksZEGMVZmRNVmoFMVQjI01dMFB5fWBUpP+10te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0pP+50te1pNDtid7jsqzQpPXXr87zstn0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PksEEHMbcHNBS3pNaAlwa0x3CCIQNSEYIwVNOmMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDNVQjIwgxbTccNChUe1YZEgdQJSEDH2pLZgh9flFyZHhTJCURKGEZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBgkJxMwKC4+OSNYZh9YQiRQMgkME2pecAh+c1F7bWpdZnhUa0YZdzFQJzBnS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkEyISkWcGBZZjlYXidaK05NS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXoHMT8TIx90WS0ZZjAMGS0GJHUxPkFqbWpdYn1YZlsXCXs/ZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBg1KAVdbXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcCgYNQ4zEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2oKNhg9KQUybWdOcG8kIxlfVSBBZmxcW3pGcBVwNAgkJiNacm0ALg5XOmMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZhU2Pz0WJAAdKEcZRCJHISEZJisbcAVwdk9uenZTYWNEZkYUEBNQNCIICD5pcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXoWPD4RLw0ZXSxRI2RQVmpBF1c/IkF/dWpeaXhRb0kZRCtQKE5NS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXoHMT8TIx90WS0ZZjAMGS0GJHUxPkFqbWpdaHxYZlsXCXUVa2lNLjIANVQ8Iw8jR3pTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZVS9GIy0LSycMNF1we1x3bx4WMygaMksRBnMYfnRIQmhDJFA1KGt3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGNBJzYKDj4uOVZ8ZhU2Pz0WJAAVPksEEHMbcHVBS3pNZwFwa0x3CigWMTl+ZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmQIBzkGcBV9ZjM2Iz4cPUdUZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2oX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MksEEGtWMzYfDiQXAlc/Mk8HIikaJCQbKEsUEDdUNCMIHxoMIxF+CwAwIzMHJSkRTEsZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcFE2ZgU+Pi5TbG1MZh9RVS0/ZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcC8GIwpSOmMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZgQ5KVBTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRARmoxNRU5NRIiKHo+PzsREgQZWSUVMisCSywCIhh4NAQkKC4AcDkdKw5WRTccTGRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bTMVcCkdNR8ZDmMGdmQZAy8NWhhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGNdMylXJiUVNWw/bhU2Pz0WJB0bNUIzEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwIw8zR3pTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZVS1RTGRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwMgAkJnQEMSQAblsXA2o/ZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNSy8NNDJwZkF3bXpTcG1UZksZEGMVZmRNS2pDcBhwZkF3R3pTcG1UZksZEGMVZmRNS2pDcBhwZkF3bXpTcG1Za0trVTBBKTYISyQMIlUxKkEALDYYAz0RIw8zEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZiwYBmQ0MVQ7FREyKD5TbW1FcGEZEGMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVTGRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmRNS2pOfRgEIw0yPTUBJG0RPgpaRC9MZisDHyVDO1EzLUEnLD5TJCJUIR5YQiJbMiEISygWJEw/KEEhJCkaMiQYLx9AOmMVZmRNS2pDcBhwZkF3bXpTcG1UZksZEGMVZmQfBCUXfnsWNAA6KHpOcA4yNApUVW1bIzNFACMAO2gxIk8HIikaJCQbKEsSEBVQJTACGXlNPl0nblF7bWlfcH1db2EZEGMVZmRNS2pD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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2 })
