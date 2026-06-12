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

local __k = 'GXDlr5ziLhlt5oJAERTUT1xf'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2 })
