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

local __k = 'rpZ09CFSnsxMJgGSZsTnNHD2'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2 })
