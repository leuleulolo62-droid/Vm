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

local __k = '6VNwqclMV6vq5vBROMj2li4Z'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2 })
