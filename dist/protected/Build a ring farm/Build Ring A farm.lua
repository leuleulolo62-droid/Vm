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
local cloneref_ = cloneref or function(x) return x end
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

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

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
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
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
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		spike = remoteSpike(),
	}
	return true
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
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
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
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
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
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
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui,
				http = opts.http, namecall = opts.namecall,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

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
local Neuter      = Neuter

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

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
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

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

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
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
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

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

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

local __k = 'sjmaWZ2roo1qpvkcApZDY6ba'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Build a ring farm/Build Ring A farm', checksum = 703594195, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
