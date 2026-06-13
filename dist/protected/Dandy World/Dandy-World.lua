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
		local n, lastHit, confirm = 0, nil, 0
		local need = opts.confirm or 2          -- require N consecutive detections (anti-false-positive)
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
				if hits[1].name == lastHit then confirm = confirm + 1
				else lastHit, confirm = hits[1].name, 1 end
				if confirm >= need then
					pcall(onDetect, hits[1].name, hits[1].detail)
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

local __k = 'qNARlpTOBg1BpUFJhsNr98RO'
local __p = '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UHVmakhTbh5WWzMjUSEqfkwVJj1iWhEyEzQqJkAVIFszGHJvUW5hckxQdG9iDldiHjoyagcYbgZRXTxvBi8zPERSDxZwLGxiHDopOlJTbFIXFnI7Hj01IAUeM2cnFUNrWXUjJAx5blIZGHJvUW5hckxQOCAhBl1iFCFmd0gHNwJcEDUqBQcvJgkCIi4uThF/TXVkLB0dLQZQVzxtUS8vNkwXMTsLCUUnAiMnJkBabh1LGDUqBQcvJgkCIi4ubRFiUHVmakhTblIZGCYuAiVvJQ0ZIGcmExhIUHVmakhTblJcVjZFUW5hcgkeMGZIAl8mel8gPwYQOhtWVnIaBSctIUIUPTw2Bl8hFX0nZkgRZ3gZGHJvGChhPAMEdC5iCENiHjoyagpTOhpcVnI9FDo0IAJQOS42Dx8qBTIjag0dKngZGHJvAys1Jx4edGcjRxxiEnxoBwkUIBtNTTYqeysvNmZ6eWJihaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jRF8UGGFhURwEHyMkERxIShxiksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOepMj4gEi8tcj4VOSA2AkJiTXU9ajcQLxFRXXJyUTU8fkwvMTknCUUxUGhmJAEfbg8zVD0sECJhNBkeNzsrCF9iFSMjJBwAZlszGHJvUScncj4VOSA2AkJsLzAwLwYHPVJYVjZvIyssPRgVJ2EdAkcnHiE1ZDgSPBdXTHI7GSsvch4VIDowCREQFTgpPg0AYC1cTjchBT1hNwIUXm9iRxEQFTgpPg0AYC1cTjchBT1hb0wlICYuFB8wFSYpJh4WHhNNUHoMHiAnOwteERkHKWURLwUHHiBaRFIZGHI9FDo0IAJQBiovCEUnA3sZLx4WIAZKMjchFUQnJwITICYtCREQFTgpPg0AYBVcTHokFDdoWExQdG8rAREQFTgpPg0AYC1aWTEnFBUqNxUtdC4sAxEQFTgpPg0AYC1aWTEnFBUqNxUteh8jFVQsBHUyIg0dbgBcTCc9H24TNwEfICoxSW4hETYuLzMYKwtkGDchFURhckxQOCAhBl1iHjQrL0hObjFWVjQmFmATFyE/AAoRPFonCQhmJRpTJRdAMnJvUW4tPQ8ROG8nERF/UDAwLwYHPVoQA3ImF24vPRhQMTliE1knHnU0LxwGPBwZVjsjUSsvNmZQdG9iC14hETlmOEhObhdPAhQmHyoHOx4DIAwqDl0mWDsnJw1aRFIZGHImF24zchgYMSFiNVQvHyEjOUYsLRNaUDcUGis4D0xNdD1iAl8menVmakgBKwZMSjxvA0QkPAh6MjosBEUrHztmGA0eIQZcS3wpGDwkegcVLWNiSR9sWV9makhTIh1aWT5vA258cj4VOSA2AkJsFzAyYgMWN1sCGDspUSAuJkwCdDsqAl9iAjAyPxodbhRYVCEqUSsvNmZQdG9iC14hETlmKxoUPVIEGCYuEyIkfBwRNyRqSR9sWV9makhTPBdNTSAhUT4iMwAcfCk3CVI2GTooYkFTPEh/USAqIiszJAkCfDsjBV0nXiAoOgkQJVpYSjU8XW5wfkwRJigxSV9rWXUjJAxaRBdXXFgpBCAiJgUfOm8QAlwtBDA1ZAEdOB1SXXokFDdtckJeemZIRxFiUDkpKQkfbgAZBXIdFCMuJgkDeignExkpFSxvcUgaKFJXVyZvA241OgkedD0nE0QwHnUgKwQAK1JcVjZFUW5hcgAfNy4uR1AwFyZmd0gHLxBVXXw/EC0qekJeemZIRxFiUDkpKQkfbgBcSycjBT1hb0wLdD8hBl0uWDMzJAsHJx1XEHtvAys1Jx4edD14Ll80Hz4jGQ0BOBdLECYuEyIkfBkeJC4hDBkjAjI1ZkhCYlJYSjU8XyBoe0wVOitrR0xIUHVmagEVbhxWTHI9FD00PhgDD34fR0UqFTtmOA0HOwBXGDQuHT0kcgkeMEViRxFiBDQkJg1dPBdUVyQqWTwkIRkcIDxuRwBrenVmakgBKwZMSjxvBTw0N0BQIC4gC1RsBTs2KwsYZgBcSycjBT1oWAkeMEUkEl8hBDwpJEghKx9WTDc8Xy0uPAIVNztqDFQ7XHUgJEF5blIZGD4gEi8tch5QaW8QAlwtBDA1ZA8WOlpSXStme25hckwZMm8sCEViAnUpOEgdIQYZSnwAHw0tOwkeIAo0Al82UCEuLwZTPBdNTSAhUSAoPkwVOitIRxFiUCcjPh0BIFJLFh0hMiIoNwIEETknCUV4MzooJA0QOlpfTTwsBScuPEReemFrbRFiUHVmakhTIh1aWT5vHiVtcgkCJm9/R0EhETkqYg4dYlIXFnxme25hckxQdG9iDldiHjoyagcYbgZRXTxvBi8zPERSDxZwLGxiEzooJA0QOlIbFnwkFDdvfE5KdG1sSUUtAyE0IwYUZhdLSntmUSsvNmZQdG9iAl8mWV8jJAx5RF8UGLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxEVvShF2XnUUBSc+biB8ax0DJBoIHSJ6eWJihaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sff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USsvNmYWISEhE1gtHnUVPgkHPVxMSCYmHCtpe2ZQdG9iC14hETlmOUhObh9YTDphFyIuPR5YICYhDBlrUHhmGRwSOgEXSzc8AicuPD8ENT02TjtiUHVmJgcQLx4ZUHJyUSMgJgReMiMtCENqA3VpaltFfkIQA3I8UXNhIUxddCdiTRFxRmV2QEhTblJVVzEuHW4sclFQOS42Dx8kHDopOEAAbl0ZDmJmSm5hch9QaW8xRxxiHXVsal5DRFIZGHI9FDo0IAJQJzswDl8lXjMpOAUSOlobHWJ9FXRkYl4UbmpyVVVgXHUuZkgeYlJKEVgqHypLWEFddK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2mJeY1IPFnIKIh5hsOzkdBs1DkI2FTE1akdTAxNaUDshFD1hfUw5ICovFBFtUAUqKxEWPAEzFX9vk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrSbV0tEzQqai0gHlIEGClFUW5hcj8ENTsnRwxiC19makhTblIZGCY4GD01NwhQaW8kBl0xFXlmJwkQJhtXXXJyUSggPh8VeG8rE1QvUGhmLAkfPRcVGCIjEDckIExNdCkjC0InXF9makhTblIZGCY4GD01Nwg0PTw2Bl8hFXV7ahwBOxcVMnJvUW5hckxQJyctEH4s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UHVmakhTbhtfGBccIWASJg0EMWErE1QvUCEuLwZ5blIZGHJvUW5hckxQIT8mBkUnMiAlIQ0HZjdqaHwQBS8mIUIZICovSxEQHzorZA8WOjtNXT88WWdtcikjBGERE1A2FXsvPg0eDR1VVyBjUSg0PA8EPSAsT1RuUDFvQEhTblIZGHJvUW5hckxQdG8rAREmUCEuLwZTPBdNTSAhUWZjsPv2dGoxR2pnFCYyF0padBRWSj8uBWYkfAIROSpuR1wjBD1oLAQcIQARXHtmUSsvNmZQdG9iRxFiUHVmakhTblIZSjc7BDwvck6Sw8liRRFsXnUjZAYSIxczGHJvUW5hckxQdG9iAl8mWV9makhTblIZGDchFURhckxQdG9iR1gkUBAVGkYgOhNNXXw/HS84Nx5QICcnCTtiUHVmakhTblIZGHI6ASogJgkyISwpAkVqNQYWZDcHLxVKFiIjEDckIEBQBiAtCh8lFSEJPgAWPCZWVzw8WWdtcikjBGERE1A2FXs2JgkKKwB6Vz4gA2JhNBkeNzsrCF9qFXlmLkF5blIZGHJvUW5hckxQdG9iR10tEzQqagADbk8ZXXwnBCMgPAMZMG8jCVViHTQyIkYVIh1WSnoqXyY0Pw0eOyYmSXknETkyIkFTIQAZGn9te25hckxQdG9iRxFiUHVmakgaKFJdGCYnFCBhIAkEIT0sRxlgksLJak0AbikcSzo/XW5kNh8ECW1rXVctAjgnPkAWYBxYVTdjUTouIRgCPSElT1kyWXlmJwkHJlxfVD0gA2Yle0VQMSEmbRFiUHVmakhTblIZGHJvUW4zNxgFJiFiRdPV/3VkakZdbhcXVjMiFERhckxQdG9iRxFiUHUjJAxaRFIZGHJvUW5hNwIUXm9iRxEnHjFvQA0dKngzFX9vk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrSbRxvUGJoajsmHCRwbhMDUQYEHjw1BhxIShxiksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOepMj4gEi8tcj8FJjkrEVAuUGhmMUggOhNNXXJyUTVLckxQdCEtE1gkGTA0DwYSLB5cXHJyUSggPh8VeG8sCEUrFjwjODoSIBVcGG9vQnttcjMcNTw2Jl0nAiEjLkhObkIVMnJvUW4gPBgZEz0jBRF/UDMnJhsWYngZGHJvEDs1PS0GOyYmRwxiFjQqOQ1fbhNPVzsrIy8vNQlQaW9wUh1IDXU7QGJeY1J3VyYmFyckIEyS1NtiFkQrEz5mJQZePRFLXTchUSAuJgUWLW81D1QsUDRmPh8aPQZcXHIqHzokIB9QJi4sAFRIHDolKwRTKAdXWyYmHiBhPw0bMQEtE1gkGTA0DBoSIxcREVhvUW5hOwpQBzowEVg0ETloFQYcOhtfQRU6GG41OgkedD0nE0QwHnUVPxoFJwRYVHwQHyE1OwoJEzorR1QsFF9makhTIh1aWT5vAilhb0w5Ojw2Bl8hFXsoLx9bbCFaSjcqHwk0O05ZXm9iRxExF3sIKwUWbk8ZGgt9OgogPAgJGiA2DlcrFSdkQEhTblJKX3wdFD0kJiMeBz8jEF9iTXUgKwQAK3gZGHJvAilvCCUeMCo6JVQqESMvJRpTc1J8ViciXxQIPAgVLA0nD1A0GTo0ZDsaLB5QVjVFUW5hch8Xeh8jFVQsBHV7aiQcLRNVaD4uCCszaDsRPTsECEMBGDwqLkBRHh5YQTc9NjsocEV6dG9iR10tEzQqahwfbk8ZcTw8BS8vMQleOio1TxMWFS0yBgkRKx4bEVhvUW5hJgBeByY4AhF/UAACIwVBYBxcT3p/XW5yYFxcdH9uRwJ0WV9makhTOh4XaD08GDooPQJQaW8XI1gvQnsoLx9bflwMFHJiQHhxfkxAen56SxFyWV9makhTOh4XejMsGikzPRkeMBswBl8xADQ0LwYQN1IEGGJhQ3tLckxQdDsuSXMjEz4hOAcGIBZ6Vz4gA31hb0wzOyMtFQJsFicpJzo0DFoICH5vQH5tcl5FfUViRxFiBDloDAcdOlIEGBchBCNvFAMeIGEIEkMjenVmakgHIlxtXSo7Iic7N0xNdH50bRFiUHUyJkYnKwpNez0jHjxyclFQFyAuCENxXjM0JQUhCTARCmd6XW53YkBQYn9rbRFiUHUyJkYnKwpNGG9vU2xLckxQdDsuSWcrAzwkJg1Tc1JfWT48FERhckxQICNsN1AwFTsyalVTPRUzGHJvUSIuMQ0cdDw2FV4pFXV7aiEdPQZYVjEqXyAkJURSAQYRE0MtGzBkY1NTPQZLVzkqXw0uPgMCdHJiJF4uHyd1ZA4BIR9rfxBnQ3t0fkxGZGNiUQFrS3U1PhocJRcXbDomEiUvNx8DdHJiVQpiAyE0JQMWYCJYSjchBW58chgcXm9iRxEuHzYnJkgQIQBXXSBvTG4IPB8ENSEhAh8sFSJuaD06DR1LVjc9U2d6cg8fJiEnFR8BHycoLxohLxZQTSFvTG4UFgUdeiEnEBlyXHVwY1NTLR1LVjc9Xx4gIAkeIG9/R0UuenVmakggOwBPUSQuHWAePAMEPSk7IEQrUGhmOQ95blIZGAE6AzgoJA0cehAsCEUrFiwKKwoWIlIEGCYje25hckwCMTs3FV9iAzJMLwYXRHhfTTwsBScuPEwjIT00DkcjHHs1Lxw9IQZQXjsqA2Y3e2ZQdG9iNEQwBjwwKwRdHQZYTDdhHyE1OwoZMT0HCVAgHDAialVTOHgZGHJvGChhJEwEPCosbRFiUHVmakhTIxNSXRwgBScnOwkCEj0jClRqWV9makhTblIZGDspUR00IBoZIi4uSW4hHzsoahwbKxwZSjc7BDwvcgkeMEViRxFiUHVmajsGPARQTjMjXxEiPQIedHJiNUQsIzA0PAEQK1xxXTM9BSwkMxhKFyAsCVQhBH0gPwYQOhtWVnpme25hckxQdG9iRxFiUDwgagYcOlJqTSA5GDggPkIjIC42Ah8sHyEvLAEWPDdXWTAjFCphJgQVOm8wAkU3AjtmLwYXRFIZGHJvUW5hckxQdCMtBFAuUApqagABPlIEGAc7GCIyfAoZOisPHmUtHztuY2JTblIZGHJvUW5hckwZMm8sCEViGCc2ahwbKxwZSjc7BDwvcgkeMEViRxFiUHVmakhTblJVVzEuHW4vNw0CMTw2SxEmGSYyalVTIBtVFHIiEDopfAQFMypIRxFiUHVmakhTblIZXj09URFtchhQPSFiDkEjGSc1YjocIR8XXzc7JTkoIRgVMDxqThhiFDpMakhTblIZGHJvUW5hckxQdCMtBFAuUDFmd0gmOhtVS3wrGD01MwITMWcqFUFsIDo1IxwaIRwVGCZhAyEuJkIgOzwrE1gtHnxMakhTblIZGHJvUW5hckxQdCYkR1ViTHUiIxsHbgZRXTxvFScyJkxNdCt5R18nEScjORxTc1JNGDchFURhckxQdG9iRxFiUHUjJAx5blIZGHJvUW5hckxQPSliNEQwBjwwKwRdERxWTDspCAIgMAkcdDsqAl9IUHVmakhTblIZGHJvUW5hcgUWdCEnBkMnAyFmKwYXbhZQSyZvTXNhARkCIiY0Bl1sIyEnPg1dIB1NUTQmFDwTMwIXMW82D1QsenVmakhTblIZGHJvUW5hckxQdG9iNEQwBjwwKwRdERxWTDspCAIgMAkcehkrFFggHDBmd0gHPAdcMnJvUW5hckxQdG9iRxFiUHVmakhTHQdLTjs5ECJvDQIfICYkHn0jEjAqZDwWNgYZBXJnU6zb8kxVJ28MInAQULfG3khWKlJKTCcrAmxoaAofJiIjExksFTQ0LxsHYBxYVTdjUSMgJgReMiMtCENqFDw1PkFaRFIZGHJvUW5hckxQdG9iRxEnHCYjQEhTblIZGHJvUW5hckxQdG9iRxFiIyA0PAEFLx4XZzwgBScnKyARNiouSWcrAzwkJg1Tc1JfWT48FERhckxQdG9iRxFiUHVmakhTKxxdMnJvUW5hckxQdG9iR1QsFF9makhTblIZGDchFWdLckxQdCosAzsnHjFMQEVebjNXTDtiFjwgMEyS1NtiBkQ2H3ggIxoWPVJqSScmAyMAMAUcPTs7JFAsEzAqah8bKxwZXyAuEywkNmYWISEhE1gtHnUVPxoFJwRYVHw8FDoAPBgZEz0jBRk0WV9makhTHQdLTjs5ECJvARgRICpsBl82GRI0KwpTc1JPMnJvUW4oNEwGdC4sAxEsHyFmGR0BOBtPWT5hLikzMw4zOyEsR0UqFTtMakhTblIZGHJiXG4NOx8EMSFiAV4wUDI0KwpTKwRcViZ0UTopN0wXNSInR1crAjA1ajwEJwFNXTYcADsoIAE3Ji4gR0YqFTtmKQkGKRpNMnJvUW5hckxQOCAhBl1iFycnKDo2bk8ZbSYmHT1vIAkDOyM0AmEjBD1uaDoWPh5QWzM7FCoSJgMCNSgnSXQ0FTsyOUYnORtKTDcrIj80Ox4dEz0jBRNrenVmakhTblIZUTRvFjwgMD41dC4sAxElAjQkGC1dARx6VDsqHzoEJAkeIG82D1QsenVmakhTblIZGHJvUR00IBoZIi4uSW4lAjQkCQcdIFIEGDU9ECwTF0I/OgwuDlQsBBAwLwYHdDFWVjwqEjppNBkeNzsrCF9qXntoY2JTblIZGHJvUW5hckxQdG9iDldiHjoyajsGPARQTjMjXx01MxgVei4sE1gFAjQkahwbKxwZSjc7BDwvcgkeMEViRxFiUHVmakhTblIZGHJvBS8yOUIHNSY2TwFsQGBvQEhTblIZGHJvUW5hckxQdG8QAlwtBDA1ZA4aPBcRGgE+BCczPy8ROiwnCxNrenVmakhTblIZGHJvUW5hckwjIC42FB8nAzYnOg0XCQBYWiFvTG4SJg0EJ2EnFFIjADAiDRoSLAEZE3J+e25hckxQdG9iRxFiUDAoLkF5blIZGHJvUW4kPAh6dG9iR1QuAzAvLEgdIQYZTnIuHyphARkCIiY0Bl1sLzI0KwowIRxXGCYnFCBLckxQdG9iRxERBScwIx4SIlxmXyAuEw0uPAJKECYxBF4sHjAlPkBadVJqTSA5GDggPkIvMz0jBXItHjtmd0gdJx4zGHJvUSsvNmYVOitIbRxvUBEjKxwbbhFWTTw7FDxLAAkdOzsnFB8hHzsoLwsHZlB9XTM7GWxtcgoFOiw2Dl4sWHxmGRwSOgEXXDcuBSYyclFQBzsjE0JsFDAnPgAAblkZCXIqHypoWGZdeW+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/iR2+LbrcKt5N6jx/ySwd+g8qGg5cWk3/h5Y18ZAHxvPA8CGiU+EW8DMmUNPRQSAyc9bpC5rHIOBDoucj8bPSMuR3IqFTYtQEVebpCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwmZdeW8WD1RiAzA0PA0BbhZWXSF1UW4SOQUcOCwqAlIpJSUiKxwWdDtXTj0kFA0tOwkeIGcyC1A7FSdqag8WIBdLWSYgA2JhMx4XJ2ZIShxiBz0jOA1TLwBeS3IjHiEqIUwcPSQnR0piBCw2L0hOblBaUSAsHStjLk4EJiojA1wrHDlkZkgRIQdXXDM9CB0oKAlQaW8MSxE2ESchLxxcPh1KUSYmHiBuMQkeICowRwxiJHlmZEZdbg8zFX9vJSYkcg8cPSosExEvBSYyahoWOgdLVnIuUSA0Pw4VJm8rCREZQHtoezVTOhpYTHIjECAlIUwZOjwrA1RiBD0jag8BKxdXGCggHytLf0FQNyosE1QwFTFmJQZTGlJOUSYnUSYgPgpdIyYmE1liEjozJAwSPAtqUSgqXnxvWEFdXmJvR2I2AjQyLw8KdFJLXTMrUTopN0wENT0lAkViFjwjJgxTKABWVXIuAykyckQHMW82FUhiFSMjOBFTLR1UVT0hUSAgPwlZekVvShELFnUxL0gQLxweTHIpGCAlcgUEeG8kBl0uUDcnKQNTOh0ZWXI8BS81Ow9QIi4uElRiBD0jah0AKwAZWzMhUTo0PAleXiMtBFAuUBgnKQAaIBcZBXI0UR01MxgVdHJiHDtiUHVmKx0HISFSUT4jEiYkMQdQaW8kBl0xFXlMakhTbhNMTD0cGictPg8YMSwpI1QuESxmd0hDYngZGHJvFy8tPg4RNyQUBl03FXV7alhde14ZGHJvXGNhPQIcLW83FFQmUCIuLwZTIB0ZTDM9Fis1cgoZMSMmR1gxUDwoagkBKQEzGHJvUSokMBkXBD0rCUViUHV7ag4SIgFcFHJvUWNschwCPSE2FBEjAjI1agcdLRcZTzoqH241PQsXOCombUw/el9rZ0g9ASZ8AnIdHiwtPRRQMCAnFBEMPwFmKwQfIQUZSjcuFScvNUwCMmENCXIuGTAoPiEdOB1SXXJnBjwoJgldOyEuHhhsenhraj8WbhFYVnU7UT0gJAlQICcnR14wGTIvJAkfbhpYVjYjFDxvciUWdDsqAhElETgjbRtTGzsZSzc7Am4oJkBQOzowFBE1GTkqahoWPh5YWzdvGDpLf0FQfC4sAxE0GTYjah4WPAFYEXxvJi81MQQUOyhiDUQxBHU0L0USPgJVUTc8USE0IB9QMTknFUhiQHtzOUgEJwZRVyc7US0pNw8bPSElSTsuHzYnJkgsJhNXXD4qAw8iJgUGMW9/R1cjHCYjQAQcLRNVGA0jED01FgkSISgWDlwnUGhmemJ5Y18ZbCAmFD1hNxoVJjZiBF4vHTooagYSIxcZXj09UTopN0xSIC4wAFQ2UCUpOQEHJx1XGnJgUWwiNwIEMT1gR1crFTkiagEdbhNLXyFheyIuMQ0cdCk3CVI2GTooag0LOgBYWyYbEDwmNxhYNT0lFBhIUHVmagEVbgZASDdnEDwmIUVQKnJiRUUjEjkjaEgHJhdXGCAqBTszPEwePSNiAl8menVmakheY1J9USAqEjphPBkdMT0rBBEkGTAqLht5blIZGDQgA24efkwbdCYsR1gyETw0OUAIRFIZGHJvUW5hcBgRJignExNuUHcyKxoUKwZpVyEmBScuPE5cdG0yCEIrBDwpJEpfblBaXTw7FDxjfkxSNyosE1QwIDo1aER5blIZGHJvUW5jNxQAMSw2AlVgXHVkOg0BKBdaTAIgAic1OwMedmNiRVkrBAUpOQEHJx1XGn5vUyAkNwgcMW1ubRFiUHVmakhTbAhWVjcMFCA1Nx5SeG9gBFgwEzkjCQ0dOhdLGn5vUyMoNhwfPSE2RR1iUiMnJh0WbF4zGHJvUTNocggfXm9iRxFiUHVmJgcQLx4ZTnJyUS8zNR8rPxJIRxFiUHVmakgaKFJNQSIqWThoclFNdG0sElwgFSdkahwbKxwZSjc7BDwvchpQMSEmbRFiUHUjJAx5blIZGH9iUR0uPwkEPSInFBEsFSYyLwxTJxxKUTYqUS9hcBYfOipgR14wUHckJR0dKhNLQXBvBS8jPgl6dG9iR1ctAnUZZkgYbhtXGDs/ECczIUQLdG04CF8nUnlmaAocOxxdWSA2U2JhcB8bPSMuBFknEz5kZkhRPRlQVD4MGSsiOU5QKWZiA15IUHVmakhTblJVVzEuHW4yJw5QaW8jFVYxKz4bQEhTblIZGHJvGChhJhUAMWcxElNrUGh7akoHLxBVXXBvBSYkPGZQdG9iRxFiUHVmakgVIQAZZ35vGnxhOwJQPT8jDkMxWC5maAsWIAZcSnBjUWwxPR8ZICYtCRNuUHcyKxoUKwYbFHJtHCclIgMZOjtgR0xrUDEpQEhTblIZGHJvUW5hckxQdG8rARE2CSUjYhsGLClSCg9mUXN8ck4eISIgAkNgUCEuLwZTPBdNTSAhUT00MDcbZhJiAl8menVmakhTblIZGHJvUSsvNmZQdG9iRxFiUDAoLmJTblIZXTwre25hckwCMTs3FV9iHjwqQA0dKngzFX9vITwkJhgJeT8wDl82A3UnahwSLB5cGCYgUTopN0wTOyExCF0nUH0pJA1TIhdPXT5vFSskIkV6OCAhBl1iFiAoKRwaIRwZXCciAQ8zNR9YNT0lFBhIUHVmagEVbgZASDdnEDwmIUVQKnJiRUUjEjkjaEgHJhdXGCI9GCA1ek4rDX0JR3UjHjE/F0gAJRtVVHIsGSsiOUwRJigxXRNuUDQ0LRtadVJLXSY6AyBhNwIUXm9iRxEyAjwoPkBRFSsLc3ILECAlKzFQaXJ/R0IpGTkqagsbKxFSGDM9Fj1hb1FNdmZIRxFiUDMpOEgYYlJPGDshUT4gOx4DfC4wAEJrUDEpQEhTblIZGHJvGChhJhUAMWc0ThF/TXVkPgkRIhcbGCYnFCBLckxQdG9iRxFiUHVmOhoaIAYRGnJvU2JhOUBQdnJiHBNrenVmakhTblIZGHJvUSguIEwbZmNiEQNiGTtmOgkaPAERTntvFSFhIh4ZOjtqRRFiUHVmakpfbhkLFHJtTGxtchpCfW8nCVVIUHVmakhTblIZGHJvATwoPBhYdm9iGhNrenVmakhTblIZXT48FERhckxQdG9iRxFiUHU2OAEdOlobGHJtXW4qfkxSaW1uR0duUHduaEZdOgtJXXo5WGBvcEVSfUViRxFiUHVmag0dKngZGHJvFCAlWAkeMEVIC14hETlmLB0dLQZQVzxvHjszAQcZOCMBD1QhGx0nJAwfKwARSD4uCCszfkwXMSEnFVA2HydqagkBKQEQMnJvUW5sf0w0MS03ABEyAjwoPkhbIRxcFSEnHjphIgkCdDstAFYuFXUyJUgSOB1QXHI8AS8se2ZQdG9iDldiPTQlIgEdK1xqTDM7FGAlNw4FMx8wDl82UDQoLkhbOhtaU3pmUWNhDQARJzsGAlM3FwEvJw1abkwZCXI7GSsvWExQdG9iRxFiLzknORw3KxBMXwYmHCthb0wEPSwpTxhIUHVmakhTblJdTT8/MDwmIUQRJigxTjtiUHVmLwYXRHgZGHJvGChhPAMEdAIjBFkrHjBoGRwSOhcXWSc7Hh0qOwAcNycnBFpiBD0jJGJTblIZGHJvUWNscj4VIDowCVgsF3UoJRwbJxxeGD8uGisychgYMW8xAkM0FSdhOUhJBxxPVzkqMiIoNwIEdDsqFV41ULfG3kgROwYZTzdvGS83N0weO0ViRxFiUHVmakVebgVYQXI7Hm4nPR4HNT0mR0UtUCEuL0gcPBteUTwuHW4pMwIUOCowRxkQHzcqJRBTKB1LWjsrAm4zNw0UPSElR34sMzkvLwYHBxxPVzkqWGBLckxQdG9iRxFvXXUVJUgaKFJAVydvBi8vJkwEPCpiFVQlBTknOEgmB1JbWTEkXW41Jx4edDsqAhE2HzIhJg1TIRRfGDMhFW4zNwYfPSFsbRFiUHVmakhTPBdNTSAhe25hckwVOitIbRFiUHUvLEg+LxFRUTwqXx01MxgVei43E14RGzwqJgsbKxFSfDcjEDdhbExAdDsqAl9IUHVmakhTblJNWSEkXzkgOxhYGS4hD1gsFXsVPgkHK1xYTSYgIiUoPgATPCohDHUnHDQ/Y2JTblIZXTwre0RhckxQeWJiIVgwAyFmPhoKdFJLXSY6AyBhJgQVdDsjFVYnBHUyIg1TPRdLTjc9USc1IQkcMm8xAl82UCA1QEhTblJVVzEuHW41Mx4XMTtiWhEnCCE0KwsHGhNLXzc7WS8zNR9ZXm9iRxErFnUyKxoUKwYZTDoqH24zNxgFJiFiE1AwFzAyag0dKngzGHJvUWNscioROCMgBlIpUH0pJAQKbgdKXTZvBiYkPEweO282BkMlFSFmLAEWIhYZXj06HyphOwJQNT0lFBhIUHVmahoWOgdLVnICEC0pOwIVehw2BkUnXjMnJgQRLxFSbjMjBCtLNwIUXkUuCFIjHHUgPwYQOhtWVnImHz01MwAcHC4sA10nAn1vQEhTblJVVzEuHW4zNExNdBo2Dl0xXicjOQcfOBdpWSYnWWwTNxwcPSwjE1QmIyEpOAkUK1x8TjchBT1vAQcZOCMhD1QhGwA2LgkHK1AQMnJvUW4oNEweOztiFVdiHydmJAcHbgBfAhs8MGZjAAkdOzsnIUQsEyEvJQZRZ1JNUDchUTwkJhkCOm8kBl0xFXUjJAx5blIZGH9iURkTGzg1eQAMK2h4UDsjPA0BbgBcWTZvAyhvHQIzOCYnCUULHiMpIQ15blIZGCApXwEvEQAZMSE2Ll80Hz4jalVTIQdLazkmHSICOgkTPwcjCVUuFSdMakhTbi1RWTwrHSszEw8EPTknRwxiBCczL2JTblIZSjc7BDwvchgCISpIAl8mel8qJQsSIlJfTTwsBScuPEwDIC4wE2YjBDYuLgcUZlszGHJvUScnciERNycrCVRsLyInPgsbKh1eGCYnFCBhIAkEIT0sR1QsFF9makhTAxNaUDshFGAeJQ0ENycmCFZiTXUyKxsYYAFJWSUhWSg0PA8EPSAsTxhIUHVmakhTblJOUDsjFG4MMw8YPSEnSWI2ESEjZAkGOh1qUzsjHS0pNw8bdCAwR3wjEz0vJA1dHQZYTDdhFSsjJwsgJiYsExEmH19makhTblIZGHJvUW5sf0wiMWI1FVg2FXUyIg1TJhNXXD4qA24xNx4ZOysrBFAuHCxmIwZTLRNKXXI7GSthNQ0dMWgxR2QLUCcjZxsWOlJQTHxFUW5hckxQdG9iRxFiXXhmHQ1TLRNXHyZvEiYkMQdQIyctR141HiZmIxxTrPKtGCUqUSQ0IRhQOzknFUYwGSEjZGJTblIZGHJvUW5hckwZOjw2Bl0uODQoLgQWPFoQMnJvUW5hckxQdG9iR0UjAz5oPQkaOloIFmJme25hckxQdG9iAl8menVmakhTblIZdTMsGScvN0IvIy42BFkmHzJmd0gdJx4zGHJvUSsvNkV6MSEmbTskBTslPgEcIFJ0WTEnGCAkfB8VIA43E14RGzwqJgsbKxFSECRme25hckw9NSwqDl8nXgYyKxwWYBNMTD0cGictPg8YMSwpRwxiBl9makhTJxQZTnI7GSsvcgUeJzsjC10KETsiJg0BZlsCGCE7EDw1BQ0ENycmCFZqWXUjJAx5KxxdMlgpBCAiJgUfOm8PBlIqGTsjZBsWOjZcWicoITwoPBhYImZIRxFiUBgnKQAaIBcXayYuBStvNgkSISgSFVgsBHV7ah55blIZGDspUThhJgQVOm8rCUI2ETkqAgkdKh5cSnpmSm4yJg0CIBgjE1IqFDohYkFTKxxdMjchFURLf0FQttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWQEVebksXGBMaJQFhAiUzHxoSbRxvULfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqFgjHi0gPkwxITstN1ghGyA2alVTNVJqTDM7FG58chdQJjosCVgsF3V7ag4SIgFcFHI9ECAmN0xNdH5wSxErHiEjOB4SIlIEGGJhRG48chF6MjosBEUrHztmCx0HISJQWzk6AWAyJg0CIGdrbRFiUHUvLEgyOwZWaDssGjsxfD8ENTsnSUM3HjsvJA9TOhpcVnI9FDo0IAJQMSEmbRFiUHUHPxwcHhtaUyc/Xx01MxgVej03CV8rHjJmd0gHPAdcMnJvUW4UJgUcJ2EuCF4yWDMzJAsHJx1XEHtv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GCkpJgIVJzxiCENiQV9makhTblIZGB4mFiY1OwIXegwuCFIpJDwrL0hTc1JvUSE6ECIyfDMSNSwpEkFsMzkpKQMnJx9cGD09UX91WExQdG9iRxFiPDwhIhwaIBUXfz4gEy8tAQQRMCA1FBF/UAMvOR0SIgEXZzAuEiU0IkI3OCAgBl0RGDQiJR8AbgwEGDQuHT0kWExQdG8nCVVIFTsiQA4GIBFNUT0hURgoIRkRODxsFFQ2PjoAJQ9bOFszGHJvURgoIRkRODxsNEUjBDBoJAc1IRUZBXI5Sm4jMw8bIT8ODlYqBDwoLUBaRFIZGHImF243chgYMSFiK1glGCEvJA9dCB1efTwrUXNhYwlGb28ODlYqBDwoLUY1IRVqTDM9BW58cl0VYkViRxFiFTk1L0g/JxVRTDshFmAHPQs1OitiWhEUGSYzKwQAYC1bWTEkBD5vFAMXESEmR14wUGR2elhIbj5QXzo7GCAmfCofMxw2BkM2UGhmHAEAOxNVS3wQEy8iORkAegktAGI2EScyagcBbkIZXTwreysvNmZ6eWJihaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jrOep2sffk9vRsPngttrShaTSksDWqP3jRF8UGGN9X24UG0yS1NtiC14jFHUJKBsaKhtYVgcmUWYYYCdZdC4sAxEgBTwqLkgHJhcZTzshFSE2WEFddK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX4LfT2orm3pCsqLDa4azUwo7lxK3X99PX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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, antiSpy = { kick = true, halt = true } })
