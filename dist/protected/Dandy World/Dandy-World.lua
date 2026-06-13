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

local __k = 'CWh4OPtNjL9mPi3JKcFegxsC'
local __p = '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IDJAFh0lGh0PPk8EMwwRY0EPKQYGFFMULCUDRz8xFytKbBlNcEkTanZDIQQKHUkEJiM7UT0mHS0PZBs6PxtYOTsCJQBFUXkvLDQJWG8FBysYBVcdJR1gLzkVLwYCWE5jJDYFUXUXETo5KUsbOQpWYmk2NQAVMR0zNiM7UT0mHS0PbhBnPAZQKydDCgwAEAcqLTBIFG9wVG5KbBlQcA5SJy5ZAQATKxYxNT4LUWdyOCcNJE0EPg4RY0EPKQYGFFMVKiUcQS48IT0PPhlNcEkTanZDIQQKHUkEJiM7UT0mHS0PZBs7ORtHPyoPExYCClFqSTsHVy48VAIFL1gBAAVSMy4RZkVHWFNjfnc4WC4pETwZYnUCMwhfGicCPwAVcnkqJXcGWztwEy8HKQMkIyVcKy8GIk1OWAcrJjlIUy49EWAmI1gJNQ0JHSoKMk1OWBYtJ11iGWJwltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjQGZOZlRJWDAMDREhc0V9WW6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39tpKgoEGR9jADgGUiY3VHNKN0RnEwZdLCIEaCImNTYcDRYlcW9wVG5KbARNci1SJC8aYRZHLxwxLzNKPgw/GigDKxc9HChwDxQqAkVHWFNjY3dVFH5mQXtYdAtc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cEkTamtDZgkIGxIvYzgDGG81BjxKcRkdMwhfJmMFKExtWFNjY3dIFG9wVG5KJV9NPgZHaiQIZhEPHR1jNDYaWmdyLxdYB2RNPAZcOnFDZEVJVlM3LCQcRiY+E2YPPktEeUlWJC9pZkVHWFNjY3dIFG9wGCEJLVVNNB0Td2sXPxUCUBQmNx4GQCoiAi8GZRlQbUkRLD4NJREOFx1hYzYGUG83ETojIk0IIh9SJmNKZgoVWBQmNx4GQCoiAi8GRhlNcEkTamtDZkVHWAciMDxGQy45AGYOOBBncEkTamtDZkUCFhdJY3dIFCo+EGdgKVcJWmNVPyUAMgwIFlMWNz4ER2E0HT0eLVcONUFSZmsBb29HWFNjKjFIWiAkVC9KI0tNPgZHailDMg0CFlMxJiMdRiFwGS8eJBcFJQ5Wai4NIm9HWFNjMTIcQT0+VGYLbBRNMkAdByoEKAwTDRcmSTIGUEVaWWNKrqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zTEhKWEBtYwUteQAEMR1gYRRNsvyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3ch8sIDYEFB01GSEeKUpNbUlIahQAJwYPHVN+YywVGG8PETgPIk0ecFQTJCIPZhhtFBwgIjtIUjo+FzoDI1dNNR9WJD8QbkxtWFNjYz4OFB01GSEeKUpDDwxFLyUXNUUGFhdjETIFWzs1B2A1KU8IPh1AZBsCNAAJDFM3KzIGFD01ADsYIhk/NQRcPi4QaDoCDhYtNyRIUSE0fm5KbBk/NQRcPi4QaDoCDhYtNyRICW8FACcGPxcfNRpcJj0GFgQTEFsALDkOXSh+MRgvAm0+DzlyHgNKTEVHWFMxJiMdRiFwJisHI00II0dsLz0GKBEUchYtJ10OQSEzACcFIhk/NQRcPi4QaAICDFsoJi5BPm9wVG4DKhk/NQRcPi4QaDoEGRArJgwDUTYNVC8EKBk/NQRcPi4QaDoEGRArJgwDUTYNWh4LPlwDJElHIi4NZhcCDAYxLXc6USI/ACsZYmYOMQpbLxAIIxw6WBYtJ11IFG9wGCEJLVVNPgheL2teZiYIFhUqJHk6cQIfIAs5F1IIKTQTJTlDLQAeclNjY3cEWywxGG4POhlQcAxFLyUXNU1OQ1MqJXcGWztwEThKOFEIPklBLz8WNAtHFhovYzIGUEVwVG5KIFYOMQUTOGteZgARQjUqLTMuXT0jAA0CJVUJeAdSJy5KTEVHWFMqJXcaFDs4ESBKHlwAPx1WOWU8JQQEEBYYKDIRaW9tVDxKKVcJWkkTamsRIxESCh1jMV0NWitaEjsEL00EPwcTGC4OKRECC10lKiUNHCQ1DWJKYhdDeWMTamtDKgoEGR9jMXdVFB01GSEeKUpDNwxHYiAGP0xcWBolYzkHQG8iVDoCKVdNIgxHPzkNZgMGFAAmYzIGUEVwVG5KIFYOMQUTKzkENUVaWAciITsNGj8xFyVCYhdDeWMTamtDNAATDQEtYycLVSM8XCgfIloZOQZdYmJDNF8hEQEmEDIaQioiXDoLLlUIfhxdOioALU0GChQwb3dZGG8xBikZYldEeUlWJC9KTAAJHHklNjkLQCY/Gm44KVQCJAxAZCINMAoMHVsoJi5EFGF+WmdgbBlNcAVcKSoPZhdHRVMRJjoHQCojWikPOBEGNRAacWsKIEUJFwdjMXccXCo+VDwPOEwfPklVKycQI0UCFhdJY3dIFCM/Fy8GbFgfNxoTd2sXJwcLHV0zIjQDHGF+WmdgbBlNcAVcKSoPZhcCCwYvNyRICW8rVD4JLVUBeA9GJCgXLwoJUFpjMTIcQT0+VDxQBVcbPwJWGS4RMAAVUAciITsNGjo+BC8JJxEMIg5AZmtSakUGChQwbTlBHW81GipDbERncEkTaiIFZgsIDFMxJiQdWDsjL383bE0FNQcTOC4XMxcJWBUiLyQNFCo+EERKbBlNJAhRJi5NNAAKFwUmayUNRzo8AD1GbAhEWkkTamsRIxESCh1jNyUdUWNwAC8IIFxDJQdDKygIbhcCCwYvNyRBPio+EEQMOVcOJABcJGsxIwgIDBYwbTQHWiE1FzpCJ1wUfElVJGJpZkVHWB8sIDYEFD1wSW44KVQCJAxAZCwGMk0MHQpqSXdIFG85Em4EI01NIklcOGsNKRFHCl0MLRQEXSo+AAscKVcZcB1bLyVDNAATDQEtYzkBWG81GipgbBlNcBtWPj4RKEUVVjwtADsBUSEkMTgPIk1XEwZdJC4AMk0BDR0gNz4HWmd+WmBDRhlNcEkTamtDKgoEGR9jLDxEFCoiBm5XbEkOMQVfYi0NakVJVl1qSXdIFG9wVG5KJV9NPgZHaiQIZhEPHR1jNDYaWmdyLxdYB2RNMwZdJC4AMkVFVl0oJi5GGm1qVGxEYk0CIx1BIyUEbgAVClpqYzIGUEVwVG5KKVcJeWNWJC9pTEhKWJHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5ERHYRlZfklhBQQuZjciKzwPFgMhewFaWWNKrqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zTAkIGxIvYwUHWyJwSW4RMTNnfUQTCycPZjEQEQA3JjNIYCA/Gm4HI10IPBoTIyVDMg0CWBA2MSUNWjtwBiEFITMLJQdQPiIMKEU1FxwubTANQBsnHT0eKV0eeEA5amtDZgkIGxIvYzgdQG9tVDUXRhlNcElfJSgCKkUVFxwuY2pIYyAiHz0aLVoIai9aJC8lLxcUDDArKjsMHG0TATwYKVcZAgZcJ2lKTEVHWFMqJXcGWztwBiEFIRkZOAxdajkGMhAVFlMsNiNIUSE0fm5KbBkLPxsTFWdDIkUOFlMqMzYBRjx4BiEFIQMqNR13LzgAIwsDGR03MH9BHW80G0RKbBlNcEkTaiIFZgFdMQACa3UlWys1GGxDbE0FNQc5amtDZkVHWFNjY3dIWCAzFSJKIhlQcA0dBCoOI29HWFNjY3dIFG9wVG5HYRkuPwReJSVDKAQKER0keXdUei49EXAnI1ceJAxBZmsuKQsUDBYxMHcOWyM0ETxKL1EEPA1BLyVPZgoVWBsiMHclWyEjACsYbFgZJBtaKD4XI29HWFNjY3dIFG9wVG4DKhkDag9aJC9LZCgIFgA3JiVKHW8/Bm4Odn4IJChHPjkKJBATHVthCiQlWyEjACsYbhBNPxsTYi9NFgQVHR03YzYGUG80Wh4LPlwDJEd9KyYGZlhaWFEOLDkbQCoiB2xDbE0FNQc5amtDZkVHWFNjY3dIFG9wVCIFL1gBcAFBOmteZgFdPhotJxEBRjwkNyYDIF1FciFGJyoNKQwDKhwsNwcJRjtyXW4FPhkJfjlBIyYCNBw3GQE3SXdIFG9wVG5KbBlNcEkTamsKIEUPCgNjNz8NWm8kFSwGKRcEPhpWOD9LKRATVFM4YzoHUCo8VHNKKBVNIgZcPmteZg0VCF9jLTYFUW9tVCBQK0oYMkERByQNNRECCldhb3VKHW8tXW4PIl1ncEkTamtDZkVHWFNjJjkMPm9wVG5KbBlNNQdXQGtDZkUCFhdJY3dIFD01ADsYIhkCJR05LyUHTG9KVVMCLztIeS4zHCcEKRkAPw1WJjhDMQwTEFM3KzIBRm8zGyMaIFwZOQZdai8CMgRtHgYtICMBWyFwJiEFIRcKNR1+KygLLwsCC1tqSXdIFG88Gy0LIBkCJR0Td2sYO29HWFNjLzgLVSNwBiEFIRlQcD5cOCAQNgQEHUkFKjkMciYiBzopJFABNEERCT4RNAAJDCEsLDpKHUVwVG5KJV9NPgZHajkMKQhHDBsmLXcaUTslBiBKI0wZcAxdLkFDZkVHHhwxYwhEFCtwHSBKJUkMORtAYjkMKQhdPxY3BzIbVyo+EC8EOEpFeUATLiRpZkVHWFNjY3cBUm80TgcZDRFPHQZXLydBb0UGFhdjazNGei49EXQMJVcJeEt+KygLLwsCWlpjLCVIUGEeFSMPdl8EPg0baAwGKAAVGQcsMXVBFCAiVCpQC1wZER1HOCIBMxECUFEKMBoJVyc5GitIZRBNJAFWJEFDZkVHWFNjY3dIFG88Gy0LIBkfPwZHanZDIl8hER0nBT4aRzsTHCcGKG4FOQpbAzgibkclGQAmEzYaQG18VDoYOVxEWkkTamtDZkVHWFNjYz4OFD0/GzpKOFEIPmMTamtDZkVHWFNjY3dIFG9wGCEJLVVNIApHanZDIl8gHQcCNyMaXS0lACtCbnoCPRlfLz8KKQs3HQEgJjkcVSg1VmdgbBlNcEkTamtDZkVHWFNjY3dIFG8/Bm4Odn4IJChHPjkKJBATHVthEyUHUz01Bz1IZTNNcEkTamtDZkVHWFNjY3dIFG9wVCEYbF1XFwxHCz8XNAwFDQcma3UrWyIgGCseJVYDckA5amtDZkVHWFNjY3dIFG9wVDoLLlUIfgBdOS4RMk0IDQdvYyxiFG9wVG5KbBlNcEkTamtDZkVHWFMuLDMNWG9tVCpGbEsCPx0Td2sRKQoTVFMtIjoNFHJwEGAkLVQIfGMTamtDZkVHWFNjY3dIFG9wVG5KbEkIIgpWJD9De0UXGwdvSXdIFG9wVG5KbBlNcEkTamtDZkVHGxwuMzsNQCpwSW4Odn4IJChHPjkKJBATHVthADgFRCM1ACsObhBNbVQTPjkWI0UIClMneRANQA4kADwDLkwZNUERAzggKQgXFBY3JjNKHW9tSW4ePkwIfGMTamtDZkVHWFNjY3dIFG9wCWdgbBlNcEkTamtDZkVHHR0nSXdIFG9wVG5KKVcJWkkTamsGKAFtWFNjYyUNQDoiGm4FOU1nNQdXQEFOa0UkGR0sLT4LVSNwHToPIRkDMQRWOWsFNAoKWCEmMzsBVy4kESo5OFYfMQ5WZAIXIwgqFxc2LzIbFK3Q4G4fP1wJcB1caiIHIwsTERU6SXpFFDwgFTkEKV1NIABQIT4TNUUOFlM3KzJIVzoiBisEOBkfPwZeamMXLgAeXwEmYzkJWSo0VCsSLVoZPBATJiIII0UTEBZjLjgMQSM1XWBgHlYCPUd6Hg4uGSsmNTYQY2pIT0VwVG5KBFwMPB1bASIXZlhHDAE2JntIZCAgVHNKOEsYNUUTGTsGIwEkGR0nOndVFDsiAStGbHsMPg1SLS5De0UTCgYmb11IFG9wPSAZOEsYMx1aJSUQZlhHDAE2JntIZCAgNiEeOFUIcFQTPjkWI0lHMgYuMzIady4yGCtKcRkZIhxWZms3JxUCWE5jNyUdUWNaVG5KbGkfPx1WIyUhJxdHRVM3MSINGG8DGSEBKXsCPQsTd2sXNBACVFMGKTILQA0lADoFIhlQcB1BPy5PZiYPFxAsLzYcUW9tVDoYOVxBWkkTamskMwgFGR8vY2pIQD0lEWJKH00CIB5SPigLZlhHDAE2JntIZzs1FSIeJHoMPg1KanZDMhcSHV9jEDwBWCMTHCsJJ3oMPg1KanZDMhcSHV9JY3dIFA45BgYFPldNbUlHOD4GakUiAAcxIjQcXSA+Jz4PKV0uMQdXM2teZhEVDRZvYwEJWDk1VHNKOEsYNUUTCSMMJQoLGQcmATgQFHJwADwfKRVncEkTagQRKAQKHR03Y2pIQD0lEWJKBlgaMhtWKyAGNEVaWAcxNjJEFBwkFSMDIlguMQdXM2teZhEVDRZvYxUHWg0/Gm5XbE0fJQwfQGtDZkUkEAEqMCMFVTwTGyEBJVxNbUlHOD4GakUjGR0nOhIJRzs1BgsNK0pNbUlHOD4Gam8acnlubncpWCNwBCcJJ1gPPAwTIz8GKxZHER1jNz8NFCwlBjwPIk1NIgZcJ0EFMwsEDBosLXc6WyA9WikPOHAZNQRAYmJpZkVHWB8sIDYEFCAlAG5XbEIQWkkTamsPKQYGFFMxLDgFFHJwIyEYJ0odMQpWcA0KKAEhEQEwNxQAXSM0XGwpOUsfNQdHGCQMK0dOclNjY3cBUm8+GzpKPlYCPUlHIi4NZhcCDAYxLXcHQTtwESAORhlNcElfJSgCKkUUHRYtY2pITzJaVG5KbFUCMwhfai0WKAYTERwtYyMaTQ40EGYOZTNNcEkTamtDZgwBWB0sN3cMFCAiVD0PKVc2NDQTPiMGKEUVHQc2MTlIUSE0fm5KbBlNcEkTOS4GKD4DJVN+YyMaQSpaVG5KbBlNcEkeZ2suJxEEEFMhOncNTC4zAG4DOFwAcAdSJy5DCTdHGgpjMyUNRyo+FytKI19NMUljOCQbLwgODAoTMTgFRDtwXCMFP01NIABQIT4TNUUPGQUmYzgGUWZaVG5KbBlNcElfJSgCKkUKGQcgKzIbei49EW5XbGsCPwQdAx8mCzopOT4GEAwMGgExGSs3bARQcB1BPy5pZkVHWFNjY3cEWywxGG4CLUo9IgZeOj9De0UDQjUqLTMuXT0jAA0CJVUJBwFaKSMqNSRPWiMxLC8BWSYkDR4YI1QdJEsfaj8RMwBOWA1+YzkBWEVwVG5KbBlNcAVcKSoPZgwULBwsLz4bXG9tVCpQBUoseEtnJSQPZExHFwFjJ20vUTsRADoYJVsYJAwbaAIQDxECFVFqYzgaFCtqMyseDU0ZIgBRPz8GbkcuDBYuCjNKHW8uSW4EJVVncEkTamtDZkUOHlMuIiMLXCojOi8HKRkCIklaOR8MKQkOCxtjLCVIHCcxBx4YI1QdJElSJC9DIl8uCzJrYRoHUCo8VmdDbE0FNQc5amtDZkVHWFNjY3dIWCAzFSJKPlYCJGMTamtDZkVHWFNjY3cBUm80TgcZDRFPBAZcJmlKZhEPHR1jMTgHQG9tVCpQClADNC9aODgXBQ0OFBdrYR8JWis8EWxDRhlNcEkTamtDZkVHWBYvMDIBUm80TgcZDRFPHQZXLydBb0UTEBYtYyUHWztwSW4OYmkfOQRSODIzJxcTWBwxYzNSciY+EAgDPkoZEwFaJi80LgwEEDowAn9Kdi4jER4LPk1PfElHOD4Gb29HWFNjY3dIFG9wVG4PIEoIOQ8TLnEqNSRPWjEiMDI4VT0kVmdKOFEIPklBJSQXZlhHHFMmLTNiFG9wVG5KbBlNcEkTIy1DNAoIDFM3KzIGPm9wVG5KbBlNcEkTamtDZkUTGREvJnkBWjw1BjpCI0wZfElIQGtDZkVHWFNjY3dIFG9wVG5KbBlNPQZXLydDe0UDVFMxLDgcFHJwBiEFOBVncEkTamtDZkVHWFNjY3dIFG9wVG4ELVQIcFQTLmUtJwgCQhQwNjVAFmcLFWMQERBFCygeEBZKZElHWlZyY3JaFmZ8VGNHbBs+IAxWLggCKAEeWlOhxcVIFhwgESsObHoMPg1KaEFDZkVHWFNjY3dIFG9wVG5KMRBncEkTamtDZkVHWFNjJjkMPm9wVG5KbBlNNQdXQGtDZkUCFhdJY3dIFGJ9VB0JLVdNPQZXLycQZgQJHFM3LDgER28xAG4POlwfKUlXLzsXLkVPEQcmLiRIWS4pVCwPbFADcBpGKGYFKQkDHQEwal1IFG9wEiEYbGZBcA0TIyVDLxUGEQEwayUHWyJqMyseCFweMwxdLioNMhZPUVpjJzhiFG9wVG5KbBkENklXcAIQB01FNRwnJjtKHW8/Bm4OdnAeEUERHiQMKkdOWAcrJjlIQD0pNSoOZF1EcAxdLkFDZkVHHR0nSXdIFG8iETofPldNPxxHQC4NIm9tVV5jDCMAUT1wBCILNVwfI04TPiQMKBZHUBY7IDsdUCY+E24fPxBnNhxdKT8KKQtHKhwsLnkPUTsfACYPPm0CPwdAYmJpZkVHWB8sIDYEFCAlAG5XbEIQWkkTamsPKQYGFFMzLzYRUT0jVHNKG1YfOxpDKygGfCMOFhcFKiUbQAw4HSIOZBskPi5SJy4zKgQeHQEwYX5iFG9wVCcMbFcCJElDJioaIxcUWAcrJjlIRiokATwEbFYYJElWJC9pZkVHWBUsMXc3GG89VCcEbFAdMQBBOWMTKgQeHQEweRANQAw4HSIOPlwDeEAaai8MTEVHWFNjY3dIXSlwGXQjP3hFciRcLi4PZExHGR0nYzpGei49EW4UcRkhPwpSJhsPJxwCCl0NIjoNFDs4ESBgbBlNcEkTamtDZkVHFBwgIjtIXD0gVHNKIQMrOQdXDCIRNREkEBovJ39KfDo9FSAFJV0/PwZHGioRMkdOclNjY3dIFG9wVG5KbFUCMwhfaiMWK0VaWB55BT4GUAk5Bj0eD1EEPA18LAgPJxYUUFELNjoJWiA5EGxDRhlNcEkTamtDZkVHWBolYz8aRG8kHCsEbE0MMgVWZCINNQAVDFssNiNEFDRwGSEOKVVNbUleZmsRKQoTWE5jKyUYGG8+FSMPbARNPUd9KyYGakUPDR4iLTgBUG9tVCYfIRkQeUlWJC9pZkVHWFNjY3cNWitaVG5KbFwDNGMTamtDNAATDQEtYzgdQEU1GipgRhRAcD1bL2sGKgARGQcsMXcYWzw5ACcFIhlFNwhHL2sXKUUJHQs3YzEEWyAiXUQMOVcOJABcJGsxKQoKVhQmNxIEUTkxACEYHFYeeEA5amtDZgkIGxIvYzIEUTlwSW49I0sGIxlSKS5ZAAwJHDUqMSQcdyc5GCpCbnwBNR9SPiQRNUdOclNjY3cBUm81GCscbE0FNQc5amtDZkVHWFMvLDQJWG8gVHNKKVUIJlN1IyUHAAwVCwcAKz4EUBg4HS0CBUoseEtxKzgGFgQVDFFvYyMaQSp5fm5KbBlNcEkTIy1DNkUTEBYtYyUNQDoiGm4aYmkCIwBHIyQNZgAJHHljY3dIUSE0fisEKDNnfUQTqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTSXpFFHp+VB0+DW0+WkQeaqn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW010EWywxGG45OFgZI0kOajBDKwQEEBotJiQsWyE1VHNKfBVNOR1WJzgzLwYMHRdjfndYGG81By0LPFwJFxtSKDhDe0VXVFMnJjYcXDxwSW5aYBkeNRpAIyQNFREGCgdjfnccXSw7XGdKMTMLJQdQPiIMKEU0DBI3MHkaUTw1AGZDbGoZMR1AZCYCJQ0OFhYwBzgGUWNwJzoLOEpDOR1WJzgzLwYMHRdvYwQcVTsjWisZL1gdNQ10OCoBNUlHKwciNyRGUCoxACYZbARNYEUDZntPdl5HKwciNyRGRyojBycFImoZMRtHanZDMgwEE1tqYzIGUEU2ASAJOFACPklgPioXNUsSCAcqLjJAHUVwVG5KIFYOMQUTOWteZggGDBttJTsHWz14ACcJJxFEcEQTGT8CMhZJCxYwMD4HWhwkFTweZTNNcEkTJiQAJwlHEFN+YzoJQCd+EiIFI0tFI0kcanhVdlVOQ1MwY2pIR299VCZKZhleZlkDQGtDZkULFxAiL3cFFHJwGS8eJBcLPAZcOGMQZkpHTkNqeHdIFDxwSW4ZbBRNPUkZan1TTEVHWFMxJiMdRiFwBzoYJVcKfg9cOCYCMk1FXUNxJ21NBH00Tmtafl1PfElbZmsOakUUUXkmLTNiPmJ9VKz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2kFOa0VRVlMGEAdI1s/EVBodJUoZNQ1AamRDCwQEEBotJiRIG28ZACsHPxlCcDlfKzIGNBZtVV5jocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6RlUCMwhfag4wFkVaWAhJY3dIFBwkFToPbARNK2MTamtDZkVHWAc0KiQcUStwSW4MLVUeNUUTJyoALgwJHVN+YzEJWDw1WG4DOFwAcFQTLCoPNQBLWAMvIi4NRm9tVCgLIEoIfGMTamtDZkVHWAc0KiQcUSsUHT0eLVcONUkOaj8RMwBLclNjY3dIFG9wByYFO3YDPBBwJiQQI0VaWBUiLyQNGG9wFyIFP1w/MQdUL2teZlNXVHljY3dIFG9wVDodJUoZNQ1wJScMNEVaWDAsLzgaB2E2BiEHHn4veFsGf2dDcFVLWEVzantiFG9wVG5KbBkAMQpbIyUGBQoLFwFjfncrWyM/Bn1EKksCPTt0CGNSdFVLWEFxc3tIBX1gXWJgbBlNcEkTamsKMgAKOxwvLCVIFG9wSW4pI1UCIlodLDkMKzcgOltxdmJEFH1gRGJKeglEfGMTamtDZkVHWAMvIi4NRgw/GCEYbBlQcCpcJiQRdUsBChwuERAqHH98VHxbfBVNYlsKY2dpZkVHWA5vSXdIFG8PAC8NPxlQcBITPjwKNRECHFN+YywVGG89FS0CJVcIcFQTMTZPZgwTHR5jfncTSWNwBCILNVwfcFQTMTZDO0ltWFNjYwgLWyE+VHNKN0RBWhQ5QCcMJQQLWBU2LTQcXSA+VCMLJ1wvEkFSLiQRKAACVFM3Ji8cGG8zGyIFPhVNOAxaLSMXb29HWFNjLzgLVSNwFixKcRkkPhpHKyUAI0sJHQRrYRUBWCMyGy8YKH4YOUsaQGtDZkUFGl0NIjoNFHJwVhdYB2YoAzkRcWsBJEsmHBwxLTINFHJwFSoFPlcINWMTamtDJAdJKxo5JndVFBoUHSNYYlcIJ0EDZmtSflVLWENvYz8NXSg4AG4FPhleYEA5amtDZgcFViA3NjMbeyk2BysebARNBgxQPiQRdUsJHQRrc3tIB2NwRGdgbBlNcAtRZAoPMQQeCzwtFzgYFHJwADwfKQJNMgsdByobAgwUDBItIDJICW9hRH5aRhlNcElfJSgCKkULGREmL3dVFAY+BzoLIloIfgdWPWNBEgAfDD8iITIEFmZaVG5KbFUMMgxfZAkCJQ4AChw2LTM8Ri4+Bz4LPlwDMxATd2tTaFFtWFNjYzsJVio8WgwLL1IKIgZGJC8gKQkICkBjfncrWyM/Bn1EKksCPTt0CGNSdklHSUNvY2VYHUVwVG5KIFgPNQUdGSIZI0VaWCYHKjpaGikiGyM5L1gBNUECZmtSb15HFBIhJjtGdiAiECsYH1AXNTlaMi4PZlhHSHljY3dIWC4yESJEClYDJEkOag4NMwhJPhwtN3kiQT0xT24GLVsIPEdnLzMXFQwdHVN+Y2ZcPm9wVG4GLVsIPEdnLzMXBQoLFwFwY2pIVyA8GzxRbFUMMgxfZB8GPhFHRVM3Ji8cD288FSwPIBc9MRtWJD9De0UFGnljY3dIWCAzFSJKP00fPwJWanZDDwsUDBItIDJGWionXGw/BWoZIgZYL2lKTEVHWFMwNyUHXyp+NyEGI0tNbUlQJScMNF5HCwcxLDwNGhs4HS0BIlweI0kOanpNc15HCwcxLDwNGh8xBisEOBlQcAVSKC4PTEVHWFMhIXk4VT01GjpKcRkMNAZBJC4GTEVHWFMxJiMdRiFwFixGbFUMMgxfQC4NIm9tFBwgIjtIUjo+FzoDI1dNMwVWKzkhMwYMHQdrISILXyokXURKbBlNNgZBahRPZgcFWBotYycJXT0jXCwfL1IIJEATLiRpZkVHWFNjY3cBUm8yFm4LIl1NMgsdGioRIwsTWAcrJjlIVi1qMCsZOEsCKUEaai4NIm9HWFNjJjkMPio+EERgIFYOMQUTLD4NJREOFx1jNicMVTs1NjsJJ1wZeAtGKSAGMklHEQcmLiREFCw/GCEYYBkLPxteKz8XIxdOclNjY3cEWywxGG4ZKVwDcFQTMTZpZkVHWB8sIDYEFBB8VCYYPBlQcDxHIycQaAMOFhcOOgMHWyF4XURKbBlNNgZBahRPZgBHER1jKicJXT0jXCceKVQeeUlXJUFDZkVHWFNjYyQNUSELEWAYI1YZDUkOaj8RMwBtWFNjY3dIFG88Gy0LIBkPMkkOaikWJQ4CDCgmbSUHWzsNfm5KbBlNcEkTIy1DKAoTWBEhYyMAUSFwFixKcRkAMQJWCAlLI0sVFxw3b3cNGiExGStGbFoCPAZBY3BDJBAEExY3GDJGRiA/ABNKcRkPMklWJC9pZkVHWFNjY3cEWywxGG4GLVsIPEkOaikBfCMOFhcFKiUbQAw4HSIOG1EEMwF6OQpLZDECAAcPIjUNWG15fm5KbBlNcEkTIy1DKgQFHR9jNz8NWkVwVG5KbBlNcEkTamsPKQYGFFMnKiQcPm9wVG5KbBlNcEkTaiIFZg0VCFM3KzIGFCs5BzpKcRk4JABfOWUHLxYTGR0gJn8ARj9+JCEZJU0EPwcfai5NNAoIDF0TLCQBQCY/GmdKKVcJWkkTamtDZkVHWFNjYz4OFAoDJGA5OFgZNUdAIiQUCQsLATAvLCQNFC4+EG4OJUoZcAhdLmsHLxYTWE1jBgQ4GhwkFToPYloBPxpWGCoNIQBHDBsmLV1IFG9wVG5KbBlNcEkTamtDJAdJPR0iITsNUG9tVCgLIEoIWkkTamtDZkVHWFNjYzIERypaVG5KbBlNcEkTamtDZkVHWBEhbRIGVS08ESpKcRkZIhxWQGtDZkVHWFNjY3dIFG9wVG4GLVsIPEdnLzMXZlhHHhwxLjYcQCoiVC8EKBkLPxteKz8XIxdPHV9jJz4bQGZwGzxKKRcDMQRWQGtDZkVHWFNjY3dIFCo+EERKbBlNcEkTai4NIm9HWFNjJjkMPm9wVG4MI0tNIgZcPmdDJAdHER1jMzYBRjx4FjsJJ1wZeUlXJUFDZkVHWFNjYz4OFCE/AG4ZKVwDCxtcJT8+ZhEPHR1JY3dIFG9wVG5KbBlNOQ8TKClDMg0CFlMhIW0sUTwkBiETZBBNNQdXQGtDZkVHWFNjY3dIFC0lFyUPOGIfPwZHF2teZgsOFHljY3dIFG9wVCsEKDNNcEkTLyUHTAAJHHlJJSIGVzs5GyBKCWo9fhpWPh8ULxYTHRdrNX5iFG9wVAs5HBc+JAhHL2UXMQwUDBYnY2pIQkVwVG5KJV9NPgZHaj1DMg0CFlMgLzIJRg0lFyUPOBEoAzkdFT8CIRZJDAQqMCMNUGZrVAs5HBcyJAhUOWUXMQwUDBYnY2pITzJwESAORlwDNGNVPyUAMgwIFlMGEAdGRyokOS8JJFADNUFFY0FDZkVHPSATbQQcVTs1WiMLL1EEPgwTd2sVTEVHWFMqJXcGWztwAm4eJFwDcApfLyoRBBAEExY3axI7ZGEPAC8NPxcAMQpbIyUGb15HPSATbQgcVSgjWiMLL1EEPgwTd2sYO0UCFhdJJjkMPiklGi0eJVYDcCxgGmUQIxEuDBYuayFBPm9wVG4vH2lDAx1SPi5NLxECFVN+YyFiFG9wVCcMbFcCJElFaj8LIwtHGx8mIiUqQSw7ETpCCWo9fjZHKywQaAwTHR5qeHctZx9+KzoLK0pDOR1WJ2teZh4aWBYtJ10NWitaEjsEL00EPwcTDxgzaBYCDCMvIi4NRmcmXURKbBlNFTpjZBgXJxECVgMvIi4NRm9tVDhgbBlNcABVaiUMMkURWAcrJjlIVyM1FTwoOVoGNR0bDxgzaDoTGRQwbScEVTY1BmdRbHw+AEdsPioENUsXFBI6JiVICW8rCW4PIl1nNQdXQEEFMwsEDBosLXctZx9+BzoLPk1FeWMTamtDLwNHPSATbQgLWyE+WiMLJVdNJAFWJGsRIxESCh1jJjkMPm9wVG4vH2lDDwpcJCVNKwQOFlN+YwUdWhw1BjgDL1xDGAxSOD8BIwQTQjAsLTkNVzt4EjsEL00EPwcbY0FDZkVHWFNjYz4OFAoDJGA5OFgZNUdHPSIQMgADWAcrJjliFG9wVG5KbBlNcEkTPzsHJxECOgYgKDIcHAoDJGA1OFgKI0dHPSIQMgADVFMRLDgFGig1ABodJUoZNQ1AYmJPZiA0KF0QNzYcUWEkAycZOFwJEwZfJTlPZgMSFhA3KjgGHCp8VCpDRhlNcEkTamtDZkVHWFNjY3cBUm80VC8EKBkoAzkdGT8CMgBJDAQqMCMNUAs5BzoLIloIcB1bLyVDNAATDQEtY39K1tXwVGsZbGJINBpHF2lKfAMICh4iN38NGiExGStGbFQMJAEdLCcMKRdPHFpqYzIGUEVwVG5KbBlNcEkTamtDZkVHChY3NiUGFG2y7u5KbhlDfklWZCUCKwBtWFNjY3dIFG9wVG5KKVcJeWMTamtDZkVHWBYtJ11IFG9wVG5KbFALcCxgGmUwMgQTHV0uIjQAXSE1VDoCKVdncEkTamtDZkVHWFNjNicMVTs1NjsJJ1wZeCxgGmU8MgQAC10uIjQAXSE1WG44I1YAfg5WPgYCJQ0OFhYwa35EFAoDJGA5OFgZNUdeKygLLwsCOxwvLCVEFCklGi0eJVYDeAwfai9KTEVHWFNjY3dIFG9wVG5KbBkBPwpSJmsQZlhHWpHZ2ndKFGF+VCtEIlgANWMTamtDZkVHWFNjY3dIFG9wHShKKRcOPwRDJi4XI0UTEBYtYyRICW9yltL5bH0iHiwRai4NIm9HWFNjY3dIFG9wVG5KbBlNOQ8TL2UTIxcEHR03YzYGUG8+GzpKKRcOPwRDJi4XI0UTEBYtYyRICW94Vqzw1RlINEwWaGJZIAoVFRI3azoJQCd+EiIFI0tFNUdDLzkAIwsTUVpjJjkMPm9wVG5KbBlNcEkTamtDZkUOHlMnYyMAUSFwB25XbEpNfkcTYmlDHUADCwceYX5SUiAiGS8eZFQMJAEdLCcMKRdPHFpqYzIGUEVwVG5KbBlNcEkTamtDZkVHChY3NiUGFDxaVG5KbBlNcEkTamtDIwsDUXljY3dIFG9wVCsEKDNNcEkTamtDZgwBWDYQE3k7QC4kEWADOFwAcB1bLyVpZkVHWFNjY3dIFG9wAT4OLU0IEhxQIS4XbiA0KF0cNzYPR2E5ACsHYBk/PwZeZCwGMiwTHR4wa35EFAoDJGA5OFgZNUdaPi4OBQoLFwFvYzEdWiwkHSEEZFxBcA0aQGtDZkVHWFNjY3dIFG9wVG4DKhkJcB1bLyVDNAATDQEtY39K1tjWVGsZbGJINBpHF2lKfAMICh4iN38NGiExGStGbFQMJAEdLCcMKRdPHFpqYzIGUEVwVG5KbBlNcEkTamtDZkVHChY3NiUGFG2y48hKbhlDfklWZCUCKwBtWFNjY3dIFG9wVG5KKVcJeWMTamtDZkVHWBYtJ11IFG9wVG5KbFALcCxgGmUwMgQTHV0zLzYRUT1wACYPIjNNcEkTamtDZkVHWFM2MzMJQCoSAS0BKU1FFTpjZBQXJwIUVgMvIi4NRmNwJiEFIRcKNR18PiMGNDEIFx0wa35EFAoDJGA5OFgZNUdDJioaIxckFx8sMXtIUjo+FzoDI1dFNUUTLmJpZkVHWFNjY3dIFG9wVG5KbFUCMwhfaiMTZlhHHV0rNjoJWiA5EG4LIl1NPQhHImUFKgoIClsmbT8dWS4+GycOYnEIMQVHImJDKRdHWl5hSXdIFG9wVG5KbBlNcEkTamsKIEUDWAcrJjlIRiokATwEbBFPsv68am4QZj5CCxszb3dNUDwkKWxDdl8CIgRSPmMGaAsGFRZvYyMHRzsiHSANZFEdeUUTJyoXLksBFBwsMX8MHWZwESAORhlNcEkTamtDZkVHWFNjY3caUTslBiBKbtv630kRamVNZgBJFhIuJl1IFG9wVG5KbBlNcElWJC9KTEVHWFNjY3dIUSE0fm5KbBkIPg0aQC4NIm9tVV5jocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6RhRAcF4dahg2FDMuLjIPYx8teB8VJh1gYRRNsvyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3ch8sIDYEFBwlBjgDOlgBcFQTMWswMgQTHVN+YyxiFG9wVCAFOFALOQxBDyUCJAkCHFN+YzEJWDw1WG4EI00ENgBWOBkCKAICWE5jcGJEFBA8FT0eDVUIIh1WLmteZlVLclNjY3cJWjs5MzwLLhlQcA9SJjgGam9HWFNjIiIcWw4mGycObARNNghfOS5PZgQRFxonETYGUypwSW5YeRVnLUlOQEFOa0UpFwcqJT4NRm+y9NpKPUwEMwITJSVONQYVHRYtYzkHQCY2DW4dJFwDcAgTPjwKNRECHFMmLSMNRjxwBi8EK1xnPAZQKydDIBAJGwcqLDlIWS47EQAFOFALOQxBDDkCKwBPUXljY3dIXSlwJzsYOlAbMQUdFSUMMgwBATQ2KnccXCo+VDwPOEwfPklgPzkVLxMGFF0cLTgcXSkpMzsDbFwDNGMTamtDKgoEGR9jMDBICW8ZGj0eLVcONUddLzxLZDYEChYmLRAdXW15fm5KbBkeN0d9KyYGZlhHWipxCBMJWispOiEeJV8ENRsRQGtDZkUUH10RJiQNQAA+Jz4LO1dNbUlVKycQI29HWFNjMDBGbgY+ECsSDlwFMR9aJTlDe0UiFgYubQ0hWis1DAwPJFgbOQZBZBgKJAkOFhRJY3dIFDw3Wh4LPlwDJEkOagcMJQQLKB8iOjIaDhgxHTosI0suOABfLmNBFgkGARYxBCIBFmZaVG5KbFUCMwhfaj8PZlhHMR0wNzYGVyp+GisdZBs5NRFHBioBIwlFUXljY3dIQCN+JycQKRlQcDx3IyZRaAsCD1tzb3dbBn98VH5GbApbeWMTamtDMglJKBwwKiMBWyFwSW4/CFAAYkddLzxLdktSVFNucmFYGG9gWn9SYBldeWMTamtDMglJOhIgKDAaWzo+EBoYLVceIAhBLyUAP0VaWENtcWJiFG9wVDoGYnsMMwJUOCQWKAEkFx8sMWRICW8TGyIFPgpDNhtcJxkkBE1WSF9jcmdEFH1lXURKbBlNJAUdDCQNMkVaWDYtNjpGciA+AGAgOUsMWkkTamsXKkszHQs3ED4SUW9tVH9cRhlNcElHJmU3Ix0TOxwvLCVbFHJwNyEGI0tefg9BJSYxASdPSkZ2b3deBGNwQn5DRhlNcElHJmU3Ix0TWE5jYXViFG9wVDoGYm8EIwBRJi5De0UBGR8wJl1IFG9wACJEHFgfNQdHanZDNQJtWFNjYzsHVy48VD0ePlYGNUkOagINNREGFhAmbTkNQ2dyIQc5OEsCOwwRY3BDNREVFxgmbRQHWCAiVHNKD1YBPxsAZC0RKQg1PzFrcWJdGG9mRGJKeglEa0lAPjkMLQBJLBsqIDwGUTwjVHNKfgJNIx1BJSAGaDUGChYtN3dVFDs8fm5KbBkBPwpSJmsAKRcJHQFjfnchWjwkFSAJKRcDNR4baB4qBQoVFhYxYX5TFCw/BiAPPhcuPxtdLzkxJwEODQBjfnc9cCY9WiAPOxFdfEkFY3BDJQoVFhYxbQcJRio+AG5XbE0BWkkTamswMxcREQUiL3k3WiAkHSgTC0wEcFQTOSxpZkVHWCA2MSEBQi48WhEEI00ENhB/KykGKkVaWAcvSXdIFG8iETofPldNIw45LyUHTG8BDR0gNz4HWm8DATwcJU8MPEdALz8tKREOHhomMX8eHUVwVG5KH0wfJgBFKydNFREGDBZtLTgcXSk5ETwvIlgPPAxXanZDMG9HWFNjKjFIQm8kHCsERhlNcEkTamtDKwQMHT0sNz4OXSoiMjwLIVxFeWMTamtDZkVHWBolYwQdRjk5Ai8GYmYOPwddaj8LIwtHChY3NiUGFCo+EERKbBlNcEkTahgWNBMODhIvbQgLWyE+VHNKHkwDAwxBPCIAI0svHRIxNzUNVTtqNyEEIlwOJEFVPyUAMgwIFltqSXdIFG9wVG5KbBlNcABVaiUMMkU0DQE1KiEJWGEDAC8eKRcDPx1aLCIGNCAJGREvJjNIQCc1Gm4YKU0YIgcTLyUHTEVHWFNjY3dIFG9wVCIFL1gBcDYfaiMRNkVaWCY3KjsbGik5GionNW0CPwcbY0FDZkVHWFNjY3dIFG85Em4EI01NOBtDaj8LIwtHChY3NiUGFCo+EERKbBlNcEkTamtDZkULFxAiL3cGUS4iET0eYBkJORpHanZDKAwLVFMuIiMAGiclEytgbBlNcEkTamtDZkVHHhwxYwhEFDtwHSBKJUkMORtAYhkMKQhJHxY3FyABRzs1ED1CZRBNNAY5amtDZkVHWFNjY3dIFG9wVCIFL1gBcA0Td2s2MgwLC10nKiQcVSEzEWYCPklDAAZAIz8KKQtLWAdtMTgHQGEAGz0DOFACPkA5amtDZkVHWFNjY3dIFG9wVCcMbF1NbElXIzgXZhEPHR1jJz4bQG9tVCpRbFcIMRtWOT9De0UTWBYtJ11IFG9wVG5KbBlNcElWJC9pZkVHWFNjY3dIFG9wHShKH0wfJgBFKydNGQsIDBolOhsJVio8VDoCKVdncEkTamtDZkVHWFNjY3dIFCY2VCAPLUsIIx0TKyUHZgEOCwdjf2pIZzoiAiccLVVDAx1SPi5NKAoTERUqJiU6VSE3EW4eJFwDWkkTamtDZkVHWFNjY3dIFG9wVG5KH0wfJgBFKydNGQsIDBolOhsJVio8WhgDP1APPAwTd2sXNBACclNjY3dIFG9wVG5KbBlNcEkTamtDFRAVDho1IjtGayE/ACcMNXUMMgxfZB8GPhFHRVNrYbXylG91B24kCXg/cIuz3mtGIkUUDAYnMHVBDik/BiMLOBEDNQhBLzgXaAsGFRZvYzoJQCd+EiIFI0tFNABAPmJKTEVHWFNjY3dIFG9wVG5KbBkIPBpWQGtDZkVHWFNjY3dIFG9wVG5KbBlNAxxBPCIVJwlJJx0sNz4OTQMxFisGYm8EIwBRJi5De0UBGR8wJl1IFG9wVG5KbBlNcEkTamtDIwsDclNjY3dIFG9wVG5KbFwDNGMTamtDZkVHWBYtJ35iFG9wVCsEKDMIPg05QGZOZiQJDBpuJCUJVm+y9NpKLUwZP0RVIzkGNUU0CQYqMTopViY8HToTD1gDMwxfajwLIwtHHwEiITUNUEU2ASAJOFACPklgPzkVLxMGFF0wJiMpWjs5MzwLLhEbeWMTamtDFRAVDho1IjtGZzsxACtELVcZOS5BKylDe0URclNjY3cBUm8mVC8EKBkDPx0TGT4RMAwRGR9tHDAaVS0TGyAEbE0FNQc5amtDZkVHWFNubnckXTwkESBKKlYfcA5BKylDIxMCFgd4YyMAUW83FSMPbF8EIgxAah8ULxYTHRcQMiIBRiIXBi8IbE4FNQcTKSoWIQ0TclNjY3dIFG9wGCEJLVVNNxtSKBkmZlhHLQcqLyRGRiojGyIcKWkMJAEbaBkGNgkOGxI3JjM7QCAiFSkPYnwbNQdHOWU3MQwUDBYnECYdXT09MzwLLhtEWkkTamtDZkVHERVjJCUJVh0VVC8EKBkKIghRGA5NCQskFBomLSMtQio+AG4eJFwDWkkTamtDZkVHWFNjYwQdRjk5Ai8GYmYKIghRCSQNKEVaWBQxIjU6cWEfGg0GJVwDJCxFLyUXfCYIFh0mICNAUjo+FzoDI1dFfkcdY0FDZkVHWFNjY3dIFG9wVG5KJV9NPgZHahgWNBMODhIvbQQcVTs1Wi8EOFAqIghRaj8LIwtHChY3NiUGFCo+EERKbBlNcEkTamtDZkVHWFNjNzYbX2EnFSceZAlDYFwaQGtDZkVHWFNjY3dIFG9wVG44KVQCJAxAZC0KNABPWiAyNj4aWQwxGi0PIBtEWkkTamtDZkVHWFNjY3dIFG8DAC8ePxcIIwpSOi4HARcGGgBjfnc7QC4kB2APP1oMIAxXDTkCJBZHU1NySXdIFG9wVG5KbBlNcAxdLmJpZkVHWFNjY3cNWitaVG5KbFwBIwxaLGsNKRFHDlMiLTNIZzoiAiccLVVDDw5BKykgKQsJWAcrJjliFG9wVG5KbBk+JRtFIz0CKks4HwEiIRQHWiFqMCcZL1YDPgxQPmNKfUU0DQE1KiEJWGEPEzwLLnoCPgcTd2sNLwltWFNjYzIGUEU1GipgRhRAcC1WKz8LZgYIDR03JiViZio9GzoPPxcOPwddLygXbkcjHRI3K3VEFCklGi0eJVYDeEATGT8CMhZJHBYiNz8bFHJwJzoLOEpDNAxSPiMQZk5HSVMmLTNBPkV9WW6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39tpa0hHQF1jDhYrfAYeMW4rGW0iHShnAwQtZofn7FMCNiMHFBw7HSIGbHoFNQpYQGZOZofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pEV9WW4+JFxNIwxBPC4RZgEIHQB5Y3c7XyY8GC0CKVoGBRlXKz8GfCwJDhwoJhQEXSo+AGYaIFgUNRsfaiwGKAAVGQcsMXtIVT03B2dgYRRNJwFWOC5DJxcAC1MvLDgDR288HSUPbEJNJBBDL2teZkcEEQEgLzJKSG0kBisLKFQEPAURZmsBKRAJHBIxOgQBTipwSW4kYBkZMRtULz9MNgoUEQcqLDlHVyo+ACsYbARNBEUTZGVNZhhtVV5jFz8NFCw8HSsEOBkAJRpHajkGMhAVFlMiYzkdWS01Bm4DIhk2YEcdexZDMg0GDFMvIjkMR285Gj0DKFxNJAFWaiwRIwAJWAksLTJiGWJwFysEOFwfNQ0TJSVDEkUQEQcrYz8JWCl9AycOOFFNMgZGJC8CNBw0EQkmbGVGPmJ9fmNHbGoZIghHLywafEUVHRInYyMAUW8kFTwNKU1NNgBWJi9DIBcIFVMiMTAbFGcnEW4ePkBNNR9WODJDJQoKFRwtYzkJWSp5WkRHYRkkNklEL2sAJwtADFMlKjkMFCYkWG4MLVUBcAtSKSBDMgpHGVMwNzYcXSxwAi8GOVxNJAFWaj4QIxdHGxItYyMdWip+fiIFL1gBcCRSKSMKKABHRVM4YwQcVTs1VHNKNzNNcEkTKz4XKTYMER8vID8NVyRwSW4MLVUeNUU5amtDZgQSDBwQKD4EWCw4ES0BCFwBMRATd2tTam9HWFNjJTYEWC0xFyU8LVUYNUkOantNc0lHWFNjbnpIWyE8DW4fP1wJcB5bLyVDKApHDBIxJDIcFCk5ESIObFAecABdaioRIRZtWFNjYzMNVjo3JDwDIk1NcEkOai0CKhYCVFNjY3pFFD8iHSAePxkMIg5AaiQNJQBHDxsmLXccWyg3GCsORkQQWmMeZ2stCTEiQlMRLDUEWzdwECEPPxkjHz0TKycPKRJHChYiJz4GU28iEmAlInoBOQxdPgINMAoMHVNrNCUBQCp9GyAGNRBDWkQeahwGZgYGFlQ3YyQJQipwACYPbFYfOQ5aJCoPZg0GFhcvJiVGFAY2VDoCKRkKMQRWbThDEyxHCxY3MHcBQGNwGzsYPxkaOQVfajkGNgkGGxZjKiNiGWJwXC8EKBkbOQpWaj0GNBYGUV1jFDYcVyc0GylKJkweJElBL2YCNhULERYwYzgdRjxwETgPPkBNYEcGOWsULxEPFwY3YzQAUSw7HSANYjMBPwpSJms8LgQJHB8mMRYLQCYmEW5XbF8MPBpWQCcMJQQLWCwvIiQccCoyASk+JVQIcFQTekFpa0hHLAEqJiRIUTk1BjdKL1YAPQZdaiUCKwBHHhwxYyMAUW9yAC8YK1wZcBlcOSIXLwoJWlNsY3ULUSEkETxIbF8ENQVXaiINZgQVHwBtSTsHVy48VCgfIloZOQZdai4bMhcGGwcXIiUPUTt4FTwNPxBncEkTaiIFZhEeCBZrIiUPR2ZwCnNKbk0MMgVWaGsXLgAJWAEmNyIaWm8+HSJKKVcJWkkTamtOa0UjEQEmICNIWjo9ETwDLxkLOQxfLjhpZkVHWBUsMXc3GG87VCcEbFAdMQBBOWMYTEVHWFNjY3dIFjsxBikPOBtBcEtHKzkEIxE3FwAqNz4HWm18VGwaI0oEJABcJGlPZkcEHR03JiVKGG9yFysEOFwfAAZAaGdpZkVHWFNjY3dKUTcgES0eKV1PfEkROi4RIAAEDCMsMD4cXSA+VmJKblEEJDlcOSIXLwoJWl9jYTkNUSs8EWxGRhlNcEkTamtDZB8IFhYAJjkcUT1yWG5IL1AfMwVWCS4NMgAVWl9jYToBUD8/HSAebhVNch9SJj4GZEltWFNjYypBFCs/fm5KbBlNcEkTJiQAJwlHDlN+YzYaUzwLHxNgbBlNcEkTamsKIEUTAQMmayFBFHJtVGwEOVQPNRsRaj8LIwtHChY3NiUGFDlwESAORhlNcElWJC9pZkVHWF5uYwQHWSokHSMPPxkDNRpHLy9DLwsUERcmYzZIFjU/GitIbFYfcEtRJT4NIgQVAVFjNzYKWCpaVG5KbF8CIklsZmsIZgwJWBozIj4aR2crVGwQI1cIckUTaCkMMwsDGQE6YXtIFjw7HSIGL1EIMwIRZmtBNQ4OFB8AKzILX21wCWdKKFZncEkTamtDZkULFxAiL3cbQS1wSW4LPl4eCwJuQGtDZkVHWFNjKjFIQDYgEWYZOVtEcFQOamkXJwcLHVFjNz8NWkVwVG5KbBlNcEkTamsFKRdHJ19jKGVIXSFwHT4LJUseeBITaCgGKBECClFvY3UYWzw5ACcFIhtBcEtHKzkEIxFFVFNhLj4MRCA5GjpIbEREcA1cQGtDZkVHWFNjY3dIFG9wVG4DKhkZKRlWYjgWJD4MSi5qY2pVFG0+ASMIKUtPcB1bLyVDNAATDQEtYyQdVhQ7RhNKKVcJWkkTamtDZkVHWFNjYzIGUEVwVG5KbBlNcAxdLkFDZkVHHR0nSXdIFG8iETofPldNPgBfQC4NIm9tVV5jEyUNQDspWT4YJVcZI0lSaj8CJAkCWAcsYyMAUW8zGyAZI1UIcEFcJC5DKgARHR9jJzINRGZaGCEJLVVNNhxdKT8KKQtHHAYuMxYaUzx4FTwNPxBncEkTaiIFZhEeCBZrIiUPR2ZwCnNKbk0MMgVWaGsXLgAJWAMxKjkcHG0LLXwhbH0MPg1KF2sQLQwLFFMgKzILX28xBikZdhtBcAhBLThKfUUVHQc2MTlIUSE0fm5KbBkdIgBdPmNBHTxVM1MHIjkMTRJwSXNXbEoGOQVfaigLIwYMWBIxJCRICXJtVmdgbBlNcA9cOGsIakURWBotYycJXT0jXC8YK0pEcA1cQGtDZkVHWFNjKjFIQDYgEWYcZRlQbUkRPioBKgBFWAcrJjliFG9wVG5KbBlNcEkTOjkKKBFPWlNjYXtIX2NwVnNKNxtEWkkTamtDZkVHWFNjYzEHRm87RmJKOgtNOQcTOioKNBZPDlpjJzhIRD05GjpCbhlNcEkTamlPZg5VVFNhfnVEFDliXW4PIl1ncEkTamtDZkVHWFNjMyUBWjt4Vm5KMRtEWkkTamtDZkVHHR8wJl1IFG9wVG5KbBlNcElDOCINMk1FWFNhb3cDGG9ySWxGbE9BcEsbaGVNMhwXHVs1anlGFmZyXURKbBlNcEkTai4NIm9HWFNjJjkMPio+EERgIFYOMQUTLD4NJREOFx1jLCIaZyQ5GCIpJFwOOyFSJC8PIxdPCB8iOjIaGG83ESAPPlgZPxsfaioRIRZOclNjY3dFGW8UESwfKxkdIgBdPmtLKQsCVQArLCNIRCoiVDoFK14BNUlHJWsCMAoOHFMwMzYFHUVwVG5KJV9NHQhQIiINI0s0DBI3JnkMUS0lEx4YJVcZcAhdLmtLMgwEE1tqY3pIayMxBzouKVsYNz1aJy5KZltHSVM3KzIGPm9wVG5KbBlNDwVSOT8nIwcSHycqLjJICW8kHS0BZBBncEkTamtDZkUDDR4zAiUPR2cxBikZZTNNcEkTLyUHTG9HWFNjKjFIWiAkVAMLL1EEPgwdGT8CMgBJGQY3LAQDXSM8FyYPL1JNJAFWJEFDZkVHWFNjY3pFFB01ADsYIlADN0ldJT8LLwsAWB4iKDIbFDs4EW4ZKUsbNRsUOWtZDwsRFxgmADsBUSEkVDoCPlYacIuz3msBMxFHDxZjKzYeUW8+G0RKbBlNcEkTamZOZhIGAVM3LHcOWz0nFTwObE0CcB1bL2sMNAwAER0iL3cAVSE0GCsYbBE/PwtfJTNDIAoVGhonMHcaUS40HSANbHYDEwVaLyUXDwsRFxgmanliFG9wVG5KbBlAfUlgJWsKIEUeFwZjNDYGQG8kHCtKPlwKJQVSOGs2D0UFGRAob3ccQT0+VDoCKRkZPw5UJi5DKQMBWBItJ3caUSU/HSBERhlNcEkTamtDNAATDQEtSXdIFG81GipgRhlNcElaLGsuJwYPER0mbQQcVTs1Wi8fOFY+OwBfJigLIwYMPBYvIi5ICm9gVDoCKVdncEkTamtDZkUTGQAobSAJXTt4OS8JJFADNUdgPioXI0sGDQcsEDwBWCMzHCsJJ30IPAhKY0FDZkVHHR0nSV1IFG9wWWNKClAfIx0TPjkafEUVHQc2MTlIQCc1VDoLPl4IJElHIi5DNQAVDhYxYz4cRyo8Em4ZKVcZcBxAQGtDZkULFxAiL3ccVT03ETpKcRkIKB1BKygXEgQVHxY3azYaUzx5fm5KbBkENklHKzkEIxFHDBsmLXcaUTslBiBKOFgfNwxHai4NIm9tWFNjY3pFFAkxGCIILVoGcEFcJCcaZhAUHRdjND8NWm8+G24eLUsKNR0TLCIGKgFHHhw2LTNIXSFwFTwNPxBncEkTajkGMhAVFlMOIjQAXSE1Wh0eLU0Ifg9SJicBJwYMLhIvNjJiUSE0fkQGI1oMPElVPyUAMgwIFlMqLSQcVSM8PC8EKFUIIkEaQGtDZkULFxAiL3caUm9tVBseJVUefhtWOSQPMAA3GQcra3U6UT88HS0LOFwJAx1cOCoEI0siDhYtNyRGZyQ5GCIJJFwOOzxDLioXI0dOclNjY3cBUm8+GzpKPl9NPxsTJCQXZhcBQjowAn9KZio9GzoPCkwDMx1aJSVBb0UTEBYtYyUNQDoiGm4MLVUeNUlWJC9pZkVHWF5uYwA6fRsVWQEkAGBXcAdWPC4RZhcCGRdjMTFGeyETGCcPIk0kPh9cIS5pZkVHWAElbRgGdyM5ESAeBVcbPwJWanZDKRAVKxgqLzsrXCozHwYLIl0BNRs5amtDZjoPGR0nLzIadSwkHTgPbARNJBtGL0FDZkVHChY3NiUGFDsiAStgKVcJWmNfJSgCKkUBDR0gNz4HWm8jAC8YOG4MJApbLiQEbkxtWFNjYz4OFAIxFyYDIlxDDx5SPigLIgoAWAcrJjlIRiokATwEbFwDNGMTamtDCwQEEBotJnk3Qy4kFyYOI15NbUlHKzgIaBYXGQQtazEdWiwkHSEEZBBncEkTamtDZkUQEBovJnclVSw4HSAPYmoZMR1WZCoWMgo0ExovLzQAUSw7VCEYbHQMMwFaJC5NFREGDBZtJzIKQSgABicEOBkJP2MTamtDZkVHWFNjY3dFGW8CEWMdPlAZNUlHIi5DLgQJHB8mMXcYUT05GyoDL1gBPBATIyVDJQQUHVM3KzJIUy49EWkZbGwkcBtWZzgGMkUODF1JY3dIFG9wVG5KbBlNfUQTHS5DJQQJXwdjID8NVyRwAyYFbFYaPhoTIz9DpOXzWAQmYz0dRztwGzgPPk4fOR1WZEFDZkVHWFNjY3dIFG85Gj0eLVUBGAhdLicGNE1OclNjY3dIFG9wVG5KbE0MIwIdPSoKMk1WVkNqSXdIFG9wVG5KKVcJWkkTamtDZkVHNRIgKz4GUWEPAy8eL1EJPw4Td2sNLwltWFNjYzIGUGZaESAORjMLJQdQPiIMKEUqGRArKjkNGjw1AA8fOFY+OwBfJigLIwYMUAVqSXdIFG8dFS0CJVcIfjpHKz8GaAQSDBwQKD4EWCw4ES0BbARNJmMTamtDLwNHDlM3KzIGFCY+BzoLIFUlMQdXJi4RbkxcWAA3IiUcYy4kFyYOI15FeUlWJC9pIwsDcnklNjkLQCY/Gm4nLVoFOQdWZDgGMiECGgYkEyUBWjt4AmdgbBlNcCRSKSMKKABJKwciNzJGUCoyASk6PlADJEkOaj1pZkVHWBolYyFIQCc1Gm4DIkoZMQVfAioNIgkCCltqeHcbQC4iABkLOFoFNAZUYmJDIwsDchYtJ11iGWJwltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjQGZOZlxJWDIWFxhIZAYTPxs6RhRAcIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6HkvLDQJWG8RAToFHFAOOxxDanZDPUU0DBI3JndVFDRwBjsEIlADN0kOai0CKhYCVFMxIjkPUW9tVH9YYBkEPh1WOD0CKkVaWENtdncVFDJaEjsEL00EPwcTCz4XKTUOGxg2M3kbQC4iAGZDRhlNcElaLGsiMxEIKBogKCIYGhwkFToPYksYPgdaJCxDMg0CFlMxJiMdRiFwESAORhlNcElyPz8MFgwEEwYzbQQcVTs1WjwfIlcEPg4Td2sXNBACclNjY3c9QCY8B2AGI1YdeA9GJCgXLwoJUFpjMTIcQT0+VA8fOFY9OQpYPztNFREGDBZtKjkcUT0mFSJKKVcJfGMTamtDZkVHWBU2LTQcXSA+XGdKPlwZJRtdagoWMgo3ERAoNidGZzsxACtEPkwDPgBdLWsGKAFLWBU2LTQcXSA+XGdgbBlNcEkTamtDZkVHFBwgIjtIa2NwHDwabARNBR1aJjhNIAwJHD46FzgHWmd5fm5KbBlNcEkTamtDZgwBWB0sN3cARj9wACYPIhkfNR1GOCVDIwsDclNjY3dIFG9wVG5KbF8CIklsZmsKMgAKWBotYz4YVSYiB2Y4I1YAfg5WPgIXIwgUUFpqYzMHPm9wVG5KbBlNcEkTamtDZkUOHlMWNz4ER2E0HT0eLVcONUFbODtNFgoUEQcqLDlEFCYkESNEPlYCJEdjJTgKMgwIFlpjf2pIdTokGx4DL1IYIEdgPioXI0sVGR0kJnccXCo+fm5KbBlNcEkTamtDZkVHWFNjY3dIGWJwIy8GJxkCJgxBaj8LI0UODBYuYyUJQCc1Bm4eJFgDcA1aOC4AMkUTHR8mMzgaQG8kG24LOlYENElAOi4GIkUBFBIkSXdIFG9wVG5KbBlNcEkTamtDZkVHEAEzbRQuRi49EW5XbHorIgheL2UNIxJPEQcmLnkaWyAkWh4FP1AZOQZdamBDEAAEDBwxcHkGUTh4RGJKfhVNYEAaQGtDZkVHWFNjY3dIFG9wVG5KbBlNAx1SPjhNLxECFQATKjQDUStwSW45OFgZI0daPi4ONTUOGxgmJ3dDFH5aVG5KbBlNcEkTamtDZkVHWFNjY3ccVTw7WjkLJU1FYEcCf2JpZkVHWFNjY3dIFG9wVG5KbFwDNGMTamtDZkVHWFNjY3cNWitaVG5KbBlNcElWJC9KTAAJHHklNjkLQCY/Gm4rOU0CAABQIT4TaBYTFwNrancpQTs/JCcJJ0wdfjpHKz8GaBcSFh0qLTBICW82FSIZKRkIPg05QGZOZofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pEV9WW5bfBdNHSZlDwYmCDFHUAAiJTJIRi4+EysZdxkKMQRWaiMCNUUGWAAmMSENRmIjHSoPbEodNQxXaigLIwYMUXlubneKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2alnPAZQKydDCwoRHR4mLSNICW8rVB0eLU0IcFQTMUFDZkVHDxIvKAQYUSo0VHNKfQxBcANGJzszKRICClN+Y2JYGG85GiggOVQdcFQTLCoPNQBLWB0sIDsBRG9tVCgLIEoIfGMTamtDIAkeWE5jJTYERyp8VCgGNWodNQxXanZDc1VLWBItNz4pcgRwSW4ePkwIfElAKz0GIjUIC1N+YzkBWGNaVG5KbFsUIAhAORgTIwADOxIzY2pIUi48BytGbBRAcABVaj4QIxdHDxItNyRIXCY3HCsYbE0FMQcTGQolAzoqOSscEActcQtaCWJKE1oCPgcTd2sYO0UacnkvLDQJWG82ASAJOFACPklSOjsPPy0SFRItLD4MHGZaVG5KbFUCMwhfahRPZjpLWBs2LndVFBokHSIZYl8EPg1+Mx8MKQtPUUhjKjFIWiAkVCYfIRkZOAxdajkGMhAVFlMmLTNiFG9wVCYfIRc6MQVYGTsGIwFHRVMOLCENWSo+AGA5OFgZNUdEKycIFRUCHRdJY3dIFD8zFSIGZF8YPgpHIyQNbkxHEAYubR0dWT8AGzkPPhlQcCRcPC4OIwsTViA3IiMNGiUlGT46I04IIklWJC9KTEVHWFMzIDYEWGc2ASAJOFACPkEaaiMWK0syCxYJNjoYZCAnETxKcRkZIhxWai4NIkxtHR0nSTEdWiwkHSEEbHQCJgxeLyUXaBYCDCQiLzw7RCo1EGYcZTNNcEkTPGteZhEIFgYuITIaHDl5VCEYbAhYWkkTamsKIEUJFwdjDjgeUSI1GjpEH00MJAwdKDITJxYUKwMmJjMrVT9wFSAObE9NbklwJSUFLwJJKzIFBggldRcPJx4vCX1NJAFWJGsVZlhHOxwtJT4PGhwRMgs1AXg1DzpjDw4nZgAJHHljY3dIeSAmESMPIk1DAx1SPi5NMQQLEyAzJjIMFHJwAkRKbBlNMRlDJjIrMwgGFhwqJ39BPio+EEQMOVcOJABcJGsuKRMCFRYtN3kbUTsaASMaHFYaNRsbPGJDCwoRHR4mLSNGZzsxACtEJkwAIDlcPS4RZlhHDBwtNjoKUT14AmdKI0tNZVkIaioTNgkeMAYuIjkHXSt4XW4PIl1nNhxdKT8KKQtHNRw1JjoNWjt+ByseBVcLGhxeOmMVb29HWFNjDjgeUSI1GjpEH00MJAwdIyUFDBAKCFN+YyFiFG9wVCcMbE9NMQdXaiUMMkUqFwUmLjIGQGEPFyEEIhcEPg95PyYTZhEPHR1JY3dIFG9wVG4nI08IPQxdPmU8JQoJFl0qLTEiQSIgVHNKGUoIIiBdOj4XFQAVDhogJnkiQSIgJisbOVweJFNwJSUNIwYTUBU2LTQcXSA+XGdgbBlNcEkTamtDZkVHERVjLTgcFAI/AisHKVcZfjpHKz8GaAwJHjk2LidIQCc1Gm4YKU0YIgcTLyUHTEVHWFNjY3dIFG9wVCIFL1gBcDYfahRPZg0SFVN+YwIcXSMjWigDIl0gKT1cJSVLb29HWFNjY3dIFG9wVG4DKhkFJQQTPiMGKEUPDR55AD8JWig1JzoLOFxFFQdGJ2UrMwgGFhwqJwQcVTs1IDcaKRcnJQRDIyUEb0UCFhdJY3dIFG9wVG4PIl1EWkkTamsGKhYCERVjLTgcFDlwFSAObHQCJgxeLyUXaDoEFx0tbT4GUgUlGT5KOFEIPmMTamtDZkVHWD4sNTIFUSEkWhEJI1cDfgBdLAEWKxVdPBowIDgGWiozAGZDdxkgPx9WJy4NMks4GxwtLXkBWikaASMabARNPgBfQGtDZkUCFhdJJjkMPiklGi0eJVYDcCRcPC4OIwsTVgAmNxkHVyM5BGYcZTNNcEkTByQVIwgCFgdtECMJQCp+GiEJIFAdcFQTPEFDZkVHERVjNXcJWitwGiEebHQCJgxeLyUXaDoEFx0tbTkHVyM5BG4eJFwDWkkTamtDZkVHNRw1JjoNWjt+Ky0FIldDPgZQJiITZlhHKgYtEDIaQiYzEWA5OFwdIAxXcAgMKAsCGwdrJSIGVzs5GyBCZTNNcEkTamtDZkVHWFMqJXcGWztwOSEcKVQIPh0dGT8CMgBJFhwgLz4YFDs4ESBKPlwZJRtdai4NIm9HWFNjY3dIFG9wVG4GI1oMPElQIioRZlhHNBwgIjs4WC4pETxED1EMIghQPi4RfUUOHlMtLCNIVycxBm4eJFwDcBtWPj4RKEUCFhdJY3dIFG9wVG5KbBlNNgZBahRPZhVHER1jKicJXT0jXC0CLUtXFwxHDi4QJQAJHBItNyRAHWZwECFgbBlNcEkTamtDZkVHWFNjYz4OFD9qPT0rZBsvMRpWGioRMkdOWBItJ3cYGgwxGg0FIFUENAwTPiMGKEUXVjAiLRQHWCM5ECtKcRkLMQVAL2sGKAFtWFNjY3dIFG9wVG5KKVcJWkkTamtDZkVHHR0nal1IFG9wESIZKVALcAdcPmsVZgQJHFMOLCENWSo+AGA1L1YDPkddJSgPLxVHDBsmLV1IFG9wVG5KbHQCJgxeLyUXaDoEFx0tbTkHVyM5BHQuJUoOPwddLygXbkxcWD4sNTIFUSEkWhEJI1cDfgdcKScKNkVaWB0qL11IFG9wESAORlwDNGNfJSgCKkUBDR0gNz4HWm8jAC8YOH8BKUEaQGtDZkULFxAiL3c3GG84Bj5GbFEYPUkOah4XLwkUVhUqLTMlTRs/GyBCZQJNOQ8TJCQXZg0VCFMsMXcGWztwHDsHbE0FNQcTOC4XMxcJWBYtJ11IFG9wGCEJLVVNMh8Td2sqKBYTGR0gJnkGUTh4VgwFKEA7NQVcKSIXP0dOQ1MhNXklVTcWGzwJKRlQcD9WKT8MNFZJFhY0a2YNDWNhEXdGfVxUeVITKD1NEAALFxAqNy5ICW8GES0eI0tefgdWPWNKfUUFDl0TIiUNWjtwSW4CPklncEkTaicMJQQLWBEkY2pIfSEjAC8EL1xDPgxEYmkhKQEePwoxLHVBD28yE2AnLUE5PxtCPy5De0UxHRA3LCVbGiE1A2ZbKQBBYQwKZnoGf0xcWBEkbQdICW9hEXpRbFsKfjlSOC4NMkVaWBsxM11IFG9wOSEcKVQIPh0dFSgMKAtJHh86AQFEFAI/AisHKVcZfjZQJSUNaAMLATEEY2pIVjl8VCwNRhlNcElbPyZNFgkGDBUsMTo7QC4+EG5XbE0fJQw5amtDZigIDhYuJjkcGhAzGyAEYl8BKTxDLioXI0VaWCE2LQQNRjk5FytEHlwDNAxBGT8GNhUCHEkALDkGUSwkXCgfIloZOQZdYmJpZkVHWFNjY3cBUm8+GzpKAVYbNQRWJD9NFREGDBZtJTsRFDs4ESBKPlwZJRtdai4NIm9HWFNjY3dIFCM/Fy8GbFoMPUkOajwMNA4UCBIgJnkrQT0iESAeD1gANRtSQGtDZkVHWFNjLzgLVSNwGW5XbG8IMx1cOHhNKAAQUFpJY3dIFG9wVG4DKhk4IwxBAyUTMxE0HQE1KjQNDgYjPysTCFYaPkF2JD4OaC4CATAsJzJGY2ZwVG5KbBlNcElHIi4NZghHRVMuY3xIVy49Wg0sPlgANUd/JSQIEAAEDBwxYzIGUEVwVG5KbBlNcABVah4QIxcuFgM2NwQNRjk5FytQBUomNRB3JTwNbiAJDR5tCDIRdyA0EWA5ZRlNcEkTamtDZhEPHR1jLndVFCJwWW4JLVRDEy9BKyYGaCkIFxgVJjQcWz1wESAORhlNcEkTamtDLwNHLQAmMR4GRDokJysYOlAONVN6OQAGPyEIDx1rBjkdWWEbETcpI10IfigaamtDZkVHWFNjNz8NWm89VHNKIRlAcApSJ2UgABcGFRZtET4PXDsGES0eI0tNNQdXQGtDZkVHWFNjKjFIYTw1BgcEPEwZAwxBPCIAI18uCzgmOhMHQyF4MSAfIRcmNRBwJS8GaCFOWFNjY3dIFG9wACYPIhkAcFQTJ2tIZgYGFV0ABSUJWSp+JicNJE07NQpHJTlDIwsDclNjY3dIFG9wHShKGUoIIiBdOj4XFQAVDhogJm0hRwQ1DQoFO1dFFQdGJ2UoIxwkFxcmbQQYVSw1XW5KbBlNJAFWJGsOZlhHFVNoYwENVzs/Bn1EIlwaeFkfanpPZlVOWBYtJ11IFG9wVG5KbFALcDxALzkqKBUSDCAmMSEBVypqPT0hKUApPx5dYg4NMwhJMxY6ADgMUWEcESgeH1EENh0aaj8LIwtHFVN+YzpIGW8GES0eI0tefgdWPWNTakVWVFNzancNWitaVG5KbBlNcElaLGsOaCgGHx0qNyIMUW9uVH5KOFEIPkleanZDK0syFho3Y31IeSAmESMPIk1DAx1SPi5NIAkeKwMmJjNIUSE0fm5KbBlNcEkTKD1NEAALFxAqNy5ICW89fm5KbBlNcEkTKCxNBSMVGR4mY2pIVy49Wg0sPlgANWMTamtDIwsDUXkmLTNiWCAzFSJKKkwDMx1aJSVDNREICDUvOn9BPm9wVG4MI0tND0UTIWsKKEUOCBIqMSRAT202GDc/PF0MJAwRZmkFKhwlLlFvYTEETQ0XVjNDbF0CWkkTamtDZkVHFBwgIjtIV29tVAMFOlwANQdHZBQAKQsJIxgeSXdIFG9wVG5KJV9NM0lHIi4NTEVHWFNjY3dIFG9wVCcMbE0UIAxcLGMAb0VaRVNhERUwZywiHT4eD1YDPgxQPiIMKEdHDBsmLXcLDgs5By0FIlcIMx0bY2sGKhYCWBB5BzIbQD0/DWZDbFwDNGMTamtDZkVHWFNjY3clWzk1GSsEOBcyMwZdJBAIG0VaWB0qL11IFG9wVG5KbFwDNGMTamtDIwsDclNjY3cEWywxGG41YBkyfElbPyZDe0UyDBovMHkOXSE0OTc+I1YDeEA5amtDZgwBWBs2LnccXCo+VCYfIRc9PAhHLCQRKzYTGR0nY2pIUi48BytKKVcJWgxdLkEFMwsEDBosLXclWzk1GSsEOBceNR11JjJLMExHNRw1JjoNWjt+JzoLOFxDNgVKanZDMF5HERVjNXccXCo+VD0eLUsZFgVKYmJDIwkUHVMwNzgYciMpXGdKKVcJcAxdLkEFMwsEDBosLXclWzk1GSsEOBceNR11JjIwNgACHFs1anclWzk1GSsEOBc+JAhHL2UFKhw0CBYmJ3dVFDs/GjsHLlwfeB8aaiQRZlBXWBYtJ10OQSEzACcFIhkgPx9WJy4NMksUHQcCLSMBdQkbXDhDRhlNcEl+JT0GKwAJDF0QNzYcUWExGjoDDX8mcFQTPEFDZkVHERVjNXcJWitwGiEebHQCJgxeLyUXaDoEFx0tbTYGQCYRMgVKOFEIPmMTamtDZkVHWD4sNTIFUSEkWhEJI1cDfghdPiIiAC5HRVMPLDQJWB88FTcPPhckNAVWLnEgKQsJHRA3azEdWiwkHSEEZBBncEkTamtDZkVHWFNjKjFIWiAkVAMFOlwANQdHZBgXJxECVhItNz4pcgRwACYPIhkfNR1GOCVDIwsDclNjY3dIFG9wVG5KbEkOMQVfYi0WKAYTERwta35IYiYiADsLIGweNRsJCSoTMhAVHTAsLSMaWyM8ETxCZQJNBgBBPj4CKjAUHQF5ADsBVyQSAToeI1dfeD9WKT8MNFdJFhY0a35BFCo+EGdgbBlNcEkTamsGKAFOclNjY3cNWDw1HShKIlYZcB8TKyUHZigIDhYuJjkcGhAzGyAEYlgDJAByDABDMg0CFnljY3dIFG9wVAMFOlwANQdHZBQAKQsJVhItNz4pcgRqMCcZL1YDPgxQPmNKfUUqFwUmLjIGQGEPFyEEIhcMPh1aCw0oZlhHFhovSXdIFG81GipgKVcJWg9GJCgXLwoJWD4sNTIFUSEkWj0LOlw9PxobY0FDZkVHFBwgIjtIa2NwHDwabARNBR1aJjhNIAwJHD46FzgHWmd5T24DKhkFIhkTPiMGKEUqFwUmLjIGQGEDAC8eKRceMR9WLhsMNUVaWBsxM3k4Wzw5ACcFIgJNIgxHPzkNZhEVDRZjJjkMPio+EEQMOVcOJABcJGsuKRMCFRYtN3kaUSwxGCI6I0pFeWMTamtDLwNHNRw1JjoNWjt+JzoLOFxDIwhFLy8zKRZHDBsmLXc9QCY8B2AeKVUIIAZBPmMuKRMCFRYtN3k7QC4kEWAZLU8INDlcOWJYZhcCDAYxLXccRjo1VCsEKDMIPg05BiQAJwk3FBI6JiVGdycxBi8JOFwfEQ1XLy9ZBQoJFhYgN38OQSEzACcFIhFEWkkTamsXJxYMVgQiKiNABGFmXXVKLUkdPBB7PyYCKAoOHFtqSXdIFG85Em4nI08IPQxdPmUwMgQTHV0lLy5IQCc1Gm4ZOFgfJC9fM2NKZgAJHHkmLTNBPkV9WW6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39uB0/WF7eOh1seKod+y4d6I2amPxfnR39tpa0hHSUJtYwEhZxoROB1gYRRNsvyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3ch8sIDYEFBk5BzsLIEpNbUlIahgXJxECWE5jOHcOQSM8FjwDK1EZcFQTLCoPNQBLWB0sBTgPFHJwEi8GP1xNLUUTFSkCJQ4SCFN+YywVFDJaGCEJLVVNNhxdKT8KKQtHGhIgKCIYeCY3HDoDIl5FeWMTamtDLwNHFhY7N38+XTwlFSIZYmYPMQpYPztKZhEPHR1jMTIcQT0+VCsEKDNNcEkTHCIQMwQLC10cITYLXzogWgwYJV4FJAdWOThDZkVHRVMPKjAAQCY+E2AoPlAKOB1dLzgQTEVHWFMVKiQdVSMjWhEILVoGJRkdCScMJQ4zER4mY3dIFG9tVAIDK1EZOQdUZAgPKQYMLBouJl1IFG9wIicZOVgBI0dsKCoALRAXVjQvLDUJWBw4FSoFO0pNbUl/IywLMgwJH10ELzgKVSMDHC8OI04eWkkTams1LxYSGR8wbQgKVSw7AT5EClYKFQdXamtDZkVHWFN+YxsBUyckHSANYn8CNyxdLkFDZkVHLhowNjYER2EPFi8JJ0wdfi9cLRgXJxcTWFNjY3dICW8cHSkCOFADN0d1JSwwMgQVDHkmLTNiUjo+FzoDI1dNBgBAPyoPNUsUHQcFNjsEVj05EyYeZE9EWkkTams1LxYSGR8wbQQcVTs1WigfIFUPIgBUIj9De0URQ1MhIjQDQT8cHSkCOFADN0EaQGtDZkUOHlM1YyMAUSFwOCcNJE0EPg4dCDkKIQ0TFhYwMHdVFHxrVAIDK1EZOQdUZAgPKQYMLBouJndVFH5kT24mJV4FJABdLWUkKgoFGR8QKzYMWzgjVHNKKlgBIww5amtDZgALCxZJY3dIFG9wVG4mJV4FJABdLWUhNAwAEActJiQbFHJwIicZOVgBI0dsKCoALRAXVjExKjAAQCE1Bz1KI0tNYWMTamtDZkVHWD8qJD8cXSE3Wg0GI1oGBABeL2tDe0UxEQA2IjsbGhAyFS0BOUlDEwVcKSA3LwgCWBwxY2ZcPm9wVG5KbBlNHABUIj8KKAJJPx8sITYEZycxECEdPxlQcD9aOT4CKhZJJxEiIDwdRGEXGCEILVU+OAhXJTwQZhtaWBUiLyQNPm9wVG4PIl1nNQdXQC0WKAYTERwtYwEBRzoxGD1EP1wZHgZ1JSxLMExtWFNjYwEBRzoxGD1EH00MJAwdJCQlKQJHRVM1eHcKVSw7AT4mJV4FJABdLWNKTEVHWFMqJXceFDs4ESBKAFAKOB1aJCxNAAoAPR0nY2pIBSpmT24mJV4FJABdLWUlKQI0DBIxN3dVFH41QkRKbBlNNQVAL2svLwIPDBotJHkuWygVGipKcRk7ORpGKycQaDoFGRAoNidGciA3MSAObFYfcFgDentYZikOHxs3KjkPGgk/Ex0eLUsZcFQTHCIQMwQLC10cITYLXzogWggFK2oZMRtHaiQRZlVHHR0nSTIGUEVaWWNKrqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zpPD3mubTocL41trAltv6rqz9svyjqN7zTEhKWEJxbXc9fW+y9NpKIFYMNEl8KDgKIgwGFiYqY38xBgR5VC8EKBkPJQBfLmsXLgBHDxotJzgfPmJ9VKz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2qn21ofy6JHW07X9pK3F5Kz/3Nv4wIum2kETNAwJDFtrYQwxBgQNVAIFLV0EPg4TBSkQLwEOGR0WKncOWz1wUT1KYhdDckAJLCQRKwQTUDAsLTEBU2EXNQMvE3csHSwaY0FpKgoEGR9jDz4KRi4iDWJKGFEIPQx+KyUCIQAVVFMQIiENeS4+FSkPPjMBPwpSJmsMLTAuWE5jMzQJWCN4EjsEL00EPwcbY0FDZkVHNBohMTYaTW9wVG5KbARNPAZSLjgXNAwJH1skIjoNDgckAD4tKU1FEwZdLCIEaDAuJyEGExhIGmFwVgIDLksMIhAdJj4CZExOUFpJY3dIFBs4ESMPAVgDMQ5WOGteZgkIGRcwNyUBWih4Ey8HKQMlJB1DDS4XbiYIFhUqJHk9fRACMR4lbBdDcEtSLi8MKBZILBsmLjIlVSExEysYYlUYMUsaY2NKTEVHWFMQIiENeS4+FSkPPhlNbUlfJSoHNREVER0kazAJWSpqPDoePH4IJEFwJSUFLwJJLTocERI4e29+Wm5ILV0JPwdAZRgCMAAqGR0iJDIaGiMlFWxDZRFEWgxdLmJpLwNHFhw3YzgDYQZwGzxKIlYZcCVaKDkCNBxHDBsmLV1IFG9wAy8YIhFPCzABAWsrMwc6WDUiKjsNUG8kG24GI1gJcCZROSIHLwQJLRptYxYKWz0kHSANYhtEWkkTams8AUs+SjgcBxYmcBYPPBsoE3UiES12DmteZgsOFEhjMTIcQT0+fisEKDNnPAZQKydDCRUTERwtMHtIYCA3EyIPPxlQcCVaKDkCNBxJNwM3KjgGR2NwOCcIPlgfKUdnJSwEKgAUcj8qISUJRjZ+MiEYL1wuOAxQISkMPkVaWBUiLyQNPkU8Gy0LIBkLJQdQPiIMKEUpFwcqJS5AQCYkGCtGbF0IIwofai4RNExtWFNjYxsBVj0xBjdQAlYZOQ9KYjBpZkVHWFNjY3c8XTs8EW5KbBlNcEkOai4RNEUGFhdja3UtRj0/Bm6IzJtNckkdZGsXLxELHVpjLCVIQCYkGCtGRhlNcEkTamtDAgAUGwEqMyMBWyFwSW4OKUoOcAZBamlBam9HWFNjY3dIFBs5GStKbBlNcEkTanZDckltWFNjYypBPio+EERgIFYOMQUTHSINIgoQWE5jDz4KRi4iDXQpPlwMJAxkIyUHKRJPA3ljY3dIYCYkGCtKbBlNcEkTamtDZkVaWFEHIjkMTWgjVBkFPlUJcEnRyulDZjxVM1MLNjVIFDlyVGBEbHoCPg9aLWUwBTcuKCccFRI6GEVwVG5KClYCJAxBamtDZkVHWFNjY3dVFG0JRgVKH1ofORlHagkCJQ5VOhIgKHdI1s/yVG5IbBdDcCpcJC0KIUsgOT4GHBkpeQp8fm5KbBkjPx1aLDIwLwECWFNjY3dIFHJwVhwDK1EZckU5amtDZjYPFwQANiQcWyITATwZI0tNbUlHOD4Gam9HWFNjADIGQCoiVG5KbBlNcEkTamteZhEVDRZvSXdIFG8RAToFH1ECJ0kTamtDZkVHWE5jNyUdUWNaVG5KbGsIIwBJKykPI0VHWFNjY3dICW8kBjsPYDNNcEkTCSQRKAAVKhInKiIbFG9wVG5XbAhdfGNOY0FpKgoEGR9jFzYKR29tVDVgbBlNcDpGOD0KMAQLWE5jFD4GUCAnTg8OKG0MMkERGT4RMAwRGR9hb3dIFjw4HSsGKBtEfGMTamtDCwQEEBotJiRICW8HHSAOI05XEQ1XHioBbkcqGRArKjkNR218VG5IO0sIPgpbaGJPTEVHWFMKNzIFR29wVG5XbG4EPg1cPXEiIgEzGRFrYR4cUSIjVmJKbBlNcEtDKygIJwICWlpvSXdIFG8AGC8TKUtNcEkOahwKKAEID0kCJzM8VS14Vh4GLUAIIksfamtDZkcSCxYxYX5EPm9wVG4nJUoOcEkTamteZjIOFhcsNG0pUCsEFSxCbnQEIwoRZmtDZkVHWFEqLTEHFmZ8fm5KbBkuPwdVIywQZkVaWCQqLTMHQ3URECo+LVtFcipcJC0KIRZFVFNjY3UMVTsxFi8ZKRtEfGMTamtDFQATDBotJCRICW8HHSAOI05XEQ1XHioBbkc0HQc3KjkPR218VG5IP1wZJABdLThBb0ltWFNjYxQaUSs5AD1KbARNBwBdLiQUfCQDHCciIX9Kdz01ECcePxtBcEkTaCMGJxcTWlpvSSpiPmJ9VKz+zNv50Iunyms3BydHSVOhw8NIZxoCIgc8DXVNsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQfiIFL1gBcDpGOB8BPilHRVMXIjUbGhwlBjgDOlgBaihXLgcGIBEzGREhLC9AHUU8Gy0LIBk+JRtnPSIQMgADWE5jECIaYC0oOHQrKF05MQsbaB8ULxYTHRdjBgQ4FmZaGCEJLVVNAxxBBCQXLwMeWFN+YwQdRhsyDAJQDV0JBAhRYmktKREOHhomMXVBPkUDATw+O1AeJAxXcAoHIikGGhYvayxIYCooAG5XbBslOQ5bJiIELhEUWBY1JiURFBsnHT0eKV1NBAZcJGsKKEUTEBZjICIaRio+AG4YI1YAcB5aPiNDKAQKHVNoYzMBRzsxGi0PYhtBcC1cLzg0NAQXWE5jNyUdUW8tXUQ5OUs5JwBAPi4HfCQDHDcqNT4MUT14XUQ5OUs5JwBAPi4HfCQDHCcsJDAEUWdyMR06GE4EIx1WLmlPZh5HLBY7N3dVFG0EAycZOFwJcCxgGmlPZiECHhI2LyNICW82FSIZKRVNEwhfJikCJQ5HRVMGEAdGRyokIDkDP00INElOY0EwMxczDxowNzIMDg40EBoFK14BNUERDxgzEhIOCwcmJxMBRztyWG4RbG0IKB0Td2tBFQ0ID1MnKiQcVSEzEWxGbH0INghGJj9De0UTCgYmb11IFG9wNy8GIFsMMwITd2sFMwsEDBosLX8eHW8VJx5EH00MJAwdPjwKNRECHDcqMCMJWiw1VHNKOhkIPg0TN2JpFRAVLAQqMCMNUHURECo+I14KPAwbaA4wFjYPFwQMLTsRdyM/BytIYBkWcD1WMj9De0VFMBonJncBUm8kGyFKKlgfckUTDi4FJxALDFN+YzEJWDw1WERKbBlNBAZcJj8KNkVaWFEMLTsRFD01GioPPhkoAzkTLCQRZgAJDBo3KjIbFDg5ACYDIhkuPAZAL2sxJwsAHV1hb11IFG9wNy8GIFsMMwITd2sFMwsEDBosLX8eHW8VJx5EH00MJAwdOSMMMSoJFAoALzgbUW9tVDhKKVcJcBQaQBgWNDEQEQA3JjNSdSs0JyIDKFwfeEt2GRsgKgoUHSEiLTANFmNwD24+KUEZcFQTaAgPKRYCWAEiLTANFmNwMCsMLUwBJEkOan1TakUqER1jfndaBGNwOS8SbARNYlkDZmsxKRAJHBotJHdVFH98VB0fKl8EKEkOamlDNRFFVHljY3dIdy48GCwLL1JNbUlVPyUAMgwIFls1anctZx9+JzoLOFxDMwVcOS4xJwsAHVN+YyFIUSE0VDNDRmoYIj1EIzgXIwFdORcnDzYKUSN4VhodJUoZNQ0TKSQPKRdFUUkCJzMrWyM/Bh4DL1IIIkERDxgzEhIOCwcmJxQHWCAiVmJKNzNNcEkTDi4FJxALDFN+YxI7ZGEDAC8eKRcZJwBAPi4HBQoLFwFvYwMBQCM1VHNKbm0aORpHLy9DAzY3WBAsLzgaFmNaVG5KbHoMPAVRKygIZlhHHgYtICMBWyF4F2dKCWo9fjpHKz8GaBEQEQA3JjMrWyM/Bm5XbFpNNQdXajZKTG80DQENLCMBUjZqNSoOAFgPNQUbMWs3Ix0TWE5jYQcHRDxwFW4YKV1NMghdJC4RZgsCGQFjNz8NFDs/BG4FKhkUPxxBajgANAACFlM0KzIGFC5wIDkDP00INElWJD8GNBZHCAEsOz4FXTspWmxGbH0CNRpkOCoTZlhHDAE2JncVHUUDATwkI00ENhAJCy8HAgwRERcmMX9BPhwlBgAFOFALKVNyLi83KQIAFBZrYRkHQCY2HSsYbhVNK0lnLzMXZlhHWic0KiQcUStwJDwFNFAAOR1KagUMMgwBERYxYXtIcCo2FTsGOBlQcA9SJjgGakUkGR8vITYLX29tVB0fPk8EJghfZDgGMisIDBolKjIaFDJ5fh0fPncCJABVM3EiIgE0FBonJiVAFgE/ACcMJVwfAghdLS5BakUcWCcmOyNICW9yIDwDK14IIklBKyUEI0dLWDcmJTYdWDtwSW5ZeRVNHQBdanZDd1VLWD4iO3dVFH5iRGJKHlYYPg1aJCxDe0VXVFMQNjEOXTdwSW5IbEoZckU5amtDZiYGFB8hIjQDFHJwEjsEL00EPwcbPGJDFRAVDho1IjtGZzsxACtEIlYZOQ9aLzkxJwsAHVN+YyFIUSE0VDNDRjMBPwpSJmswMxczGgsRY2pIYC4yB2A5OUsbOR9SJnEiIgE1ERQrNwMJVi0/DGZDRlUCMwhfahgWNCQJDBoEMTYKFHJwJzsYGFsVAlNyLi83JwdPWjItNz5Fcz0xFmxDRlUCMwhfahgWNCYIHBYwY3dIFHJwJzsYGFsVAlNyLi83JwdPWjAsJzIbFmZafh0fPngDJAB0OCoBfCQDHD8iITIEHDRwICsSOBlQcEtyPz8MKwQTERAiLzsRFDwhAScYIRQOMQdQLycQZhIPHR1jInc8QyYjACsObF4fMQtAajIMM0tHKwYxNT4eVSNwGCcMKUoMJgxBZGlPZiEIHQAUMTYYFHJwADwfKRkQeWNgPzkiKBEOPwEiIW0pUCsUHTgDKFwfeEA5GT4RBwsTETQxIjVSdSs0ICENK1UIeEtyJD8KARcGGlFvYyxIYCooAG5XbBssJR1cahgSMwwVFV4AIjkLUSNwGyBKK0sMMksfag8GIAQSFAdjfncOVSMjEWJgbBlNcD1cJScXLxVHRVNhBT4aUTxwACYPbGocJQBBJwoBLwkODAoAIjkLUSNwBisHI00IcB1bL2sOKQgCFgdjOjgdFCg1AG4NPlgPMgxXZGlPTEVHWFMAIjsEVi4zH25XbGoYIh9aPCoPaBYCDDItNz4vRi4yVDNDRjM+JRtwJS8GNV8mHBcPIjUNWGcrVBoPNE1NbUkRGC4HIwAKWBotbjAJWSpwFyEOKUpDcCtGIycXawwJWB8qMCNIRio2BisZJFwecAZQKSoQLwoJGR8vOnlKGG8UGysZG0sMIEkOaj8RMwBHBVpJECIadyA0ET1QDV0JFABFIy8GNE1OciA2MRQHUCojTg8OKHsYJB1cJGMYZjECAAdjfndKZio0ESsHbHghHElRPyIPMkgOFlMgLDMNR218VAgfIlpNbUlVPyUAMgwIFltqSXdIFG82GzxKExVNMwZXL2sKKEUOCBIqMSRAdyA+EicNYnoiFCxgY2sHKW9HWFNjY3dIFB01GSEeKUpDOQdFJSAGbkckFxcmBiENWjtyWG4JI10IeWMTamtDZkVHWAciMDxGQy45AGZaYg1EWkkTamsGKAFtWFNjYxkHQCY2DWZID1YJNRoRZmtBEhcOHRdjYXdGGm9zNyEEKlAKfip8Dg4wZktJWFFjIDgMUTx+VmdgKVcJcBQaQBgWNCYIHBYweRYMUAY+BDseZBsuJRpHJSYgKQECWl9jOHc8UTckVHNKbnoYIx1cJ2sAKQECWl9jBzIOVTo8AG5XbBtPfEljJioAIw0IFBcmMXdVFG0zGyoPbFEIIgwRZmsgJwkLGhIgKHdVFCklGi0eJVYDeEATLyUHZhhOciA2MRQHUCojTg8OKHsYJB1cJGMYZjECAAdjfndKZio0ESsHbFoYIx1cJ2sAKQECWl9jBSIGV29tVCgfIloZOQZdYmJpZkVHWB8sIDYEFCw/ECtKcRkiIB1aJSUQaCYSCwcsLhQHUCpwFSAObHYdJABcJDhNBRAUDBwuADgMUWEGFSIfKRkCIkkRaEFDZkVHERVjIDgMUW9tSW5IbhkZOAxdagUMMgwBAVthADgMUW18VGwvIUkZKUsfaj8RMwBOQ1MxJiMdRiFwESAORhlNcElhLyYMMgAUVhotNTgDUWdyNyEOKXwbNQdHaGdDJQoDHVp4YxkHQCY2DWZID1YJNUsfamk3NAwCHEljYXdGGm8zGyoPZTMIPg0TN2JpTEhKWJHXw7X8tK3E9G4+DXtNYknRyt9DCyQkMDoNBgRI1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnch8sIDYEFAIxFyYmbARNBAhROWUuJwYPER0mMG0pUCscESgeC0sCJRlRJTNLZCgGGxsqLTJIcRwAVmJKbk4fNQdQImlKTCgGGxsPeRYMUAMxFisGZEJNBAxLPmteZkcvERQrLz4PXDsjVCscKUsUcARSKSMKKABHDxo3K3cBQDxwFyEHPFUIJABcJGtGaEdLWDcsJiQ/Ri4gVHNKOEsYNUlOY0EuJwYPNEkCJzMsXTk5ECsYZBBnHQhQIgdZBwEDLBwkJDsNHG0VJx4nLVoFOQdWaGdDPUUzHQs3Y2pIFgIxFyYDIlxNFTpjaGdDAgABGQYvN3dVFCkxGD0PYBkuMQVfKCoALUVaWDYQE3kbUTsdFS0CJVcIcBQaQAYCJQ0rQjInJxsJVio8XGwnLVoFOQdWaigMKgoVWlp5AjMMdyA8Gzw6JVoGNRsbaA4wFigGGxsqLTIrWyM/BmxGbEJncEkTag8GIAQSFAdjfnctZx9+JzoLOFxDPQhQIiINIyYIFBwxb3c8XTs8EW5XbBsgMQpbIyUGZiA0KFMgLDsHRm18fm5KbBkuMQVfKCoALUVaWBU2LTQcXSA+XC1DbHw+AEdgPioXI0sKGRArKjkNdyA8GzxKcRkOcAxdLmseb29tFBwgIjtIeS4zHBxKcRk5MQtAZAYCJQ0OFhYweRYMUB05EyYeC0sCJRlRJTNLZCQSDBxjMDwBWCNwFyYPL1JPfEkRIS4aZExtNRIgKwVSdSs0OC8IKVVFK0lnLzMXZlhHWiEmIjMbFDs4EW4ZKUsbNRsUOWsXJxcAHQdjJSUHWW8kHCtKP1IEPAUeKSMGJQ5HGQEkMHcJWitwBiseOUsDI0laPmVDEQQTGxsnLDBIRip9HSAZOFgBPBoTIy1DMg0CWBQiLjJIRiojEToZbFAZfksfag8MIxYwChIzY2pIQD0lEW4XZTMgMQpbGHEiIgEjEQUqJzIaHGZaOS8JJGtXEQ1XHiQEIQkCUFECNiMHZyQ5GCIpJFwOO0sfajBDEgAfDFN+Y3UpQTs/VB0BJVUBcCpbLygIZElHPBYlIiIEQG9tVCgLIEoIfGMTamtDEgoIFAcqM3dVFG0RAToFYUkMIxpWOWsALxcEFBZjIjkMFDsiES8OIVABPElAISIPKkUEEBYgKCRIVjZwBiseOUsDOQdUaj8LI0UUHQE1JiVPR28/AyBKOFgfNwxHaj0CKhACVlFvSXdIFG8TFSIGLlgOO0kOagYCJQ0OFhZtMDIcdTokGx0BJVUBMwFWKSBDO0xtNRIgKwVSdSs0JyIDKFwfeEt1KycPJAQEEyUiLyINFmNwD24+KUEZcFQTaA0CKgkFGRAoYyEJWDo1VGYDKhkDP0lHKzkEIxFHER1jIiUPR2ZyWG4uKV8MJQVHanZDdktSVFMOKjlICW9gWn5GbHQMKEkOanpNdklHKhw2LTMBWihwSW5YYDNNcEkTHiQMKhEOCFN+Y3UnWiMpVDsZKV1NOQ8TPS5DJQQJXwdjIiIcW2I0EToPL01NJAFWaj8CNAICDF1jFyURFH9+R25FbAlDZUkcantNcUUOHlMqN3cFXTwjET1EbhVncEkTaggCKgkFGRAoY2pIUjo+FzoDI1dFJkATByoALgwJHV0QNzYcUWE2FSIGLlgOOz9SJj4GZlhHDlMmLTNISWZaOS8JJGtXEQ1XGScKIgAVUFEQKD4EWAw4ES0BCFwBMRARZmsYZjECAAdjfndKZiojBCEEP1xNNAxfKzJBakUjHRUiNjscFHJwRGJKAVADcFQTemVTakUqGQtjfndZGnp8VBwFOVcJOQdUanZDdElHKwYlJT4QFHJwVm4ZbhVncEkTah8MKQkTEQNjfndKZC4lBytKLlwLPxtWaioNNRICChotJHlIBG9tVCcEP00MPh0daGdpZkVHWDAiLzsKVSw7VHNKKkwDMx1aJSVLMExHNRIgKz4GUWEDAC8eKRcMJR1cGSAKKgkEEBYgKBMNWC4pVHNKOhkIPg0TN2JpCwQEECF5AjMMcCYmHSoPPhFEWiRSKSMxfCQDHCcsJDAEUWdyMCsIOV4+OwBfJggLIwYMWl9jOHc8UTckVHNKbsnywPITDi4BMwJdWAMxKjkcFC4iEz1KOFZNMwZdOSQPI0dLWDcmJTYdWDtwSW4MLVUeNUU5amtDZjEIFx83KidICW9yJDwDIk0ecB1bL2sQLQwLFF4gKzILX28xBikZbBEdIgxAOWslf0UTF1MwJjJBGm8FBytKOFEEI0lcJCgGZhEIWB8mIiUGFDs4EW4eLUsKNR0TLCIGKgFHFhIuJntIQCc1Gm4eOUsDcAZVLGVBam9HWFNjADYEWC0xFyVKcRkgMQpbIyUGaBYCDDcmISIPZD05GjpKMRBnHQhQIhlZBwEDOgY3NzgGHDRwICsSOBlQcEthL2YKKBYTGR8vYz8HWyRwGiEdbhVncEkTah8MKQkTEQNjfndKciAiFytKPlxAMRlDJjJDLwNHEQdjMCMHRD81EG4dI0sGOQdUaioFMgAVWBJjMTIbRC4nGmBIYDNNcEkTDD4NJUVaWBU2LTQcXSA+XGdgbBlNcEkTamsuJwYPER0mbSQNQA4lACE5J1ABPApbLygIbgMGFAAmamxIQC4jH2AdLVAZeFkden5KfUUqGRArKjkNGjw1AA8fOFY+OwBfJigLIwYMUAcxNjJBPm9wVG5KbBlNHgZHIy0abkc0ExovL3crXCozH2xGbBs/NURbJSQIIwFJWlpJY3dIFCo+EG4XZTNnfUQTqN/jpPHnmufDYwMpdm9jVKzq2BkkBCx+GWuB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uVtFBwgIjtIfTs9OG5XbG0MMhodAz8GKxZdORcnDzIOQAgiGzsaLlYVeEt6Pi4OZiA0KFFvY3UYVSw7FSkPbhBnGR1eBnEiIgErGREmL38TFBs1DDpKcRlPGABUIicKIQ0TC1MmNTIaTW8gHS0BLVsBNUlaPi4OZgwJWAcrJncLQT0iESAebEsCPwQdaGdDAgoCCyQxIidICW8kBjsPbEREWiBHJwdZBwEDPBo1KjMNRmd5fgceIXVXEQ1XHiQEIQkCUFEGEAchQCo9VmJKNxk5NRFHanZDZCwTHR5jBgQ4FmNwMCsMLUwBJEkOai0CKhYCVFMAIjsEVi4zH25XbHw+AEdALz8qMgAKWA5qSR4cWQNqNSoOAFgPNQUbaAIXIwhHGxwvLCVKHXURECopI1UCIjlaKSAGNE1FPSATCiMNWQw/GCEYbhVNK2MTamtDAgABGQYvN3dVFAoDJGA5OFgZNUdaPi4OBQoLFwFvYwMBQCM1VHNKbnAZNQQTDxgzZgYIFBwxYXtiFG9wVA0LIFUPMQpYanZDIBAJGwcqLDlAV2ZwMR06YmoZMR1WZCIXIwgkFx8sMXdVFCxwESAObEREWmNfJSgCKkUuDB4RY2pIYC4yB2AjOFwAI1NyLi8xLwIPDDQxLCIYViAoXGwrOU0CcBlaKSAWNkdLWFEwIiENFmZaPToHHgMsNA1/KykGKk0cWCcmOyNICW9yIy8GJ0pNJAYTJC4CNAceWBo3JjobFC4+EG4NPlgPI0lHIi4OaEU1GR0kJncBR28zGyAZKUsbMR1aPC5DJBxHHBYlIiIEQGFyWG4uI1weBxtSOmteZhEVDRZjPn5ifTs9JnQrKF0pOR9aLi4RbkxtMQcuEW0pUCsEGykNIFxFcihGPiQzLwYMDQNhb3cTFBs1DDpKcRlPERxHJWszLwYMDQNjLTIJRi0pVCceKVQeckUTDi4FJxALDFN+YzEJWDw1WERKbBlNEwhfJikCJQ5HRVMlNjkLQCY/GmYcZRkENklFaj8LIwtHOQY3LAcBVyQlBGAZOFgfJEEaai4PNQBHOQY3LAcBVyQlBGAZOFYdeEATLyUHZgAJHFM+al0hQCICTg8OKGoBOQ1WOGNBFgwEEwYzETYGUypyWG4RbG0IKB0Td2tBFgwEEwYzYyUJWig1VmJKCFwLMRxfPmteZlRVVFMOKjlICW9lWG4nLUFNbUkLemdDFAoSFhcqLTBICW9gWG45OV8LORETd2tBZhYTWl9JY3dIFAwxGCIILVoGcFQTLD4NJREOFx1rNX5IdTokGx4DL1IYIEdgPioXI0sVGR0kJndVFDlwESAObEREWiBHJxlZBwEDKx8qJzIaHG0AHS0BOUkkPh1WOD0CKkdLWAhjFzIQQG9tVGwpJFwOO0laJD8GNBMGFFFvYxMNUi4lGDpKcRldflwfagYKKEVaWENtcXtIeS4oVHNKeRVNAgZGJC8KKAJHRVNxb3c7QSk2HTZKcRlPcBoRZkFDZkVHOxIvLzUJVyRwSW4MOVcOJABcJGMVb0UmDQcsEz4LXzogWh0eLU0IfgBdPi4RMAQLWE5jNXcNWitwCWdgRhRAcIunyqn3xofz+FMXAhVIAG+y9NpKHHUsCSxhaqn3xofz+JHXw7X8tK3E9Kz+zNv50Iunyqn3xofz+JHXw7X8tK3E9Kz+zNv50Iunyqn3xofz+JHXw7X8tK3E9Kz+zNv50Iunyqn3xofz+JHXw7X8tK3E9Kz+zNv50Iunyqn3xofz+JHXw7X8tK3E9Kz+zNv50Iunyqn3xofz+JHXw7X8tK3E9Kz+zNv50Iunyqn3xofz+JHXw7X8tK3E9Kz+zNv50IunykEPKQYGFFMTLyU8VjccVHNKGFgPI0djJioaIxddORcnDzIOQBsxFiwFNBFEWgVcKSoPZigIDhYXIjVICW8AGDw+LkEhaihXLh8CJE1FNRw1JjoNWjtyXUQGI1oMPEllIzg3JwdHWE5jEzsaYC0oOHQrKF05MQsbaB0KNRAGFABhal1ieSAmERoLLgMsNA1/KykGKk0cWCcmOyNICW9yltTKbH4MPQwTIioQZgRHCxYxNTIaGTw5ECtKP0kINQ0TKSMGJQ5JWDcmJTYdWDsjVD0eLUBNJQdXLzlDMg0CWAcrMTIbXCA8EGBIYBkpPwxAHTkCNkVaWAcxNjJISWZaOSEcKW0MMlNyLi8nLxMOHBYxa35ieSAmERoLLgMsNA1gJiIHIxdPWiQiLzw7RCo1EGxGbEJNBAxLPmteZkcwGR8oYwQYUSo0VmJKCFwLMRxfPmteZlRSVFMOKjlICW9hQWJKAVgVcFQTeHlPZjcIDR0nKjkPFHJwRGJKH0wLNgBLanZDZEUUDAYnMHgbFmNaVG5KbG0CPwVHIztDe0VFKxIlJncaVSE3EW4DPxkYIElHJWtBZktJWDAsLTEBU2EDNQgvE3QsCDZgGg4mAkVJVlNhbXcvVSI1VCoPKlgYPB0TIzhDd1BJWl9JY3dIFAwxGCIILVoGcFQTByQVIwgCFgdtMDIcYy48Hx0aKVwJcBQaQAYMMAAzGRF5AjMMYCA3EyIPZBsvKRlSOTgwNgACHDAiM3VEFDRwICsSOBlQcEtyJicMMUUVEQAoOncbRCo1ED1KZAdfYkARZmsnIwMGDR83Y2pIUi48BytGbGsEIwJKanZDMhcSHV9JY3dIFBs/GyIeJUlNbUkRHyUPKQYMC1M3KzJIRyM5ECsYbFgPPx9WanlRaEUqGQpjNyUBUyg1Bm4ZPFwINElVJioEaEdLclNjY3crVSM8Fi8JJxlQcA9GJCgXLwoJUAVqSXdIFG9wVG5KAVYbNQRWJD9NFREGDBZtIS4YVTwjJz4PKV0uMRkTd2sVTEVHWFNjY3dIXSlwOz4eJVYDI0dkKycIFRUCHRdjIjkMFAAgACcFIkpDBwhfIRgTIwADVj4iO3ccXCo+fm5KbBlNcEkTamtDZkhKWDwhMD4MXS4+ISdKKFYIIwcUPmsGPhUICxZjJy4GVSI5F24ZIFAJNRsTJyobfUUSCxYxYzodRztwBitHP1wZcB9SJj4GZggGFgYiLzsRPm9wVG5KbBlNNQdXQGtDZkUCFhdjPn5ieSAmERoLLgMsNA1gJiIHIxdPWjk2Lic4Wzg1BmxGbEJNBAxLPmteZkctDR4zYwcHQyoiVmJKCFwLMRxfPmteZlBXVFMOKjlICW9lRGJKAVgVcFQTeHtTakU1FwYtJz4GU29tVH5GbHoMPAVRKygIZlhHNRw1JjoNWjt+ByseBkwAIDlcPS4RZhhOcj4sNTI8VS1qNSoOGFYKNwVWYmkqKAMtDR4zYXtIT28EETYebARNciBdLCINLxECWDk2LidKGG8UESgLOVUZcFQTLCoPNQBLWDAiLzsKVSw7VHNKAVYbNQRWJD9NNQATMR0lCSIFRG8tXUQnI08IBAhRcAoHIjEIHxQvJn9KeiAzGCcabhVNcBITHi4bMkVaWFENLDQEXT9yWG5KbBlNcEkTDi4FJxALDFN+YzEJWDw1WG4pLVUBMghQIWteZigIDhYuJjkcGjw1AAAFL1UEIElOY0EuKRMCLBIheRYMUAs5AicOKUtFeWN+JT0GEgQFQjInJwMHUyg8EWZIClUUckUTMWs3Ix0TWE5jYREETW18VAoPKlgYPB0Td2sFJwkUHV9jET4bXzZwSW4ePkwIfGMTamtDEgoIFAcqM3dVFG0cHSUPIEBNJAYTPjkKIQICClMiLSMBGSw4ES8ebFALcBxALy9DJQQVHR8mMCQETWFyWERKbBlNEwhfJikCJQ5HRVMOLCENWSo+AGAZKU0rPBATN2JpCwoRHSciIW0pUCsDGCcOKUtFci9fMxgTIwADWl9jOHc8UTckVHNKbn8BKUlAOi4GIkdLWDcmJTYdWDtwSW5ffBVNHQBdanZDd1VLWD4iO3dVFH1gRGJKHlYYPg1aJCxDe0VXVFMAIjsEVi4zH25XbHQCJgxeLyUXaBYCDDUvOgQYUSo0VDNDRnQCJgxnKylZBwEDPBo1KjMNRmd5fgMFOlw5MQsJCy8HEgoAHx8ma3UpWjs5NQghbhVNK0lnLzMXZlhHWjItNz5FdQkbVmJKCFwLMRxfPmteZhEVDRZvSXdIFG8EGyEGOFAdcFQTaAkPKQYMC1M3KzJIBn99GScEOU0IcABXJi5DLQwEE11hb3crVSM8Fi8JJxlQcCRcPC4OIwsTVgAmNxYGQCYRMgVKMRBnHQZFLyYGKBFJCxY3AjkcXQ4WP2YePkwIeWN+JT0GEgQFQjInJxMBQiY0ETxCZTMgPx9WHioBfCQDHDE2NyMHWmcrVBoPNE1NbUkRGSoVI0UEDQExJjkcFD8/ByceJVYDckUTDD4NJUVaWBU2LTQcXSA+XGdKJV9NHQZFLyYGKBFJCxI1JgcHR2d5VDoCKVdNHgZHIy0abkc3FwBhb3U7VTk1EGBIZRkIPBpWagUMMgwBAVthEzgbFmNyOiFKL1EMIksfPjkWI0xHHR0nYzIGUG8tXUQnI08IBAhRcAoHIicSDAcsLX8TFBs1DDpKcRlPAgxQKycPZhYGDhYnYycHRyYkHSEEbhVNFhxdKWteZgMSFhA3KjgGHGZwHShKAVYbNQRWJD9NNAAEGR8vEzgbHGZwACYPIhkjPx1aLDJLZDUIC1FvYQUNVy48GCsOYhtEcAxfOS5DCAoTERU6a3U4WzxyWGwkI00FOQdUajgCMAADWl83MSINHW81GipKKVcJcBQaQEE1LxYzGRF5AjMMeC4yESJCNxk5NRFHanZDZDIICh8nYzsBUyckHSANbBJNIAVSMy4RZiA0KF1hb3csWyojIzwLPBlQcB1BPy5DO0xtLhowFzYKDg40EAoDOlAJNRsbY0E1LxYzGRF5AjMMYCA3EyIPZBsrJQVfKDkKIQ0TWl9jOHc8UTckVHNKbn8YPAVROCIELhFFVFMHJjEJQSMkVHNKKlgBIwwfaggCKgkFGRAoY2pIYiYjAS8GPxceNR11PycPJBcOHxs3YypBPhk5BxoLLgMsNA1nJSwEKgBPWj0sBTgPFmNwVG5KbBkWcD1WMj9De0VFKhYuLCENFCk/E2xGbH0INghGJj9De0UBGR8wJntIdy48GCwLL1JNbUllIzgWJwkUVgAmNxkHciA3VDNDRm8EIz1SKHEiIgEjEQUqJzIaHGZaIicZGFgPaihXLh8MIQILHVthBgQ4ZCMxDSsYbhVNcBITHi4bMkVaWFETLzYRUT1wMR06bhVNFAxVKz4PMkVaWBUiLyQNGG8TFSIGLlgOO0kOag4wFksUHQcTLzYRUT1wCWdgGlAeBAhRcAoHIikGGhYva3U4WC4pETxKL1YBPxsRY3EiIgEkFx8sMQcBVyQ1BmZICWo9AAVSMy4RBQoLFwFhb3cTPm9wVG4uKV8MJQVHanZDAzY3ViA3IiMNGj88FTcPPnoCPAZBZms3LxELHVN+Y3U4WC4pETxKCWo9cApcJiQRZEltWFNjYxQJWCMyFS0BbARNNhxdKT8KKQtPG1pjBgQ4GhwkFToPYkkBMRBWOAgMKgoVWE5jIHcNWitwCWdgRlUCMwhfahsPNDEFACFjfnc8VS0jWh4GLUAIIlNyLi8xLwIPDCciITUHTGd5fiIFL1gBcD1DGCQMK0VaWCMvMQMKTB1qNSoOGFgPeEthJSQOZjE3C1FqSTsHVy48VBoaHFUfI0kOahsPNDEFACF5AjMMYC4yXGw6IFgUNRsTHhtBb29tLAMRLDgFDg40EAILLlwBeBITHi4bMkVaWFEXJjsNRCAiAG4LPlYYPg0TPiMGZgYSCgEmLSNIRiA/GWBIYBkpPwxAHTkCNkVaWAcxNjJISWZaID44I1YAaihXLg8KMAwDHQFral08RB0/GyNQDV0JEhxHPiQNbh5HLBY7N3dVFG2y8txKCVUIJghHJTlBakUhDR0gY2pIUjo+FzoDI1dFeWMTamtDKgoEGR9jM3dVFB0/GyNEK1wZFQVWPCoXKRc3FwBral1IFG9wHShKPBkZOAxdah4XLwkUVgcmLzIYWz0kXD5KZxk7NQpHJTlQaAsCD1tzb2NEBGZ5T24kI00ENhAbaB8zZElFmvXRYxIEUTkxACEYbhBncEkTai4PNQBHNhw3KjERHG0EJGxGbncCcAxfLz0CMgoVWl83MSINHW81GipgKVcJcBQaQB8TFAoIFUkCJzMqQTskGyBCNxk5NRFHanZDZIfh6lMNJjYaUTwkVCMLL1EEPgwRZmslMwsEWE5jJSIGVzs5GyBCZTNNcEkTJiQAJwlHJ19jKyUYFHJwIToDIEpDNgBdLgYaEgoIFltqSXdIFG85Em4EI01NOBtDaj8LIwtHNhw3KjERHG0EJGxGbncCcApbKzlBahEVDRZqeHcaUTslBiBKKVcJWkkTamsPKQYGFFMhJiQcGG8yEG5XbFcEPEUTJyoXLksPDRQmSXdIFG82GzxKExVNPUlaJGsKNgQOCgBrETgHWWE3ETonLVoFOQdWOWNKb0UDF3ljY3dIFG9wVCIFL1gBcA0Td2s2MgwLC10nKiQcVSEzEWYCPklDAAZAIz8KKQtLWB5tMTgHQGEAGz0DOFACPkA5amtDZkVHWFMqJXcMFHNwFipKOFEIPklRLmteZgFcWBEmMCNICW89VCsEKDNNcEkTLyUHTEVHWFMqJXcKUTwkVDoCKVdNBR1aJjhNMgALHQMsMSNAViojAGAYI1YZfjlcOSIXLwoJWFhjFTILQCAiR2AEKU5FYEUHZntKb15HNhw3KjERHG0EJGxGbtvrwkkRZGUBIxYTVh0iLjJBPm9wVG4PIEoIcCdcPiIFP01FLCNhb3UmW289FS0CJVcIckVHOD4Gb0UCFhdJJjkMFDJ5fhoaHlYCPVNyLi8hMxETFx1rOHc8UTckVHNKbtvrwkl9LyoRIxYTWBo3JjpKGG8WASAJbARNNhxdKT8KKQtPUXljY3dIWCAzFSJKExVNOBtDanZDExEOFABtJT4GUAIpICEFIhFEWkkTamsKIEUJFwdjKyUYFDs4ESBKAlYZOQ9KYmk3FkdLWj0sYzQAVT1yWDoYOVxEa0lBLz8WNAtHHR0nSXdIFG88Gy0LIBkPNRpHZmsBIkVaWB0qL3tIWS4kHGACOV4IWkkTamsFKRdHJ19jKncBWm85BC8DPkpFAgZcJ2UEIxEuDBYuMH9BHW80G0RKbBlNcEkTaicMJQQLWBdjfnc9QCY8B2AOJUoZMQdQL2MLNBVJKBwwKiMBWyF8VCdEPlYCJEdjJTgKMgwIFlpJY3dIFG9wVG4DKhkJcFUTKC9DMg0CFlMhJ3dVFCtrVCwPP01NbUlaai4NIm9HWFNjJjkMPm9wVG4DKhkPNRpHaj8LIwtHLQcqLyRGQCo8ET4FPk1FMgxAPmURKQoTViMsMD4cXSA+VGVKGlwOJAZBeWUNIxJPSF9wb2dBHXRwOiEeJV8UeEtnGmlPZIfh6lNhbXkKUTwkWiALIVxEWkkTamsGKhYCWD0sNz4OTWdyIB5IYBsjP0laPi4ONUdLDAE2Jn5IUSE0fisEKBkQeWM5JiQAJwlHHgYtICMBWyFwEyseHFUMKQxBBCoOIxZPUXljY3dIWCAzFSJKI0wZcFQTMTZpZkVHWBUsMXc3GG8gVCcEbFAdMQBBOWMzKgQeHQEweRANQB88FTcPPkpFeUATLiRpZkVHWFNjY3cBUm8gVDBXbHUCMwhfGicCPwAVWAcrJjlIQC4yGCtEJVceNRtHYiQWMklHCF0NIjoNHW81GipgbBlNcAxdLkFDZkVHERVjYDgdQG9tSW5abE0FNQcTPioBKgBJER0wJiUcHCAlAGJKbhEDPwdWY2lKZgAJHHljY3dIRiokATwEbFYYJGNWJC9pEhU3FAEweRYMUAMxFisGZEJNBAxLPmteZkczHR8mMzgaQG8kG24LIlYZOAxBajsPJxwCClMqLXccXCpwBysYOlwffksfag8MIxYwChIzY2pIQD0lEW4XZTM5IDlfODhZBwEDPBo1KjMNRmd5fhoaHFUfI1NyLi8nNAoXHBw0LX9KYD8AGC8TKUtPfElIah8GPhFHRVNhEzsJTSoiVmJKGlgBJQxAanZDIQATKB8iOjIaei49ET1CZRVNFAxVKz4PMkVaWFFrLTgGUWZyWG4pLVUBMghQIWteZgMSFhA3KjgGHGZwESAObEREWj1DGicRNV8mHBcBNiMcWyF4D24+KUEZcFQTaBkGIBcCCxtjLz4bQG18VAgfIlpNbUlVPyUAMgwIFltqSXdIFG85Em4lPE0EPwdAZB8TFgkGARYxYzYGUG8fBDoDI1cefj1DGicCPwAVViAmNwEJWDo1B24eJFwDcCZDPiIMKBZJLAMTLzYRUT1qJyseGlgBJQxAYiwGMjULGQomMRkJWSojXGdDbFwDNGNWJC9DO0xtLAMTLyUbDg40EAwfOE0CPkFIah8GPhFHRVNhFzIEUT8/BjpKOFZNIwxfLygXIwFFVFMFNjkLFHJwEjsEL00EPwcbY0FDZkVHFBwgIjtIWm9tVAEaOFACPhodHjszKgQeHQFjIjkMFAAgACcFIkpDBBljJioaIxdJLhIvNjJiFG9wVGNHbHUCPwITIyVDDwsgGR4mEzsJTSoiB24MI0tNJAFWIzlDMgoIFnljY3dIWCAzFSJKO0pNbUlkJTkINRUGGxZ5BT4GUAk5Bj0eD1EEPA0baAINAQQKHSMvIi4NRjxyXURKbBlNOQ8TPThDMg0CFnljY3dIFG9wVCIFL1gBcAQTd2sUNV8hER0nBT4aRzsTHCcGKBEDeWMTamtDZkVHWB8sIDYEFCciBG5XbFRNMQdXaiZZAAwJHDUqMSQcdyc5GCpCbnEYPQhdJSIHFAoIDCMiMSNKHUVwVG5KbBlNcABVaiMRNkUTEBYtYwIcXSMjWjoPIFwdPxtHYiMRNks3FwAqNz4HWm97VBgPL00CIlodJC4UbldLSF9zan5TFD01ADsYIhkIPg05amtDZgAJHHljY3dIeiAkHSgTZBs5AEsfamkzKgQeHQFjLTgcFCY+WSkLIVxPfElHOD4Gb28CFhdjPn5iPmJ9VKz+zNv50Iunyms3BydHTVOhw8NIeQYDN26I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOnR3suB0uWF7POh19eKoM+y4M6I2LmPxOk5JiQAJwlHNRowIBtICW8EFSwZYnQEIwoJCy8HCgABDDQxLCIYViAoXGwtLVQIcE8TGT8CMhZFVFNhKjkOW215fgMDP1ohaihXLgcCJAALUAhjFzIQQG9tVGwtLVQIcABdLCRDJwsDWB8qNTJIRyojBycFIhkeJAhHOWVBakUjFxYwFCUJRG9tVDoYOVxNLUA5ByIQJSldORcnBz4eXSs1BmZDRnQEIwp/cAoHIikGGhYva39KZCMxFytQbBweckAJLCQRKwQTUDAsLTEBU2EXNQMvE3csHSwaY0EuLxYENEkCJzMkVS01GGZCbmkBMQpWagInfEVCHFFqeTEHRiIxAGYpI1cLOQ4dGgciBSA4MTdqal0lXTwzOHQrKF0pOR9aLi4RbkxtFBwgIjtIWC08OS8JJBlNcFQTByIQJSldORcnDzYKUSN4VgMLL1EEPgxAaigMKxULHQcmJ21IBG15fiIFL1gBcAVRJgIXIwgUWFN+YxoBRywcTg8OKHUMMgxfYmkqMgAKC1MzKjQDUStwVG5KbANNYEsaQCcMJQQLWB8hLxAaVS0jVG5XbHQEIwp/cAoHIikGGhYva3UvRi4yB24PP1oMIAxXamtDZl9HSFFqSTsHVy48VCIIIH0IMR1bOWteZigOCxAPeRYMUAMxFisGZBspNQhHIjhDZkVHWFNjY3dIFHVwRGxDRlUCMwhfaicBKjAXDBouJndVFAI5By0mdngJNCVSKC4PbkcyCAcqLjJIFG9wVG5KbBlNcFMTentZdlVdSENhal0lXTwzOHQrKF0pOR9aLi4RbkxtNRowIBtSdSs0NjseOFYDeBITHi4bMkVaWFERJiQNQG8jAC8ePxtBcC9GJChDe0UBDR0gNz4HWmd5VB0eLU0efhtWOS4XbkxcWD0sNz4OTWdyJzoLOEpPfEthLzgGMktFUVMmLTNISWZafiIFL1gBcCRaOSgxZlhHLBIhMHklXTwzTg8OKGsENwFHDTkMMxUFFwtrYQQNRjk1BmxGbBsaIgxdKSNBb28qEQAgEW0pUCscFSwPIBEWcD1WMj9De0VFKhYpLD4GFCAiVCYFPBkZP0lSai0RIxYPWAAmMSENRmFyWG4uI1weBxtSOmteZhEVDRZjPn5ieSYjFxxQDV0JFABFIy8GNE1Ocj4qMDQ6Dg40EAwfOE0CPkFIah8GPhFHRVNhETICWyY+VDoCJUpNIwxBPC4RZEltWFNjYxEdWixwSW4MOVcOJABcJGNKZgIGFRZ5BDIcZyoiAicJKRFPBAxfLzsMNBE0HQE1KjQNFmZqICsGKUkCIh0bCSQNIAwAViMPAhQtawYUWG4mI1oMPDlfKzIGNExHHR0nYypBPgI5By04dngJNCtGPj8MKE0cWCcmOyNICW9yJysYOlwfcAFcOmtLNAQJHBwuanVEPm9wVG4sOVcOcFQTLD4NJREOFx1ral1IFG9wVG5KbHcCJABVM2NBDgoXWl9jYQQNVT0zHCcEKxdDfksaQGtDZkVHWFNjNzYbX2EjBC8dIhELJQdQPiIMKE1OclNjY3dIFG9wVG5KbFUCMwhfah8wZlhHHxIuJm0vUTsDETwcJVoIeEtnLycGNgoVDCAmMSEBVypyXURKbBlNcEkTamtDZkULFxAiL3cgQDsgJysYOlAONUkOaiwCKwBdPxY3EDIaQiYzEWZIBE0ZIDpWOD0KJQBFUXljY3dIFG9wVG5KbBkBPwpSJmsMLUlHChYwY2pIRCwxGCJCKkwDMx1aJSVLb29HWFNjY3dIFG9wVG5KbBlNIgxHPzkNZgIGFRZ5CyMcRAg1AGZCblEZJBlAcGRMIQQKHQBtMTgKWCAoWi0FIRYbYUZUKyYGNUpCHFwwJiUeUT0jWx4fLlUEM1ZAJTkXCRcDHQF+AiQLEiM5GScecQhdYEsacC0MNAgGDFsALDkOXSh+JAIrD3wyGS0aY0FDZkVHWFNjY3dIFG81GipDRhlNcEkTamtDZkVHWBolYzkHQG8/H24eJFwDcCdcPiIFP01FMBwzYXtKfDskBAkPOBkLMQBfLy9NZEkTCgYmamxIRiokATwEbFwDNGMTamtDZkVHWFNjY3cEWywxGG4FJwtBcA1SPipDe0UXGxIvL38OQSEzACcFIhFEcBtWPj4RKEUvDAczEDIaQiYzEXQgH3YjFAxQJS8GbhcCC1pjJjkMHUVwVG5KbBlNcEkTamsKIEUJFwdjLDxaFCAiVCAFOBkJMR1SaiQRZgsIDFMnIiMJGisxAC9KOFEIPkl9JT8KIBxPWjssM3VEFg0xEG4YKUodPwdAL2VBahEVDRZqeHcaUTslBiBKKVcJWkkTamtDZkVHWFNjYzEHRm8PWG4ZPk9NOQcTIzsCLxcUUBciNzZGUC4kFWdKKFZncEkTamtDZkVHWFNjY3dIFCY2VD0YOhcdPAhKIyUEZgQJHFMwMSFGWS4oJCILNVwfI0lSJC9DNRcRVgMvIi4BWihwSG4ZPk9DPQhLGicCPwAVC1NuY2ZIVSE0VD0YOhcENElNd2sEJwgCVjksIR4MFDs4ESBgbBlNcEkTamtDZkVHWFNjY3dIFG8EJ3Q+KVUIIAZBPh8MFgkGGxYKLSQcVSEzEWYpI1cLOQ4dGgciBSA4MTdvYyQaQmE5EGJKAFYOMQVjJioaIxdOQ1MxJiMdRiFaVG5KbBlNcEkTamtDZkVHWBYtJ11IFG9wVG5KbBlNcElWJC9pZkVHWFNjY3dIFG9wOiEeJV8UeEt7JTtBakcpF1MwJiUeUT1wEiEfIl1DckVHOD4Gb29HWFNjY3dIFCo+EGdgbBlNcAxdLmseb29tVV5jDz4eUW8lBCoLOFxNPAZcOkEXJxYMVgAzIiAGHCklGi0eJVYDeEA5amtDZhIPER8mYyMJRyR+Ay8DOBFceUlXJUFDZkVHWFNjYycLVSM8XCgfIloZOQZdYmJpZkVHWFNjY3dIFG9wHShKIFsBHQhQImtDZgQJHFMvITslVSw4Wh0POG0IKB0TamsXLgAJWB8hLxoJVydqJyseGFwVJEERByoALgwJHQBjIDgFRCM1ACsOdhlPcEcdahgXJxEUVh4iID8BWiojMCEEKRBNNQdXQGtDZkVHWFNjY3dIFCY2VCIIIHAZNQRAamsCKAFHFBEvCiMNWTx+JyseGFwVJEkTPiMGKEULGh8KNzIFR3UDETo+KUEZeEt6Pi4ONUUXERAoJjNIFG9wVHRKbhlDfklgPioXNUsODBYuMAcBVyQ1EGdKKVcJWkkTamtDZkVHWFNjYz4OFCMyGAkYLVsecElSJC9DKgcLPwEiISRGZyokICsSOBlNJAFWJGsPJAkgChIhMG07UTsEETYeZBsqIghROWsGNQYGCBYnY3dIFHVwVm5EYhk+JAhHOWUGNQYGCBYnBCUJVjx5VCsEKDNNcEkTamtDZkVHWFMqJXcEViMUES8eJEpNMQdXaicBKiECGQcrMHk7UTsEETYebE0FNQcTJikPAgAGDBsweQQNQBs1DDpCbn0IMR1bOWtDZkVHWFNjY3dIDm9yVGBEbGoZMR1AZC8GJxEPC1pjJjkMPm9wVG5KbBlNcEkTaiIFZgkFFCYzNz4FUW8xGipKIFsBBRlHIyYGaDYCDCcmOyNIQCc1Gm4GLlU4IB1aJy5ZFQATLBY7N39KYT8kHSMPbBlNcEkTamtDZkVdWFFjbXlIZzsxAD1EOUkZOQRWYmJKZgAJHHljY3dIFG9wVCsEKBBncEkTai4NIm8CFhdqSV1FGW+y4M6I2LmPxOkTHgohZl1HmvPXYxQ6cQsZIB1Krq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQfiIFL1gBcCpBBmteZjEGGgBtACUNUCYkB3QrKF0hNQ9HDTkMMxUFFwtrYRYKWzokVDoCJUpNGBxRaGdDZAwJHhxhal0rRgNqNSoOAFgPNQUbMWs3Ix0TWE5jYRMJWispUz1KG1YfPA0TqMv3ZjxVM1MLNjVKGG8UGysZG0sMIEkOaj8RMwBHBVpJACUkDg40EAILLlwBeBITHi4bMkVaWFEQNiUeXTkxGGMMI1oYIwxXaiMWJEtHPSATb3cJWjs5WSkYLVtBcBpYIycPawYPHRAob3cJQTs/VD4DL1IYIEcRZmsnKQAULwEiM3dVFDsiAStKMRBnExt/cAoHIiEODhonJiVAHUUTBgJQDV0JHAhRLydLbkc0GwEqMyNIQioiBycFIhlXcExAaGJZIAoVFRI3axQHWik5E2A5D2skAD1sHA4xb0xtOwEPeRYMUAMxFisGZBs4GUlfIykRJxceWFNjY3dSFAAyBycOJVgDBQARY0EgNCldORcnDzYKUSN4VhsjbFgYJAFcOGtDZkVHWEljGmUDFBwzBicaOBkvMQpYeAkCJQ5FUXkAMRtSdSs0OC8IKVVFeEtgKz0GZgMIFBcmMXdIFG9qVGsZbhBXNgZBJyoXbiYIFhUqJHk7dRkVKxwlA21EeWM5JiQAJwlHOwERY2pIYC4yB2ApPlwJOR1AcAoHIjcOHxs3BCUHQT8yGzZCbm0MMkl0PyIHI0dLWFEuLDkBQCAiVmdgD0s/aihXLgcCJAALUAhjFzIQQG9tVGw7OVAOO0lBLy0GNAAJGxZjodf8FDg4FTpKKVgOOElHKylDIgoCC0lhb3csWyojIzwLPBlQcB1BPy5DO0xtOwEReRYMUAs5AicOKUtFeWNwOBlZBwEDNBIhJjtAT28EETYebARNcouz6GswMxcREQUiL3eKtNtwIDkDP00INEl2GRtPZgsIDBolKjIaGG8xGjoDYV4fMQsfaigMIgAUVlFvYxMHUTwHBi8abARNJBtGL2seb28kCiF5AjMMeC4yESJCNxk5NRFHanZDZIfn2lMOIjQAXSE1B26IzK1NHQhQIiINI0UiKyNjIjkMFC4lACFKP1IEPAUeKSMGJQ5JWl9jBzgNRxgiFT5KcRkZIhxWajZKTCYVKkkCJzMkVS01GGYRbG0IKB0Td2tBpOXFWDo3JjobFK3Q4G4jOFwAcCxgGmsCKAFHGQY3LHcYXSw7AT5EbhVNFAZWORwRJxVHRVM3MSINFDJ5fg0YHgMsNA1/KykGKk0cWCcmOyNICW9yls7IbGkBMRBWOGuBxvFHNRw1JjoNWjt8VCgGNRVNPgZQJiITakUVFxwubCcEVTY1Bm4+HEpDckUTDiQGNTIVGQNjfnccRjo1VDNDRnofAlNyLi8vJwcCFFs4YwMNTDtwSW5IrrnPcCRaOShDpOXzWD8qNTJIRzsxAD1GbEoIIh9WOGsRIw8IER1sKzgYGm18VAoFKUo6IghDanZDMhcSHVM+al0rRh1qNSoOAFgPNQUbMWs3Ix0TWE5jYbXolm8TGyAMJV4ecIuz3mswJxMCVx8sIjNIRD01BysebEkfPw9aJi4QaEdLWDcsJiQ/Ri4gVHNKOEsYNUlOY0EgNDddORcnDzYKUSN4D24+KUEZcFQTaKnj5EU0HQc3KjkPR2+y9NpKGXBNIBtWLDhPZgQEDBosLXcAWzs7ETcZYBkZOAxeL2VBakUjFxYwFCUJRG9tVDoYOVxNLUA5QGZOZofz+JHXw7X8tG8ENQxKexmP0P0TGQ43EiwpPyBjocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jTAkIGxIvYwQNQANwSW4+LVsefjpWPj8KKAIUQjInJxsNUjsXBiEfPFsCKEERAyUXIxcBGRAmYXtIFiI/GiceI0tPeWNgLz8vfCQDHD8iITIEHDRwICsSOBlQcEtlIzgWJwlHCAEmJTIaUSEzET1KKlYfcB1bL2sOIwsSWBo3MDIEUmFyWG4uI1weBxtSOmteZhEVDRZjPn5iZyokOHQrKF0pOR9aLi4RbkxtKxY3D20pUCsEGykNIFxFcjpbJTwgMxYTFx4ANiUbWz1yWG4RbG0IKB0Td2tBBRAUDBwuYxQdRjw/BmxGbH0INghGJj9De0UTCgYmb11IFG9wNy8GIFsMMwITd2sFMwsEDBosLX8eHW8cHSwYLUsUfjpbJTwgMxYTFx4ANiUbWz1wSW4cbFwDNElOY0EwIxErQjInJxsJVio8XGwpOUsePxsTCSQPKRdFUUkCJzMrWyM/Bh4DL1IIIkERCT4RNQoVOxwvLCVKGG8rfm5KbBkpNQ9SPycXZlhHOxwtJT4PGg4TNwskGBVNBABHJi5De0VFOwYxMDgaFAw/GCEYbhVncEkTaggCKgkFGRAoY2pIUjo+FzoDI1dFM0ATBiIBNAQVAUkQJiMrQT0jGzwpI1UCIkFQY2sGKAFHBVpJEDIceHURECouPlYdNAZEJGNBCAoTERU6ED4MUW18VDVKGlgBJQxAanZDPUVFNBYlN3VEFG0CHSkCOBtNLUUTDi4FJxALDFN+Y3U6XSg4AGxGbG0IKB0Td2tBCAoTERUqIDYcXSA+VD0DKFxPfGMTamtDBQQLFBEiIDxICW82ASAJOFACPkFFY2svLwcVGQE6eQQNQAE/ACcMNWoENAwbPGJDIwsDWA5qSQQNQANqNSoOCEsCIA1cPSVLZDAuKxAiLzJKGG8rVBgLIEwII0kOajBDZFJSXVFvYWZYBGpyWGxbfgxIckURe35TY0dHBV9jBzIOVTo8AG5XbBtcYFkWaGdDEgAfDFN+Y3U9fW8DFy8GKRtBWkkTamsgJwkLGhIgKHdVFCklGi0eJVYDeB8aagcKJBcGCgp5EDIccB8ZJy0LIFxFJAZdPyYBIxdPDkkkMCIKHG11UWxGbhtEeUATLyUHZhhOciAmNxtSdSs0MCccJV0IIkEaQBgGMildORcnDzYKUSN4VgMPIkxNGwxKKCINIkdOQjInJxwNTR85FyUPPhFPHQxdPwAGPwcOFhdhb3cTPm9wVG4uKV8MJQVHanZDBQoJHhokbQMncwgcMREhCWBBcCdcHwJDe0UTCgYmb3c8UTckVHNKbm0CNw5fL2suIwsSWl9JPn5iZyokOHQrKF0pOR9aLi4RbkxtKxY3D20pUCsSAToeI1dFK0lnLzMXZlhHWiYtLzgJUG8YASxIYBkpPxxRJi4gKgwEE1N+YyMaQSp8fm5KbBk5PwZfPiITZlhHWiEmLjgeUTxwACYPbGwkcAhdLmsHLxYEFx0tJjQcR281AisYNU0FOQdUZGlPTEVHWFMFNjkLFHJwEjsEL00EPwcbY0FDZkVHWFNjYxI7ZGEjETo+O1AeJAxXYi0CKhYCUUhjBgQ4Gjw1AAMLL1EEPgwbLCoPNQBOQ1MGEAdGRyokPToPIRELMQVAL2JYZiA0KF0wJiM4WC4pETxCKlgBIwwaQGtDZkVHWFNjKjFIcRwAWhEJI1cDfgRSIyVDMg0CFlMGEAdGayw/GiBEIVgEPlN3IzgAKQsJHRA3a35IUSE0fm5KbBlNcEkTByQVIwgCFgdtMDIcciMpXCgLIEoIeVITByQVIwgCFgdtMDIceiAzGCcaZF8MPBpWY3BDCwoRHR4mLSNGRyokPSAMBkwAIEFVKycQI0xcWD4sNTIFUSEkWj0POHgDJAByDABLIAQLCxZqSXdIFG9wVG5KJV9NAxxBPCIVJwlJJxAsLTlIQCc1Gm45OUsbOR9SJmU8JQoJFkkHKiQLWyE+ES0eZBBNNQdXQGtDZkVHWFNjKjFIZzoiAiccLVVDDwdcPiIFPyISEVM3KzIGFBwlBjgDOlgBfjZdJT8KIBwgDRp5BzIbQD0/DWZDbFwDNGMTamtDZkVHWCwEbQ5afxAUNQAuFWYlBStsBgQiAiAjWE5jLT4EPm9wVG5KbBlNHABROCoRP18yFh8sIjNAHUVwVG5KKVcJcBQaQEEPKQYGFFMQJiM6FHJwIC8IPxc+NR1HIyUENV8mHBcRKjAAQAgiGzsaLlYVeEtyKT8KKQtHMBw3KDIRR218VGwBKUBPeWNgLz8xfCQDHD8iITIEHDRwICsSOBlQcEtiPyIALUUMHQowYzEHRm8/GitHP1ECJElSKT8KKQsUVlFvYxMHUTwHBi8abARNJBtGL2seb280HQcReRYMUAs5AicOKUtFeWNgLz8xfCQDHD8iITIEHG0EESIPPFYfJElHJWsGKgARGQcsMXVBDg40EAUPNWkEMwJWOGNBDgoTExY6BjsNQm18VDVgbBlNcC1WLCoWKhFHRVNhBHVEFAI/ECtKcRlPBAZULScGZElHLBY7N3dVFG0VGCscLU0CIksfQGtDZkUkGR8vITYLX29tVCgfIloZOQZdYioAMgwRHVpJY3dIFG9wVG4DKhkMMx1aPC5DMg0CFnljY3dIFG9wVG5KbBkBPwpSJmsTZlhHKhwsLnkPUTsVGCscLU0CIjlcOWNKTEVHWFNjY3dIFG9wVCcMbElNJAFWJGs2MgwLC103JjsNRCAiAGYabBJNBgxQPiQRdUsJHQRrc3tcGH95XXVKAlYZOQ9KYmkrKREMHQphb3WKst1wMSIPOlgZPxsRY2sGKAFtWFNjY3dIFG81GipgbBlNcAxdLmseb280HQcReRYMUAMxFisGZBs5NQVWOiQRMkUTF1MtJjYaUTwkVCMLL1EEPgwRY3EiIgEsHQoTKjQDUT14VgYFOFIIKSRSKSNBakUcclNjY3csUSkxASIebARNciERZmsuKQECWE5jYQMHUyg8EWxGbG0IKB0Td2tBCwQEEBotJnVEPm9wVG4pLVUBMghQIWteZgMSFhA3KjgGHC4zACccKRBncEkTamtDZkUOHlMtLCNIVSwkHTgPbE0FNQcTOC4XMxcJWBYtJ11IFG9wVG5KbFUCMwhfahRPZg0VCFN+YwIcXSMjWigDIl0gKT1cJSVLb15HERVjLTgcFCciBG4eJFwDcBtWPj4RKEUCFhdJY3dIFG9wVG4GI1oMPElRLzgXakUFHFN+YzkBWGNwGS8eJBcFJQ5WQGtDZkVHWFNjJTgaFBB8VCNKJVdNORlSIzkQbjcIFx5tJDIceS4zHCcEKUpFeUATLiRpZkVHWFNjY3dIFG9wGCEJLVVNNEkOah4XLwkUVhcqMCMJWiw1XCYYPBc9PxpaPiIMKElHFV0xLDgcGh8/ByceJVYDeWMTamtDZkVHWFNjY3cBUm80VHJKLl1NJAFWJGsBIkVaWBd4YzUNRztwSW4HbFwDNGMTamtDZkVHWBYtJ11IFG9wVG5KbFALcAtWOT9DMg0CFlMWNz4ER2EkESIPPFYfJEFRLzgXaBcIFwdtEzgbXTs5GyBKZxk7NQpHJTlQaAsCD1tzb2NEBGZ5T24kI00ENhAbaAMMMg4CAVFvYbXupm9yWmAIKUoZfgdSJy5KZgAJHHljY3dIUSE0VDNDRmoIJDsJCy8HCgQFHR9rYQMHUyg8EW4+O1AeJAxXag4wFkdOQjInJxwNTR85FyUPPhFPGAZHIS4aAzY3Wl9jOF1IFG9wMCsMLUwBJEkOamk3ZElHNRwnJndVFG0EGykNIFxPfElnLzMXZlhHWjYQE3VEPm9wVG4pLVUBMghQIWteZgMSFhA3KjgGHC4zACccKRBncEkTamtDZkUOHlMiICMBQipwACYPIjNNcEkTamtDZkVHWFMvLDQJWG8mVHNKIlYZcCxgGmUwMgQTHV03ND4bQCo0fm5KbBlNcEkTamtDZiA0KF0wJiM8QyYjACsOZE9EWkkTamtDZkVHWFNjYz4OFBs/EykGKUpDFTpjHjwKNRECHFM3KzIGFBs/EykGKUpDFTpjHjwKNRECHEkQJiM+VSMlEWYcZRkIPg05amtDZkVHWFNjY3dIeiAkHSgTZBslPx1YLzJBakVFLAQqMCMNUG8VJx5KbhlDfkkbPGsCKAFHWjwNYXcHRm9yOwgsbhBEWkkTamtDZkVHHR0nSXdIFG81GipKMRBnAwxHGHEiIgErGREmL39KZiozFSIGbEoMJgxXajsMNUdOQjInJxwNTR85FyUPPhFPGAZHIS4aFAAEGR8vYXtIT0VwVG5KCFwLMRxfPmteZkc1Wl9jDjgMUW9tVGw+I14KPAwRZms3Ix0TWE5jYQUNVy48GGxGRhlNcElwKycPJAQEE1N+YzEdWiwkHSEEZFgOJABFL2JDLwNHGRA3KiENFDs4ESBKAVYbNQRWJD9NNAAEGR8vEzgbHGZrVAAFOFALKUERAiQXLQAeWl9hETILVSM8ESpEbhBNNQdXai4NIkUaUXlJDz4KRi4iDWA+I14KPAx4LzIBLwsDWE5jDCccXSA+B2AnKVcYGwxKKCINIm9tVV5jocPo1tvQltrqbG0FNQRWamBDFQQRHVMiJzMHWjxwltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zqN/jpPHnmufDocPo1tvQltrqrq3tsv2zQCIFZjEPHR4mDjYGVSg1Bm4LIl1NAwhFLwYCKAQAHQFjNz8NWkVwVG5KGFEIPQx+KyUCIQAVQiAmNxsBVj0xBjdCAFAPIghBM2JpZkVHWCAiNTIlVSExEysYdmoIJCVaKDkCNBxPNBohMTYaTWZaVG5KbGoMJgx+KyUCIQAVQjokLTgaURs4ESMPH1wZJABdLThLb29HWFNjEDYeUQIxGi8NKUtXAwxHAywNKRcCMR0nJi8NR2crVGwnKVcYGwxKKCINIkdHBVpJY3dIFBs4ESMPAVgDMQ5WOHEwIxEhFx8nJiVAdyA+EicNYmosBixsGAQsEkxtWFNjYwQJQiodFSALK1wfajpWPg0MKgECClsALDkOXSh+Jw88CWYuFi5gY0FDZkVHKxI1JhoJWi43ETxQDkwEPA1wJSUFLwI0HRA3KjgGHBsxFj1ED1YDNgBUOWJpZkVHWCcrJjoNeS4+FSkPPgMsIBlfMx8MEgQFUCciISRGZyokACcEK0pEWkkTamsTJQQLFFslNjkLQCY/GmZDbGoMJgx+KyUCIQAVQj8sIjMpQTs/GCELKHoCPg9aLWNKZgAJHFpJJjkMPkV9WW45OFgfJElHIi5DAzY3WB8sLCdIHCYkVCEEIEBNIgxdLi4RNUUCFhIhLzIMFCwxACsNI0sENRoaQA4wFksUDBIxN39BPkUeGzoDKkBFcjABAWsrMwdFVFNhDzgJUCo0VCgFPhlPcEcdaggMKAMOH10EAhotawEROQtKYhdNckcTGjkGNRZHKhokKyMrQD08VDoFbE0CNw5fL2VBb28XChotN39AFhQJRgU3bHUCMQ1WLmsFKRdHXQBjawcEVSw1PSpKaV1EfksacC0MNAgGDFsALDkOXSh+Mw8nCWYjESR2ZmsgKQsBERRtExspdwoPPQpDZTM='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, antiSpy = { kick = true, halt = true } })
