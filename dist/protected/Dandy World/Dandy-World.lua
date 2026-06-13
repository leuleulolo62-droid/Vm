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
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
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

local __k = 'b7V1kVgAS7lIqyRA6Kbb9YNJ'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, antiSpy = { kick = true, halt = true } })
