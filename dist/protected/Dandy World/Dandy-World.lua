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
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
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

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
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
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
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
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
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
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

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
local License     = License

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

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

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

local __k = '5lcXiN1lAfkAfjWhj33rqFMm'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-z4JROHxa1bAW
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, watermark = 'Y2k-z4JROHxa1bAW', neuterAC = true, antiSpy = { kick = true, halt = true } })
