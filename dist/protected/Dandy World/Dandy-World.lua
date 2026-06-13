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

local __k = '3coBLfpp5Ol7a6MlIUn74G80'
local __p = 'Hk40GUaE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvNlYmxGUDR0AShuRmVtOwYHInMUZ9qwp0NPG34tUDhgDUwXFwdjXGdlThcUZxgQE0NPYmxGUFAVb0wXQRZtTGl1RkRdKV9cVk4JKyADUBJAJgBTSDxtTGl1L3YZM1FVQUMcNz4QGQZUI0xfFFRtCiYnTmdYJltVegdPc3pTRUINfV0DVANtRA00AFNNYEsQZAwdLihPelAVb0xiKAxtTGl1IVVHLlxZUg06K2xOKUJ+bz9UE189GGkXD1RfdXpRUAhGSGxGUFBmOxVbBAxtIiw6ABdtdXMcEwQDLTtGFRZTKg9DEhptHyQ6AUNcZ0xHVgYBMWBGFgVZI0xEAEAoQz09C1pRZ0tFQxMAMDhselAVb0xmNH8OJ2kGOnZmExjSs/dPMi0VBBUVJgJDDhYsAjB1PFhWK1dIEwYXJy8TBB9Hbw1ZBRY/GSd7ZD0UZxgQZwINMXZsUFAVb0wXg7bvTBogHEFdMVlcE0NPoMzyUCRCJh9DBFJtKRoFQhdaKExZVQoKMGBGER5BJkFQE1cvQGk0G0NballGXAoLSGxGUFAVb463wxYADSo9B1lRNBgQE4Hv1mwrERNdJgJSQXMePGV1D0JAKBhDWAoDLmEFGBVWJEAXAlkgHCUwGl5bKRgVH0MONzgJXRlbOwlFAFU5Zml1ThcUZ9qwkUMmNikLA1AVb0wXQdTN+GkcGlJZZ31jY09PIzkSH1BFJg9cFEZhTCA7GFJaM1dCSkMZKykRFQI/b0wXQRZtjsn3TmdYJkFVQUNPYmxGkvChbz9HBFMpQyMgA0cbIVRJHA0AISAPAFAdPA1RBBY/DScyC0QdaxhRXRcGbz8SBR4ZbzhnEjxtTGl1ThfWx5oQfgocIWxGUFAVb0zV4aJtICAjCxdHM1lEQE9PITkUAhVbO0xRDVkiHmV1HVJGMV1CExEKKCMPHl9dIBw9QRZtTGl1jLeWZ3tfXQUGJT9GUFAVreyjQWUsGiwYD1lVIF1CExMdJz8DBFBGIwNDEjxtTGl1ThfWx5oQYAYbNiUIFwMVb0zV4aJtOQB1HkVRIUsQGEMOITgPHx4VJwNDClM0H2l+TkNcIlVVExMGIScDAnoVb0wXQRav7Ot1LUVRI1FEQENPYmyE8OQVDg5YFEJtR2khD1UUIE1ZVwZlSGxGUFDX1cwXNV4oTC40A1IUL1lDEwADKykIBF1GJghSQVcjGCB4DV9RJkweEycKJC0THARGbw1FBBY5GScwChdHJl5VHWlPYmxGUFAVBAlSERYaDSU+PUdRIlwQ0erLYn5UUBFbK0xWF1kkCGk9G1BRZ0xVXwYfLT4SA1BBIExEFVc0TDw7ClJGZ0xYVkMdIygHAl4/rfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2ei1oRWZeBxYSK2cMXHxrA3l+dzowChkkLzx6DihyJRY5BCw7ZBcUZxhHUhEBam49KUJ+byRCA2ttLSUnC1ZQPhhcXAILJyhGkvChbw9WDVptICA3HFZGPgJlXQ8AIyhOWVBTJh5EFRhvRUN1ThcUNV1ERhEBSCkIFHpqCEJuU30SKAgbKm5rD21ybC8gAwgjNFAIbxhFFFNHZiU6DVZYZ2hcUhoKMD9GUFAVb0wXQRZtUWkyD1pRfX9VRzAKMDoPExUdbTxbAE8oHjp3Rz1YKFtRX0M9JzwKGRNUOwlTMkIiHigyCwoUIFldVlkoJzg1FQJDJg9SSRQfCTk5B1RVM11UYBcAMC0BFVIcRQBYAlchTBsgAGRRNU5ZUAZPYmxGUFAVckxQAFsoVg4wGmRRNU5ZUAZHYB4THiNQPRpeAlNvRUM5AVRVKxhnXBEEMTwHExUVb0wXQRZtTHR1CVZZIgJ3Vhc8Jz4QGRNQZ05gDkQmHzk0DVIWbjJcXAAOLmwzAxVHBgJHFEIeCTsjB1RRZwUQVAICJ3YhFQRmKh5BCFUoRGsAHVJGDlZARhc8Jz4QGRNQbUU9DVkuDSV1Il5TL0xZXQRPYmxGUFAVb0wKQVEsASxvKVJAFF1CRQoMJ2REPBlSJxheD1FvRUM5AVRVKxhmWhEbNy0KJQNQPUwXQRZtTHR1CVZZIgJ3Vhc8Jz4QGRNQZ05hCEQ5GSg5O0RRNRoZOQ8AIS0KUDxaLA1bMVosFSwnThcUZxgQDkM/Li0fFQJGYSBYAlchPCU0F1JGTTJZVUMBLThGFxFYKlZ+EnoiDS0wCh8dZ0xYVg1PJS0LFV55IA1TBFJ3Oyg8Gh8dZ11eV2llb2FGkuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdZmR4TgYaZ3t/fSUmBUZLXVDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dlfAlhXJlQQcAwBJCUBUE0VNBE9IlkjCiAyQHB1Cn1vfSIiB2xGUFAVb1EXQ3IsAi0sSUQUEFdCXwdNSA8JHhZcKEJnLXcOKRYcKhcUZxgQE0NSYn1QRUUHd14GVQN4Zgo6AFFdIBZjcDEmEhg5JjVnb0wXQRZwTGtkQAcadxo6cAwBJCUBXiV8ED5yMXltTGl1ThcUZwUQEQsbNjwVSl8aPQ1AT1EkGCEgDEJHIkpTXA0bJyISXhNaIkNuU10eDzs8HkN2JltbASEOISdJPxJGJgheAFgYBWY4D15aaBo6cAwBJCUBXiN0GSloM3kCOGl1ThcUZwUQEScOLCgfJx9HIwgVa3UiAi88CRlnBm51bCApBR9GUFAVb0wKQRQJDScxF2BbNVRUHAAALCoPFwMXRS9YD1AkC2cBIXBzC31veCY2YmxGUFAIb05lCFElGAo6AENGKFQSOSAALCoPF150DC9yL2JtTGl1ThcUZxgNEyAALiMUQ15TPQNaM3EPRHl5TgUFdxQQAVFWa0ZsXV0VHANRFRY+DS8wGk4UJFlAQEMbNyIDFFBBIExEFVc0TDw7ClJGZ0xYVkMcJz4QFQISPExEEVMoCGk2BlJXLDJzXA0JKytIIzFzCjN6IG4SPxkQK3MUehgCAUNPb2FGBBhQbxhYDlhqH2kxC1FVMlREEwocYn1TXUEDY0xEEUQkAj11HkJHL11DEx1dcEZsXV0VChpSD0JtHCghBkQ+BFdeVQoIbAkwNT5hHDNnIGIFTHR1TGVRN1RZUAIbJyg1BB9HLgtST3M7CSchHRU+TRUdEygBLTsIUBVDKgJDQVooDS91AFZZIks6cAwBJCUBXiJwAiNjJGVtUWkuZBcUZxgdHkM8Nz4QGQZUI2YXQRZtPzggB0VZBFleUAYDYmxGUFAVb1EXQ2U8GSAnA3ZWLlRZRxosIyIFFRwXY2YXQRZtISY7HUNRNXlERwIMKQ8KGRVbO1EXQ3siAjohC0V1M0xRUAgsLiUDHgQXY2YXQRZtKCw0Gl8UZxgQE0NPYmxGUFAVb1EXQ3IoDT09K0FRKUwSH2lPYmxGIhVGPw1ADxZtTGl1ThcUZxgQE15PYB4DAwBUOAJyF1MjGGt5ZBcUZxgdHkMiIy8OGR5QPEwYQV85CSQmZBcUZxh9UgAHKyIDNQZQIRgXQRZtTGl1UxcWCllTWwoBJwkQFR5BbUA9QRZtTBo+B1tYJFBVUAg6MigHBBUVb0wKQRQeByA5AlRcIltbZhMLIzgDUlw/b0wXQWU5AzkcAENRNVlTRwoBJWxGUFAIb05kFVk9JSchC0VVJExZXQRNbkZGUFAVBhhSDHM7CSchThcUZxgQE0NPYnFGUjlBKgFyF1MjGGt5ZBcUZxh3Vg0KMC0SHwJgPwhWFVNtTGl1UxcWAF1eVhEONiMUJQBRLhhSQxpHTGl1Tn5AIlVgWgAENzwjBhVbO0wXQRZwTGscGlJZF1FTWBYfBzoDHgQXY2YXQRZtQWR1L1VdK1FEWgYcYmNGAwBHJgJDaxZtTGkGHkVdKUwQE0NPYmxGUFAVb0wXXBZvPzknB1lAAk5VXRdNbkZGUFAVDg5eDV85FQwjC1lAZxgQE0NPYnFGUjFXJgBeFU8IGiw7GhUYTRgQE0MsLiUDHgR0LQVbCEI0TGl1ThcUehgScA8GJyISMRJcIwVDGHM7CSchTBs+ZxgQE05CYgEPAxM/b0wXQWIoACwlAUVAZxgQE0NPYmxGUFAIb05jBFooHCYnGhUYTRgQE0M/KyIBUFAVb0wXQRZtTGl1ThcUehgSYwoBJQkQFR5BbUA9QRZtTA4wGnJYIk5RRwwdYmxGUFAVb0wKQRQKCT0QAlJCJkxfQTMAMSUSGR9bbUA9QRZtTA4wGnRcJkpRUBcKMBwJA1AVb0wKQRQKCT0WBlZGJltEVhE/LT8PBBlaIU4baxZtTGkHC1ZQPm1AE0NPYmxGUFAVb0wXXBZvPiw0Ck5hN31GVg0bYGBsUFAVby9fAFgqCQo9D0UUZxgQE0NPYmxbUFJ2Jw1ZBlMOBCgnTBs+ZxgQEyAOMCgwHwRQb0wXQRZtTGl1ThcJZxpzUhELFCMSFTVDKgJDQxpHTGl1TmFbM11UE0NPYmxGUFAVb0wXQRZwTGsDAUNRIxocOR5lSGFLUDNaKwlEQR4uAyQ4G1ldM0EdWA0ANSJKUAJQKR5SEl5tDTp1ClJCNBhCVg8KIz8DWXp2IAJRCFFjLwYRK2QUehhLOUNPYmxEIxFFPwReE0M+TmV1THN1CXxpEU9PYAMpICNiCj9nKHoBKQ0cOhUYZxpgfDM/G25KelAVb0wVI3oMLwIaO2MWaxgScSIhBgUyIyBwDCV2LRRhTGsYL356E31+ci0sB25Keg0/RUEaQdTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh1zIdHkNdbGwzJDl5HGYaTBav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qg6XwwMIyBGJQRcIx8XXBY2EUNfCEJaJExZXA1PFzgPHAMbPQlEDlo7CRk0Gl8cN1lEW0plYmxGUBxaLA1bQVU4HmloTlBVKl06E0NPYioJAlBGKgsXCFhtHCghBg1TKllEUAtHYBc4VV5oZE4eQVIiZml1ThcUZxgQWgVPLCMSUBNAPUxDCVMjTDswGkJGKRheWg9PJyICelAVb0wXQRZtDzwnTgoUJE1CCSUGLCggGQJGOy9fCFopRDowCR4+ZxgQEwYBJkZGUFAVPQlDFEQjTCogHD1RKVw6OQUaLC8SGR9bbzlDCFo+Qi4wGnRcJkoYGmlPYmxGHB9WLgAXAl4sHmloTntbJFlcYw8OOykUXjNdLh5WAkIoHkN1ThcULl4QXQwbYi8OEQIVOwRSDxY/CT0gHFkUKVFcEwYBJkZGUFAVYkEXKFhtKCg7Ck4TNBhnXBEDJmwSGBUVOwNYDxYvAy0sTltdMV1DExYBJikUUAdaPQdEEVcuCWccAHBVKl1gXwIWJz4VXFBXOhgXFV4oZml1ThcZahh8XAAOLhwKEQlQPUJ0CVc/DSohC0UUK1FeWEMGMWwVFQQVOARSDxYkAmQyD1pRTRgQE0MDLS8HHFBdPRwXXBYuBCgnVHFdKVx2WhEcNg8OGRxRZ05/FFssAiY8CmVbKExgUhEbYGVsUFAVbwBYAlchTCEgAxcJZ1tYUhFVBCUIFDZcPR9DIl4kAC0aCHRYJktDG0EnNyEHHh9cK04eaxZtTGk8CBdcNUgQUg0LYiQTHVBBJwlZQUQoGDwnABdXL1lCH0MHMDxKUBhAIkxSD1JHTGl1TkVRM01CXUMBKyBsFR5RRWYaTBYPCTohQ1JSIVdCR0MMKi0UERNBKh4XDVkiBzwlTkNcJkwQUg8cLWwFGBVWJB8XKFgKDSQwPltVPl1CQEMJLSACFQI/KRlZAkIkAyd1O0NdK0seVQoBJgEfJB9aIUQeaxZtTGk5AVRVKxhTWwIdbmwOAgAZbwRCDBZwTBwhB1tHaV9VRyAHIz5OWXoVb0wXCFBtDyE0HBdAL11eExEKNjkUHlBWJw1FTRYlHjl5Tl9BKhhVXQdlYmxGUBxaLA1bQUE+THR1OVhGLEtAUgAKeAoPHhRzJh5EFXUlBSUxRhV9KX9RXgY/Li0fFQJGbUU9QRZtTCAzTkBHZ0xYVg1lYmxGUFAVb0xbDlUsAGk4ClsUehhHQFkpKyICNhlHPBh0CV8hCGEZAVRVK2hcUhoKMGIoER1QZmYXQRZtTGl1Tl5SZ1VUX0MbKikIelAVb0wXQRZtTGl1TltbJFlcEwtPf2wLFBwPCQVZBXAkHjohLV9dK1wYESsaLy0IHxlRHQNYFWYsHj13Rz0UZxgQE0NPYmxGUFBZIA9WDRYlBGloTlpQKwJ2Wg0LBCUUAwR2JwVbBXkrLyU0HUQcZXBFXgIBLSUCUlk/b0wXQRZtTGl1ThcULl4QW0MOLChGGBgVOwRSDxY/CT0gHFkUKlxcH0MHbmwOGFBQIQg9QRZtTGl1ThdRKVw6E0NPYikIFHpQIQg9a1A4AiohB1haZ21EWg8cbDgDHBVFIB5DSUYiH2BfThcUZ1RfUAIDYhNKUBhHP0wKQWM5BSUmQFFdKVx9SjcALSJOWXoVb0wXCFBtBDslTlZaIxhAXBBPNiQDHlBdPRwZInA/DSQwTgoUBH5CUg4KbCIDB1hFIB8eWhY/CT0gHFkUM0pFVkMKLChsUFAVbx5SFUM/AmkzD1tHIjJVXQdlSCoTHhNBJgNZQWM5BSUmQFtbKEgYVAYbCyISFQJDLgAbQUQ4Aic8AFAYZ15eGmlPYmxGBBFGJEJEEVc6AmEzG1lXM1FfXUtGSGxGUFAVb0wXFl4kACx1HEJaKVFeVEtGYigJelAVb0wXQRZtTGl1TltbJFlcEwwEbmwDAgIVckxHAlchAGEzAB4+ZxgQE0NPYmxGUFAVJgoXD1k5TCY+TkNcIlYQRAIdLGREKykHBDEXDVkiHHN1TBcaaRhEXBAbMCUIF1hQPR4eSBYoAi1fThcUZxgQE0NPYmxGHB9WLgAXBUJtUWkhF0dRb19VRyoBNikUBhFZZkwKXBZvCjw7DUNdKFYSEwIBJmwBFQR8IRhSE0AsAGF8TlhGZ19VRyoBNikUBhFZRUwXQRZtTGl1ThcUZ0xRQAhBNS0PBFhRO0U9QRZtTGl1ThdRKVw6E0NPYikIFFk/KgJTazwrGSc2Gl5bKRhlRwoDMWICGQNBLgJUBB4sQGk3Rz0UZxgQWgVPLCMSUBEVIB4XD1k5TCt1Gl9RKRhCVhcaMCJGHRFBJ0JfFFEoTCw7Cj0UZxgQQQYbNz4IUFhUb0EXAx9jISgyAF5AMlxVOQYBJkZsXV0Vrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFZBoZZwseEzEqDwMyNSM/YkEXg6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkTVRfUAIDYh4DHR9BKh8XXBY2TBY2D1RcIhgNExgSbmw5FQZQIRhEQQttAiA5Tko+K1dTUg9PJDkIEwRcIAIXBEAoAj0mRh4+ZxgQEwoJYh4DHR9BKh8ZPlM7CSchHRdVKVwQYQYCLTgDA15qKhpSD0I+Qhk0HFJaMxhEWwYBYj4DBAVHIUxlBFsiGCwmQGhRMV1eRxBPJyICelAVb0xlBFsiGCwmQGhRMV1eRxBPf2wzBBlZPEJFBEUiAD8wPlZALxBzXA0JKytINSZwAThkPmYMOAF8ZBcUZxhCVhcaMCJGIhVYIBhSEhgSCT8wAENHTV1eV2kJNyIFBBlaIUxlBFsiGCwmQFBRMxBbVhpGSGxGUFBcKUxlBFsiGCwmQGhXJltYVjgEJzU7UBFbK0xlBFsiGCwmQGhXJltYVjgEJzU7XiBUPQlZFRY5BCw7TkVRM01CXUM9JyEJBBVGYTNUAFUlCRI+C05pZ11eV2lPYmxGHB9WLgAXD1cgCWloTnRbKV5ZVE09BwEpJDVmFAdSGGttAzt1BVJNTRgQE0MDLS8HHFBQOUwKQVM7CSchHR8dfBhZVUMBLThGFQYVOwRSDxY/CT0gHFkUKVFcEwYBJkZGUFAVIwNUAFptHmloTlJCfX5ZXQcpKz4VBDNdJgBTSVgsASx8ZBcUZxhZVUMdYjgOFR4VHQlaDkIoH2cKDVZXL11rWAYWH2xbUAIVKgJTaxZtTGknC0NBNVYQQWkKLChsFgVbLBheDlhtPiw4AUNRNBZWWhEKaicDCVwVYUIZSDxtTGl1AlhXJlQQQUNSYh4DHR9BKh8ZBlM5RCIwFx4PZ1FWEw0ANmwUUARdKgIXE1M5GTs7TlFVK0tVEwYBJkZGUFAVIwNUAFptDTsyHRcJZ0xRUQ8KbDwHExsdYUIZSDxtTGl1HFJAMkpeExMMIyAKWBZAIQ9DCFkjRGB1HA1yLkpVYAYdNCkUWARULQBST0MjHCg2BR9VNV9DH0NebmwHAhdGYQIeSBYoAi18ZFJaIzJWRg0MNiUJHlBnKgFYFVM+QiA7GFhfIhBbVhpDYmJIXlk/b0wXQVoiDyg5TkUUehhiVg4ANikVXhdQO0RcBE9kV2k8CBdaKEwQQUMbKikIUAJQOxlFDxYrDSUmCxdRKVw6E0NPYiAJExFZbw1FBkVtUWkhD1VYIhZAUgAEamJIXlk/b0wXQVoiDyg5TkVRNE1cRxBPf2wdUABWLgBbSVA4AiohB1habxEQQQYbNz4IUAIPBgJBDl0oPywnGFJGb0xRUQ8KbDkIABFWJERWE1E+QGlkQhdVNV9DHQ1Ga2wDHhQcbxE9QRZtTCAzTllbMxhCVhAaLjgVK0FobxhfBFhtHiwhG0VaZ15RXxAKYikIFHoVb0wXFVcvACx7HFJZKE5VGxEKMTkKBAMZb10eaxZtTGknC0NBNVYQRxEaJ2BGBBFXIwkZFFg9DSo+RkVRNE1cRxBGSCkIFHpTOgJUFV8iAmkHC1pbM11DHQAALCIDEwQdJAlOTRYrAmBfThcUZ1RfUAIDYj5GTVBnKgFYFVM+Qi4wGh9fIkEZOUNPYmwPFlBbIBgXExYiHmk7AUMUNRZ/XSADKykIBDVDKgJDQUIlCSd1HFJAMkpeEw0GLmwDHhQ/b0wXQUQoGDwnABdGaXdecA8GJyISNQZQIRgNIlkjAiw2Gh9SMlZTRwoALGRIXl4cRUwXQRZtTGl1AlhXJlQQXAhDYikUAlAIbxxUAFohRC87QhcaaRYZOUNPYmxGUFAVJgoXD1k5TCY+TkNcIlYQRAIdLGREKykHBDEXAlkjAiw2GhcWaRZbVhpBbG5cUFIbYRhYEkI/BScyRlJGNREZEwYBJkZGUFAVKgJTSDwoAi1fZBoZZ9qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4HoYYkwDTxYfIwYYTmVxFHd8ZjcmDQJsXV0Vrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFZFtbJFlcEzEALSFGTVBOMmY9TBttLSU5TmNDLktEVgdPFiMJHlBYIAhSDUVtBSd1Gl9RZ1tFQREKLDhGAh9aImZRFFguGCA6ABdmKFddHQQKNhgRGQNBKghESR9HTGl1TltbJFlcEwwaNmxbUAtIRUwXQRYhAyo0AhdGKFddE15PFSMUGwNFLg9SW3AkAi0TB0VHM3tYWg8Lam4lBQJHKgJDM1kiAWt8ZBcUZxhZVUMBLThGAh9aIkxDCVMjTDswGkJGKRhfRhdPJyICelAVb0xRDkRtM2V1ChddKRhZQwIGMD9OAh9aIlZwBEIJCTo2C1lQJlZEQEtGa2wCH3oVb0wXQRZtTCAzTlMODktxG0EiLSgDHFIcbxhfBFhHTGl1ThcUZxgQE0NPLiMFERwVIUwKQVJjIig4Cz0UZxgQE0NPYmxGUFAYYkx0DlsgAyd1AFZZLlZXCUNTDC0LFU54IAJEFVM/QGkYAVlHM11CQEMJLSACFQIVLAReDVI/CSd5TlhGZ1BRQEMiLSIVBBVHbw1DFUQkDjwhCz0UZxgQE0NPYmxGUFBcKUxZW1AkAi19THpbKUtEVhFNa2wJAlBRdStSFXc5GDs8DEJAIhASehAiLSIVBBVHbUUXDkRtRC17PlZGIlZEEwIBJmwCXiBUPQlZFRgDDSQwTgoJZxp9XA0cNikUA1IcbxhfBFhHTGl1ThcUZxgQE0NPYmxGUBxaLA1bQV4/HGloTlMOAVFeVyUGMD8SMxhcIwgfQ344ASg7AV5QFVdfRzMOMDhEWVBaPUxTT2Y/BSQ0HE5kJkpEOUNPYmxGUFAVb0wXQRZtTGk8CBdcNUgQRwsKLGwSERJZKkJeD0UoHj19AUJAaxhLEw4AJikKUE0VK0AXE1kiGGloTl9GNxQQXQICJ2xbUB4PKB9CAx5vISY7HUNRNRwSH0FNa2wbWVBQIQg9QRZtTGl1ThcUZxgQVg0LSGxGUFAVb0wXBFgpZml1ThdRKVw6E0NPYj4DBAVHIUxYFEJHCScxZD0ZahhxXw9PDy0FGBlbKkxaDlIoADp1GV5ALxhEWwYGMGwFHx1FIwlDCFkjTC00GlY+IU1eUBcGLSJGIh9aIkJQBEIADSo9B1lRNBAZOUNPYmwKHxNUI0xYFEJtUWkuEz0UZxgQXwwMIyBGAh9aIkwKQWEiHiImHlZXIgJ2Wg0LBCUUAwR2JwVbBR5vLzwnHFJaM2pfXA5Na0ZGUFAVJgoXD1k5TDs6AVoUM1BVXUMdJzgTAh4VIBlDQVMjCEN1ThcUIVdCEzxDYihGGR4VJhxWCEQ+RDs6AVoOAF1EdwYcISkIFBFbOx8fSB9tCCZfThcUZxgQE0MGJGwCSjlGDkQVLFkpCSV3RxdVKVwQGwdBDC0LFUpTJgJTSRQADSo9B1lRZREQXBFPJmIoER1QdQpeD1JlTg4wAFJGJkxfQUFGYiMUUBQPCAlDIEI5HiA3G0NRbxp5QC4OISQPHhUXZkUXFV4oAkN1ThcUZxgQE0NPYmwKHxNUI0xFDlk5THR1Cg1yLlZUdQodMTglGBlZKztfCFUlJToURhV2JktVYwIdNm5KUARHOgkeaxZtTGl1ThcUZxgQEwoJYj4JHwQVOwRSDzxtTGl1ThcUZxgQE0NPYmxGHB9WLgAXEVU5THR1Cg1zIkxxRxcdKy4TBBUdbS9YDEYhCT08AVlkIkpTVg0bIysDUlk/b0wXQRZtTGl1ThcUZxgQE0NPYmwJAlBRdStSFXc5GDs8DEJAIhASYxEAJT4DAwMXZmYXQRZtTGl1ThcUZxgQE0NPYmxGUB9HbwgNJlM5LT0hHF5WMkxVG0EsLSEWHBVBJgNZQx9HTGl1ThcUZxgQE0NPYmxGUARULQBST18jHywnGh9bMkwcExhlYmxGUFAVb0wXQRZtTGl1ThcUZxhdXAcKLmxbUBQZbx5YDkJtUWknAVhAaxheUg4KYnFGFF57LgFSTTxtTGl1ThcUZxgQE0NPYmxGUFAVbxxSE1UoAj11UxdEJEwcOUNPYmxGUFAVb0wXQRZtTGl1ThcUJFddQw8KNilGTVBRdStSFXc5GDs8DEJAIhAScAwCMiADBBVRbUUXXAttGDsgCxdbNRhUCSQKNg0SBAJcLRlDBB5vJToWAVpEK11EVgdNa2xbTVBBPRlSTTxtTGl1ThcUZxgQE0NPYmxGDVk/b0wXQRZtTGl1ThcUIlZUOUNPYmxGUFAVKgJTaxZtTGkwAFM+ZxgQExEKNjkUHlBaOhg9BFgpZkN4Qxd3JlZfXQoMIyBGGQRQIkxZAFsoH2kzHFhZZ2pVQw8GIS0SFRRmOwNFAFEoQgAhC1p5KFxFXwYcYq7m5FBAPAlTQUIiTCAxC1lALl5JOU5CYj8WEQdbKggXEV8uBzwlHRddKRhEWwZPITkUAhVbO0xFDlkgTGEhBlJNYEpVEw0OLykCUBVNLg9DDU9tACA+CxdAL10QXgwLNyADWV4/HQNYDBgEOAwYMXl1Cn1jE15POUZGUFAVBwlWDUIlJyAhTgoUM0pFVk9PEiMWUE0VOx5CBBptPzkwC1N3JlZUSkNSYjgUBRUZby5WD1IsCyx1UxdANU1VH2lPYmxGOR5GOx5CAkIkAycmTgoUM0pFVk9PEiMWMh9BOwBSQQttGDsgCxsUDU1dQwYdAS0EHBUVckxDE0MoQGkBD0dRZwUQRxEaJ2BsUFAVbzxFDkIoBScXD0UUehhEQRYKbmw1HR9eKi5YDFRtUWkhHEJRaxh1WQYMNg4TBARaIUwKQUI/GSx5TnRcKFtfXwIbJ2xbUARHOgkbaxZtTGkSG1pWJlRcE15PNj4TFVwVHBhYEUEsGCo9TgoUM0pFVk9PETgDERxBJy9WD1I0THR1GkVBIhQQYAgGLiAlGBVWJC9WD1I0THR1GkVBIhQ6E0NPYg0PAjhaPQIXXBY5HjwwQhdxP0xCUgAbKyMIIwBQKgh0AFgpFWloTkNGMl0cEzUOLjoDUE0VOx5CBBptLyE6DVhYJkxVcQwXYnFGBAJAKkA9QRZtTAYnAFZZIlZEE15PNj4TFVwVBQ1AA0QoDSIwHBcJZ0xCRgZDYh8SER1cIQ10AFgpFWloTkNGMl0cEyEALA4JHlAIbxhFFFNhZml1Thd3L0pZQBcCIz8lHx9eJgkXXBY5HjwwQhdwJlZUSiYOMTgDAjVSKB8XXBY5HjwwQj1JTTIdHkMuLiBGABlWJA1VDVNtBT0wA0QULlYQRwsKYi8TAgJQIRgXE1kiAUMzG1lXM1FfXUM9LSMLXhdQOyVDBFs+RGBfThcUZ1RfUAIDYiMTBFAIbxdKaxZtTGk5AVRVKxhCXAwCYnFGJx9HJB9HAFUoVg88AFNyLkpDRyAHKyACWFJ2Oh5FBFg5PiY6AxUdTRgQE0MGJGwIHwQVPQNYDBY5BCw7TkVRM01CXUMANzhGFR5RRUwXQRYhAyo0AhdHIl1eE15POTFsUFAVbwBYAlchTC8gAFRALldeExcdOw0CFFhRZmYXQRZtTGl1Tl5SZ1ZfR0MLYiMUUANQKgJsBWttGCEwABdGIkxFQQ1PJyICelAVb0wXQRZtHywwAGxQGhgNExcdNylsUFAVb0wXQRZgQWkYD0NXLxhSSkMKOi0FBFBcOwlaQVgsASx1IWUUJUEQQxEKMSkIExUVIAoXABYdHiYtB1pdM0FgQQwCMjhGWB1aPBgXEV8uBzwlHRdcJk5VEwwBJ2VsUFAVb0wXQRYhAyo0AhdZJkxTWwYcDC0LFVAIbz5YDltjJR0QI2h6BnV1YDgLbAIHHRVob1EKQUI/GSxfThcUZxgQE0MDLS8HHFBdLh9nE1kgHD11UxdQfX5ZXQcpKz4VBDNdJgBTNl4kDyEcHXYcZWhCXBsGLyUSCSBHIAFHFRRhTD0nG1IdZ0YNEw0GLkZGUFAVb0wXQVoiDyg5Tl5HE1dfXwocKmxbUBQPBh92SRQZAyY5TB4UKEoQV1koJzgnBARHJg5CFVNlTgAmJ0NRKhoZEwwdYihcNxVBDhhDE18vGT0wRhV9M11degdNa2wYTVBbJgA9QRZtTGl1ThddIRhdUhcMKikVPhFYKkxYExYkHx06AVtdNFAQXBFPaiQHAyBHIAFHFRYsAi11Cg19NHkYES4AJikKUlkcbxhfBFhHTGl1ThcUZxgQE0NPLiMFERwVPQNYFTxtTGl1ThcUZxgQE0MGJGwCSjlGDkQVNVkiAGt8TkNcIlYQQQwANmxbUBQPCQVZBXAkHjohLV9dK1wYESsOLCgKFVIcRUwXQRZtTGl1ThcUZ11cQAYGJGwCSjlGDkQVLFkpCSV3RxdAL11eExEALThGTVBRYTxFCFssHjAFD0VAZ1dCEwdVBCUIFDZcPR9DIl4kAC0CBl5XL3FDcktNAC0VFSBUPRgVTRY5HjwwRz0UZxgQE0NPYmxGUFBQIx9SCFBtCHMcHXYcZXpRQAY/Iz4SUlkVOwRSDxY/AyYhTgoUIxhVXQdlYmxGUFAVb0wXQRZtBS91HFhbMxhEWwYBSGxGUFAVb0wXQRZtTGl1ThdAJlpcVk0GLD8DAgQdIBlDTRY2Zml1ThcUZxgQE0NPYmxGUFAVb0wXDFkpCSV1UxdQaxhCXAwbYnFGAh9aO0A9QRZtTGl1ThcUZxgQE0NPYmxGUFBbLgFSQQttCGcbD1pRfV9DRgFHYGQ9EV1PEkUfOndgNhR8TBsUZR0BE0ZdYGVKUF0Yb05kEVMoCAo0AFNNZRjStfFPYB8WFRVRby9WD1I0TkN1ThcUZxgQE0NPYmxGUFAVMkU9QRZtTGl1ThcUZxgQVg0LSGxGUFAVb0wXBFgpZml1ThdRKVw6E0NPYmFLUCNWLgIXDFkpCSUmTlZaIxhEXAwDMWwHBFBQOQlFGBYpCTkhBhccLkxVXhBPLy0fUBJQbwVZQUU4DmQzAVtQIkpDGmlPYmxGFh9HbzMbQVJtBSd1B0dVLkpDGxEALSFcNxVBCwlEAlMjCCg7GkQcbhEQVwxlYmxGUFAVb0xeBxYpVgAmLx8WCldUVg9Na2wJAlBRdSVEIB5vOCY6AhUdZ0xYVg1PNj4fMRRRZwgeQVMjCEN1ThcUIlZUOUNPYmwUFQRAPQIXDkM5Ziw7Cj0+ahUQfBcHJz5GABxUNglFEhFtGCY6AEQUb11IUA8aJiUIF1BAPEU9B0MjDz08AVkUFVdfXk0IJzgpBBhQPThYDlg+RGBfThcUZ1RfUAIDYiMTBFAIbxdKaxZtTGk5AVRVKxhAXwIWJz4VUE0VGANFCkU9DSowVHFdKVx2WhEcNg8OGRxRZ05+D3EsASwFAlZNIkpDEUplYmxGUBlTbwJYFRY9ACgsC0VHZ0xYVg1PMCkSBQJbbwNCFRYoAi1fThcUZ15fQUMwbmwLUBlbbwVHAF8/H2ElAlZNIkpDCSQKNg8OGRxRPQlZSR9kTC06ZBcUZxgQE0NPKypGHUp8PC0fQ3siCCw5TB4UJlZUEw5BDC0LFVBLckx7DlUsABk5D05RNRZ+Ug4KYjgOFR4/b0wXQRZtTGl1ThcUK1dTUg9PKj4WUE0VIlZxCFgpKiAnHUN3L1FcV0tNCjkLER5aJghlDlk5PCgnGhUdTRgQE0NPYmxGUFAVbwBYAlchTCEgAxcJZ1UKdQoBJgoPAgNBDAReDVICCgo5D0RHbxp4Rg4OLCMPFFIcRUwXQRZtTGl1ThcUZ1FWEwsdMmwSGBVbbxhWA1ooQiA7HVJGMxBfRhdDYjdGHR9RKgAXXBYgQGknAVhAZwUQWxEfbmwIER1Qb1EXDBgDDSQwQhdcMlVRXQwGJmxbUBhAIkxKSBYoAi1fThcUZxgQE0MKLChsUFAVbwlZBTxtTGl1HFJAMkpeEwwaNkYDHhQ/RUEaQWIlCWkwAlJCJkxfQUMfLT8PBBlaIUwfBlc5CWkhARdaIkBEEwUDLSMUWXpTOgJUFV8iAmkHAVhZaV9VRyYDJzoHBB9HHwNESR9HTGl1TltbJFlcEwYDJzpGTVBiIB5cEkYsDyxvKF5aI35ZQRAbASQPHBQdbSlbBEAsGCYnHRUdTRgQE0MGJGwDHBVDbxhfBFhHTGl1ThcUZxhcXAAOLmwWUE0VKgBSFwwLBScxKF5GNExzWwoDJhsOGRNdBh92SRQPDTowPlZGMxocExcdNylPelAVb0wXQRZtBS91HhdAL11eExEKNjkUHlBFYTxYEl85BSY7TlJaIzIQE0NPJyICehVbK2Y9TBttjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2gOU5CYnlIUCNhDjhkaxtgTKvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo2kDLS8HHFBmOw1DEhZwTDJ1A1ZXL1FeVhArLSIDUE0Vf0AXCEIoAToFB1RfIlwQDkNfbmwDAxNUPwlTJkQsDjp1UxcEaxhUVgIbKj9GTVAFY0xEBEU+BSY7PUNVNUwQDkMbKy8NWFkVMmZRFFguGCA6ABdnM1lEQE0dJz8DBFgcbz9DAEI+QiQ0DV9dKV1DdwwBJ2BGIwRUOx8ZCEIoAToFB1RfIlwcEzAbIzgVXhVGLA1HBFIKHig3HRsUFExRRxBBJikHBBhGb1EXURp9QHl5XgwUFExRRxBBMSkVAxlaIT9DAEQ5THR1Gl5XLBAZEwYBJkYABR5WOwVYDxYeGCghHRlBN0xZXgZHa0ZGUFAVIwNUAFptH2loTlpVM1AeVQ8ALT5OBBlWJEQeQRttPz00GkQaNF1DQAoALB8SEQJBZmYXQRZtACY2D1sULxgNEw4ONiRIFhxaIB4fEhZiTHpjXgcdfBhDE15PMWxLUBgVZUwEVwZ9Zml1ThdYKFtRX0MCYnFGHRFBJ0JRDVkiHmEmThgUcQgZCENPYj9GTVBGb0EXDBZnTH9lZBcUZxhCVhcaMCJGAwRHJgJQT1AiHiQ0Gh8WYggCV1lKcn4CSlUFfQgVTRYlQGk4QhdHbjJVXQdlSGFLUJKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/EN4QxcCaRh1YDNPoMzyUCRCJh9DBFI+TGZ1I1ZXL1FeVhBPbWwvBBVYPEwYQWYhDTAwHEQ+ahUQ0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlRQBYAlchTAwGPhcJZ0M6E0NPYh8SEQRQb1EXGjxtTGl1ThcUZ0xHWhAbJyhGTVBTLgBEBBptASg2Bl5aIhgNEwUOLj8DXFBcOwlaQQttCig5HVIYZ0hcUhoKMGxbUBZUIx9STTxtTGl1ThcUZ0xHWhAbJygiGQNBLgJUBBZwTD0nG1IYTRgQE0NPYmxGAxhaOCNZDU8OACYmCxcJZ15RXxAKbmxGExxaPAllAFgqCWloTgEEazIQE0NPYmxGUARCJh9DBFIOAyU6HBcJZ3tfXwwdcWIAAh9YHSt1SQR4WWV1WAcYZw4AGk9lYmxGUFAVb0xaAFUlBScwLVhYKEoQDkMsLSAJAkMbKR5YDGQKLmFkXAcYZwoCA09Pc35WWVw/b0wXQRZtTGk8GlJZBFdcXBFPYmxGTVB2IABYEwVjCjs6A2VzBRACBlZDYn5WQFwVeVweTTxtTGl1ThcUZ0hcUhoKMA8JHB9Hb0wKQXUiACYnXRlSNVddYSQtanxKUEIEf0AXUwR0RWVfThcUZ0UcOUNPYmw5BBFSPEwKQU1tGD48HUNRIxgNExgSbmwLERNdJgJSQQttFzR5Tl5AIlUQDkMUP2BGABxUNglFQQttFzR1Exs+ZxgQEzwMLSIIUE0VNBEba0tHZiU6DVZYZ15FXQAbKyMIUB1UJAl1Ix4sCCYnAFJRaxhEVhsbbmwFHxxaPUAXCVMkCyEhRz0UZxgQXwwMIyBGEhIVckx+D0U5DSc2CxlaIk8YESEGLiAEHxFHKytCCBRkZml1ThdWJRZ+Ug4KYnFGUikHBDNyMmZvV2k3DBl1I1dCXQYKYnFGERRaPQJSBDxtTGl1DFUaFFFKVkNSYhkiGR0HYQJSFh59QGlkVgcYZwgcEwsKKysOBFBaPUwEUR9HTGl1TlVWaWtERgccDSoAAxVBb1EXN1MuGCYnXRlaIk8YA09PcWBGQFk/b0wXQVQvQgg5GVZNNHdeZwwfYnFGBAJAKlcXA1RjISgtKl5HM1leUAZPf2xXQEAFRUwXQRYhAyo0AhdYJlpVX0NSYgUIAwRUIQ9ST1goG2F3OlJMM3RRUQYDYGVsUFAVbwBWA1MhQgs0DVxTNVdFXQc7MC0IAwBUPQlZAk9tUWllQAM+ZxgQEw8OICkKXjJULAdQE1k4Ai0WAVtbNQsQDkMsLSAJAkMbKR5YDGQKLmFkXhsUdggcE1Ffa0ZGUFAVIw1VBFpjPyAvCxcJZ210Wg5dbCoUHx1mLA1bBB58QGlkRwwUK1lSVg9BACMUFBVHHAVNBGYkFCw5TgoUdzIQE0NPLi0EFRwbCQNZFRZwTAw7G1oaAVdeR00lNz4HS1BZLg5SDRgZCTEhPV5OIhgNE1JbSGxGUFBZLg5SDRgZCTEhLVhYKEoDE15PISMKHwIObwBWA1MhQh0wFkMUehhEVhsbeWwKERJQI0JnAEQoAj11UxdWJTIQE0NPLiMFERwVPBhFDl0oTHR1J1lHM1leUAZBLCkRWFJgBj9DE1kmCWt8ZBcUZxhDRxEAKSlIMx9ZIB4XXBYuAyU6HAwUNExCXAgKbBgOGRNeIQlEEhZwTHh7WwwUNExCXAgKbBwHAhVbO0wKQVosDiw5ZBcUZxhSUU0/Iz4DHgQVckxWBVk/AiwwZBcUZxhCVhcaMCJGEhIZbwBWA1MhZiw7Cj0+K1dTUg9PJDkIEwRcIAIXAlooDTsXG1RfIkwYURYMKSkSWXoVb0wXB1k/TBZ5TlVWZ1FeExMOKz4VWBJALAdSFR9tCCZfThcUZxgQE0MGJGwEElBUIQgXA1RjPCgnC1lAZ0xYVg1PIC5cNBVGOx5YGB5kTCw7Cj0UZxgQVg0LSCkIFHo/IwNUAFptCjw7DUNdKFYQRhMLIzgDMgVWJAlDSVQ4DyIwGhsULkxVXhBDYi8JHB9HY0xRDkQgDT0hC0UdTRgQE0MDLS8HHFBGKglZQQttFzRfThcUZ1RfUAIDYhNKUBhHP0wKQWM5BSUmQFFdKVx9SjcALSJOWXoVb0wXB1k/TBZ5TlIULlYQWhMOKz4VWBlBKgFESBYpA0N1ThcUZxgQExAKJyI9FV5HIANDPBZwTD0nG1I+ZxgQE0NPYmwKHxNUI0xVAxZwTCsgDVxRM2NVHREALTg7elAVb0wXQRZtBS91AFhAZ1pSExcHJyJGEhIVckxaAF0oLgt9CxlGKFdEH0MKbCIHHRUZbw9YDVk/RXJ1DEJXLF1EaAZBMCMJBC0VckxVAxYoAi1fThcUZxgQE0MDLS8HHFBZLg5SDRZwTCs3VHFdKVx2WhEcNg8OGRxRGAReAl4EHwh9TGNRP0x8UgEKLm5PelAVb0wXQRZtBS91AlZWIlQQRwsKLEZGUFAVb0wXQRZtTGk5AVRVKxhUWhAbSGxGUFAVb0wXQRZtTCAzTl9GNxhEWwYBYigPAwQVckxiFV8hH2cxB0RAJlZTVksHMDxIIB9GJhheDlhhTCx7HFhbMxZgXBAGNiUJHlkVKgJTaxZtTGl1ThcUZxgQEwoJYgk1IF5mOw1DBBg+BCYiIVlYPntcXBAKYi0IFFBRJh9DQVcjCGkxB0RAZwYQdjA/bB8SEQRQYQ9bDkUoPig7CVIUM1BVXWlPYmxGUFAVb0wXQRZtTGl1DFUaAlZRUQ8KJmxbUBZUIx9SaxZtTGl1ThcUZxgQEwYDMSlsUFAVb0wXQRZtTGl1ThcUZ1pSHSYBIy4KFRQVckxDE0MoZml1ThcUZxgQE0NPYmxGUFBZLg5SDRgZCTEhTgoUIVdCXgIbNikUUBFbK0xRDkQgDT0hC0UcIhQQVwocNmVGHwIVKkJZAFsoZml1ThcUZxgQE0NPYikIFHoVb0wXQRZtTCw7Cj0UZxgQVg0LSGxGUFBTIB4XE1kiGGV1DFUULlYQQwIGMD9OEgVWJAlDSBYpA0N1ThcUZxgQEwoJYiIJBFBGKglZOkQiAz0ITkNcIlY6E0NPYmxGUFAVb0wXCFBtDit1Gl9RKRhSUVkrJz8SAh9MZ0UXBFgpZml1ThcUZxgQE0NPYi4TExtQOzdFDlk5MWloTlldKzIQE0NPYmxGUBVbK2YXQRZtCScxZFJaIzI6VRYBITgPHx4VCj9nT0UoGB0iB0RAIlwYRUplYmxGUDVmH0JkFVc5CWchGV5HM11UE15PNEZGUFAVJgoXD1k5TD91Gl9RKRhTXwYOMA4TExtQO0RyMmZjMz00CUQaM09ZQBcKJmVdUDVmH0JoFVcqH2chGV5HM11UE15POTFGFR5RRQlZBTwrGSc2Gl5bKRh1YDNBMSkSPRFWJwVZBB47RUN1ThcUAmtgHTAbIzgDXh1ULAReD1NtUWkjZBcUZxhZVUMBLThGBlBBJwlZQVUhCSgnLEJXLF1EGyY8EmI5BBFSPEJaAFUlBScwRwwUAmtgHTwbIysVXh1ULAReD1NtUWkuExdRKVw6Vg0LSCoTHhNBJgNZQXMePGcmC0N9M11dGxVGSGxGUFBwHDwZMkIsGCx7B0NRKhgNExVlYmxGUBlTbwJYFRY7TD09C1kUJFRVUhEtNy8NFQQdCj9nT2k5DS4mQF5AIlUZCEMqERxILwRUKB8ZCEIoAWloTkxJZ11eV2kKLChsFgVbLBheDlhtKRoFQERRM2hcUhoKMGQQWXoVb0wXJGUdQhohD0NRaUhcUhoKMGxbUAY/b0wXQV8rTCc6GhdCZ0xYVg1PISADEQJ3Og9cBEJlKRoFQGhAJl9DHRMDIzUDAlkObylkMRgSGCgyHRlEK1lJVhFPf2wdDVBQIQg9BFgpZkMzG1lXM1FfXUMqERxIAwRUPRgfSDxtTGl1B1EUAmtgHTwMLSIIXh1UJgIXFV4oAmknC0NBNVYQVg0LSGxGUFBwHDwZPlUiAid7A1ZdKRgNEzEaLB8DAgZcLAkZKVMsHj03C1ZAfXtfXQ0KIThOFgVbLBheDlhlRUN1ThcUZxgQEwoJYgk1IF5mOw1DBBg5GyAmGlJQZ0xYVg1lYmxGUFAVb0wXQRZtGTkxD0NRBU1TWAYbagk1IF5qOw1QEhg5GyAmGlJQaxhiXAwCbCsDBCRCJh9DBFI+RGB5TnJnFxZjRwIbJ2ISBxlGOwlTIlkhAzt5TlFBKVtEWgwBailKUBQcRUwXQRZtTGl1ThcUZxgQE0MGJGwCUBFbK0xyMmZjPz00GlIaM09ZQBcKJggPAwRUIQ9SQUIlCSd1HFJAMkpeE0tNoNbGUFVGbzcSBUU5MWt8VFFbNVVRR0sKbCIHHRUZbwFWFV5jCiU6AUUcIxEZEwYBJkZGUFAVb0wXQRZtTGl1ThcUNV1ERhEBYm6E6tAVbUwZTxYoQic0A1I+ZxgQE0NPYmxGUFAVKgJTSDxtTGl1ThcUZ11eV2lPYmxGUFAVbwVRQXMePGcGGlZAIhZdUgAHKyIDUARdKgI9QRZtTGl1ThcUZxgQRhMLIzgDMgVWJAlDSXMePGcKGlZTNBZdUgAHKyIDXFBnIANaT1EoGAQ0DV9dKV1DG0pDYgk1IF5mOw1DBBggDSo9B1lRBFdcXBFDYioTHhNBJgNZSVNhTC18ZBcUZxgQE0NPYmxGUFAVb0xbDlUsAGkmTgoUZdqqqkNNYmJIUBUbIQ1aBDxtTGl1ThcUZxgQE0NPYmxGGRYVKkJUDls9ACwhCxdAL11eExBPf2xEkuymbyh4L3NvTCw7Cj0UZxgQE0NPYmxGUFAVb0wXCFBtCWclC0VXIlZEEwIBJmwIHwQVKkJUDls9ACwhCxdAL11eExBPf2xOUpKv1kwSBRNoTmBvCFhGKllEGw4ONiRIFhxaIB4fBBg9CTs2C1lAbhEQVg0LSGxGUFAVb0wXQRZtTGl1ThddIRhUExcHJyJGA1AIbx8XTxhtRGt1NRJQNExtEUpVJCMUHRFBZwFWFV5jCiU6AUUcIxEZEwYBJkZGUFAVb0wXQRZtTGl1ThcUNV1ERhEBYj9sUFAVb0wXQRZtTGl1C1lQbjIQE0NPYmxGUBVbK2YXQRZtTGl1Tl5SZ31jY008Ni0SFV5cOwlaQUIlCSdfThcUZxgQE0NPYmxGBQBRLhhSI0MuBywhRnJnFxZvRwIIMWIPBBVYY0xlDlkgQi4wGn5AIlVDG0pDYgk1IF5mOw1DBBgkGCw4LVhYKEocEwUaLC8SGR9bZwkbQVJkZml1ThcUZxgQE0NPYmxGUFBcKUxTQUIlCSd1HFJAMkpeE0tNoNvgUFVGbzcSBUU5MWt8VFFbNVVRR0sKbCIHHRUZbwFWFV5jCiU6AUUcIxEZEwYBJkZGUFAVb0wXQRZtTGl1ThcUNV1ERhEBYm6E5/YVbUwZTxYoQic0A1I+ZxgQE0NPYmxGUFAVKgJTSDxtTGl1ThcUZ11eV2lPYmxGUFAVbwVRQXMePGcGGlZAIhZAXwIWJz5GBBhQIWYXQRZtTGl1ThcUZxhFQwcONikkBRNeKhgfJGUdQhYhD1BHaUhcUhoKMGBGIh9aIkJQBEICGCEwHGNbKFZDG0pDYgk1IF5mOw1DBBg9ACgsC0V3KFRfQU9PJDkIEwRcIAIfBBptCGBfThcUZxgQE0NPYmxGUFAVbwBYAlchTCElTgoUIhZYRg4OLCMPFFBUIQgXDFc5BGczAlhbNRBVHQsaLy0IHxlRYSRSAFo5BGB1AUUUZRUSOUNPYmxGUFAVb0wXQRZtTGk8CBdQZ0xYVg1PMCkSBQJbb0QVg6HCTGwmTmwRNFBAH0NKJj8SLVIcdQpYE1ssGGEwQFlVKl0cExcAMTgUGR5SZwRHSBptASghBhlSK1dfQUsLa2VGFR5RRUwXQRZtTGl1ThcUZxgQE0MdJzgTAh4VbY6g7hZvTGd7TlIaKVldVmlPYmxGUFAVb0wXQRYoAi18ZBcUZxgQE0NPJyICelAVb0xSD1JkZiw7Cj0+ahUQ0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlRUEaQQFjTBoAPGF9EXl8EysqDhwjIiM/YkEXg6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkTVRfUAIDYh8TAgZcOQ1bQQttF2kGGlZAIhgNExhlYmxGUB5aOwVRCFM/KSc0DFtRIxgNEwUOLj8DXFBbIBheB18oHhs0AFBRZwUQAFZDYhMKEQNBDgBSE0IoCGloTgcYTRgQE0MOLDgPNwJULUwKQVAsADowQj0UZxgQUhYbLQ0QHxlRb1EXB1chHyx5TlZCKFFUYQIBJSlGTVAHekA9HBYwZkN4Qxd6KExZVQoKMGyE8OQVPhleAl1tAyd4HVRGIl1eEw0ANiUACVBCJwlZQVdtGD48HUNRIxhVXRcKMD9GAhFbKAk9DVkuDSV1CEJaJExZXA1PLy0NFT5aOwVRCFM/Kjs0A1IcbjIQE0NPKypGIwVHOQVBAFpjMyc6Gl5SPn9FWkMbKikIUAJQOxlFDxYeGTsjB0FVKxZvXQwbKyofNwVcbwlZBTxtTGl1AlhXJlQQQARPf2wvHgNBLgJUBBgjCT59TGRXNV1VXSQaK25PelAVb0xEBhgDDSQwTgoUZWECeCcOLCgfPh9BJgpeBERvZml1ThdHIBZiVhAKNgMIIwBUOAIXXBYrDSUmCz0UZxgQQARBGAUIFBVNDQlfAEAkAzt1UxdxKU1dHTkmLCgDCDJQJw1BCFk/Qho8DFtdKV86E0NPYj8BXiBUPQlZFRZwTAU6DVZYF1RRSgYdeBsHGQRzIB50CV8hCGF3PltVPl1CdBYGYGVsUFAVbwBYAlchTD05TgoUDlZDRwIBISlIHhVCZ05jBE45ICg3C1sWbjIQE0NPNiBIIxlPKkwKQWMJBSRnQFlRMBAAH0NccHxKUEAZb18BSDxtTGl1GlsaF1dDWhcGLSJGTVBgCwVaUxgjCT59XhkBaxgdAlVfbmxWXkENY0wHSDxtTGl1GlsaBVlTWAQdLTkIFCRHLgJEEVc/CSc2FxcJZwgeAVZlYmxGUARZYS5WAl0qHiYgAFN3KFRfQVBPf2wlHxxaPV8ZB0QiARsSLB8FdxQQAlNDYn5TWXoVb0wXFVpjKiY7GhcJZ31eRg5BBCMIBF5/Oh5WaxZtTGkhAhlgIkBEYAoVJ2xbUEEDRUwXQRY5AGcBC09ABFdcXBFcYnFGMx9ZIB4ET1A/AyQHKXUcdQ0FH0NZcmBGRkAcRUwXQRY5AGcBC09AZwUQEUFlYmxGUARZYTpeEl8vACx1UxdSJlRDVmlPYmxGBBwbHw1FBFg5THR1HVA+ZxgQEw8AIS0KUANBPQNcBBZwTAA7HUNVKVtVHQ0KNWREJTlmOx5YClNvRXJ1HUNGKFNVHSAALiMUUE0VDANbDkR+Qi8nAVpmAHoYAVZabmxQQFwVeVweWhY+GDs6BVIaE1BZUAgBJz8VUE0VfVcXEkI/AyIwQGdVNV1eR0NSYjgKelAVb0xbDlUsAGk2AUVaIkoQDkMmLD8SER5WKkJZBEFlThwcLVhGKV1CEUpUYi8JAh5QPUJ0DkQjCTsHD1NdMksQDkM6BiULXh5QOEQHTRZ7RXJ1DVhGKV1CHTMOMCkIBFAIbxhbaxZtTGkGG0VCLk5RX00wLCMSGRZMCBleQQttHy5fThcUZ2tFQRUGNC0KXi9bIBheB08BDSswAhcJZ0xcOUNPYmwUFQRAPQIXElFHCScxZD1SMlZTRwoALGw1BQJDJhpWDRg+CT0bAUNdIVFVQUsZa0ZGUFAVHBlFF187DSV7PUNVM10eXQwbKyoPFQJwIQ1VDVMpTHR1GD0UZxgQWgVPNGwSGBVbRUwXQRZtTGl1A1ZfInZfRwoJKykUNgJUIgkfSDxtTGl1ThcUZ1FWEzAaMDoPBhFZYTNUDlgjTD09C1kUNV1ERhEBYikIFHoVb0wXQRZtTBogHEFdMVlcHTwMLSIIUE0VHRlZMlM/GiA2Cxl8IllCRwEKIzhcMx9bIQlUFR4rGSc2Gl5bKRAZOUNPYmxGUFAVb0wXQV8rTCc6GhdnMkpGWhUOLmI1BBFBKkJZDkIkCiAwHHJaJlpcVgdPNiQDHlBHKhhCE1htCScxZBcUZxgQE0NPYmxGUBxaLA1bQWlhTCEnHhcJZ21EWg8cbCoPHhR4NjhYDlhlRUN1ThcUZxgQE0NPYmwPFlBbIBgXCUQ9TD09C1kUNV1ERhEBYikIFHoVb0wXQRZtTGl1ThdYKFtRX0MBJy0UFQNBY0xTCEU5THR1AF5YaxhdUhcHbCQTFxU/b0wXQRZtTGl1ThcUIVdCEzxDYjhGGR4VJhxWCEQ+RBs6AVoaIF1EZxQGMTgDFAMdZkUXBVlHTGl1ThcUZxgQE0NPYmxGUBxaLA1bQVJtUWkAGl5YNBZUWhAbIyIFFVhdPRwZMVk+BT08AVkYZ0weQQwANmI2HwNcOwVYDx9HTGl1ThcUZxgQE0NPYmxGUBlTbwgXXRYpBTohTkNcIlYQVwocNmxbUBQObwJSAEQoHz11UxdAZ11eV2lPYmxGUFAVb0wXQRYoAi1fThcUZxgQE0NPYmxGGRYVHBlFF187DSV7MVlbM1FWSi8OICkKUARdKgI9QRZtTGl1ThcUZxgQE0NPYiUAUB5QLh5SEkJtDScxTlNdNEwQD15PETkUBhlDLgAZMkIsGCx7AFhALl5ZVhE9IyIBFVBBJwlZaxZtTGl1ThcUZxgQE0NPYmxGUFAVHBlFF187DSV7MVlbM1FWSi8OICkKXiZcPAVVDVNtUWkhHEJRTRgQE0NPYmxGUFAVb0wXQRZtTGl1PUJGMVFGUg9BHSIJBBlTNiBWA1MhQh0wFkMUehgYEYH14mxDA1B7Ci1lQdTN+GlwChdHM01UQEFGeCoJAh1UO0RZBFc/CTohQFlVKl0cEw4ONiRIFhxaIB4fBV8+GGB8ZBcUZxgQE0NPYmxGUFAVb0xSDUUoZml1ThcUZxgQE0NPYmxGUFAVb0wXMkM/GiAjD1saGFZfRwoJOwAHEhVZYTpeEl8vACx1UxdSJlRDVmlPYmxGUFAVb0wXQRZtTGl1C1lQTRgQE0NPYmxGUFAVbwlZBTxtTGl1ThcUZ11eV0plYmxGUBVbK2ZSD1JHZmR4TnZaM1EdVBEOIGyE8OQVLhlDDhsrBTswHRdnNk1ZQQ4uICUKGQRMDA1ZAlMhTD49C1kUIEpRUQEKJkYABR5WOwVYDxYeGTsjB0FVKxZDVhcuLDgPNwJULURBSDxtTGl1PUJGMVFGUg9BETgHBBUbLgJDCHE/DSt1UxdCTRgQE0MGJGwQUBFbK0xZDkJtPzwnGF5CJlQebAQdIy4lHx5bbxhfBFhHTGl1ThcUZxgdHkMjKz8SFR4VKQNFQVE/DSt1C0FRKUwLExcHJ2wBER1QbwpeE1M+TB0iB0RAIlxjQhYGMCEhAhFXbxtfBFhtDyggCV9ATRgQE0NPYmxGHB9WLgAXBkQsDhsQTgoUEkxZXxBBMCkVHxxDKjxWFV5lThswHltdJFlEVgc8NiMUERdQYSlBBFg5H2cBGV5HM11UYBIaKz4LNwJULU4eaxZtTGl1ThcULl4QVBEOIB4jUBFbK0xQE1cvPgx7IVl3K1FVXRcqNCkIBFBBJwlZaxZtTGl1ThcUZxgQEzAaMDoPBhFZYTNQE1cvLyY7ABcJZ19CUgE9B2IpHjNZJglZFXM7CSchVHRbKVZVUBdHJDkIEwRcIAIfTxhjRUN1ThcUZxgQE0NPYmxGUFAVJgoXD1k5TBogHEFdMVlcHTAbIzgDXhFbOwVwE1cvTD09C1kUNV1ERhEBYikIFHoVb0wXQRZtTGl1ThcUZxgQRwIcKWIRERlBZ1wZUQNkZml1ThcUZxgQE0NPYmxGUFBnKgFYFVM+Qi88HFIcZWtBRgodLw8HHhNQI04eaxZtTGl1ThcUZxgQE0NPYmw1BBFBPEJSElUsHCwxKUVVJUsQDkM8Ni0SA15QPA9WEVMpKzs0DEQUbBgBOUNPYmxGUFAVb0wXQVMjCGBfThcUZxgQE0MKLChsUFAVbwlbElMkCmk7AUMUMRhRXQdPETkUBhlDLgAZPlE/DSsWAVlaZ0xYVg1lYmxGUFAVb0xkFEQ7BT80AhlrIEpRUSAALCJcNBlGLANZD1MuGGF8VRdnMkpGWhUOLmI5FwJULS9YD1htUWk7B1s+ZxgQEwYBJkYDHhQ/RUEaQXIoDT09TlRbMlZEVhFlECkLHwRQPEJUDlgjCSohRhVwIllEW0FDYioTHhNBJgNZSR9tPz00GkQaI11RRwscYnFGIwRUOx8ZBVMsGCEmThwUdhhVXQdGSEZLXVDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dlfQxoUfxYQfiIsCgUoNVB0Gjh4LHcZJQYbTtW00xhxRhcAYh8NGRxZby9fBFUmZmR4TtWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60kZLXVBhJwkXElM/GiwnTlNbIksKE0M8KSUKHBNdKg9cNEYpDT0wVH5aMVdbViADKykIBFhFIw1OBERhTC4wAFJGJkxfQU9PIz4BA1k/YkEXFl4oHix1D0VTNBhcXAwEMWwKGRtQbxcXFU89CWloThVXLkpTXwZNPm4SAhVUKwFeDVpvQGk3AUJaI1lCSjAGOClGTVB7Y0xDAEQqCT16HlhHLkxZXA1AISkIBBVHb1EXNRptQmd7Tko+ahUQZwsKYi8KGRVbO0xaFEU5TDswGkJGKRhREw0aLy4DAlBcIUxsURhjXRR1Gl9VMxhcUg0LMWwPHgNcKwkXFV4oTC4nC1JaZ0JfXQZlb2FGExVbOwlFBFJtAyd1OhdDLkxYEwsOLipLBxlROwQXA1k4Ai00HE5nLkJVHFFBSGFLel0Ybz9DE1c5CS4sVBdGIllUExcHJ2wSEQJSKhgXB18oAC11CEVbKhhRQQQcYmQRFVBBPRUXBEAoHjB1DVhZKldeEw0OLylPXnoYYkx+BxY6CWk2D1kTMxhWWg0LYiUSXFBTLgBbQVQsDyJ1GlgUJhhDRwIbKy9GBhFZOgkXFV4oTDwmC0UUJFleExcaLClIehxaLA1bQXssDyE8AFIUehhLEzAbIzgDUE0VNGYXQRZtDTwhAWRfLlRcUAsKISdGTVBTLgBEBBpHTGl1TlZBM1djWAoDLi8OFRNeCwlbAE9tUWllQj0UZxgQVQIDLi4HExtjLgBCBBZwTHl7WxsUZxgQHk5PLSIKCVBAPAlTQUElCSd1AFgUM1lCVAYbYioPFRxRbwVEQV8jTCgnCUQ+ZxgQEwcKIDkBIAJcIRgXQRZwTC80AkRRaxgQE05CYjwUGR5BPExWE1E+TCY7DVIUMFBVXUMbLSsBHBVRRRFKazxgQWkbIWNxfRhiXAEDLTRGFB9QPEx5LmJtDSU5AUAUNV1RVwoBJWwUFl56IS9bCFMjGAA7GFhfIhgYRBEGNilLHx5ZNkUZaxtgTB4wTlRVKR9EExAONClGBBhQbwNFCFEkAig5Tl9VKVxcVhFBYgUAUARdKkxQAFsoSzp1O34UNF1EQEMGNmBGHwVHPExACFohTDswHltVJF0QWhdlb2FGWBFbK0xBCFUoTD8wHERVbhYQZAIbISQCHxcVJRlEFRY/CWQ0HkdYLl1DEwwaMD9GFQZQPRUXURh4H2kiB0NcKE1EEwAHJy8NGR5SYWZbDlUsAGkKBlZaI1RVQSIMNiUQFVAIbwpWDUUoZiU6DVZYZ2dcUhAbBikEBRdhJgFSQQttXENfQxoUE0pZVhBPJzoDAgkVLANaDFkjTCc0A1IUIVdCExcHJ2xEBBFHKAlDQUYiHyAhB1haZRgfE0EMJyISFQIXbwpeBFopTCA7TlZGIEseOQ8AIS0KUBZAIQ9DCFkjTCwtGkVVJExkUhEIJzhOEQJSPEU9QRZtTCAzTkNNN10YUhEIMWVGDk0VbRhWA1ooTmkhBlJaZ0pVRxYdLGwIGRwVKgJTaxZtTGl4QxdwLkpVUBdPLDkLFQJcLExRCFMhCDpfThcUZ15fQUMwbmwNUBlbbwVHAF8/H2EuZBcUZxgQE0NPYDgHAhdQO04bQRQ5DTsyC0NkKEtZRwoALG5KUFJFIB9eFV8iAmt5ThVXIlZEVhFNbmxEExVbOwlFMVk+TmVfThcUZxgQE0NNJzQWFRNBKggVTRZvHCwnCFJXM2hfQAobKyMIUlwVbQReFWYiHyAhB1haZRQQEQ0KJygKFVIZRUwXQRZtTGl1TE1bKV1zVg0bJz5EXFAXLAVFAlooLyw7GlJGZRQQEQ4GJjwJGR5BbUAXQ0AsADwwTBs+ZxgQEx5GYigJelAVb0wXQRZtACY2D1sUMRgNEwIdJT89Gy0/b0wXQRZtTGk8CBdAPkhVGxVGYnFbUFJbOgFVBERvTD09C1kUNV1ERhEBYjpGFR5RRUwXQRYoAi1fThcUZxUdEzAALykSGR1QPExZBEU5CS11B1lHLlxVEwJPYDYJHhUXbwNFQRQvAzw7ClZGPhoQRwINLilsUFAVbwpYExYSQGk+Tl5aZ1FAUgodMWQdUFJPIAJSQxptTis6G1lQJkpJEU9PYD8NGRxZLARSAl1vQGl3HVxdK1RzWwYMKW5GDVkVKwM9QRZtTGl1ThdYKFtRX0McNy5GTVBUPQtEOl0QZml1ThcUZxgQWgVPNjUWFVhGOg4eQQtwTGshD1VYIhoQRwsKLEZGUFAVb0wXQRZtTGkzAUUUGBQQWFFPKyJGGQBUJh5ESU1tTiowAENRNRocE0EfLT8PBBlaIU4bQRQ5DTsyC0MWaxgSXgoLMiMPHgQXbxEeQVIiZml1ThcUZxgQE0NPYmxGUFBcKUxDGEYoRDogDGxfdWUZE15SYm4IBR1XKh4VQUIlCSd1HFJAMkpeExAaIBcNQi0VKgJTaxZtTGl1ThcUZxgQEwYBJkZGUFAVb0wXQVMjCEN1ThcUIlZUOUNPYmwUFQRAPQIXD18hZiw7Cj0+ahUQYxEKNjgfXQBHJgJDEhYsTD00DFtRZ0xfExcHJ2wFHx5GIABSQR4iAix1AlJCIlQQVwYKMmVsHB9WLgAXB0MjDz08AVkUI01dQyIdJT9OEQJSPEU9QRZtTCAzTkNNN10YUhEIMWVGDk0VbRhWA1ooTmkhBlJaZ0hCWg0bam49KUJ+byhWD1I0MWkmBV5YKxhTWwYMKWwHAhdGdU4bQVc/Czp8VRdGIkxFQQ1PJyICelAVb0xHE18jGGF3NW4GDBh0Ug0LOxFGTU0Ibx9cCFohTCo9C1RfZ1lCVBBPf3FbUlk/b0wXQVAiHmk+QhdCZ1FeExMOKz4VWBFHKB8eQVIiZml1ThcUZxgQWgVPNjUWFVhDZkwKXBZvGCg3AlIWZ0xYVg1lYmxGUFAVb0wXQRZtHDs8AEMcZRgQEU9PKWBGUk0VNE4eaxZtTGl1ThcUZxgQEwUAMGwNQlwVOV4XCFhtHCg8HEQcMREQVwxPMj4PHgQdbUwXQRZtTGt5TlwGaxgSDkFDYjpUWVBQIQg9QRZtTGl1ThcUZxgQQxEGLDhOUlAVMk4eaxZtTGl1ThcUIlRDVmlPYmxGUFAVb0wXQRY9HiA7Gh8WZxgSH0MEbmxETVIZbxobQRRlTmd7Gk5EIhBGGk1BYGVEWXoVb0wXQRZtTCw7Cj0UZxgQVg0LSCkIFHo/IwNUAFptCjw7DUNdKFYQXBYdEScPHBx2JwlUCn4sAi05C0UcN1RRSgYdbmwBFR5QPQ1DDkRhTCgnCUQdTRgQE0NCb2wiFRJAKExHE18jGGl9AVlRaktYXBdPMikUUARaKAtbBBY5A2k0GFhdIxhDQwICa0ZGUFAVJgoXLFcuBCA7CxlnM1lEVk0LJy4TFyBHJgJDQVcjCGl9Gl5XLBAZE05PHSAHAwRxKg5CBmIkASx8TgkUdhhEWwYBSGxGUFAVb0wXPlosHz0RC1VBIGxZXgZPf2wSGRNeZ0U9QRZtTGl1ThdQMlVAchEIMWQHAhdGZmYXQRZtCScxZD0UZxgQWgVPLCMSUD1ULAReD1NjPz00GlIaJk1EXDAEKyAKExhQLAcXFV4oAkN1ThcUZxgQE05CYh4DBAVHIQVZBhYjAz09B1lTZ1VRWAYcYjgOFVBGKh5BBERqH2lvJ1lCKFNVcA8GJyISUARdPQNAQdTN+Gk3G0MUMF0QWwIZJ2wIH3oVb0wXQRZtTGR4TkBVPhhEXEMJLT4REQJRbxhYQUIlCWk6HF5TLlZRX0MHIyICHBVHb0RlDlQhAzF1CFhGJVFUQEMdJy0CGR5SbyNZIlokCSchJ1lCKFNVGk1lYmxGUFAVb0waTBYeA2k8CBdNKE0QRAIBNmwSGBUVPQlQFFosHmkAJxdWJltbH0MbNz4IUARdKkxDDlEqACx1AVFSZ1leV0MdJyYJGR4bRUwXQRZtTGl1HFJAMkpeOUNPYmwDHhQ/RUwXQRYkCmkYD1RcLlZVHTAbIzgDXhFAOwNkCl8hACo9C1RfA11cUhpPfGxWUARdKgI9QRZtTGl1ThdAJktbHRQOKzhOPRFWJwVZBBgeGCghCxlVMkxfYAgGLiAFGBVWJChSDVc0RUN1ThcUIlZUOWlPYmxGXV0VCQVFEkJtGDssVBdGIkxFQQ1PNiQDUARUPQtSFRY5BCx1HVJGMV1CEwobMSkKFlBGKgJDQUM+Zml1ThdYKFtRX0MbIz4BFQQVckxSGUI/DSohOlZGIF1EGwIdJT9PelAVb0xeBxY5DTsyC0MUM1BVXUMdJzgTAh4VOw1FBlM5TCw7Cj0+ZxgQE05CYgoHHBxXLg9cQR4iAiUsTkJHIlwQRAsKLGwIH1BBLh5QBEJtCiAwAlMUIVdFXQdPKyJGEQJSPEU9QRZtTDswGkJGKRh9UgAHKyIDXiNBLhhST1AsACU3D1RfEVlcRgZlJyICenpZIA9WDRYrGSc2Gl5bKRhZXRAbIyAKOBFbKwBSEx5kZml1ThdYKFtRX0MdJGxbUCVBJgBET0QoHyY5GFJkJkxYG0E9JzwKGRNUOwlTMkIiHigyCxlxMV1eRxBBEScPHBxWJwlUCmM9CCghCxUdTRgQE0MGJGwIHwQVPQoXDkRtAiYhTkVSfXFDcktNECkLHwRQCRlZAkIkAyd3RxdAL11eExEKNjkUHlBTLgBEBBYoAi1fThcUZxUdEzQ9CxgjXT97AzUNQVgoGiwnTkVRJlwQQQVBDSIlHBlQIRh+D0AiByxfThcUZ0pWHSwBASAPFR5BBgJBDl0oTHR1AUJGFFNZXw8sKikFGzhUIQhbBERHTGl1TmhcJlZUXwYdAy8SGQZQb1EXFUQ4CUN1ThcUNV1ERhEBYjgUBRU/KgJTazwhAyo0AhdSMlZTRwoALGwVBBFHOztWFVUlCCYyRh4+ZxgQEwoJYgEHExhcIQkZPkEsGCo9ClhTZ0xYVg1PMCkSBQJbbwlZBTxtTGl1I1ZXL1FeVk0wNS0SExhRIAsXXBY5DTo+QEREJk9eGwUaLC8SGR9bZ0U9QRZtTGl1ThdDL1FcVkMiIy8OGR5QYT9DAEIoQiggGlhnLFFcXwAHJy8NUB9HbyFWAl4kAix7PUNVM10eVwYNNys2AhlbO0xTDjxtTGl1ThcUZxgQE0NCb2w0FV1CPQVDBBY5BCx1BlZaI1RVQUMfJz4PHxRcLA1bDU9tBSd1DVZHIhhEWwZPJS0LFVdGbzl+QUQoQTowGhddMxY6E0NPYmxGUFAVb0wXTBttOyx1DVZaYEwQUAsKISdGBxhabwNAD0VtBT11jLegZ09VEwkaMThGHwZQPRtFCEIoQkN1ThcUZxgQE0NPYmwPHgNBLgBbKVcjCCUwHB8dTRgQE0NPYmxGUFAVbxhWEl1jGyg8Gh8FaQgZOUNPYmxGUFAVKgJTaxZtTGl1ThcUCllTWwoBJ2I5BxFBLARTDlFtUWk7B1s+ZxgQEwYBJmVsFR5RRWZRFFguGCA6ABd5JltYWg0KbD8DBDFAOwNkCl8hACo9C1Rfb04ZOUNPYmwrERNdJgJST2U5DT0wQFZBM1djWAoDLi8OFRNeb1EXFzxtTGl1B1EUMRhEWwYBYiUIAwRUIwB/AFgpACwnRh4PZ0tEUhEbFS0SExhRIAsfSBYoAi1fC1lQTTJWRg0MNiUJHlB4Lg9fCFgoQjowGnNRJU1XYxEGLDhOBlk/b0wXQXssDyE8AFIaFExRRwZBJikEBRdlPQVZFRZwTD9fThcUZ1FWExVPNiQDHlBcIR9DAFohJCg7CltRNRAZCEMcNi0UBCdUOw9fBVkqRGB1C1lQTV1eV2llb2FGkuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdZmR4Tg4aZ3llZyxPEgUlOyVlRUEaQdTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh1zJcXAAOLmwnBQRaHwVUCkM9THR1FRdnM1lEVkNSYjdGAgVbIQVZBhZwTC80AkRRaxhCUg0IJ2xbUEEHY0xeD0IoHj80AhcJZwgeBkMSYjFsFgVbLBheDlhtLTwhAWddJFNFQ00cNi0UBFgcRUwXQRYkCmkUG0NbF1FTWBYfbB8SEQRQYR5CD1gkAi51Gl9RKRhCVhcaMCJGFR5RRUwXQRYMGT06Pl5XLE1AHTAbIzgDXgJAIQJeD1FtUWkhHEJRTRgQE0M6NiUKA15ZIANHSVA4AiohB1habxEQQQYbNz4IUDFAOwNnCFUmGTl7PUNVM10eWg0bJz4QERwVKgJTTTxtTGl1ThcUZ15FXQAbKyMIWFkVPQlDFEQjTAggGlhkLltbRhNBETgHBBUbPRlZD18jC2kwAFMYZ15FXQAbKyMIWFk/b0wXQRZtTGl1ThcUK1dTUg9PHWBGGAJFb1EXNEIkADp7CF5aI3VJZwwALGRPelAVb0wXQRZtTGl1Tl5SZ1ZfR0MHMDxGBBhQIUxFBEI4Hid1C1lQTRgQE0NPYmxGUFAVbwpYExYSQGk8GlJZZ1FeEwofIyUUA1hnIANaT1EoGAAhC1pHbxEZEwcASGxGUFAVb0wXQRZtTGl1ThddIRhlRwoDMWICGQNBLgJUBB4lHjl7PlhHLkxZXA1DYiUSFR0bPQNYFRgdAzo8Gl5bKREQD15PAzkSHyBcLAdCERgeGCghCxlGJlZXVkMbKikIelAVb0wXQRZtTGl1ThcUZxgQE0NPb2FGJxFZJExYF1M/TD09CxddM11dExEONiQDAlBBJw1ZQVIkHiw2GhdAIlRVQwwdNmwSH1BUOQNeBRY+HCwwChdSK1lXOUNPYmxGUFAVb0wXQRZtTGl1ThcUL0pAHSApMC0LFVAIby9xE1cgCWc7C0AcLkxVXk0dLSMSXiBaPAVDCFkjTGJ1OFJXM1dCAE0BJztOQFwVfUAXUR9kZml1ThcUZxgQE0NPYmxGUFAVb0wXMkIsGDp7B0NRKktgWgAEJyhGTVBmOw1DEhgkGCw4HWddJFNVV0NEYn1sUFAVb0wXQRZtTGl1ThcUZxgQE0MbIz8NXgdUJhgfURh8WWBfThcUZxgQE0NPYmxGUFAVbwlZBTxtTGl1ThcUZxgQE0MKLChsUFAVb0wXQRYoAi18ZFJaIzJWRg0MNiUJHlB0OhhYMV8uBzwlQERAKEgYGkMuNzgJIBlWJBlHT2U5DT0wQEVBKVZZXQRPf2wAERxGKkxSD1JHZmR4TtWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60kZLXVAEf0IXLHkbKQQQIGMUb0tRVQZPMC0IFxVGdExQAFsoTCE0HRdVZ0tVQRUKMGEVGRRQbx9HBFMpTCo9C1RfbjIdHkON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vw9DVkuDSV1I1hCIlVVXRdPf2wdUCNBLhhSQQttF0N1ThcUMFlcWDAfJykCUE0VflkbQVw4ATkFAUBRNRgNE1ZfbmwPHhZ/OgFHQQttCig5HVIYZ1ZfUA8GMmxbUBZUIx9STTxtTGl1CFtNZwUQVQIDMSlKUBZZNj9HBFMpTHR1WwcYZ1leRwouBAdGTVBBPRlSTRY+DT8wCmdbNBgNEw0GLmBsUFAVbw5OEVc+HxolC1JQBFlAE15PJC0KAxUZb0EaQV8rTDwmC0UUMFleRxBPKiUBGBVHbxhfAFhtPwgTK2h5BmBvYDMqBwhsDVwVEA9YD1htUWkuExdJTTJcXAAOLmwABR5WOwVYDxYsHDk5F39BKlleXAoLamVsUFAVbwBYAlchTBZ5TmgYZ1BFXkNSYhkSGRxGYQpeD1IAFR06AVkcbgMQWgVPLCMSUBhAIkxDCVMjTDswGkJGKRhVXQdlYmxGUBhAIkJgAFomPzkwC1MUehh9XBUKLykIBF5mOw1DBBg6DSU+PUdRIlw6E0NPYjwFERxZZwpCD1U5BSY7Rh4UL01dHSkaLzw2HwdQPUwKQXsiGiw4C1lAaWtEUhcKbCYTHQBlIBtSExYoAi18ZBcUZxhAUAIDLmQABR5WOwVYDx5kTCEgAxlhNF16Rg4fEiMRFQIVckxDE0MoTCw7Ch4+IlZUOQUaLC8SGR9bbyFYF1MgCSchQERRM29RXwg8MikDFFhDZmYXQRZtGmloTkNbKU1dUQYdajpPUB9Hb10CaxZtTGk8CBdaKEwQfgwZJyEDHgQbHBhWFVNjDjAlD0RHFEhVVgcsIzxGER5RbxoXXxYOAyczB1AaFHl2djwiAxQ5IyBwCigXFV4oAmkjTgoUBFdeVQoIbB8nNjVqAi1vPmUdKQwRTlJaIzIQE0NPDyMQFR1QIRgZMkIsGCx7GVZYLGtAVgYLYnFGBnoVb0wXAEY9ADAdG1pVKVdZV0tGSCkIFHpTOgJUFV8iAmkYAUFRKl1eR00cJzgsBR1FHwNABERlGmB1I1hCIlVVXRdBETgHBBUbJRlaEWYiGywnTgoUM1deRg4NJz5OBlkVIB4XVAZ2TCglHltND01dUg0AKyhOWVBQIQg9B0MjDz08AVkUCldGVg4KLDhIAxVBBgJRK0MgHGEjRz0UZxgQfgwZJyEDHgQbHBhWFVNjBSczJEJZNxgNExVlYmxGUBlTbxoXAFgpTCc6Ghd5KE5VXgYBNmI5Ex9bIUJeD1AHGSQlTkNcIlY6E0NPYmxGUFB4IBpSDFMjGGcKDVhaKRZZXQUlNyEWUE0VGh9SE38jHDwhPVJGMVFTVk0lNyEWIhVEOglEFQwOAyc7C1RAb15FXQAbKyMIWFk/b0wXQRZtTGl1ThcULl4QXQwbYgEJBhVYKgJDT2U5DT0wQF5aIXJFXhNPNiQDHlBHKhhCE1htCScxZBcUZxgQE0NPYmxGUBxaLA1bQWlhTBZ5Tl9BKhgNEzYbKyAVXhZcIQh6GGIiAyd9Rz0UZxgQE0NPYmxGUFBcKUxfFFttGCEwABdcMlUKcAsOLCsDIwRUOwkfJFg4AWcdG1pVKVdZVzAbIzgDJAlFKkJ9FFs9BScyRxdRKVw6E0NPYmxGUFBQIQgeaxZtTGkwAkRRLl4QXQwbYjpGER5RbyFYF1MgCSchQGhXKFZeHQoBJAYTHQAVOwRSDzxtTGl1ThcUZ3VfRQYCJyISXi9WIAJZT18jCgMgA0cOA1FDUAwBLCkFBFgcdEx6DkAoASw7GhlrJFdeXU0GLCosBR1Fb1EXD18hZml1ThdRKVw6Vg0LSCoTHhNBJgNZQXsiGiw4C1lAaUtVRy0AISAPAFhDZmYXQRZtISYjC1pRKUweYBcONilIHh9WIwVHQQttGkN1ThcULl4QRUMOLChGHh9BbyFYF1MgCSchQGhXKFZeHQ0AISAPAFBBJwlZaxZtTGl1ThcUCldGVg4KLDhILxNaIQIZD1kuACAlTgoUFU1eYAYdNCUFFV5mOwlHEVMpVgo6AFlRJEwYVRYBITgPHx4dZmYXQRZtTGl1ThcUZxhZVUMBLThGPR9DKgFSD0JjPz00GlIaKVdTXwofYjgOFR4VPQlDFEQjTCw7Cj0UZxgQE0NPYmxGUFBZIA9WDRYuBCgnTgoUC1dTUg8/Li0fFQIbDARWE1cuGCwnVRddIRheXBdPISQHAlBBJwlZQUQoGDwnABdRKVw6E0NPYmxGUFAVb0wXB1k/TBZ5TkcULlYQWhMOKz4VWBNdLh4NJlM5KCwmDVJaI1leRxBHa2VGFB8/b0wXQRZtTGl1ThcUZxgQEwoJYjxcOQN0Z051AEUoPCgnGhUdZ1leV0MfbA8HHjNaIwBeBVNtGCEwABdEaXtRXSAALiAPFBUVckxRAFo+CWkwAFM+ZxgQE0NPYmxGUFAVKgJTaxZtTGl1ThcUIlZUGmlPYmxGFRxGKgVRQVgiGGkjTlZaIxh9XBUKLykIBF5qLANZDxgjAyo5B0cUM1BVXWlPYmxGUFAVbyFYF1MgCSchQGhXKFZeHQ0AISAPAEpxJh9UDlgjCSohRh4PZ3VfRQYCJyISXi9WIAJZT1giDyU8HhcJZ1ZZX2lPYmxGFR5RRQlZBTwhAyo0AhdSMlZTRwoALGwVBBFHOypbGB5kZml1ThdYKFtRX0MwbmwOAgAZbwRCDBZwTBwhB1tHaV5ZXQciOxgJHx4dZlcXCFBtAiYhTl9GNxhfQUMBLThGGAVYbxhfBFhtHiwhG0VaZ11eV2lPYmxGHB9WLgAXA0BtUWkcAERAJlZTVk0BJztOUjJaKxVhBFoiDyAhFxUdfBhSRU0iIzQgHwJWKkwKQWAoDz06HAQaKV1HG1IKe2BXFUkZfgkOSA1tDj97OFJYKFtZRxpPf2wwFRNBIB4ET1goG2F8VRdWMRZgUhEKLDhGTVBdPRw9QRZtTCU6DVZYZ1pXE15PCyIVBBFbLAkZD1M6RGsXAVNNAEFCXEFGeWwEF154LhRjDkQ8GSx1UxdiIltEXBFcbCIDB1gEKlUbUFN0QHgwVx4PZ1pXHTNPf2xXFUQObw5QT2YsHiw7GhcJZ1BCQ2lPYmxGPR9DKgFSD0JjMyo6AFkaIVRJcTVDYgEJBhVYKgJDT2kuAyc7QFFYPnp3E15PIDpKUBJSRUwXQRYlGSR7PltVM15fQQ48Ni0IFFAIbxhFFFNHTGl1TnpbMV1dVg0bbBMFHx5bYQpbGGM9CCghCxcJZ2pFXTAKMDoPExUbHQlZBVM/Pz0wHkdRIwJzXA0BJy8SWBZAIQ9DCFkjRGBfThcUZxgQE0MGJGwIHwQVAgNBBFsoAj17PUNVM10eVQ8WYjgOFR4VPQlDFEQjTCw7Cj0UZxgQE0NPYiAJExFZbw9WDBZwTD46HFxHN1lTVk0sNz4UFR5BDA1aBEQsZml1ThcUZxgQXwwMIyBGHVAIbzpSAkIiHnp7AFJDbxE6E0NPYmxGUFBcKUxiElM/JSclG0NnIkpGWgAKeAUVOxVMCwNADx4IAjw4QHxRPntfVwZBFWVGUFAVb0wXQRY5BCw7TloUehhdE0hPIS0LXjNzPQ1aBBgBAyY+OFJXM1dCEwYBJkZGUFAVb0wXQV8rTBwmC0V9KUhFRzAKMDoPExUPBh98BE8JAz47RnJaMlUeeAYWASMCFV5mZkwXQRZtTGl1TkNcIlYQXkNSYiFGXVBWLgEZInA/DSQwQHtbKFNmVgAbLT5GFR5RRUwXQRZtTGl1B1EUEktVQSoBMjkSIxVHOQVUBAwEHwIwF3NbMFYYdg0aL2ItFQl2IAhST3dkTGl1ThcUZxgQRwsKLGwLUE0VIkwaQVUsAWcWKEVVKl0eYQoIKjgwFRNBIB4XBFgpZml1ThcUZxgQWgVPFz8DAjlbPxlDMlM/GiA2Cw19NHNVSicANSJONR5AIkJ8BE8OAy0wQHMdZxgQE0NPYmxGBBhQIUxaQQttAWl+TlRVKhZzdREOLylIIhlSJxhhBFU5Azt1C1lQTRgQE0NPYmxGGRYVGh9SE38jHDwhPVJGMVFTVlkmMQcDCTRaOAIfJFg4AWceC053KFxVHTAfIy8DWVAVb0wXFV4oAmk4TgoUKhgbEzUKITgJAkMbIQlASQZhTHh5TgcdZ11eV2lPYmxGUFAVbwVRQWM+CTscAEdBM2tVQRUGISlcOQN+KhVzDkEjRAw7G1oaDF1JcAwLJ2IqFRZBHAReB0JkTD09C1kUKhgNEw5Pb2wwFRNBIB4ET1goG2FlQhcFaxgAGkMKLChsUFAVb0wXQRYkCmk4QHpVIFZZRxYLJ2xYUEAVOwRSDxYgTHR1AxlhKVFEE0lPDyMQFR1QIRgZMkIsGCx7CFtNFEhVVgdPJyICelAVb0wXQRZtDj97OFJYKFtZRxpPf2wLelAVb0wXQRZtDi57LXFGJlVVE15PIS0LXjNzPQ1aBDxtTGl1C1lQbjJVXQdlLiMFERwVKRlZAkIkAyd1HUNbN35cSktGSGxGUFBTIB4XPhptB2k8ABddN1lZQRBHOW4AHAlgPwhWFVNvQGszAk52ERocEQUDOw4hUg0cbwhYaxZtTGl1ThcUK1dTUg9PIWxbUD1aOQlaBFg5QhY2AVlaHFNtOUNPYmxGUFAVJgoXAhY5BCw7ZBcUZxgQE0NPYmxGUBlTbxhOEVMiCmE2RxcJehgSYSE3ES8UGQBBDANZD1MuGCA6ABUUM1BVXUMMeAgPAxNaIQJSAkJlRWkwAkRRZ1sKdwYcNj4JCVgcbwlZBTxtTGl1ThcUZxgQE0MiLToDHRVbO0JoAlkjAhI+MxcJZ1ZZX2lPYmxGUFAVbwlZBTxtTGl1C1lQTRgQE0MDLS8HHFBqY0xoTRYlGSR1UxdhM1FcQE0JKyICPQlhIANZSR9HTGl1Tl5SZ1BFXkMbKikIUBhAIkJnDVc5CiYnA2RAJlZUE15PJC0KAxUVKgJTa1MjCEMzG1lXM1FfXUMiLToDHRVbO0JEBEILADB9GB4UCldGVg4KLDhIIwRUOwkZB1o0THR1GAwULl4QRUMbKikIUANBLh5DJ1o0RGB1C1tHIhhDRwwfBCAfWFkVKgJTQVMjCEMzG1lXM1FfXUMiLToDHRVbO0JEBEILADAGHlJRIxBGGkMiLToDHRVbO0JkFVc5CWczAk5nN11VV0NSYjgJHgVYLQlFSUBkTCYnTgIEZ11eV2kJNyIFBBlaIUx6DkAoASw7GhlHIkxxXRcGAwotWAYcRUwXQRYAAz8wA1JaMxZjRwIbJ2IHHgRcDip8QQttGkN1ThcULl4QRUMOLChGHh9BbyFYF1MgCSchQGhXKFZeHQIBNiUnNjsVOwRSDzxtTGl1ThcUZ3VfRQYCJyISXi9WIAJZT1cjGCAUKHwUehh8XAAOLhwKEQlQPUJ+BVooCHMWAVlaIltEGwUaLC8SGR9bZ0U9QRZtTGl1ThcUZxgQWgVPLCMSUD1aOQlaBFg5QhohD0NRaVleRwouBAdGBBhQIUxFBEI4Hid1C1lQTRgQE0NPYmxGUFAVbxxUAFohRC8gAFRALldeG0pPFCUUBAVUIzlEBER3LyglGkJGIntfXRcdLSAKFQIdZlcXN18/GDw0AmJHIkoKcA8GISckBQRBIAIFSWAoDz06HAUaKV1HG0pGYikIFFk/b0wXQRZtTGkwAFMdTRgQE0MKLj8DGRYVIQNDQUBtDScxTnpbMV1dVg0bbBMFHx5bYQ1ZFV8MKgJ1Gl9RKTIQE0NPYmxGUD1aOQlaBFg5QhY2AVlaaVleRwouBAdcNBlGLANZD1MuGGF8VRd5KE5VXgYBNmI5Ex9bIUJWD0IkLQ8eTgoUKVFcOUNPYmwDHhQ/KgJTa1A4AiohB1haZ3VfRQYCJyISXgNUOQlnDkVlRUN1ThcUK1dTUg9PHWBGGAJFb1EXNEIkADp7CF5aI3VJZwwALGRPS1BcKUxfE0ZtGCEwABd5KE5VXgYBNmI1BBFBKkJEAEAoCBk6HRcJZ1BCQ00/LT8PBBlaIVcXE1M5GTs7TkNGMl0QVg0LSCkIFHpTOgJUFV8iAmkYAUFRKl1eR00dJy8HHBxlIB8fSDxtTGl1B1EUCldGVg4KLDhIIwRUOwkZElc7CS0FAUQUM1BVXUM6NiUKA15BKgBSEVk/GGEYAUFRKl1eR008Ni0SFV5GLhpSBWYiH2BuTkVRM01CXUMbMDkDUBVbK2ZSD1JHICY2D1tkK1lJVhFBASQHAhFWOwlFIFIpCS1vLVhaKV1TR0sJNyIFBBlaIUQeaxZtTGkhD0RfaU9RWhdHcmJQWUsVLhxHDU8FGSQ0AFhdIxAZOUNPYmwPFlB4IBpSDFMjGGcGGlZAIhZWXxpPNiQDHlBGOw1FFXAhFWF8TlJaIzJVXQdGSEZLXVDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dm3+6fW0qjSpvON19yE5eDX2vzV9Kav+dlfQxoUdgkeEzUmERknPCM/YkEXg6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkTVRfUAIDYhoPAwVUIx8XXBY2TBohD0NRZwUQSEMJNyAKEgJcKARDQQttCig5HVIYZ1ZfdQwIYnFGFhFZPAkXHBptMys0DVxBNxgNExgSYjFsHB9WLgAXB0MjDz08AVkUJVlTWBYfDiUBGARcIQsfSDxtTGl1B1EUKV1IR0s5Kz8TERxGYTNVAFUmGTl8TkNcIlYQQQYbNz4IUBVbK2YXQRZtOiAmG1ZYNBZvUQIMKTkWXjJHJgtfFVgoHzp1ThcUehh8WgQHNiUIF153PQVQCUIjCTomZBcUZxhmWhAaIyAVXi9XLg9cFEZjLyU6DVxgLlVVE0NPYmxbUDxcKARDCFgqQgo5AVRfE1FdVmlPYmxGJhlGOg1bEhgSDig2BUJEaX9cXAEOLh8OERRaOB8XXBYBBS49Gl5aIBZ3XwwNIyA1GBFRIBtEaxZtTGkDB0RBJlRDHTwNIy8NBQAbCQNQJFgpTGl1ThcUZxgNEy8GJSQSGR5SYSpYBnMjCEN1ThcUEVFDRgIDMWI5EhFWJBlHT3AiCxohD0VAZxgQE0NPf2wqGRddOwVZBhgLAy4GGlZGMzJVXQdlJDkIEwRcIAIXN18+GSg5HRlHIkx2Rg8DID4PFxhBZxoeaxZtTGkDB0RBJlRDHTAbIzgDXhZAIwBVE18qBD11UxdCfBhSUgAENzwqGRddOwVZBh5kZml1ThddIRhGExcHJyJGPBlSJxheD1FjLjs8CV9AKV1DQENSYn9dUDxcKARDCFgqQgo5AVRfE1FdVkNSYn1SS1B5JgtfFV8jC2cSAlhWJlRjWwILLTsVUE0VKQ1bElNHTGl1TlJYNF06E0NPYmxGUFB5JgtfFV8jC2cXHF5TL0xeVhAcYnFGJhlGOg1bEhgSDig2BUJEaXpCWgQHNiIDAwMVIB4XUDxtTGl1ThcUZ3RZVAsbKyIBXjNZIA9cNV8gCWl1UxdiLktFUg8cbBMEERNeOhwZIloiDyIBB1pRZ1dCE1JbSGxGUFAVb0wXLV8qBD08AFAaAFRfUQIDESQHFB9CPEwKQWAkHzw0AkQaGFpRUAgaMmIhHB9XLgBkCVcpAz4mTkkJZ15RXxAKSGxGUFBQIQg9BFgpZi8gAFRALldeEzUGMTkHHAMbPAlDL1kLAy59GB4+ZxgQEzUGMTkHHAMbHBhWFVNjAiYTAVAUehhGCEMNIy8NBQB5JgtfFV8jC2F8ZBcUZxhZVUMZYjgOFR4VAwVQCUIkAi57KFhTAlZUE15PcylQS1B5JgtfFV8jC2cTAVBnM1lCR0NSYn0DRnoVb0wXBFo+CWkZB1BcM1FeVE0pLSsjHhQVckxhCEU4DSUmQGhWJltbRhNBBCMBNR5RbwNFQQd9XHluTntdIFBEWg0IbAoJFyNBLh5DQQttOiAmG1ZYNBZvUQIMKTkWXjZaKD9DAEQ5TCYnTgcUIlZUOQYBJkZsXV0Vrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFjKKkpa2g0fb/oNn2kuWlrfmng6PdjtzFZBoZZwkCHUM6C2yE8OQVIwNWBRYCDjo8Cl5VKW1ZE0s2cAdPUBFbK0xVFF8hCGkhBlIUMFFeVwwYSGFLUJKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/KvA/tWh19qlo4H60q7z4JKg346i8dTY/EMlHF5aMxAYETg2cAc7UDxaLgheD1FtIysmB1NdJlZlWkMJLT5GVQMVYUIZQx93CiYnA1ZAb3tfXQUGJWIhMT1wECJ2LHNkRUNfAlhXJlQQfwoNMC0UCVwVGwRSDFMADSc0CVJGaxhjUhUKDy0IERdQPWZbDlUsAGk6BWJ9ZwUQQwAOLiBOFgVbLBheDlhlRUN1ThcUC1FSQQIdO2xGUFAVb1EXDVksCDohHF5aIBBXUg4KeAQSBAByKhgfIlkjCiAyQGJ9GGp1YyxPbGJGUjxcLR5WE09jADw0TB4dbxE6E0NPYhgOFR1QAg1ZAFEoHmloTltbJlxDRxEGLCtOFxFYKlZ/FUI9KywhRnRbKV5ZVE06CxM0NSB6b0IZQRQsCC06AEQbE1BVXgYiIyIHFxVHYQBCABRkRWF8ZBcUZxhjUhUKDy0IERdQPUwXXBYhAygxHUNGLlZXGwQOLylcOARBPytSFR4OAyczB1AaEnFvYSY/DWxIXlAXLghTDlg+Qxo0GFJ5JlZRVAYdbCATEVIcZkQea1MjCGBfB1EUKVdEEwwEFwVGHwIVIQNDQXokDjs0HE4UM1BVXWlPYmxGBxFHIUQVOm9/J2kdG1VpZ35RWg8KJmwSH1BZIA1TQXkvHyAxB1ZaElEeEyINLT4SGR5SYU4eaxZtTGkKKRltdXNvdyIhBhU5OCV3ECB4IHIIKGloTlldKwMQQQYbNz4IehVbK2Y9DVkuDSV1IUdALldeQE9PFiMBFxxQPEwKQXokDjs0HE4aCEhEWgwBMWBGPBlXPQ1FGBgZAy4yAlJHTXRZUREOMDVINh9HLAl0CVMuBys6FhcJZ15RXxAKSEYKHxNUI0xRFFguGCA6ABd6KExZVRpHNiUSHBUZbwhSElVhTCwnHB4+ZxgQEy8GID4HAgkPAQNDCFA0RDJfThcUZxgQE0M7KzgKFVAVb0wXQRZwTCwnHBdVKVwQG0EqMD4JAlDXz84XQxZjQmkhB0NYIhEQXBFPNiUSHBUZRUwXQRZtTGl1KlJHJEpZQxcGLSJGTVBRKh9UQVk/TGt3Qj0UZxgQE0NPYhgPHRUVb0wXQRZtTHR1Whs+ZxgQEx5GSCkIFHo/IwNUAFptOyA7ClhDZwUQfwoNMC0UCUp2PQlWFVMaBScxAUAcPDIQE0NPFiUSHBUVb0wXQRZtTGl1ThcJZxp0Ug0LO2sVUCdaPQBTQRav7Ot1Tm4GDBh4RgFPYjpEUF4bby9YD1AkC2cGLWV9F2xvZSY9bkZGUFAVCQNYFVM/TGl1ThcUZxgQE0NSYm4/QjsVHA9FCEY5TAs0DVwGBVlTWENPoMzEUFAXb0IZQXUiAi88CRlzBnV1bC0uDwlKelAVb0x5DkIkCjAGB1NRZxgQE0NPYnFGUiJcKARDQxpHTGl1TmRcKE9zRhAbLSElBQJGIB4XXBY5HjwwQj0UZxgQcAYBNikUUFAVb0wXQRZtTGloTkNGMl0cOUNPYmwnBQRaHARYFhZtTGl1ThcUZwUQRxEaJ2BsUFAVbz5SEl83DSs5CxcUZxgQE0NPf2wSAgVQY2YXQRZtLyYnAFJGFVlUWhYcYmxGUFAIb10HTTwwRUNfAlhXJlQQZwINMWxbUAs/b0wXQWU4Hj88GFZYZwUQZAoBJiMRSjFRKzhWAx5vPzwnGF5CJlQSH0NPYD8OGRVZK04eTTxtTGl1I1ZXL1FeVhBPf2wxGR5RIBsNIFIpOCg3RhV5JltYWg0KMW5KUFAXOB5SD1UlTmB5ZBcUZxh5RwYCMWxGUFAIbzteD1IiG3MUClNgJloYESobJyEVUlwVb0wXQRQ9DSo+D1BRZREcOUNPYmw2HBFMKh4XQRZwTB48AFNbMAJxVwc7Iy5OUiBZLhVSExRhTGl1ThVBNF1CEUpDSGxGUFB4Jh9UQRZtTGloTmBdKVxfRFkuJigyERIdbSFeElVvQGl1ThcUZxpZXQUAYGVKelAVb0x0DlgrBS4mThcJZ29ZXQcANXYnFBRhLg4fQ3UiAi88CUQWaxgQE0ELIzgHEhFGKk4eTTxtTGl1PVJAM1FeVBBPf2wxGR5RIBsNIFIpOCg3RhVnIkxEWg0IMW5KUFAXPAlDFV8jCzp3Rxs+ZxgQEyAdJygPBAMVb1EXNl8jCCYiVHZQI2xRUUtNAT4DFBlBPE4bQRZtTiEwD0VAZREcOR5lSGFLUJKhz46j4dTZ7GkBL3UUdhjSs/dPERk0JjljDiAXg6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmehxaLA1bQWU4Hh03FnsUehhkUgEcbB8TAgZcOQ1bW3cpCAUwCENgJlpSXBtHa0YKHxNUI0xkFEQZGyAmGlJQZwUQYBYdFi4ePEp0KwhjAFRlTh0iB0RAIlwQdjA/YGVsHB9WLgAXMkM/IiYhB1FNZxgNEzAaMBgECDwPDghTNVcvRGsbAUNdIVFVQUFGSEY1BQJhOAVEFVMpVggxCntVJV1cGxhPFikeBFAIb05/CFElACAyBkNHZ11GVhEWYhgRGQNBKggXNVkiAmk8ABdAL10QUBYdMCkIBFBHIANaQUEkGCF1AFZZIhgbEwcGMTgHHhNQYU4bQXIiCToCHFZEZwUQRxEaJ2wbWXpmOh5jFl8+GCwxVHZQI3xZRQoLJz5OWXpmOh5jFl8+GCwxVHZQI2xfVAQDJ2RENSNlGxteEkIoCGt5TkwUE11IR0NSYm4yBxlGOwlTQXMePGt5TnNRIVlFXxdPf2wAERxGKkAXIlchACs0DVwUehh1YDNBMSkSJAdcPBhSBRYwRUMGG0VgMFFDRwYLeA0CFCRaKAtbBB5vKRoFOkBdNExVVycGMThEXFBObzhSGUJtUWl3PV9bMBhUWhAbIyIFFVIZbyhSB1c4AD11UxdANU1VH2lPYmxGMxFZIw5WAl1tUWkzG1lXM1FfXUsZa2wjIyAbHBhWFVNjGD48HUNRI3xZQBcOLC8DUE0VOUxSD1JtEWBfPUJGE09ZQBcKJnYnFBRhIAtQDVNlTgwGPmRcKE9/XQ8WASAJAxUXY0xMQWIoFD11UxcWD1FUVkMGJGwSHx8VKQ1FQxptKCwzD0JYMxgNEwUOLj8DXHoVb0wXNVkiAD08HhcJZxp/XQ8WYj4DHhRQPUxyMmZtCiYnTlJaM1FEWgYcYjsPBBhcIUx0DVk+CWkHD1lTIhYSH2lPYmxGMxFZIw5WAl1tUWkzG1lXM1FfXUsZa2wjIyAbHBhWFVNjHyE6GXhaK0FzXwwcJ2xbUAYVKgJTQUtkZhogHGNDLktEVgdVAygCIxxcKwlFSRQIPxkWAlhHImpRXQQKYGBGC1BhKhRDQQttTgo5AURRZ0pRXQQKYGBGNBVTLhlbFRZwTH9lQhd5LlYQDkNdcmBGPRFNb1EXUwZ9QGkHAUJaI1FeVENSYnxKUCNAKQpeGRZwTGt1HUMWazIQE0NPAS0KHBJULAcXXBYrGSc2Gl5bKRBGGkMqERxIIwRUOwkZAloiHywHD1lTIhgNExVPJyICUA0cRT9CE2I6BTohC1MOBlxUfwINJyBOUiRCJh9DBFJtDyY5AUUWbgJxVwcsLSAJAiBcLAdSEx5vKRoFOkBdNExVVyAALiMUUlwVNGYXQRZtKCwzD0JYMxgNEyY8EmI1BBFBKkJDFl8+GCwxLVhYKEocEzcGNiADUE0VbThACEU5CS11K2RkZ1tfXwwdYGBsUFAVby9WDVovDSo+TgoUIU1eUBcGLSJOE1kVCj9nT2U5DT0wQENDLktEVgcsLSAJAlAIbw8XBFgpTDR8ZD1nMkp+XBcGJDVcMRRRAw1VBFplF2kBC09AZwUQETMAMj9GEVBHKggXA1cjAiwnTllRJkoQRwsKYjgJAFBaKUxODkM/TDo2HFJRKRhHWwYBYi1GJAdcPBhSBRYoAj0wHEQUN0pfSwoCKzgfXlIZbyhYBEUaHiglTgoUM0pFVkMSa0Y1BQJ7IBheB093LS0xKl5CLlxVQUtGSB8TAj5aOwVRGAwMCC0BAVBTK10YES0ANiUAGRVHbUAXGhYZCTEhTgoUZWxHWhAbJyhGIAJaNwVaCEI0TAc6Gl5SLl1CEU9PBikAEQVZO0wKQVAsADowQhd3JlRcUQIMKWxbUCNAPRpeF1chQjowGnlbM1FWWgYdYjFPeiNAPSJYFV8rFXMUClNnK1FUVhFHYAIJBBlTJglFM1cjCyx3QhdPZ2xVSxdPf2xEJAJcKAtSExY/DScyCxUYZ3xVVQIaLjhGTVAGekAXLF8jTHR1XwcYZ3VRS0NSYn1UQFwVHQNCD1IkAi51UxcEaxhjRgUJKzRGTVAXbx9DQxpHTGl1TnRVK1RSUgAEYnFGFgVbLBheDlhlGmB1PUJGMVFGUg9BETgHBBUbIQNDCFAkCTsHD1lTIhgNExVPJyICUA0cRWZbDlUsAGkGG0VgJUBiE15PFi0EA15mOh5BCEAsAHMUClNmLl9YRzcOIC4JCFgcRQBYAlchTBogHHZaM1F3QQINYnFGIwVHGw5PMwwMCC0BD1UcZXleRwpCBT4HElIcRQBYAlchTBogHHRbI11DE0NPYnFGIwVHGw5PMwwMCC0BD1UcZXtfVwYcYGVseiNAPS1ZFV8KHig3VHZQI3RRUQYDajdGJBVNO0wKQRQMGT06A1ZALltRXw8WYj8XBRlHIkFUAFguCSUmTkBcIlYQUkM7NSUVBBVRbwtFAFQ+TDA6GxkUFE1CRQoZIyBGHBlTKh9WF1M/Qmt5TnNbIktnQQIfYnFGBAJAKkxKSDweGTsUAENdAEpRUVkuJigiGQZcKwlFSR9HPzwnL1lALn9CUgFVAygCJB9SKABSSRQMAj08KUVVJRocExhPFikeBFAIb052FEIiTBokG15GKhVzUg0MJyBGHx4VKB5WAxRhTA0wCFZBK0wQDkMJIyAVFVw/b0wXQWIiAyUhB0cUehgSdQodJz9GBBhQbz9GFF8/AQg3B1tdM0FzUg0MJyBGAhVYIBhSQUIlCWk4AVpRKUwQSgwaYisDBFBSPQ1VA1MpQmt5ZBcUZxhzUg8DIC0FG1AIbz9CE0AkGig5QERRM3leRwooMC0EUA0cRWZkFEQOAy0wHQ11I1x8UgEKLmQdUCRQNxgXXBZvPiwxC1JZZ1FeHgQOLylGEx9RKh8ZQXQ4BSUhQ15aZ1RZQBdPMCkAAhVGJwlEQVkuDygmB1haJlRcSk1NbmwiHxVGGB5WERZwTD0nG1IUOhE6YBYdASMCFQMPDghTJV87BS0wHB8dTWtFQSAAJikVSjFRKy5CFUIiAmEuTmNRP0wQDkNNECkCFRVYby17LRYvGSA5GhpdKRhTXAcKMW5KUDZAIQ8XXBYrGSc2Gl5bKRAZOUNPYmwAHwIVEEAXAlkpCWk8ABddN1lZQRBHASMIFhlSYS94JXMeRWkxAT0UZxgQE0NPYh4DHR9BKh8ZCFg7AyIwRhV3KFxVdhUKLDhEXFBWIAhSSDxtTGl1ThcUZ0xRQAhBNS0PBFgFYVgeaxZtTGkwAFM+ZxgQEy0ANiUACVgXDANTBEVvQGl3OkVdIlwQEUNBbGxFMx9bKQVQT3UCKAwGThkaZxoQUAwLJz9IUlk/KgJTQUtkZhogHHRbI11DCSILJgUIAAVBZ050FEU5AyQWAVNRZRQQSEM7JzQSUE0VbS9CEkIiAWk2AVNRZRQQdwYJIzkKBFAIb04VTRYdACg2C19bK1xVQUNSYm4FHxRQbwRSE1NvQGkWD1tYJVlTWENSYioTHhNBJgNZSR9tCScxTkodTWtFQSAAJikVSjFRKy5CFUIiAmEuTmNRP0wQDkNNECkCFRVYbw9CEkIiAWk2AVNRZRQQdRYBIWxbUBZAIQ9DCFkjRGBfThcUZ1RfUAIDYi8JFBUVckx4EUIkAycmQHRBNExfXiAAJilGER5RbyNHFV8iAjp7LUJHM1ddcAwLJ2IwERxAKkxYExZvTkN1ThcULl4QUAwLJ2xbTVAXbUxDCVMjTAc6Gl5SPhAScAwLJ25KUFJwIhxDGBRhTD0nG1IdfBhCVhcaMCJGFR5RRUwXQRYfCSQ6GlJHaVFeRQwEJ2REMx9RKilBBFg5TmV1DVhQIhELEy0ANiUACVgXDANTBBRhTGsBHF5RIwIQEUNBbGwFHxRQZmZSD1JtEWBfZBoZZ9qks4H7wq7y8FBhDi4XUxav7N11I3Z3D3F+djBPoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0TVRfUAIDYgEHExh5b1EXNVcvH2cYD1RcLlZVQFkuJigqFRZBCB5YFEYvAzF9THpVJFBZXQZPBx82UlwVbRtFBFguBGt8ZHpVJFB8CSILJgAHEhVZZxcXNVM1GGloThV8Ll9YXwoIKjgVUBVDKh5OQVssDyE8AFIUMFFEW0MGNj9GEx9YPwBSFV8iAmlwQBUYZ3xfVhA4MC0WUE0VOx5CBBYwRUMYD1RcCwJxVwcrKzoPFBVHZ0U9LFcuBAVvL1NQE1dXVA8Kam4jIyB4Lg9fCFgoTmV1FRdgIkBEE15PYAEHExhcIQkXJGUdTmV1KlJSJk1cR0NSYioHHANQY0x0AFohDig2BRcJZ31jY00cJzgrERNdJgJSQUtkZgQ0DV94fXlUVy8OICkKWFJ4Lg9fCFgoTCo6AlhGZREKcgcLASMKHwJlJg9cBERlTgwGPnpVJFBZXQYsLSAJAlIZbxc9QRZtTA0wCFZBK0wQDkMqERxIIwRUOwkZDFcuBCA7C3RbK1dCH0M7KzgKFVAIb056AFUlBScwTnJnFxhTXA8AMG5KelAVb0x0AFohDig2BRcJZ15FXQAbKyMIWBMcbylkMRgeGCghCxlZJltYWg0KASMKHwIVckxUQVMjCGkoRz0+K1dTUg9PDy0FGCIVckxjAFQ+QgQ0DV9dKV1DCSILJh4PFxhBCB5YFEYvAzF9THZBM1cQQAgGLiBGExhQLAcVTRZvBywsTB4+CllTWzFVAygCPBFXKgAfGhYZCTEhTgoUZWpVUgccYjgOFVBGKh5BBERqH2khD0VTIkwQVREAL2wSGBUVPAdeDVpgDyEwDVwUJkpXQEMOLChGAhVBOh5ZEhYkGGd1OVZAJFBUXARPMClLGR5GOw1bDUVtBS91Gl9RZ19RXgZPMCkVFQRGbwVDTxRhTA06C0RjNVlAE15PNj4TFVBIZmZ6AFUlPnMUClNwLk5ZVwYdamVsPRFWJz4NIFIpOCYyCVtRbxpxRhcAEScPHBx2JwlUChRhTDJ1OlJMMxgNE0EuNzgJUCNeJgBbQXUlCSo+TBsUA11WUhYDNmxbUBZUIx9STTxtTGl1OlhbK0xZQ0NSYm4nBQRaYhxWEkUoH2k2B0VXK10QUg0LYjgUFRFRIgVbDRY+ByA5AhdXL11TWBBPIDVGAhVBOh5ZCFgqTD09CxdHIkpGVhFIMWwJBx4VOw1FBlM5TD80AkJRaRocOUNPYmwlERxZLQ1UChZwTAQ0DV9dKV0eQAYbAzkSHyNeJgBbAl4oDyJ1Ex4+CllTWzFVAygCIxxcKwlFSRQLDSU5DFZXLG5RXxYKYGBGC1BhKhRDQQttTg80AltWJltbExUOLjkDUFhcKUxZDhY5DTsyC0MULlYQUhEIMWVEXFBxKgpWFFo5THR1XhkBaxh9Wg1Pf2xWXkAZbyFWGRZwTHh7XhsUFVdFXQcGLCtGTVAHY2YXQRZtOCY6AkNdNxgNE0EgLCAfUAVGKggXCFBtGyx1DVZaYEwQUhYbLWECFQRQLBgXFV4oTD00HFBRMxYQZxEWYnxIQ1Aab1wZVBZiTHl7WRddIRhZR0MCKz8VFQMbbUA9QRZtTAo0AltWJltbE15PJDkIEwRcIAIfFx9tISg2Bl5aIhZjRwIbJ2IAERxZLQ1UCmAsADwwTgoUMRhVXQdPP2VsPRFWJz4NIFIpPyU8ClJGbxpjWAoDLg8OFRNeCwlbAE9vQGkuTmNRP0wQDkNNECkVAB9bPAkXBVMhDTB3QhdwIl5RRg8bYnFGQFwVAgVZQQttXGdlQhd5JkAQDkNebHlKUCJaOgJTCFgqTHR1XBsUFE1WVQoXYnFGUlBGbUA9QRZtTB06AVtALkgQDkNNEi0TAxUVLQlRDkQoTCg7HUBRNVFeVE1PcmxbUBlbPBhWD0JjTmVfThcUZ3tRXw8NIy8NUE0VKRlZAkIkAyd9GB4UCllTWwoBJ2I1BBFBKkJWFEIiPyI8AltXL11TWCcKLi0fUE0VOUxSD1JtEWBfI1ZXL2oKcgcLBiUQGRRQPUQea3ssDyEHVHZQI2xfVAQDJ2RENBVXOgtkCl8hAAo9C1RfZRQQSEM7JzQSUE0VbZyo8a1tKCw3G1AOZ0hCWg0bYi0UFwMVOwMXAlkjHyY5CxUYZ3xVVQIaLjhGTVBTLgBEBBpHTGl1TmNbKFREWhNPf2xEIAJcIRhEQUIlCWkmBV5YKxVTWwYMKWwHAhdGb0RHE1M+H2kTVxdAKBhDVgZGbGwzAxUVOwReEhYiAiowTkNbZ1RVUhEBYjgOFVBBLh5QBEJtCiAwAlMUKVldVk9PNiQDHlBBOh5ZQVkrCmd3Qj0UZxgQcAIDLi4HExsVckx6AFUlBScwQERRM3xVURYIEj4PHgQVMkU9LFcuBBtvL1NQBU1ERwwBajdGJBVNO0wKQRQfCWQ8AERAJlRcEwsALSdGHh9CbUA9QRZtTB06AVtALkgQDkNNBCMUExUVPQkaAEY9ADB1B1EULkwQQBcAMjwDFFBCIB5cCFgqTCgzGlJGZ1kQQQYcMi0RHl4XY2YXQRZtKjw7DRcJZ15FXQAbKyMIWFk/b0wXQRZtTGkYD1RcLlZVHRAKNg0TBB9mJAVbDVUlCSo+RlFVK0tVGlhPNi0VG15CLgVDSQZjXHx8VRd5JltYWg0KbD8DBDFAOwNkCl8hACo9C1Rfb0xCRgZGSGxGUFAVb0wXL1k5BS8sRhVnLFFcX0MsKikFG1IZb05lBBslAyY+C1MaZRE6E0NPYikIFFBIZmY9TBttjt3VjKO0paywEzcuAGxVUJK120x+NXMAP2m3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rc+K1dTUg9PCzgLPFAIbzhWA0VjJT0wA0QOBlxUfwYJNgsUHwVFLQNPSRQEGCw4TnJnFxocE0EfIy8NERdQbUU9KEIgIHMUClN4JlpVX0sUYhgDCAQVckwVKV8qBCU8CV9ANBhVRQYdO2wWGRNeLg5bBBYkGCw4Tl5aZ0xYVkMMNz4UFR5Bbx5YDltjTmV1KlhRNG9CUhNPf2wSAgVQbxEea385AQVvL1NQA1FGWgcKMGRPejlBIiANIFIpOCYyCVtRbxp1YDMmNikLUlwVNExjBE45THR1TH5AIlUQdjA/YGBGNBVTLhlbFRZwTC80AkRRaxhzUg8DIC0FG1AIbylkMRg+CT0cGlJZZ0UZOSobLwBcMRRRAw1VBFplTgAhC1oUJFdcXBFNa3YnFBR2IABYE2YkDyIwHB8WAmtgehcKLw8JHB9HbUAXGjxtTGl1KlJSJk1cR0NSYgk1IF5mOw1DBBgkGCw4LVhYKEocEzcGNiADUE0VbSVDBFttKRoFTlRbK1dCEU9lYmxGUDNUIwBVAFUmTHR1CEJaJExZXA1HIWVGNSNlYT9DAEIoQiAhC1p3KFRfQUNSYi9GFR5RbxEeazwhAyo0Ahd9M1ViE15PFi0EA158OwlaEgwMCC0HB1BcM39CXBYfICMeWFJ0OhhYQUYkDyIgHhUYZxpDUhUKYGVsOQRYHVZ2BVIBDSswAh9PZ2xVSxdPf2xEJxFZJB8XFVltAiw0HFVNZ1FEVg4cYi0IFFBSPQ1VEhY5BCw4QBdmJlZXVkMGMWwFHx5GKh5BAEIkGix1DE4UI11WUhYDNmJEXFBxIAlENkQsHGloTkNGMl0QTkplCzgLIkp0KwhzCEAkCCwnRh4+DkxdYVkuJigyHxdSIwkfQ3c4GCYFB1RfMkgSH0MUYhgDCAQVckwVIEM5A2kFB1RfMkgQXQYOMC4fUBlBKgFEQxptKCwzD0JYMxgNEwUOLj8DXHoVb0wXIlchACs0DVwUehhWRg0MNiUJHlhDZkxeBxY7TD09C1kUBk1EXDMGIScTAF5GOw1FFR5kTCw5HVIUBk1EXDMGIScTAF5GOwNHSR9tCScxTlJaIxhNGmkmNiE0SjFRKz9bCFIoHmF3Pl5XLE1AYQIBJSlEXFBObzhSGUJtUWl3Pl5XLE1AExEOLCsDUlwVCwlRAEMhGGloTgYGaxh9Wg1Pf2xTXFB4LhQXXBZ1XGV1PFhBKVxZXQRPf2xWXFBmOgpRCE5tUWl3TkRAZRQ6E0NPYg8HHBxXLg9cQQttCjw7DUNdKFYYRUpPAzkSHyBcLAdCERgeGCghCxlGJlZXVkNSYjpGFR5RbxEea385ARtvL1NQFFRZVwYdam42GRNeOhx+D0IoHj80AhUYZ0MQZwYXNmxbUFJ2JwlUChYkAj0wHEFVKxocEycKJC0THAQVckwHTwNhTAQ8ABcJZwgeAU9PDy0eUE0VekAXM1k4Ai08AFAUehgCH0M8NyoAGQgVckwVQUVvQEN1ThcUBFlcXwEOISdGTVBTOgJUFV8iAmEjRxd1MkxfYwoMKTkWXiNBLhhST18jGCwnGFZYZwUQRUMKLChGDVk/RUEaQdTZ7KvB7tWgxxhkciFPdmyE8OQVHyB2OHMfTKvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7KvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7KvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7KvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7KvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7KvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7KvB7tWgx9qks4H7wq7y8JKhz46j4dTZ7EM5AVRVKxhgXxE7IDQqUE0VGw1VEhgdACgsC0UOBlxUfwYJNhgHEhJaN0Qea1oiDyg5TnpbMV1kUgFPf2w2HAJhLRR7W3cpCB00DB8WCldGVg4KLDhEWXpZIA9WDRYbBToBD1UUZwUQYw8dFi4ePEp0KwhjAFRlTh88HUJVK0sSGmllDyMQFSRULVZ2BVIBDSswAh9PZ2xVSxdPf2xEkuqVbytWDFNtBCgmTlYUNF1CRQYdbz8PFBUVPBxSBFJtDyEwDVwaZ3xVVQIaLjgVUANBLhUXFFgpCTt1Gl9RZ0xYQQYcKiMKFF4XY0xzDlM+Ozs0HhcJZ0xCRgZPP2VsPR9DKjhWAwwMCC0RB0FdI11CG0plDyMQFSRULVZ2BVIeACAxC0UcZW9RXwg8MikDFFIZbxcXNVM1GGloThVjJlRbEzAfJykCUlwVCwlRAEMhGGloTgYBaxh9Wg1Pf2xXRVwVAg1PQQttXnt5TmVbMlZUWg0IYnFGQFwVHBlRB181THR1TBdHM01UQEwcYGBsUFAVbzhYDlo5BTl1UxcWFFlWVkMdIyIBFVBcPExCERY5A2l3ThkaZ3tfXQUGJWI1MTZwECF2OWkePAwQKhcaaRgSHUMoIyEDUBRQKQ1CDUJtBTp1XwIaZRQ6E0NPYg8HHBxXLg9cQQttISYjC1pRKUweQAYbFS0KGyNFKglTQUtkZgQ6GFJgJloKcgcLFiMBFxxQZ051GEYsHzoGHlJRI3tRQ0FDYjdGJBVNO0wKQRQMACU6GRdGLktbSkMcMikDFAMVZ1IFUx9vQGkRC1FVMlREE15PJC0KAxUZbz5eEl00THR1GkVBIhQ6E0NPYhgJHxxBJhwXXBZvOSc5AVRfNBhEWwZPMSAPFBVHbw1VDkAoTHtnQBd5JkEQRxEGJSsDAlBGPwlSBRYrACgyQBUYTRgQE0MsIyAKEhFWJEwKQVA4AiohB1hab04ZOUNPYmxGUFAVAgNBBFsoAj17PUNVM10eURofIz8VIwBQKgh0AEZtUWkjZBcUZxgQE0NPKypGPwBBJgNZEhgaDSU+PUdRIlwQUg0LYgMWBBlaIR8ZNlchBxolC1JQaXVRS0MbKikIelAVb0wXQRZtTGl1ThoZZ3dSQAoLKy0IJRkVKwNSElhqGGkwFkdbNF0QVxoBIyEPE1BGIwVTBERtASgtVRdBNF1CEw4aMThGAhUYPAlDQUAsADwwTlpVKU1RXw8WSGxGUFAVb0wXBFgpZml1ThdRKVwQTkplDyMQFSRULVZ2BVIeACAxC0UcZXJFXhM/LTsDAlIZbxcXNVM1GGloThV+MlVAEzMANSkUUlwVCwlRAEMhGGloTgIEaxh9Wg1Pf2xTQFwVAg1PQQttXnllQhdmKE1eVwoBJWxbUEAZby9WDVovDSo+TgoUCldGVg4KLDhIAxVBBRlaEWYiGywnTkodTXVfRQY7Iy5cMRRRGwNQBlooRGscAFF+MlVAEU9POWwyFQhBb1EXQ38jCiA7B0NRZ3JFXhNNbmwiFRZUOgBDQQttCig5HVIYZ3tRXw8NIy8NUE0VAgNBBFsoAj17HVJADlZWeRYCMmwbWXp4IBpSNVcvVggxCmNbIF9cVktNDCMFHBlFbUAXQU1tOCwtGhcJZxp+XAADKzxEXFAVb0wXQRZtKCwzD0JYMxgNEwUOLj8DXFB2LgBbA1cuB2loTnpbMV1dVg0bbD8DBD5aLABeERYwRUMYAUFRE1lSCSILJggPBhlRKh4fSDwAAz8wOlZWfXlUVzcAJSsKFVgXCQBOQxptF2kBC09AZwUQESUDO25KUDRQKQ1CDUJtUWkzD1tHIhQQYQocKTVGTVBBPRlSTTxtTGl1OlhbK0xZQ0NSYm4qGRtQIxUXFVltGDs8CVBRNRhRXRcGby8OFRFBbwVRQUM+CS11DVZGIlRVQBADO2JEXHoVb0wXIlchACs0DVwUehh9XBUKLykIBF5GKhhxDU9tEWBfI1hCImxRUVkuJig1HBlRKh4fQ3AhFRolC1JQZRQQSEM7JzQSUE0VbSpbGBY+HCwwChUYZ3xVVQIaLjhGTVAAf0AXLF8jTHR1XwcYZ3VRS0NSYn5WQFwVHQNCD1IkAi51UxcEaxhzUg8DIC0FG1AIbyFYF1MgCSchQERRM35cSjAfJykCUA0cRSFYF1MZDStvL1NQA1FGWgcKMGRPej1aOQljAFR3LS0xOlhTIFRVG0EuLDgPMTZ+bUAXGhYZCTEhTgoUZXleRwpCAwotUlwVCwlRAEMhGGloTkNGMl0cOUNPYmwyHx9ZOwVHQQttTgs5AVRfNBhEWwZPcHxLHRlbOhhSQV8pACx1BV5XLBYSH0MsIyAKEhFWJEwKQXsiGiw4C1lAaUtVRyIBNiUnNjsVMkU9LFk7CSQwAEMaNF1Ecg0bKw0gO1hBPRlSSDwAAz8wOlZWfXlUVycGNCUCFQIdZmZ6DkAoOCg3VHZQI3pFRxcALGQdUCRQNxgXXBZvPygjCxdXMkpCVg0bYjwJAxlBJgNZQxptKjw7DRcJZ15FXQAbKyMIWFkVJgoXLFk7CSQwAEMaNFlGVjMAMWRPUARdKgIXL1k5BS8sRhVkKEsSH0E8IzoDFF4XZkxSDUUoTAc6Gl5SPhASYwwcYGBEPh8VLARWExRhGDsgCx4UIlZUEwYBJmwbWXp4IBpSNVcvVggxCnVBM0xfXUsUYhgDCAQVckwVM1MuDSU5TkRVMV1UExMAMSUSGR9bbUAXJ0MjD2loTlFBKVtEWgwBamVGGRYVAgNBBFsoAj17HFJXJlRcYwwcamVGBBhQIUx5DkIkCjB9TGdbNBocETEKIS0KHBVRYU4eQVMhHyx1IFhALl5JG0E/LT9EXFJ7IBhfCFgqTDo0GFJQZRREQRYKa2wDHhQVKgJTQUtkZkMDB0RgJloKcgcLDi0EFRwdNExjBE45THR1TGBbNVRUEw8GJSQSGR5Sb0cXEVosFSwnTnJnFxYSH0MrLSkVJwJUP0wKQUI/GSx1Ex4+EVFDZwINeA0CFDRcOQVTBERlRUMDB0RgJloKcgcLFiMBFxxQZ05xFFohDjs8CV9AZRQQSEM7JzQSUE0VbSpCDVovHiAyBkMWaxh0VgUONyASUE0VKQ1bElNhTAo0AltWJltbE15PFCUVBRFZPEJEBEILGSU5DEVdIFBEEx5GSBoPAyRULVZ2BVIZAy4yAlIcZXZfdQwIYGBGUFAVb0xMQWIoFD11UxcWFV1dXBUKYioJF1IZbyhSB1c4AD11UxdSJlRDVk9PAS0KHBJULAcXXBYbBTogD1tHaUtVRy0ABCMBUA0cRTpeEmIsDnMUClNwLk5ZVwYdamVsJhlGGw1VW3cpCB06CVBYIhASdjA/EiAHCRVHbUAXQU1tOCwtGhcJZxpgXwIWJz5GNSNlbUAXJVMrDTw5GhcJZ15RXxAKbmwlERxZLQ1UChZwTAwGPhlHIkxgXwIWJz5GDVk/GQVENVcvVggxCntVJV1cG0E/Li0fFQIVLANbDkRvRXMUClN3KFRfQTMGIScDAlgXCj9nMVosFSwnLVhYKEoSH0MUSGxGUFBxKgpWFFo5THR1K2RkaWtEUhcKbDwKEQlQPS9YDVk/QGkBB0NYIhgNE0E/Li0fFQIVCj9nQVUiACYnTBs+ZxgQEyAOLiAEERNeb1EXB0MjDz08AVkcJBEQdjA/bB8SEQRQYRxbAE8oHgo6AlhGZwUQUEMKLChGDVk/RQBYAlchTBk5HGNWP2oQDkM7Iy4VXiBZLhVSEwwMCC0HB1BcM2xRUQEAOmRPehxaLA1bQWI9PiY6AxcJZ2hcQTcNOh5cMRRRGw1VSRQfAyY4TmNkNBoZOQ8AIS0KUCRFHwBFEhZwTBk5HGNWP2oKcgcLFi0EWFJlIw1OBERtOBl3Rz0+E0hiXAwCeA0CFDxULQlbSU1tOCwtGhcJZxpkVg8KMiMUBFBUPQNCD1JtGCEwTlRBNUpVXRdPMCMJHV4XY0xzDlM+Ozs0HhcJZ0xCRgZPP2VsJABnIANaW3cpCA08GF5QIkoYGmk7Mh4JHx0PDghTI0M5GCY7RkwUE11IR0NSYm6E9uIVCgBSF1c5Azt3QhdyMlZTE15PJDkIEwRcIAIfSDxtTGl1AlhXJlQQQ0NSYh4JHx0bKAlDJFooGighAUVkKEsYGmlPYmxGGRYVP0xDCVMjTBwhB1tHaUxVXwYfLT4SWAAVZExhBFU5AztmQFlRMBAAH1dDcmVPS1B7IBheB09lTh0FTBsWpb6iEyYDJzoHBB9HbUU9QRZtTCw5HVIUCVdEWgUWam4yIFIZbSJYQVMhCT80GlhGZRREQRYKa2wDHhQ/KgJTQUtkZh0lPFhbKgJxVwctNzgSHx4dNExjBE45THR1TNWy1Rh+VgIdJz8SUB1ULAReD1NvQGkTG1lXZwUQVRYBITgPHx4dZmYXQRZtACY2D1sUGBQQWxEfYnFGJQRcIx8ZB18jCAQsOlhbKRAZOUNPYmwPFlBbIBgXCUQ9TD09C1kUCVdEWgUWam4yIFIZbSJYQVUlDTt3QkNGMl0ZCEMdJzgTAh4VKgJTaxZtTGk5AVRVKxhSVhAbbmwEFFAIbwJeDRptASghBhlcMl9VOUNPYmwAHwIVEEAXDBYkAmk8HlZdNUsYYQwAL2IBFQR4Lg9fCFgoH2F8RxdQKDIQE0NPYmxGUBxaLA1bQVJtUWkAGl5YNBZUWhAbIyIFFVhdPRwZMVk+BT08AVkYZ1UeQQwANmI2HwNcOwVYDx9HTGl1ThcUZxhZVUMLYnBGEhQVOwRSDxYvCGloTlMPZ1pVQBdPf2wLUBVbK2YXQRZtCScxZBcUZxhZVUMNJz8SUARdKgIXNEIkADp7GlJYIkhfQRdHICkVBF5HIANDT2YiHyAhB1haZxMQZQYMNiMUQ15bKhsfURp5QHl8RwwUCVdEWgUWam4yIFIZbY6x8xZvQmc3C0RAaVZRXgZGSGxGUFBQIx9SQXgiGCAzFx8WE2gSH0EhLWwLERNdJgJSQxo5HjwwRxdRKVw6Vg0LYjFPeiRFHQNYDAwMCC0XG0NAKFYYSEM7JzQSUE0VbY6x8xYDCSgnC0RAZ1FEVg5NbmwgBR5Wb1EXB0MjDz08AVkcbjIQE0NPLiMFERwVEEAXCUQ9THR1O0NdK0seVQoBJgEfJB9aIUQeaxZtTGk8CBdaKEwQWxEfYjgOFR4VAQNDCFA0RGsBPhUYZXZfEwAHIz5EXARHOgkeWhY/CT0gHFkUIlZUOUNPYmwKHxNUI0xVBEU5QGk3ChcJZ1ZZX09PLy0SGF5dOgtSaxZtTGkzAUUUGBQQWkMGLGwPABFcPR8fM1kiAWcyC0N9M11dQEtGa2wCH3oVb0wXQRZtTCU6DVZYZ1wQDkM6NiUKA15RJh9DAFguCWE9HEcaF1dDWhcGLSJKUBkbPQNYFRgdAzo8Gl5bKRE6E0NPYmxGUFBcKUxTQQptDi11Gl9RKRhSV0NSYihdUBJQPBgXXBYkTCw7Cj0UZxgQVg0LSGxGUFBcKUxVBEU5TD09C1kUEkxZXxBBNikKFQBaPRgfA1M+GGcnAVhAaWhfQAobKyMIUFsVGQlUFVk/X2c7C0AcdxQDH1NGa3dGPh9BJgpOSRQZPGt5TNWy1RgSHU0NJz8SXh5UIgkeaxZtTGkwAkRRZ3ZfRwoJO2REJCAXY055DhYkGCw4HRUYM0pFVkpPJyICehVbK0xKSDxHACY2D1sUIU1eUBcGLSJGFxVBHwBWGFM/Iig4C0QcbjIQE0NPLiMFERwVIBlDQQttFzRfThcUZ15fQUMwbmwWUBlbbwVHAF8/H2EFAlZNIkpDCSQKNhwKEQlQPR8fSB9tCCZfThcUZxgQE0MGJGwWUA4IbyBYAlchPCU0F1JGZ0xYVg1PNi0EHBUbJgJEBEQ5RCYgGhsUNxZ+Ug4Ka2wDHhQ/b0wXQVMjCEN1ThcULl4QEAwaNmxbTVAFbxhfBFhtGCg3AlIaLlZDVhEbaiMTBFwVbURZDlgoRWt8TlJaIzIQE0NPMCkSBQJbbwNCFTwoAi1fOkdkK0pDCSILJgAHEhVZZxcXNVM1GGloThVgIlRVQwwdNmwSH1BUIQNDCVM/TDk5D05RNRhZXUMbKilGAxVHOQlFTxRhTA06C0RjNVlAE15PNj4TFVBIZmZjEWYhHjpvL1NQA1FGWgcKMGRPeiRFHwBFEgwMCC0RHFhEI1dHXUtNFjw2HBFMKh4VTRY2TB0wFkMUehgSYw8OOykUUlwVGQ1bFFM+THR1CVJAF1RRSgYdDC0LFQMdZkAXJVMrDTw5GhcJZxoYXQwBJ2VEXFB2LgBbA1cuB2loTlFBKVtEWgwBamVGFR5RbxEea2I9PCUnHQ11I1xyRhcbLSJOC1BhKhRDQQttThswCEVRNFAQXwocNm5KUDZAIQ8XXBYrGSc2Gl5bKRAZOUNPYmwPFlB6PxheDlg+Qh0lPltVPl1CEwIBJmwpAARcIAJET2I9PCU0F1JGaWtVRzUOLjkDA1BBJwlZQXk9GCA6AEQaE0hgXwIWJz5cIxVBGQ1bFFM+RC4wGmdYJkFVQS0OLykVWFkcbwlZBTwoAi11Ex4+E0hgXxEceA0CFDJAOxhYDx42TB0wFkMUehgSZwYDJzwJAgQVOwMXElMhCSohC1MWaxh2Rg0MYnFGFgVbLBheDlhlRUN1ThcUK1dTUg9PLGxbUD9FOwVYD0VjODkFAlZNIkoQUg0LYgMWBBlaIR8ZNUYdACgsC0UaEVlcRgZlYmxGUF0YbyBYDl1tBSd1J1lzJlVVYw8OOykUA1BTIB4XFV4oBTt1GlhbKTIQE0NPLiMFERwVOB8XXBYaAzs+HUdVJF0KdQoBJgoPAgNBDAReDVJlTgA7KVZZImhcUhoKMD9EWXoVb0wXCFBtGzp1Gl9RKTIQE0NPYmxGUBxaLA1bQVttUWkiHQ1yLlZUdQodMTglGBlZK0RZSDxtTGl1ThcUZ1RfUAIDYiQUAFAIbwEXAFgpTCRvKF5aI35ZQRAbASQPHBQdbSRCDFcjAyAxPFhbM2hRQRdNa0ZGUFAVb0wXQV8rTCEnHhdAL11eEzYbKyAVXgRQIwlHDkQ5RCEnHhlkKEtZRwoALGxNUCZQLBhYEwVjAiwiRgUYdxQAGkpUYj4DBAVHIUxSD1JHTGl1TlJaIzIQE0NPDCMSGRZMZ05jMRRhTGsFAlZNIkoQXQwbYiUIXRdUIgkVTRY5HjwwRz1RKVwQTkplSGFLUJKhz46j4dTZ7GkBL3UUchjSs/dPDwU1M1DX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bav+Mm3+rfW07jSp+ON1syE5PDX2+zV9bZHACY2D1sUClFDUC9Pf2wyERJGYSFeElV3LS0xIlJSM39CXBYfICMeWFJyLgFSQRBtPz00GkQWaxgSWg0JLW5Pej1cPA97W3cpCAU0DFJYb0MQZwYXNmxbUFJyLgFSQV8jCiZ1D1lQZ1RZRQZPMSkVAxlaIUxEFVc5H2d3QhdwKF1DZBEOMmxbUARHOgkXHB9HISAmDXsOBlxUdwoZKygDAlgcRSFeElUBVggxCntVJV1cG0tNEiAHExUPb0lEQx93CiYnA1ZAb3tfXQUGJWIhMT1wECJ2LHNkRUMYB0RXCwJxVwcjIy4DHFgdbTxbAFUoTAARVBcRIxoZCQUAMCEHBFh2IAJRCFFjPAUULXJrDnwZGmkiKz8FPEp0KwhzCEAkCCwnRh4+K1dTUg9PLi4KPRFWJ0wXQQttISAmDXsOBlxUfwINJyBOUj1ULAReD1M+TCo6A0dYIkxVV1lPcm5PehxaLA1bQVovAAAhC1pHZxgNEy4GMS8qSjFRKyBWA1MhRGscGlJZNBhAWgAEJyhGUFAVb1YXURRkZiU6DVZYZ1RSXyQdIy4VUFAIbyFeElUBVggxCntVJV1cG0EoMC0EA1BQPA9WEVMpTGl1Tg0UdxoZOQ8AIS0KUBxXIyhSAEIlH2loTnpdNFt8CSILJgAHEhVZZ05zBFc5BDp1ThcUZxgQE0NPYnZGQFIcRQBYAlchTCU3AmJEM1FdVkNSYgEPAxN5dS1TBXosDiw5RhVhN0xZXgZPYmxGUFAVb0wXQQxtXHlvXgcOdwgSGmkiKz8FPEp0KwhzCEAkCCwnRh4+ClFDUC9VAygCMgVBOwNZSU1tOCwtGhcJZxpiVhAKNmwVBBFBPE4bQXA4Aip1UxdSMlZTRwoALGRPUCNBLhhET0QoHywhRh4PZ3ZfRwoJO2REIwRUOx8VTRQfCTowGhkWbhhVXQdPP2VsehxaLA1bQXskHyoHTgoUE1lSQE0iKz8FSjFRKz5eBl45Kzs6G0dWKEAYETAKMDoDAlIZb05AE1MjDyF3Rz15LktTYVkuJigqERJQI0RMQWIoFD11UxcWFV1aXAoBYiMUUBhaP0xDDhYsTC8nC0RcZ0tVQRUKMGJEXFBxIAlENkQsHGloTkNGMl0QTkplDyUVEyIPDghTJV87BS0wHB8dTXVZQAA9eA0CFDJAOxhYDx42TB0wFkMUehgSYQYFLSUIUARdJh8XElM/GiwnTBs+ZxgQEyUaLC9GTVBTOgJUFV8iAmF8TlBVKl0KdAYbESkUBhlWKkQVNVMhCTk6HENnIkpGWgAKYGVcJBVZKhxYE0JlLyY7CF5TaWh8ciAqHQUiXFB5IA9WDWYhDTAwHB4UIlZUEx5GSAEPAxNndS1TBXQ4GD06AB9PZ2xVSxdPf2xEIxVHOQlFQV4iHGl9HFZaI1ddGkFDSGxGUFBzOgJUQQttCjw7DUNdKFYYGmlPYmxGUFAVbyJYFV8rFWF3JlhEZRQQETAKIz4FGBlbKEIZTxRkZml1ThcUZxgQRwIcKWIVABFCIURRFFguGCA6AB8dTRgQE0NPYmxGUFAVbwBYAlchTB0GTgoUIFldVlkoJzg1FQJDJg9SSRQZCSUwHlhGM2tVQRUGISlEWXoVb0wXQRZtTGl1ThdYKFtRX0MnNjgWIxVHOQVUBBZwTC40A1IOAF1EYAYdNCUFFVgXBxhDEWUoHj88DVIWbjIQE0NPYmxGUFAVb0xbDlUsAGk6BRsUNV1DE15PMi8HHBwdKRlZAkIkAyd9Rz0UZxgQE0NPYmxGUFAVb0wXE1M5GTs7TlBVKl0KexcbMgsDBFgdbQRDFUY+VmZ6CVZZIkseQQwNLiMeXhNaIkNBUBkqDSQwHRgRIxdDVhEZJz4VXyBALQBeAgk+AzshIUVQIkoNchAMZCAPHRlBcl0HURRkVi86HFpVMxBzXA0JKytIIDx0DCloKHJkRUN1ThcUZxgQE0NPYmwDHhQcRUwXQRZtTGl1ThcUZ1FWEw0ANmwJG1BBJwlZQXgiGCAzFx8WD1dAEU9NCjgSADdQO0xRAF8hCS17TBtANU1VGlhPMCkSBQJbbwlZBTxtTGl1ThcUZxgQE0MDLS8HHFBaJF4bQVIsGCh1UxdEJFlcX0sJNyIFBBlaIUQeQUQoGDwnABd8M0xAYAYdNCUFFUp/HCN5JVMuAy0wRkVRNBEQVg0La0ZGUFAVb0wXQRZtTGk8CBdaKEwQXAhdYiMUUB5aO0xTAEIsTCYnTllbMxhUUhcObCgHBBEVOwRSDxYDAz08CE4cZXBfQ0FDYA4HFFBHKh9HDlg+CWd3QkNGMl0ZCEMdJzgTAh4VKgJTaxZtTGl1ThcUZxgQEwUAMGw5XFBGPRoXCFhtBTk0B0VHb1xRRwJBJi0SEVkVKwM9QRZtTGl1ThcUZxgQE0NPYiUAUANHOUJHDVc0BScyTlZaIxhDQRVBLy0eIBxUNglFEhYsAi11HUVCaUhcUhoGLCtGTFBGPRoZDFc1PCU0F1JGNBgdE1JPIyICUANHOUJeBRYzUWkyD1pRaXJfUSoLYjgOFR4/b0wXQRZtTGl1ThcUZxgQE0NPYmwyI0phKgBSEVk/GB06PltVJF15XRAbIyIFFVh2IAJRCFFjPAUULXJrDnwcExAdNGIPFFwVAwNUAFodACgsC0UdfBhCVhcaMCJsUFAVb0wXQRZtTGl1ThcUZ11eV2lPYmxGUFAVb0wXQRYoAi1fThcUZxgQE0NPYmxGPh9BJgpOSRQFAzl3QhV6KBhDVhEZJz5GFh9AIQgZQxo5HjwwRz0UZxgQE0NPYikIFFk/b0wXQVMjCGkoRz0+ahUQfwoZJ2wTABRUOwkXDVkiHEMhD0RfaUtAUhQBaioTHhNBJgNZSR9HTGl1TkBcLlRVExcOMSdIBxFcO0QGSBYpA0N1ThcUZxgQExMMIyAKWBZAIQ9DCFkjRGBfThcUZxgQE0NPYmxGGRYVIw5bLFcuBGl1TlZaIxhcUQ8iIy8OXiNQOzhSGUJtTGkhBlJaZ1RSXy4OISRcIxVBGwlPFR5vISg2Bl5aIksQUAwCMiADBBVRdUwVQRhjTBohD0NHaVVRUAsGLCkVNB9bKkUXBFgpZml1ThcUZxgQE0NPYiUAUBxXIyVDBFs+TGk0AFMUK1pcehcKLz9IIxVBGwlPFRZtGCEwABdYJVR5RwYCMXY1FQRhKhRDSRQEGCw4HRdELltbVgdPYmxGUEoVbUwZTxYeGCghHRldM11dQDMGIScDFFkVKgJTaxZtTGl1ThcUZxgQEwoJYiAEHDdHLg5EQRYsAi11AlVYAEpRURBBESkSJBVNO0wXFV4oAmk5DFtzNVlSQFk8JzgyFQhBZ05wE1cvH2kwHVRVN11UE0NPYnZGUlAbYUxkFVc5H2cwHVRVN11UdBEOID9PUBVbK2YXQRZtTGl1ThcUZxhZVUMDICAiFRFBJx8XAFgpTCU3AnNRJkxYQE08JzgyFQhBbxhfBFhtACs5KlJVM1BDCTAKNhgDCAQdbShSAEIlH2l1ThcUZxgQE0NPeGxEUF4bbz9DAEI+Qi0wD0NcNBEQVg0LSGxGUFAVb0wXQRZtTCAzTltWK21ARwoCJ2wHHhQVIw5bNEY5BSQwQGRRM2xVSxdPNiQDHlBZLQBiEUIkASxvPVJAE11IR0tNFzwSGR1Qb0wXQRZtTGl1ThcOZxoQHU1PETgHBAMbOhxDCFsoRGB8TlJaIzIQE0NPYmxGUBVbK0U9QRZtTCw7Cj1RKVwZOWlCb2yE5PDX2+zV9bZtOAgXTg8UpbikEyA9BwgvJCMVrfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmehxaLA1bQXU/IGloTmNVJUsecBEKJiUSA0p0Kwh7BFA5Kzs6G0dWKEAYESINLTkSUARdJh8XKUMvTmV1TF5aIVcSGmksMABcMRRRAw1VBFplF2kBC09AZwUQEScOLCgfVwMVGANFDVJtjsnBTm4GDBh4RgFNbmwiHxVGGB5WERZwTD0nG1IUOhE6cBEjeA0CFDxULQlbSU1tOCwtGhcJZxpjRhEZKzoHHF1TIA9CElMpTCEgDBkUAmtgH0MOLDgPXRdHLg4bQUUmBSU5Q1RcIltbH0MONzgJUABcLAdCERhvQGkRAVJHEEpRQ0NSYjgUBRUVMkU9IkQBVggxCnNdMVFUVhFHa0YlAjwPDghTLVcvCSV9RhVnJEpZQxdPNCkUAxlaIUwNQRM+TmBvCFhGKllEGyAALCoPF15mDD5+MWISOgwHRx4+BEp8CSILJgAHEhVZZ05iKBYhBSsnD0VNZxgQE0NVYgMEAxlRJg1ZNF9vRUMWHHsOBlxUfwINJyBOUiV8bw1CFV4iHml1ThcUZwIQalEEYh8FAhlFO0x1AFUmXgs0DVwWbjJzQS9VAygCPBFXKgAfSRQeDT8wTlFbK1xVQUNPYmxcUFVGbUUNB1k/ASghRnRbKV5ZVE08AxojLyJ6ADgeSDxHACY2D1sUBEpiE15PFi0EA152PQlTCEI+VggxCmVdIFBEdBEANzwEHwgdbThWAxYKGSAxCxUYZxpdXA0GNiMUUlk/DB5lW3cpCAU0DFJYb0MQZwYXNmxbUFJkOgVUChY/CS8wHFJaJF0Q0eP7YjsOEQQVKg1UCRY5DSt1ClhRNAISH0MrLSkVJwJUP0wKQUI/GSx1Ex4+BEpiCSILJggPBhlRKh4fSDwOHhtvL1NQC1lSVg9HOWwyFQhBb1EXQ9TNzmkGG0VCLk5RX0ONwthGJAdcPBhSBRYIPxl5TllbM1FWWgYdbmwHHgRcYgtFAFRhTCo6ClJHaRocEycAJz8xAhFFb1EXFUQ4CWkoRz13NWoKcgcLDi0EFRwdNExjBE45THR1TNW05Rh9UgAHKyIDA1DXz/gXLFcuBCA7CxdxFGgQUg0LYi0TBB8VPAdeDVpgDyEwDVwaZRQQdwwKMRsUEQAVckxDE0MoTDR8ZHRGFQJxVwcjIy4DHFhObzhSGUJtUWl3jLeWZ3FEVg4cYq7m5FB8OwlaQXMePGk0AFMUJk1EXEMfKy8NBQAbbUAXJVkoHx4nD0cUehhEQRYKYjFPejNHHVZ2BVIBDSswAh9PZ2xVSxdPf2xEkvCXbzxbAE8oHmm37qMUCldGVg4KLDhKUBZZNkAXD1kuACAlQhdGKFddHBMDIzUDAlBhHx8ZQxptKCYwHWBGJkgQDkMbMDkDUA0cRS9FMwwMCC0ZD1VRKxBLEzcKOjhGTVAXreyVQXskHyp1jLegZ3RZRQZPMTgHBAMZbx9SE0AoHmknC11bLlYfWwwfbG5KUDRaKh9gE1c9THR1GkVBIhhNGmksMB5cMRRRAw1VBFplF2kBC09AZwUQEYHv4GwlHx5TJgtEQdTN+GkGD0FRaFRfUgdPMj4DAxVBbxxFDlAkACwmQBUYZ3xfVhA4MC0WUE0VOx5CBBYwRUMWHGUOBlxUfwINJyBOC1BhKhRDQQttTqvVzBdnIkxEWg0IMWyE8OQVGiUXEUQoCjp5TlZXM1FfXUMHLTgNFQlGY0xDCVMgCWd3QhdwKF1DZBEOMmxbUARHOgkXHB9HZmR4TtWgx9qks4H7wmwyMTIVeEzV4aJtPwwBOn56AGsQ0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VZFtbJFlcEzAKNgBGTVBhLg5ET2UoGD08AFBHfXlUVy8KJDghAh9APw5YGR5vJSchC0VSJltVEU9PYCEJHhlBIB4VSDweCT0ZVHZQI3RRUQYDajdGJBVNO0wKQRQbBTogD1sUN0pVVQYdJyIFFQMVKQNFQUIlCWk4C1lBZ1FEQAYDJGJEXFBxIAlENkQsHGloTkNGMl0QTkplESkSPEp0KwhzCEAkCCwnRh4+FF1Ef1kuJigyHxdSIwkfQ2UlAz4WG0RAKFVzRhEcLT5EXFBObzhSGUJtUWl3LUJHM1ddEyAaMD8JAlIZbyhSB1c4AD11UxdANU1VH2lPYmxGMxFZIw5WAl1tUWkzG1lXM1FfXUsZa2wqGRJHLh5OT2UlAz4WG0RAKFVzRhEcLT5GTVBDbwlZBRYwRUMGC0N4fXlUVy8OICkKWFJ2Oh5EDkRtLyY5AUUWbgJxVwcsLSAJAiBcLAdSEx5vLzwnHVhGBFdcXBFNbmwdelAVb0xzBFAsGSUhTgoUBFdeVQoIbA0lMzV7G0AXNV85ACx1UxcWBE1CQAwdYg8JHB9HbUA9QRZtTAo0AltWJltbE15PJDkIEwRcIAIfAh9tICA3HFZGPgJjVhcsNz4VHwJ2IABYEx4uRWkwAFMUOhE6YAYbDnYnFBRxPQNHBVk6AmF3IFhALl5JYAoLJ25KUAsVGQ1bFFM+THR1FRcWC11WR0FDYm40GRddO04XHBptKCwzD0JYMxgNE0E9KysOBFIZbzhSGUJtUWl3IFhALl5ZUAIbKyMIUANcKwkVTTxtTGl1LVZYK1pRUAhPf2wABR5WOwVYDx47RWkZB1VGJkpJCTAKNgIJBBlTNj9eBVNlGmB1C1lQZ0UZOTAKNgBcMRRRCx5YEVIiGyd9TGJ9FFtRXwZNbmwdUCZUIxlSEhZwTDJ1TAABYhocEVJfcmlEXFIEfVkSQxpvXXxlSxUUOhQQdwYJIzkKBFAIb04GUQZoTmV1OlJMMxgNE0E6C2w1ExFZKk4baxZtTGkWD1tYJVlTWENSYioTHhNBJgNZSUBkTAU8DEVVNUEKYAYbBhwvIxNUIwkfFVkjGSQ3C0UcMQJXQBYNam5DVVIZbU4eSB9tCScxTkodTWtVRy9VAygCNBlDJghSEx5kZhowGnsOBlxUfwINJyBOUj1QIRkXKlM0DiA7ChUdfXlUVygKOxwPExtQPUQVLFMjGQIwF1VdKVwSH0MUSGxGUFBxKgpWFFo5THR1LVhaIVFXHTcgBQsqNS9+CjUbQXgiOQB1UxdANU1VH0M7JzQSUE0VbThYBlEhCWkYC1lBZRQ6TkplESkSPEp0KwhzCEAkCCwnRh4+FF1Ef1kuJigkBQRBIAIfGhYZCTEhTgoUZW1eXwwOJmwuBRIXY0xzDkMvACwWAl5XLBgNExcdNylKelAVb0xjDlkhGCAlTgoUZWpVXgwZJz9GBBhQbzl+QVcjCGkxB0RXKFZeVgAbMWwDBhVHNhhfCFgqQmt5ZBcUZxh2Rg0MYnFGFgVbLBheDlhlRUN1ThcUZxgQEyY8EmIVFQRhOAVEFVMpRC80AkRRbgMQdjA/bD8DBD1ULAReD1NlCig5HVIdfBh1YDNBMSkSOQRQIkRRAFo+CWBuTnJnFxZDVhc/Li0fFQIdKQ1bElNkZml1ThcUZxgQWgVPBx82Xi9WIAJZT1ssBSd1Gl9RKRh1YDNBHS8JHh4bIg1eDwwJBTo2AVlaIltEG0pPJyICelAVb0wXQRZtISYjC1pRKUweQAYbBCAfWBZUIx9SSA1tISYjC1pRKUweQAYbDCMFHBlFZwpWDUUoRXJ1I1hCIlVVXRdBMSkSOR5TBRlaER4rDSUmCx4PZ3VfRQYCJyISXgNQOy1ZFV8MKgJ9CFZYNF0ZOUNPYmxGUFAVJgoXMkM/GiAjD1saGFtfXQ1PNiQDHlBmOh5BCEAsAGcKDVhaKQJ0WhAMLSIIFRNBZ0UXBFgpZml1ThcUZxgQWgVPETkUBhlDLgAZPlgiGCAzF3BBLhhEWwYBYh8TAgZcOQ1bT2kjAz08CE5zMlEKdwYcNj4JCVgcbwlZBTxtTGl1ThcUZ2d3HTpdCRMiMT5xFjN/NHQSIAYUKnJwZwUQXQoDSGxGUFAVb0wXLV8vHignFw1hKVRfUgdHa0ZGUFAVKgJTQUtkZkM5AVRVKxhjVhc9YnFGJBFXPEJkBEI5BScyHQ11I1xiWgQHNgsUHwVFLQNPSRQMDz08AVkUD1dEWAYWMW5KUFJeKhUVSDweCT0HVHZQI3RRUQYDajdGJBVNO0wKQRQcGSA2BRdfIkFDEwUAMGwJHhUYPARYFRYsDz08AVlHaRocEycAJz8xAhFFb1EXFUQ4CWkoRz1nIkxiCSILJggPBhlRKh4fSDweCT0HVHZQI3RRUQYDam4yFRxQPwNFFRY5A2kwAlJCJkxfQUFGeA0CFDtQNjxeAl0oHmF3JlhALF1Jdg8KNG5KUAs/b0wXQXIoCiggAkMUehgSdEFDYgEJFBUVckwVNVkqCyUwTBsUE11IR0NSYm4jHBVDLhhYExRhZml1Thd3JlRcUQIMKWxbUBZAIQ9DCFkjRCg2Gl5CIhE6E0NPYmxGUFBcKUxWAkIkGix1Gl9RKTIQE0NPYmxGUFAVb0xbDlUsAGklTgoUFVdfXk0IJzgjHBVDLhhYE2YiH2F8ZBcUZxgQE0NPYmxGUBlTbxwXFV4oAmkAGl5YNBZEVg8KMiMUBFhFb0cXN1MuGCYnXRlaIk8YA09bbnxPWUsVAQNDCFA0RGsdAUNfIkESH0GNxN5GNRxQOQ1DDkRvRWkwAFM+ZxgQE0NPYmwDHhQ/b0wXQVMjCGkoRz1nIkxiCSILJgAHEhVZZ05jBFooHCYnGhdAKBheVgIdJz8SUB1ULAReD1NvRXMUClN/IkFgWgAEJz5OUjhaOwdSGHssDyF3QhdPTRgQE0MrJyoHBRxBb1EXQ35vQGkYAVNRZwUQETcAJSsKFVIZbzhSGUJtUWl3I1ZXL1FeVkFDSGxGUFB2LgBbA1cuB2loTlFBKVtEWgwBai0FBBlDKkU9QRZtTGl1ThddIRheXBdPIy8SGQZQbxhfBFhtHiwhG0VaZ11eV2lPYmxGUFAVbwBYAlchTBZ5Tl9GNxgNEzYbKyAVXhZcIQh6GGIiAyd9RwwULl4QXQwbYiQUAFBBJwlZQUQoGDwnABdRKVw6E0NPYmxGUFBZIA9WDRYvCTohQhdWIxgNEw0GLmBGHRFBJ0JfFFEoZml1ThcUZxgQVQwdYhNKUB0VJgIXCEYsBTsmRmVbKFUeVAYbDy0FGBlbKh8fSB9tCCZfThcUZxgQE0NPYmxGHB9WLgAXBRZwTBwhB1tHaVxZQBcOLC8DWBhHP0JnDkUkGCA6ABsUKhZCXAwbbBwJAxlBJgNZSDxtTGl1ThcUZxgQE0MGJGwCUEwVLQgXFV4oAmk3ChcJZ1wLEwEKMThGTVBYbwlZBTxtTGl1ThcUZ11eV2lPYmxGUFAVbwVRQVQoHz11Gl9RKRhlRwoDMWISFRxQPwNFFR4vCTohQEVbKEweYwwcKzgPHx4VZExhBFU5AztmQFlRMBAAH1dDcmVPS1B7IBheB09lTgE6GlxRPhocEYHp0GxEXl5XKh9DT1gsASx8TlJaIzIQE0NPJyICUA0cRT9SFWR3LS0xIlZWIlQYETcAJSsKFVBhOAVEFVMpTAwGPhUdfXlUVygKOxwPExtQPUQVKVk5BywsK2RkZRQQSGlPYmxGNBVTLhlbFRZwTGsBTBsUCldUVkNSYm4yHxdSIwkVTRYZCTEhTgoUZX1jY0FDSGxGUFB2LgBbA1cuB2loTlFBKVtEWgwBai0FBBlDKkU9QRZtTGl1ThddIRhRUBcGNClGBBhQIWYXQRZtTGl1ThcUZxhcXAAOLmwQUE0VIQNDQXMePGcGGlZAIhZERAocNikCelAVb0wXQRZtTGl1TnJnFxZDVhc7NSUVBBVRZxoeaxZtTGl1ThcUZxgQEwoJYhgJFxdZKh8ZJGUdOD48HUNRIxhEWwYBYhgJFxdZKh8ZJGUdOD48HUNRIwJjVhc5IyATFVhDZkxSD1JHTGl1ThcUZxgQE0NPDCMSGRZMZ05/DkImCTB3QhcWE09ZQBcKJmwjIyAVbUwZTxZlGmk0AFMUZXd+EUMAMGxEPzZzbUUeaxZtTGl1ThcUIlZUOUNPYmwDHhQVMkU9MlM5PnMUClN4JlpVX0tNECkFERxZbx9WF1MpTDk6HRUdfXlUVygKOxwPExtQPUQVKVk5BywsPFJXJlRcEU9POUZGUFAVCwlRAEMhGGloThVmZRQQfgwLJ2xbUFJhIAtQDVNvQGkBC09AZwUQETEKIS0KHFIZRUwXQRYODSU5DFZXLBgNEwUaLC8SGR9bZw1UFV87CWB1B1EUJltEWhUKYjgOFR4VAgNBBFsoAj17HFJXJlRcYwwcamVdUD5aOwVRGB5vJCYhBVJNZRQSYQYMIyAKFRQbbUUXBFgpTCw7ChdJbjI6fwoNMC0UCV5hIAtQDVMGCTA3B1lQZwUQfBMbKyMIA154KgJCKlM0DiA7Cj0+ahUQ0ffvoNjmkuS1bzhfBFsoTGJ1PVZCIhhRVwcALD9GkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNjt3VjKO0payw0ffvoNjmkuS1rfi3g6LNZiAzTmNcIlVVfgIBIysDAlBUIQgXMlc7CQQ0AFZTIkoQRwsKLEZGUFAVGwRSDFMADSc0CVJGfWtVRy8GID4HAgkdAwVVE1c/FWBfThcUZ2tRRQYiIyIHFxVHdT9SFXokDjs0HE4cC1FSQQIdO2VsUFAVbz9WF1MADSc0CVJGfXFXXQwdJxgOFR1QHAlDFV8jCzp9Rz0UZxgQYAIZJwEHHhFSKh4NMlM5JS47AUVRDlZUVhsKMWQdUFJ4KgJCKlM0DiA7ChUUOhE6E0NPYhgOFR1QAg1ZAFEoHnMGC0NyKFRUVhFHASMIFhlSYT92N3MSPgYaOh4+ZxgQEzAONCkrER5UKAlFW2UoGA86AlNRNRBzXA0JKytIIzFjCjN0J3EeRUN1ThcUFFlGVi4OLC0BFQIPDRleDVIOAyczB1BnIltEWgwBahgHEgMbDANZB18qH2BfThcUZ2xYVg4KDy0IERdQPVZ2EUYhFR06OlZWb2xRURBBESkSBBlbKB8eaxZtTGklDVZYKxBWRg0MNiUJHlgcbz9WF1MADSc0CVJGfXRfUgcuNzgJHB9UKy9YD1AkC2F8TlJaIxE6Vg0LSEZLXVBmOw1FFRY5BCx1K2RkZ1RfXBNPaiUSUB9bIxUXE1MjCCwnHRdRKVlSXwYLYi8HBBVSIB5eBEVkZgwGPhlHM1lCR0tGSEYoHwRcKRUfQ29/J2kdG1UWaxgSfwwOJikCUBZaPUwVQRhjTAo6AFFdIBZ3ci4qHQInPTUVYUIXQxhtPDswHUQUFVFXWxcsNj4KUARabxhYBlEhCWd3Rz1ENVFeR0tHYBc/QjtobyBYAFIoCGkzAUUUYksQGzMDIy8DORQVaggeTxRkVi86HFpVMxBzXA0JKytINzF4CjN5IHsIQGkWAVlSLl8eYy8uAQk5OTQcZmY='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
