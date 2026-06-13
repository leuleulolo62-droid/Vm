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

local __k = 'b2no18Jv0MRbp5pxc0rxaw0n'
local __p = 'Tx81NDva3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96JkTxEYajJxAxY7V2ZQLyxiPjxBV9Lu9hJONgNzaj5lD3JCBgReSE0AUlhBVxBOQhJOTxEYalYQbXJCUBVQWEMQWgsIGVcCBx8IBl1dahRFJD4GWT9QWEMQMzlMA1kLEBIdGkNOIwBRIXIKBVdQHgxCUigNFlMLK1ZOXgcNf0QIf2NWRQBQUCdRHBwYUENONV0cA1URQFYQbXI3OQ9QWEMQPRoSHlQHA1w7BhEQE0R7bQEBAlwADENyExsKRXIPAVlHZREYalZjOSsOFQ9QNgZfHFg4RXtCQlUCAEYYLxBWKDEWAxlQCw5fHQwJV0QZB1cAHB0YLANcIXIREUMVVxdYFxUEV0MbEkIBHUUyQFYQbXIzJXwzM0NjJjkzIxCM4qZOH1BLPhMQJDwWHxURFhoQIBcDG18WQlcWClJNPhlCbTMMFBUCDQ0eeHJBVxBONlMMHAsyalYQbXJCkrXSWDBFAA4IAVECQhJOjbGsaiJHJCEWFVFQPTBgXlgPGEQHBFsLHR0YKxhEJH8FAlQSVENRBwwOWlEYDVsKZREYalYQbbDi0hU9GQBYGxYEBBBOQtDu+xF1KxVYJDwHUHAjKE8QEw0VGBAdCVsCAxxbIhNTJn5CE1odCA9VBhEOGRBLThIPGkVXZx9eOTcQEVYEckMQUlhBV9LuwBInG1RVOVYQbXJCUNfw7EN5Bh0MV3U9Mh5ODkRMJVZAJDEJBUVcWApeBB0PA18cGxIYBlRPLwQ6bXJCUBVQmuOSUigNFkkLEBJOTxEYqPakbQESFVAUVwlFHwhOEVwXTVwBDF1ROlYYPjMEFRUCGQ1XFwtIWxAPDEYHQkJMPxgcbQYyAz9QWEMQUliD95JOL1sdDBEYalYQbXKA8KFQNApGF1gSA1EaER5ODERKOBNeOXIEHFofCk8QAR0TAVUcQkALBV5RJFlYIiJoUBVQWEMQkPjDV3MBDFQHCEIYalYQr9L2UGYRDgZ9ExYAEFUcQkIcCkJdPlZDIT0WAz9QWEMQUliD95JOMVcaG1hWLQUQbXKA8KFQLSoQAgoEEUNOSRIPDEVRJRgQJT0WG1AJC0MbUgwJEl0LQkIHDFpdOHwQbXJCUBWS+MEQMQoEE1kaERJOTxHayuIQDDANBUFQU0NEExpBEEUHBldkZREYalbS1/JCJF0VWARRHx1BH1EdQlECBlRWPltDJDYHUFQeDAodERAEFkRAQnYLCVBNJgJDbTMQFRUEDQ1VFlgSFlYLTDhOTxEYalYQBjcHABUnGQ9bIQgEElROgLvKTwMKahdeKXIDBloZHENYBx8EV0QLDlceAENMOVZEInIRBFQJWBZeFh0TV0QGBxIcDlVZOFg6r8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoQCttR1gLFhUvP01pQDM+M3EgJmsxJ2R6FTp/DBYnNBUEEAZeeFhBVxAZA0AARxNjE0R7bRoXEmhQOQ9CFxkFDhACDVMKClUYqPakbTEDHFlQNApSABkTDgo7DF4BDlUQY1ZWJCARBBtSUWkQUlhBBVUaF0AAZVRWLnxvCnw7Qn4vPCJ+NiE+P2UsPX4hLnV9DlYNbSYQBVB6cg9fERkNV2ACA0sLHUIYalYQbXJCUBVQRUNXExUETXcLFmELHUdRKRMYbwIOEUwVChASW3INGFMPDhI8CkFUIxVROTcGI0EfCgJXF0VBEFEDBwgpCkVrLwRGJDEHWBciHRNcGxsAA1UKMUYBHVBfL1QZRz4NE1QcWDFFHCsEBUYHAVdOTxEYalYQcHIFEVgVQiRVBisEBUYHAVdGTWNNJCVVPyQLE1BSUWlcHRsAGxA5DUAFHEFZKRMQbXJCUBVQWF4QFRkMEgopB0Y9CkNOIxVVZXA1H0cbCxNRER1DXjoCDVEPAxFtORNCBDwSBUEjHRFGGxsEVw1OBVMDCgt/LwJjKCAUGVYVUEFlAR0TPl4eF0Y9CkNOIxVVb3toHFoTGQ8QPhEGH0QHDFVOTxEYalYQbXJfUFIRFQYKNR0VJFUcFFsNChkaBh9XJSYLHlJSUWlcHRsAGxA4C0AaGlBUHwVVP3JCUBVQWF4QFRkMEgopB0Y9CkNOIxVVZXA0GUcEDQJcJwsEBRJHaF4BDFBUajpfLjMOIFkRAQZCUlhBVxBOXxI+A1BBLwRDYx4NE1QcKA9RCx0TfToHBBIAAEUYLRddKGgrA3kfGQdVFlBIV0QGB1xOCFBVL1h8IjMGFVFKLwJZBlBIV1UABjhkQhwYqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgck4dUklPV3MhLHQnKDsVZ1bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fM6HhcCFlxOIV0ACVhfaksQNi9oM1oeHgpXXD8gOnUxLHMjKhEYalYQbW9CUnERFgdJVQtBIF8cDlZMZXJXJBBZKnwyPHQzPTx5NlhBVxBOQhJTTwAOf0MCdWBTRABFciBfHB4IEB49IWAnP2VnHDNibXJCUBVNWEEBXEhPRxJkIV0ACVhfZCN5EgAnIHpQWEMQUlhBVw1OQFoaG0FLcFkfPzMVXlIZDAtFEA0SEkINDVwaCl9MZBVfIH07Ql4jGxFZAgwjFlMFUHAPDFoXBRRDJDYLEVslEUxdExEPWBJkIV0ACVhfZCVxGxc9Ino/LEMQUlhBVw1OQHYPAVVBHRlCITZAenYfFgVZFVYyNmYrPXEoKGIYalYQbXJfUBc0GQ1UCy8OBVwKTVEBAVdRLQUSRxENHlMZH01kPT8mO3UxKXc3TxEYalYNbXAwGVIYDCBfHAwTGFxMaHEBAVdRLVhxDhEnPmFQWEMQUlhBVxBTQnEBA15KeVhWPz0PInIyUFMcUkpQRxxOUABXRjsyZ1sQHj0EBBUDGQVVBgFBFFEeERIaGl9dLlZEInIRBFQJWBZeFh0TV0QGBxIdCkNOLwQXPnIRAFAVHENTGh0CHDotDVwIBlYWGTd2CA0vMW0vKzN1NzxBShBcUBJOQhwYPh5VbSYNH1tXC0NUFx4AAlwaQlsdTwANZ0cGYXIRAEcZFhcQAg0SH1UdQkxcXTsyZ1sQCCQHHkFQCAJEGgtrNF8ABFsJQXRuDzhkHg0yMWE4WF4QUCoEB1wHAVMaClVrPhlCLDUHXnAGHQ1EAVprfR1DQnkAAEZWahNGKDwWUFkVGQUQHBkMEkNkIV0ACVhfZCR1AB02NWZQRUNLeFhBVxBDTxI9GkNOIwBRIVhCUBVQKxJFGwoMNFEAAVcCTxEYalYQbW9CUmYBDQpCHzkDHlwHFkstDl9bLxoSYVhCUBVQNQxeAQwEBXEaFlMNBHJUIxNeOW9CUngfFhBEFwogA0QPAVktA1hdJAISYVhCUBVQPAZRBhBBVxBOQhJOTxEYalYQbW9CUnEVGRdYNw4EGURMTjhOTxEYGBNDPTMVHhVQWEMQUlhBVxBOQg9OTWNdOQZROjwnBlAeDEEceFhBVxBDTxIjDlJQIxhVPnJNUFwEHQ5DeFhBVxAjA1EGBl9dDwBVIyZCUBVQWEMQT1hDOlENClsACnROLxhEb35oUBVQWDBbGxQNFFgLAVk7H1VZPhMQbXJfUBcjEwpcHhsJElMFN0IKDkVdaFo6bXJCUGYEFxN5HAwEBVENFlsACBEYalYNbXAxBFoAMQ1EFwoAFEQHDFVMQzsYalYQBCYHHXAGHQ1EUlhBVxBOQhJOTwwYaD9EKD8nBlAeDEEceFhBVxApB1wLHVBMJQRlPTYDBFBQWEMQT1hDMFUAB0APG15KHwZULCYHUhl6WEMQUjEVEl0+C1EFGkF9PBNeOXJCUBVNWEF5Bh0MJ1kNCUceKkddJAISYVhCUBVQVU4QMxoIG1kaC1cdTx4YOQZCJDwWehVQWENjAgoIGUROQhJOTxEYalYQbXJCTRVSKxNCGxYVMkYLDEZMQzsYalYQDDALHFwEASZGFxYVVxBOQhJOTwwYaDdSJD4LBEw1DgZeBlpNfRBOQhItA1hdJAJxLzsOGUEJWEMQUlhBShBMIV4HCl9MCxRZITsWCXAGHQ1EUFRrVxBOQh9DT3xRORU6bXJCUGEVFAZAHQoVVxBOQhJOTxEYalYNbXA2FVkVCAxCBlpNfRBOQhI+Bl9falYQbXJCUBVQWEMQUlhBShBMMlsACHROLxhEb35oUBVQWCRVBj0NEkYPFl0cTxEYalYQbXJfUBc3HRd1Hh0XFkQBEGIBHFhMIxleb35oUBVQWCRVBjsJFkIPAUYLHWFXOVYQbXJfUBc3HRdzGhkTFlMaB0A+AEJRPh9fI3BOehVQWENiFxkFDmUeQhJOTxEYalYQbXJCTRVSKgZRFgE0B3UYB1waTR0yalYQbREKEVsXHSBYEwpBVxBOQhJOTxEFalRzJTMMF1AzEAJCUFRrVxBOQnEPHVVuJQJVbXJCUBVQWEMQUlhcVxItA0AKOV5MLzNGKDwWUhl6WEMQUi4OA1UKQhJOTxEYalYQbXJCUBVNWEFmHQwEExJCaE9kZRwVajVfKTcRUB0TFw5dBxYIA0lDCVwBGF8UagRVKyAHA11QGRAQFh0XBBAcB14LDkJdY3xzIjwEGVJeOyx0NytBShAVaBJOTxEaGRdAPToLAkADWk8QUDwgOXQ3QB5OTX53GiVnCAEyOXk8PSd5JlpNVxI+LWI+NhMUQFYQbXJAMnkxOyh/JyxDWxBMIHMgK3hsGSZ1DhsjPBdcWEF9MzEvI3UgI3wtKhMUQAs6R39PUNfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr05zpDTxJcQRFtHj98HlhPXRWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qBkDl0NDl0YHwJZISFCTRULBWk6FA0PFEQHDVxOOkVRJgUePzcRH1kGHTNRBhBJB1EaChtkTxEYahpfLjMOUFYFCkMNUh8AGlVkQhJOT1dXOFZDKDVCGVtQCAJEGkIGGlEaAVpGTWpmb1htZnBLUFEfckMQUlhBVxBOC1ROAV5MahVFP3IWGFAeWBFVBg0TGRAAC15OCl9cQFYQbXJCUBVQGxZCUkVBFEUcWHQHAVV+IwRDOREKGVkUUBBVFVFrVxBOQlcACzsYalYQPzcWBUceWABFAHIEGVRkaFQbAVJMIxlebQcWGVkDVgRVBjsJFkJGSzhOTxEYJhlTLD5CE10RCkMNUjQOFFECMl4PFlRKZDVYLCADE0EVCmkQUlhBHlZODF0aT1JQKwQQOToHHhUCHRdFABZBGVkCQlcACzsYalYQYH9COVtQPAJeFgFGBBA5DUACCxFMIhMQOT0NHhUSFwdJUhQIAVUdQkcAC1RKagFfPzkRAFQTHU15HD8AGlU+DlMXCkNLZlZSOCZCBF0VckMQUlhMWhAiDVEPA2FUKw9VP3whGFQCGQBEFwpBG1kACRIHHBFLLwIQOjoHHhUZFk5XExUEfRBOQhICAFJZJlZYPyJCTRUTEAJCSD4IGVQoC0AdG3JQIxpUZXAqBVgRFgxZFioOGEQ+A0AaTRgyalYQbT4NE1QcWAtFH1hcV1MGA0BUKVhWLjBZPyEWM10ZFAd/FDsNFkMdShAmGlxZJBlZKXBLehVQWENZFFgJBUBOA1wKT1lNJ1ZEJTcMUEcVDBZCHFgCH1EcThIGHUEUah5FIHIHHlF6WEMQUgoEA0UcDBIABl0yLxhUR1hPXRUyHRBEXx0HEV8cFhINB1BKKxVEKCBCHFofExZAUgwJFkROA14dABFbIhNTJiFCOVs3GQ5VIhQADlUcERIIAF1cLwQ6KycME0EZFw0QJwwIG0NABFsAC3xBHhlfI3pLehVQWENcHRsAGxANClMcQxFQOAYcbToXHRVNWDZEGxQSWVcLFnEGDkMQY3wQbXJCGVNQGwtRAFgVH1UAQkALG0RKJFZTJTMQXBUYChMcUhAUGhALDFZkTxEYahpfLjMOUEIDWF4QJRcTHEMeA1ELVXdRJBJ2JCARBHYYEQ9UWlooGXcPD1c+A1BBLwRDb3toUBVQWApWUg8SV0QGB1xkTxEYalYQbXIOH1YRFENdFhRBShAZEQgoBl9cDB9CPiYhGFwcHEt8HRsAG2ACA0sLHR92KxtVZFhCUBVQWEMQUhEHV10KDhIaB1RWQFYQbXJCUBVQWEMQUhQOFFECQlpOUhFVLhoKCzsMFHMZChBEMRAIG1RGQHobAlBWJR9UHz0NBGURChcSW3JBVxBOQhJOTxEYalZcIjEDHBUYEEMNUhUFGwooC1wKKVhKOQJzJTsOFHoWOw9RAQtJVXgbD1MAAFhcaF86bXJCUBVQWEMQUlhBHlZOChIPAVUYIh4QOToHHhUCHRdFABZBGlQCThIGQxFQIlZVIzZoUBVQWEMQUlgEGVRkQhJOT1RWLnxVIzZoelMFFgBEGxcPV2UaC14dQUVdJhNAIiAWWEUfC0o6UlhBV1wBAVMCT24Uah5CPXJfUGAEEQ9DXB4IGVQjG2YBAF8QY3wQbXJCGVNQEBFAUhkPExAeDUFOG1ldJFZYPyJMM3MCGQ5VUkVBNHYcA18LQV9dPV5AIiFLSxUCHRdFABZBA0IbBxILAVUyalYQbSAHBEACFkNWExQSEjoLDFZkZVdNJBVEJD0MUGAEEQ9DXBQOGEBGBVcaJl9MLwRGLD5OUEcFFg1ZHB9NV1YASzhOTxEYPhdDJnwRAFQHFktWBxYCA1kBDBpHZREYalYQbXJCB10ZFAYQAA0PGVkABRpHT1VXQFYQbXJCUBVQWEMQUhQOFFECQl0FQxFdOAQQcHISE1QcFEtWHFFrVxBOQhJOTxEYalYQJDRCHloEWAxbUgwJEl5OFVMcARkaES8CBg9CHFofCFkQUFhPWRAaDUEaHVhWLV5VPyBLWRUVFgc6UlhBVxBOQhJOTxEYJhlTLD5CFEFQRUNECwgEX1cLFnsAG1RKPBdcZHJfTRVSHhZeEQwIGF5MQlMACxFfLwJ5IyYHAkMRFEsZUhcTV1cLFnsAG1RKPBdcR3JCUBVQWEMQUlhBV0QPEVlAGFBRPl5UOXtoUBVQWEMQUlgEGVRkQhJOT1RWLl86KDwGej8WDQ1TBhEOGRA7FlsCHB9cIwVELDwBFR0RVENSW3JBVxBOC1ROAV5MahcQIiBCHloEWAEQBhAEGRAcB0YbHV8YJxdEJXwKBVIVWAZeFnJBVxBOEFcaGkNWal5RbX9CEhxeNQJXHBEVAlQLaFcACzsyZ1sQr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvageFVMVwNAQmArIn5sDyU6YH9CkqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xfVwBAVMCT2NdJxlEKCFCTRULWDxTExsJEhBTQkkTQxFnLwBVIyYRUAhQFgpcUgVrG18NA15OCURWKQJZIjxCFUMVFhdDWlFrVxBOQlsIT2NdJxlEKCFML1AGHQ1EAVgAGVROMFcDAEVdOVhvKCQHHkEDVjNRAB0PAxAaClcAT0NdPgNCI3IwFVgfDAZDXCcEAVUAFkFOCl9cQFYQbXIwFVgfDAZDXCcEAVUAFkFOUhFtPh9cPnwQFUYfFBVVIhkVHxgtDVwIBlYWDyB1AwYxL2UxLCsZeFhBVxAcB0YbHV8YGBNdIiYHAxsvHRVVHAwSfVUABjgIGl9bPh9fI3IwFVgfDAZDXB8EAxgFB0tHZREYalZZK3IwFVgfDAZDXCcCFlMGB2kFCkhlahdeKXIwFVgfDAZDXCcCFlMGB2kFCkhlZCZRPzcMBBUEEAZeUgoEA0UcDBI8ClxXPhNDYw0BEVYYHThbFwE8V1UABjhOTxEYJhlTLD5CHlQdHUMNUjsOGVYHBRw8Knx3HjNjFjkHCWhQFxEQGR0YfRBOQhICAFJZJlZVO3JfUFAGHQ1EAVBITBAHBBIAAEUYLwAQOToHHhUCHRdFABZBGVkCQlcACzsYalYQIT0BEVlQCkMNUh0XTXYHDFYoBkNLPjVYJD4GWFsRFQYZeFhBVxAHBBIcT0VQLxgQHzcPH0EVC01vERkCH1U1CVcXMhEFagQQKDwGehVQWENCFwwUBV5OEDgLAVUyLANeLiYLH1tQKgZdHQwEBB4IC0ALR1pdM1oQY3xMWT9QWEMQHhcCFlxOEBJTT2NdJxlEKCFMF1AEUAhVC1FaV1kIQlwBGxFKagJYKDxCAlAEDRFeUh4AG0MLQlcACzsYalYQIT0BEVlQGRFXAVhcV0QPAF4LQUFZKR0YY3xMWT9QWEMQAB0VAkIAQkINDl1UYhBFIzEWGVoeUEoQAEInHkILMVccGVRKYgJRLz4HXkAeCAJTGVAABVcdThJfQxFZOBFDYzxLWRUVFgcZeB0PEzoIF1wNG1hXJFZiKD8NBFADVgpeBBcKEhgFB0tCTx8WZF86bXJCUFkfGwJcUgpBShA8B18BG1RLZBFVOXoJFUxZQ0NZFFgPGEROEBIaB1RWagRVOScQHhUWGQ9DF1gEGVRkQhJOT11XKRdcbTMQF0ZQRUNEExoNEh4eA1EFRx8WZF86bXJCUFkfGwJcUgoEBEUCFkFOUhFDagZTLD4OWFMFFgBEGxcPXxlOEFcaGkNWagQKBDwUH14VKwZCBB0TX0QPAF4LQURWOhdTJnoDAlIDVEMBXlgABVcdTFxHRhFdJBIZbS9oUBVQWApWUhYOAxAcB0EbA0VLEUdtbSYKFVtQCgZEBwoPV1YPDkELT1RWLnwQbXJCBFQSFAYeAB0MGEYLSkALHERUPgUcbWNLehVQWENCFwwUBV5OFkAbCh0YPhdSITdMBVsAGQBbWgoEBEUCFkFHZVRWLnxWODwBBFwfFkNiFxUOA1UdTFEBAV9dKQIYJjcbXBUWFko6UlhBV1wBAVMCT0MYd1ZiKD8NBFADVgRVBlAKEklHaBJOTxFRLFZeIiZCAhUfCkNeHQxBBR4hDHECBlRWPjNGKDwWUEEYHQ0QAB0VAkIAQlwHAxFdJBI6bXJCUEcVDBZCHFgTWX8AIV4HCl9MDwBVIyZYM1oeFgZTBlAHAl4NFlsBARkWZFgZR3JCUBVQWEMQHhcCFlxODVlCT1RKOFYNbSIBEVkcUAVeXlhPWR5HaBJOTxEYalYQJDRCHloEWAxbUgwJEl5OFVMcARkaES8CBg9CE1oeFgZTBlhDWR4FB0tAQRMCalQeYyYNA0ECEQ1XWh0TBRlHQlcACzsYalYQKDwGWT8VFgc6eFVMV9L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2nwdYHJWXhUiNyx9UiokJH8iN2YnIH8yZ1sQr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvageBQOFFECQmABAFwYd1ZLMFhoXRhQOQ9cUiwWHkMaB1ZOO15XJFZdIjYHHEZQEQ0QBhAEV1MbEEALAUUYOBlfIFgEBVsTDApfHFgzGF8DTFULG2VPIwVEKDYRWBx6WEMQUhQOFFECQl0bGxEFag1NR3JCUBUcFwBRHlgTGF8DQg9OOF5KIQVALDEHSnMZFgd2GwoSA3MGC14KRxN7PwRCKDwWIlofFUEZeFhBVxAHBBIAAEUYOBlfIHIWGFAeWBFVBg0TGRABF0ZOCl9cQFYQbXIEH0dQJ08QFlgIGRAHElMHHUIQOBlfIGglFUE0HRBTFxYFFl4aERpHRhFcJXwQbXJCUBVQWApWUhxbPkMvShAjAFVdJlQZbSYKFVt6WEMQUlhBVxBOQhJOA15bKxoQI3JfUFFeNgJdF3JBVxBOQhJOTxEYalYdYHIhH1gdFw0QHBkMHl4JWBJSIVBVL0h9IjwRBFACVEN9HRYSA1UcERIIAF1cLwQQLjoLHFECHQ0cUhcTV1gPERIjAF9LPhNCbTMWBEcZGhZEF3JBVxBOQhJOTxEYalZZK3IMSlMZFgcYUDUOGUMaB0BMRhFXOFZUdxUHBHQEDBFZEA0VEhhMK0EjAF9LPhNCb3tCH0dQUAceIhkTEl4aQlMACxFcZCZRPzcMBBs+GQ5VUkVcVxIjDVwdG1RKOVQZbSYKFVt6WEMQUlhBVxBOQhJOTxEYahpfLjMOUF0CCEMNUhxbMVkABnQHHUJMCR5ZITZKUn0FFQJeHREFJV8BFmIPHUUaY1ZfP3IGXmUCEQ5RAAExFkIaaBJOTxEYalYQbXJCUBVQWENZFFgJBUBOFloLARFMKxRcKHwLHkYVChcYHQ0VWxAVQl8BC1RUaksQKX5CAlofDEMNUhATBxxODFMDChEFahgKKiEXEh1SNQxeAQwEBRRMThBMRhFFY1ZVIzZoUBVQWEMQUlhBVxBOB1wKZREYalYQbXJCFVsUckMQUlgEGVRkQhJOT0NdPgNCI3INBUF6HQ1UeHJMWhAvDl5OIlBbIh9eKHIPH1EVFBAQBREVHxAaClcHHRFbJRtAITcWGVoeWAdRBhlrEUUAAUYHAF8YGBlfIHwFFUE9GQBYGxYEBBhHaBJOTxFUJRVRIXINBUFQRUNLD3JBVxBODl0NDl0YOBlfIHJfUGIfCghDAhkCEgooC1wKKVhKOQJzJTsOFB1SOxZCAB0PA2IBDV9MRjsYalYQJDRCHloEWBFfHRVBA1gLDBIcCkVNOBgQIicWUFAeHGkQUlhBEV8cQm1CT1UYIxgQJCIDGUcDUBFfHRVbMFUaJlcdDFRWLhdeOSFKWRxQHAw6UlhBVxBOQhIHCRFccD9DDHpAPVoUHQ8SW1gAGVROSlZAIVBVL0xWJDwGWBc9GQBYGxYEVRlODUBOCx92KxtVdzQLHlFYWiRVHB0TFkQBEBBHT15KahIKCjcWMUEECgpSBwwEXxInEX8PDFlRJBMSZHtCBF0VFmkQUlhBVxBOQhJOTxFUJRVRIXIQH1oEWF4QFkInHl4KJFscHEV7Ih9cKQUKGVYYMRBxWlojFkMLMlMcGxMUagJCODdLehVQWEMQUlhBVxBOQlsIT0NXJQIQOToHHj9QWEMQUlhBVxBOQhJOTxEYJhlTLD5CAFYEWF4QFkImEkQvFkYcBlNNPhMYbxENHUUcHRdZHRYxEkINB1waDlZdaF86bXJCUBVQWEMQUlhBVxBOQhJOTxFXOFZUdxUHBHQEDBFZEA0VEhhMMkABCENdOQUSZFhCUBVQWEMQUlhBVxBOQhJOTxEYahlCbTZYN1AEORdEABEDAkQLShAtAFxIJhNEJD0MUhx6WEMQUlhBVxBOQhJOTxEYagJRLz4HXlweCwZCBlAOAkRCQklkTxEYalYQbXJCUBVQWEMQUlhBVxADDVYLAxEFahIcbSANH0FQRUNCHRcVWxAAA18LTwwYLlh+LD8HXD9QWEMQUlhBVxBOQhJOTxEYalYQbSIHAlYVFhcQT1gRFERCaBJOTxEYalYQbXJCUBVQWEMQUlhBFF8DEl4LG1QYd1ZUdxUHBHQEDBFZEA0VEhhMIV0DH11dPhNUb3tCTQhQDBFFF1gOBRAKWHULG3BMPgRZLycWFR1SMRBzHRURG1UaB1ZMRhEFd1ZEPycHXD9QWEMQUlhBVxBOQhJOTxEYN186bXJCUBVQWEMQUlhBEl4KaBJOTxEYalYQKDwGehVQWENVHBxrVxBOQkALG0RKJFZfOCZoFVsUcmkdX1giFl4BDFsNDl0YIwJVIHIMEVgVC0NWABcMV2ILEl4HDFBMLxJjOT0QEVIVVipEFxUsGFQbDlcdT9O43lZFPjcGUEEfWApUFxYVHlYXaB9DT0JIKwFeKDZCAFwTExZAAVgIGRAaCldODERKOBNeOXIQH1odWEtEGh0YUEILQlwPAlRcahNILDEWHExQFApbF1gVH1VOD10KGl1dY1g6Hz0NHRs5LCZ9LTYgOnU9Qg9OFDsYalYQBTcDHEEYMwpEUkVBA0IbBx5OP15IaksQOSAXFRlQKxNVFxwiFl4KGxJTT0VKPxMcbRADHlERHwYQT1gVBUULTjhOTxEYAxhDOSAXE0EZFw1DUkVBA0IbBx5OP15ICBlEOT4HUAhQDBFFF1RBPUUDElccLFBaJhMQcHIWAkAVVENkEwgEVw1OFkAbCh0yalYQbQIQH0EVEQ1yEwpBShAaEEcLQxFrJxlbKBANHVdQRUNEAA0EWxArCFcNG3NNPgJfI3JfUEECDQYcUjsJGFMBDlMaChEFagJCODdOehVQWEN3BxUDFlwCQg9OG0NNL1oQHiYNAEIRDABYUkVBA0IbBx5OPEVdKxpEJREDHlEJWF4QBgoUEhxOMVkHA117IhNTJhEDHlEJWF4QBgoUEhxkQhJOT3BROD5fPzxCTRUEChZVXlgkD0QcA1EaBl5WGQZVKDYhEVsUAUMNUgwTAlVCQmQPA0ddaksQOSAXFRlQOwtfERcNFkQLIF0WTwwYPgRFKH5oUBVQWCxCHBkMEl4aQg9OG0NNL1oQBzMVEkcVGQhVAFhcV0QcF1dCT2JMKxtZIzMhEVsUAUMNUgwTAlVCQnABAXNXJFYNbSYQBVBcckMQUlgiH0IHEUYDDkJ7JRlbJDdCTRUEChZVXlglFl4KG3cPHEVdODNXKiFCTRUEChZVXnIcfTpDTxIvA10YOh9TJjMAHFBQERdVHwtBHl5OFloLT1JNOARVIyZCAlofFWlWBxYCA1kBDBI8AF5VZBFVORsWFVgDUEo6UlhBV1wBAVMCT15NPlYNbSkfehVQWENcHRsAGxAcDV0DTwwYHRlCJiESEVYVQiVZHBwnHkIdFnEGBl1cYlRzOCAQFVsEKgxfH1pIfRBOQhIHCRFWJQIQPz0NHRUEEAZeUgoEA0UcDBIBGkUYLxhUR3JCUBUcFwBRHlgSElUAQg9OFEwyalYQbT4NE1QcWAVFHBsVHl8AQkYcFnBcLl5UZFhCUBVQWEMQUhEHV14BFhIKT15KagVVKDw5FGhQDAtVHFgTEkQbEFxOCl9cQFYQbXJCUBVQCwZVHCMFKhBTQkYcGlQyalYQbXJCUBVdVUN9EwwCHxAMGxILF1BbPlZZOTcPUFsRFQYQPSpBFUlOEkALHFRWKRMQIjRCERUgCgxIGxUIA0k+EF0DH0UYYhtfPiZCAFwTExZAAVgJFkYLQl0AChgyalYQbXJCUBUcFwBRHlgMFkQNClcdIVBVL1YNbQANH1heMTd1PycvNn0rMWkKQX9ZJxNtbW9fUEECDQY6UlhBVxBOQhICAFJZJlZYLCEyAlodCBcQT1gFTXYHDFYoBkNLPjVYJD4GJ10ZGwt5ATlJVWAcDUoHAlhMMyZCIj8SBBdcWBdCBx1IV05TQlwHAzsYalYQbXJCUFkfGwJcUhESI18BDlsdBxEFahIKBCEjWBckFwxcUFFBGEJOBggpCkV5PgJCJDAXBFBYWipDOwwEGhJHQl0cT1UCDRNEDCYWAlwSDRdVWlooA1UDK1ZMRhFGd1ZeJD5oUBVQWEMQUlgIERADA0YNB1RLBBddKHINAhUZCzdfHRQIBFhODUBOR1lZOSZCIj8SBBURFgcQFkIoBHFGQH8BC1RUaF8ZbSYKFVt6WEMQUlhBVxBOQhJOA15bKxoQPz0NBD9QWEMQUlhBVxBOQhIHCRFccD9DDHpAJFofFEEZUgwJEl5OEF0BGxEFahIKCzsMFHMZChBEMRAIG1RGQHoPAVVUL1QZR3JCUBVQWEMQUlhBV1UCEVcHCRFccD9DDHpAPVoUHQ8SW1gVH1UAQkABAEUYd1ZUYwIQGVgRChpgEwoVV18cQlZUKVhWLjBZPyEWM10ZFAdnGhECH3kdIxpMLVBLLyZRPyZAXBUEChZVW3JBVxBOQhJOTxEYalZVISEHGVNQHFl5ATlJVXIPEVc+DkNMaF8QOToHHhUCFwxEUkVBExALDFZkTxEYalYQbXJCUBVQEQUQABcOAxAaClcAZREYalYQbXJCUBVQWEMQUlgVFlICBxwHAUJdOAIYIicWXBULckMQUlhBVxBOQhJOTxEYalYQbXJCHVoUHQ8QT1gFWxAcDV0aTwwYOBlfOX5oUBVQWEMQUlhBVxBOQhJOTxEYalZeLD8HUAhQHE1+ExUETVcdF1BGTRljK1tKEHtKK3RdIj4ZUFRBVRVfQhdcTRgUalsdbXAxAFAVHCBRHBwYVRCM5KBOTWJILxNUbREDHlEJWmkQUlhBVxBOQhJOTxEYalYQMHtoUBVQWEMQUlhBVxBOB1wKZREYalYQbXJCFVsUckMQUlgEGVRkQhJOTxwVaiVTLDxCHVoUHQ9DUhkPExAaDV0CHBFZPlZVOzcQCRUUHRNEGlhJHkQLD0FOAlBBahRVbTsMUEYFGk5WHRQFEkIdSzhOTxEYLBlCbQ1OUFFQEQ0QGwgAHkIdSkABAFwCDRNECTcRE1AeHAJeBgtJXhlOBl1kTxEYalYQbXILFhUUQipDM1BDOl8KB15MRhFXOFZUdxsRMR1SLAxfHlpIV0QGB1xOG0NBCxJUZTZLUFAeHGkQUlhBEl4KaBJOTxFKLwJFPzxCH0AEcgZeFnJrWh1OLUYGCkMYOhpRNDcQAxJQDAxfHAtBX1UWAV4bC1hWLVZFPntoFkAeGxdZHRZBJV8BDxwJCkV3Ph5VPwYNH1sDUEo6UlhBV1wBAVMCT15NPlYNbSkfehVQWENcHRsAGxAeDlMXCkNLaksQGj0QG0YAGQBVSD4IGVQoC0AdG3JQIxpUZXArHnIRFQZgHhkYEkIdQBtkTxEYah9WbTwNBBUAFAJJFwoSV0QGB1xOHVRMPwRebT0XBBUVFgc6UlhBV1YBEBIxQxFVah9ebTsSEVwCC0tAHhkYEkIdWHULG3JQIxpUPzcMWBxZWAdfeFhBVxBOQhJOBlcYJ0x5PhNKUngfHAZcUFFBFl4KQl9AIVBVL1ZOcHIuH1YRFDNcEwEEBR4gA18LT0VQLxg6bXJCUBVQWEMQUlhBG18NA15OB0NIaksQIGgkGVsUPgpCAQwiH1kCBhpMJ0RVKxhfJDYwH1oEKAJCBlpIfRBOQhJOTxEYalYQbT4NE1QcWAtFH1hcV11UJFsAC3dROAVEDjoLHFE/HiBcEwsSXxImF18PAV5RLlQZR3JCUBVQWEMQUlhBV1kIQlocHxFMIhNebSYDElkVVgpeAR0TAxgBF0ZCT0oYJxlUKD5CTRUdVENCHRcVVw1OCkAeQxFWKxtVbW9CHRs+GQ5VXlgJAl0PDF0HCxEFah5FIHIfWRUVFgc6UlhBVxBOQhILAVUyalYQbTcMFD9QWEMQAB0VAkIAQl0bGztdJBI6R39PUGEYHUNVHh0XFkQBEBIeAEJRPh9fI3JKF1QEHUNEHVgPEkgaQlQCAF5KY3xWODwBBFwfFkNiHRcMWVcLFncCCkdZPhlCHT0RWBx6WEMQUhQOFFECQlcCCkcYd1ZnIiAJA0URGwYKNBEPE3YHEEEaLFlRJhIYbxcOFUMRDAxCAVpIfRBOQhIHCRFdJhNGbSYKFVt6WEMQUlhBVxACDVEPAxFIaksQKD4HBg82EQ1UNBETBEQtClsCC2ZQIxVYBCEjWBcyGRBVIhkTAxJCQkYcGlQRQFYQbXJCUBVQEQUQAlgVH1UAQkALG0RKJFZAYwINA1wEEQxeUh0PEzpOQhJOCl9cQBNeKVhoXRhQmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+aB9DTwQWaiVkDAYxehhdWIGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78jgCAFJZJlZjOTMWAxVNWBgQHxkCH1kAB0EqAF9daksQfX5CGUEVFRBgGxsKElROXxJeQxFdORVRPTcGN0cRGhAQT1hRWxAKB1MaB0IYd1YAYXIRFUYDEQxeIQwABUROXxIaBlJTYl8QMFgEBVsTDApfHFgyA1EaERwcCkJdPl4ZbQEWEUEDVg5RERAIGVUdJl0ACh0YGQJROSFMGUEVFRBgGxsKElRCQmEaDkVLZBNDLjMSFVE3CgJSAVRBJEQPFkFAC1RZPh5DbW9CQBlAVFMcQkNBJEQPFkFAHFRLOR9fIwEWEUcEWF4QBhECHBhHQlcACztePxhTOTsNHhUjDAJEAVYUB0QHD1dGRjsYalYQIT0BEVlQC0MNUhUAA1hABF4BAEMQPh9TJnpLUBhQKxdRBgtPBFUdEVsBAWJMKwREZFhCUBVQFAxTExRBHxBTQl8PG1kWLBpfIiBKAxVfWFAGQkhITBAdQg9OHBEVah4QZ3JRRgVAckMQUlgNGFMPDhIDTwwYJxdEJXwEHFofCktDUldBQQBHWRJOT0IYd1ZDbX9CHRVaWFUAeFhBVxAcB0YbHV8YOQJCJDwFXlMfCg5RBlBDUgBcBghLXwNccFMAfzZAXBUYVENdXlgSXjoLDFZkZRwVapSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6GkdX1hXWRArMWJOjbGsaiJHJCEWFVEDWEwQPxkCH1kAB0FOQBFxPhNdPnJNUGUcGRpVAAtrWh1OgKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgRz4NE1QcWCZjIlhcV0tkQhJOT2JMKwJVbW9CCz9QWEMQUlhBV0QZC0EaClUYd1ZWLD4RFRlQFQJTGhEPEhBTQlQPA0JdZlZZOTcPUAhQHgJcAR1NV0ACA0sLHREFahBRISEHXD9QWEMQUlhBV0QZC0EaClV8IwVELDwBFRVNWBdCBx1NfRBOQhJOTxEYOR5fOh0MHEwzFAxDF1hcV1YPDkELQxEYKRpfPjcwEVsXHUMNUk5RWzpOQhJOTxEYagJHJCEWFVEzFw9fAFhcV3MBDl0cXB9eOBldHxUgWAdFTU8QREhNVwZeSx5kTxEYalYQbXIPEVYYEQ1VMRcNGEJOXxItAF1XOEUeKyANHWc3OksBQEhNVwJcUh5OXgMIY1o6bXJCUBVQWENZBh0MNF8CDUBOTxEYd1ZzIj4NAgZeHhFfHyomNRhcVwdCTwMIeloQe2JLXD9QWEMQUlhBV0ACA0sLHXJXJhlCbXJfUHYfFAxCQVYHBV8DMHUsRwEUakQBfX5CQgdJUU86UlhBV01CaBJOTxFnPhdXPnJfUE5QDBRZAQwEExBTQkkTQxFVKxVYJDwHUAhQAx4cUhEVEl1OXxIVEh0YOhpRNDcQUAhQAx4QD1RrVxBOQm0NAF9WaksQNi9Oekh6cg9fERkNV1YbDFEaBl5WahtRJjcgMh0RHAxCHB0EWxAaB0oaQxFbJRpfP35CGFAZHwtEW3JBVxBODl0NDl0YKBQQcHIrHkYEGQ1TF1YPEkdGQHAHA11aJRdCKRUXGRdZckMQUlgDFR4gA18LTwwYaC8CBg0nI2VSQ0NSEFYgE18cDFcLTwwYKxJfPzwHFT9QWEMQEBpPJFkUBxJTT2R8IxsCYzwHBx1AVEMBSkhNVwBCQloLBlZQPlZfP3JRQBx6WEMQUhoDWWMaF1YdIFdeORNEbW9CJlATDAxCQVYPEkdGUh5OXB0Yel86bXJCUFcSViJcBRkYBH8ANl0eTwwYPgRFKGlCEldeNQJINhESA1EAAVdOUhEJekYAR3JCUBUcFwBRHlgNFlILDhJTT3hWOQJRIzEHXlsVD0sSJh0ZA3wPAFcCTRgyalYQbT4DElAcViFRERMGBV8bDFY6HVBWOQZRPzcME0xQRUMAXExrVxBOQl4PDVRUZDRRLjkFAloFFgdzHRQOBQNOXxItAF1XOEUeKyANHWc3OksBQlRBRgBCQgBeRjsYalYQITMAFVleKwpKF1hcV2UqC19cQVdKJRtjLjMOFR1BVEMBW0NBG1EMB15ALV5KLhNCHjsYFWUZAAZcUkVBRzpOQhJOA1BaLxoeCz0MBBVNWCZeBxVPMV8AFhwkGkNZcVZcLDAHHBskHRtEIREbEhBTQgNaZREYalZcLDAHHBskHRtEMRcNGEJdQg9ODF5UJQQLbT4DElAcVjdVCgxBShAaB0oaVBFUKxRVIXwyEUcVFhcQT1gDFTpOQhJOA15bKxoQPiYQH14VWF4QOxYSA1EAAVdAAVRPYlRlBAEWAlobHUEZeFhBVxAdFkABBFQWCRlcIiBCTRUTFw9fAENBBEQcDVkLQWVQIxVbIzcRAxVNWFIeR0NBBEQcDVkLQWFZOBNeOXJfUFkRGgZceFhBVxAMABw+DkNdJAIQcHIDFFoCFgZVeFhBVxAcB0YbHV8YKBQcbT4DElAccgZeFnJrG18NA15OCURWKQJZIjxCE1kVGRFyBxsKEkRGAEcNBFRMY3wQbXJCFloCWDwcUhoDV1kAQkIPBkNLYhRFLjkHBBxQHAw6UlhBVxBOQhIHCRFaKFZRIzZCEldeKAJCFxYVV0QGB1xODVMCDhNDOSANCR1ZWAZeFnJBVxBOB1wKZVRWLnw6IT0BEVlQHhZeEQwIGF5OF0IKDkVdCANTJjcWWFcFGwhVBlRBHkQLD0FCT1JXJhlCYXIEH0cdGRdEFwpIfRBOQhICAFJZJlZDKDcMUAhQAx46UlhBV1wBAVMCT24Uah5CPXJfUGAEEQ9DXB4IGVQjG2YBAF8QY3wQbXJCFloCWDwcUh1BHl5OC0IPBkNLYh9EKD8RWRUUF2kQUlhBVxBOQkELCl9jL1hCIj0WLRVNWBdCBx1rVxBOQhJOTxFUJRVRIXIAEhVNWAFFERMEA2sLTEABAEVlQFYQbXJCUBVQEQUQHBcVV1IMQkYGCl8YKBQQcHIPEV4VOiEYF1YTGF8aThILQV9ZJxMcbTENHFoCUVgQEA0CHFUaOVdAHV5XPisQcHIAEhUVFgc6UlhBVxBOQhICAFJZJlZcLDAHHBVNWAFSSD4IGVQoC0AdG3JQIxpUGjoLE105CyIYUCwED0QiA1ALAxMRQFYQbXJCUBVQEQUQHhkDElxOFloLATsYalYQbXJCUBVQWENcHRsAGxAKC0EaZREYalYQbXJCUBVQWApWUhATBxAaClcAT1VROQIQcHI3BFwcC01UGwsVFl4NBxoGHUEWGhlDJCYLH1tcWAYeABcOAx4+DUEHG1hXJF8QKDwGehVQWEMQUlhBVxBOQlsIT3RrGlhjOTMWFRsDEAxHPRYNDnMCDUELT1BWLlZUJCEWUFQeHENUGwsVVw5OJ2E+QWJMKwJVYzEOH0YVKgJeFR1BA1gLDDhOTxEYalYQbXJCUBVQWEMQEBpPMl4PAF4LCxEFahBRISEHehVQWEMQUlhBVxBOQlcCHFQyalYQbXJCUBVQWEMQUlhBV1IMTHcADlNULxIQcHIWAkAVckMQUlhBVxBOQhJOTxEYalZcLDAHHBskHRtEUkVBEV8cD1MaG1RKahdeKXIEH0cdGRdEFwpJEhxOBlsdGxgYJQQQKHwMEVgVckMQUlhBVxBOQhJOT1RWLnwQbXJCUBVQWAZeFnJBVxBOB1wKZREYalZWIiBCAlofDE8QEBpBHl5OElMHHUIQKANTJjcWWRUUF2kQUlhBVxBOQlsIT19XPlZDKDcMK0cfFxdtUgwJEl5kQhJOTxEYalYQbXJCGVNQGgEQBhAEGRAMAAgqCkJMOBlJZXtCFVsUckMQUlhBVxBOQhJOT1NNKR1VOQkQH1oEJUMNUhYIGzpOQhJOTxEYahNeKVhCUBVQHQ1UeB0PEzpkBEcADEVRJRgQCAEyXkYVDDdHGwsVElRGFBtkTxEYajNjHXwxBFQEHU1EBRESA1UKQg9OGTsYalYQJDRCHloEWBUQBhAEGRANDlcPHXNNKR1VOXonI2VeJxdRFQtPA0cHEUYLCxgDajNjHXw9BFQXC01EBRESA1UKQg9OFEwYLxhURzcMFD8WDQ1TBhEOGRArMWJAHFRMBxdTJTsMFR0GUWkQUlhBMmM+TGEaDkVdZBtRLjoLHlBQRUNGeFhBVxAHBBIAAEUYPFZEJTcMUFYcHQJCMA0CHFUaSnc9Px9nPhdXPnwPEVYYEQ1VW0NBMmM+TG0aDlZLZBtRLjoLHlBQRUNLD1gEGVRkB1wKZVdNJBVEJD0MUHAjKE1DFwwoA1UDSkRHZREYalZ1HgJMI0ERDAYeGwwEGhBTQkRkTxEYah9WbTwNBBUGWBdYFxZBFFwLA0AsGlJTLwIYCAEyXmoEGQRDXBEVEl1HWRIrPGEWFQJRKiFMGUEVFUMNUgMcV1UABjgLAVUyLANeLiYLH1tQPTBgXAsEA2ACA0sLHRlOY3wQbXJCNWYgVjBEEwwEWUACA0sLHREFagA6bXJCUFwWWA1fBlgXV0QGB1xODF1dKwRyODEJFUFYPTBgXCcVFlcdTEICDkhdOF8LbRcxIBsvDAJXAVYRG1EXB0BOUhFDN1ZVIzZoFVsUcmlWBxYCA1kBDBIrPGEWOQJRPyZKWT9QWEMQGx5BMmM+TG0NAF9WZBtRJDxCBF0VFkNCFwwUBV5OB1wKZREYalZ1HgJML1YfFg0eHxkIGRBTQmAbAWJdOABZLjdMOFARChdSFxkVTXMBDFwLDEUQLANeLiYLH1tYUWkQUlhBVxBOQlsIT3RrGlhjOTMWFRsEDwpDBh0FV0QGB1xkTxEYalYQbXJCUBVQDRNUEwwENUUNCVcaR3RrGlhvOTMFAxsEDwpDBh0FWxA8DV0DQVZdPiJHJCEWFVEDUEocUj0yJx49FlMaCh9MPR9DOTcGM1ocFxEcUh4UGVMaC10AR1QUahIZR3JCUBVQWEMQUlhBVxBOQhIHCRFcahdeKXInI2VeKxdRBh1PA0cHEUYLC3VROQJRIzEHUEEYHQ0QAB0VAkIAQhpMjauYalNDbQlHFEYEJUEZSB4OBV0PFhoLQV9ZJxMcbT8DBF1eHg9fHQpJExlHQlcACzsYalYQbXJCUBVQWEMQUlhBBVUaF0AATxPa0NYQb3JMXhUVVg1RHx1rVxBOQhJOTxEYalYQKDwGWT9QWEMQUlhBV1UABjhOTxEYalYQbTsEUHAjKE1jBhkVEh4DA1EGBl9dagJYKDxoUBVQWEMQUlhBVxBOF0IKDkVdCANTJjcWWHAjKE1vBhkGBB4DA1EGBl9dZlZiIj0PXlIVDC5RERAIGVUdShtCT3RrGlhjOTMWFRsdGQBYGxYENF8CDUBCT1dNJBVEJD0MWFBcWAcZeFhBVxBOQhJOTxEYalYQbXIOH1YRFENDUkVBVdL0+xJMTx8WahMeIzMPFT9QWEMQUlhBVxBOQhJOTxEYIxAQKHwBH1gAFAZEF1gVH1UAQkFOUhEaqOqjbRYtPnBSWAZeFnJBVxBOQhJOTxEYalYQbXJCGVNQHU1AFwoCEl4aQlMACxFWJQIQKHwBH1gAFAZEF1gVH1UAQkFOUhEQaJSq1HJHFBBVWkoKFBcTGlEaSl8PG1kWLBpfIiBKFRsAHRFTFxYVXhlOB1wKZREYalYQbXJCUBVQWEMQUlgIERAKQkYGCl8YOVYNbSFCXhtQUEEQKV0FBEQzQBtUCV5KJxdEZT8DBF1eHg9fHQpJExlHQlcACzsYalYQbXJCUBVQWEMQUlhBBVUaF0AAT0IyalYQbXJCUBVQWEMQFxYFXjpOQhJOTxEYahNeKVhCUBVQWEMQUhEHV3U9Mhw9G1BML1hZOTcPUEEYHQ06UlhBVxBOQhJOTxEYPwZULCYHMkATEwZEWj0yJx4xFlMJHB9RPhNdYXIwH1odVgRVBjEVEl0dShtCT3RrGlhjOTMWFRsZDAZdMRcNGEJCQlQbAVJMIxleZTdOUFFZckMQUlhBVxBOQhJOTxEYalZZK3IGUEEYHQ0QAB0VAkIAQhpMjaa+alNDbQlHFEYEJUEZSB4OBV0PFhoLQV9ZJxMcbT8DBF1eHg9fHQpJExlHQlcACzsYalYQbXJCUBVQWEMQUlhBBVUaF0AATxPa3fAQb3JMXhUVVg1RHx1rVxBOQhJOTxEYalYQKDwGWT9QWEMQUlhBV1UABjhOTxEYalYQbTsEUHAjKE1jBhkVEh4eDlMXCkMYPh5VI1hCUBVQWEMQUlhBVxAbElYPG1R6PxVbKCZKNWYgVjxEEx8SWUACA0sLHR0YGBlfIHwFFUE/DAtVACwOGF4dShtCT3RrGlhjOTMWFRsAFAJJFwoiGFwBEB5OCURWKQJZIjxKFRlQHEo6UlhBVxBOQhJOTxEYalYQbT4NE1QcWAtAUkVBEh4GF18PAV5RLlZRIzZCHVQEEE1WHhcOBRgLTFobAlBWJR9UYxoHEVkEEEoQHQpBVR1MaBJOTxEYalYQbXJCUBVQWENZFFgFV0QGB1xOHVRMPwRebXpAkqL/WEZDUiNEBFgeThJLC0JMF1QZdzQNAlgRDEtVXBYAGlVCQkYBHEVKIxhXZToSWRlQFQJEGlYHG18BEBoKRhgYLxhUR3JCUBVQWEMQUlhBVxBOQhIcCkVNOBgQb7D1/xVSWE0eUh1PGVEDBzhOTxEYalYQbXJCUBUVFgcZeFhBVxBOQhJOCl9cQFYQbXIHHlFZcgZeFnJrWh1OgKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgR39PUAJeWDBlIC4oIXEiQnorI2F9GCU6YH9CkqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xfVwBAVMCT2JNOABZOzMOUAhQA0NjBhkVEhBTQklkTxEYahhfOTsEGVACPQ1REBQEExBTQlQPA0JdZlZeIiYLFlwVCjFRHB8EVw1OUQdCT25UKwVEDD4HAkEVHEMNUkhNfRBOQhIPAUVRDQRRL3JfUFMRFBBVXnJBVxBOA0caAHBOJR9UbW9CFlQcCwYcUhkXGFkKMFMACFQYd1YCeH5oDRUNcmkdX1gvGEQHBFsLHRHayuIQPCcLE15QFw0dARsTElUAQlwBG1heM1ZHJTcMUFRQDBRZAQwEExALDEYLHUIYOBdeKjdoHFoTGQ8QFA0PFEQHDVxOAlBTLzhfOTsEGVACPhFRHx1JXjpOQhJOBlcYGQNCOzsUEVleJw1fBhEHDncbCxIaB1RWagRVOScQHhUjDRFGGw4AGx4xDF0aBldBDQNZbTcMFD9QWEMQHhcCFlxOEVVOUhFxJAVELDwBFRseHRQYUCsCBVULDHUbBhMRQFYQbXIRFxs+GQ5VUkVBVWlcKXYPAVVBBBlEJDQLFUdSckMQUlgSEB48B0ELG35WGQZROjxCTRUWGQ9DF3JBVxBOEVVANXhWLhNIDzcKEUMZFxEQT1gkGUUDTGgnAVVdMjRVJTMUGVoCVjBZEBQIGVdkQhJOT0JfZCZRPzcMBBVNWC9fERkNJ1wPG1ccVWZZIwJ2IiAhGFwcHEsSIhQADlUcJUcHTRgyalYQbT4NE1QcWBdcUkVBPl4dFlMADFQWJBNHZXA2FU0ENAJSFxRDXjpOQhJOG10WGR9KKHJfUGA0EQ4CXBYEABheThJdXQEUakYcbWFUWT9QWEMQBhRPJ18dC0YHAF8Yd1ZlCTsPQhseHRQYQlZUWxBDUwReQxEIZEcIYXJSWT9QWEMQBhRPNVENCVUcAERWLiJCLDwRAFQCHQ1TC1hcVwBAUAdkTxEYagJcYxADE14XCgxFHBwiGFwBEAFOUhF7JRpfP2FMFkcfFTF3MFBQRxxOUwJCTwMNY3wQbXJCBFlePgxeBlhcV3UAF19AKV5WPlh6OCADehVQWENEHlY1EkgaMVsUChEFakcGR3JCUBUEFE1kFwAVNF8CDUBdTwwYCRlcIiBRXlMCFw5iNTpJRQVbThJYXx0YfEYZR3JCUBUEFE1kFwAVVw1OQBBkTxEYagJcYwQLA1wSFAYQT1gHFlwdBzhOTxEYPhoeHTMQFVsEWF4QAR9rVxBOQl4BDFBUagVEPz0JFRVNWCpeAQwAGVMLTFwLGBkaHz9jOSANG1BSUVgQAQwTGFsLTHEBA15KaksQDj0OH0dDVgVCHRUzMHJGUAdbQxEOeloQe2JLSxUDDBFfGR1PI1gHAVkACkJLaksQf2lCA0ECFwhVXCgABVUAFhJTT0VUQFYQbXIOH1YRFENTHQoPEkJOXxInAUJMKxhTKHwMFUJYWjZ5MRcTGVUcQBtVT1JXOBhVP3whH0ceHRFiExwIAkNOXxI7K1hVZBhVOnpSXBVGUVgQERcTGVUcTGIPHVRWPlYNbSYOehVQWENjBwoXHkYPDhwxAV5MIxBJCicLUAhQCwQ6UlhBV2MbEEQHGVBUZCleIiYLFkw8GQFVHlhcV0QCaBJOTxFKLwJFPzxCA1J6HQ1UeHIHAl4NFlsBARFrPwRGJCQDHBsDHRd+HQwIEVkLEBoYRjsYalYQHicQBlwGGQ8eIQwAA1VADF0aBldRLwR1IzMAHFAUWF4QBHJBVxBOC1ROGRFMIhNeR3JCUBVQWEMQHxkKEn4BFlsIBlRKDARRIDdKWT9QWEMQUlhBV1kIQmEbHUdRPBdcYw0BH1seWBdYFxZBBVUaF0AAT1RWLnwQbXJCUBVQWDBFAA4IAVECTG0NAF9WaksQHycMI1ACDgpTF1YpElEcFlALDkUCCRleIzcBBB0WDQ1TBhEOGRhHaBJOTxEYalYQbXJCUFwWWA1fBlgyAkIYC0QPAx9rPhdEKHwMH0EZHgpVAD0PFlICB1ZOG1ldJFZCKCYXAltQHQ1UeFhBVxBOQhJOTxEYahpfLjMOUGpcWAtCAlhcV2UaC14dQVdRJBJ9NAYNH1tYUWkQUlhBVxBOQhJOTxFRLFZeIiZCGEcAWBdYFxZBBVUaF0AAT1RWLnwQbXJCUBVQWEMQUlgNGFMPDhIAClBKLwVEYXIGGUYEWF4QHBENWxADA0YGQVlNLRM6bXJCUBVQWEMQUlhBEV8cQm1CT0UYIxgQJCIDGUcDUDFfHRVPEFUaNkUHHEVdLgUYZHtCFFp6WEMQUlhBVxBOQhJOTxEYahpfLjMOUFFQRUNlBhENBB4KC0EaDl9bL15YPyJMIFoDERdZHRZNV0RAEF0BGx9oJQVZOTsNHhx6WEMQUlhBVxBOQhJOTxEYah9WbTZCTBUUERBEUgwJEl5OBlsdGxEFahILbTwHEUcVCxcQT1gVV1UABjhOTxEYalYQbXJCUBUVFgc6UlhBVxBOQhJOTxEYIxAQHicQBlwGGQ8eLRYOA1kIG34PDVRUagJYKDxoUBVQWEMQUlhBVxBOQhJOT1heahhVLCAHA0FQGQ1UUhwIBEROXg9OPERKPB9GLD5MI0ERDAYeHBcVHlYHB0A8Dl9fL1ZEJTcMehVQWEMQUlhBVxBOQhJOTxEYalYQHicQBlwGGQ8eLRYOA1kIG34PDVRUZCBZPjsAHFBQRUNEAA0EfRBOQhJOTxEYalYQbXJCUBVQWEMQIQ0TAVkYA15AMF9XPh9WNB4DElAcVjdVCgxBShBGQND0zxEdOVZ+CBMwUNfw7EMVFlgSA0UKERBHVVdXOBtROXoMFVQCHRBEXBYAGlVCQl8PG1kWLBpfIiBKFFwDDEoZeFhBVxBOQhJOTxEYalYQbXIHHEYVckMQUlhBVxBOQhJOTxEYalYQbXJCI0ACDgpGExRPKF4BFlsIFn1ZKBNcYwQLA1wSFAYQT1gHFlwdBzhOTxEYalYQbXJCUBVQWEMQFxYFfRBOQhJOTxEYalYQbTcMFD9QWEMQUlhBV1UABhtkTxEYahNeKVgHHlF6ck4dUjkPA1lDBUAPDRHayuIQLCcWHxgWERFVAVgyBkUHEF8vDVhUIwJJDjMME1AcWBRYFxZBEEIPAFALCztePxhTOTsNHhUjDRFGGw4AGx4dB0YvAUVRDQRRL3oUWT9QWEMQIQ0TAVkYA15APEVZPhMeLDwWGXICGQEQT1gXfRBOQhIHCRFOahdeKXIMH0FQKxZCBBEXFlxAPVUcDlN7JRhebSYKFVt6WEMQUlhBVxBDTxIiBkJMLxgQKz0QUFICGQEQFw4EGURVQkYGChFfKxtVbTQLAlADWDdHGwsVElQ9E0cHHVx/OBdSbSUKFVtQGwJFFRAVfRBOQhJOTxEYJhlTLD5CF0cRGjF1UkVBIkQHDkFAHVRLJRpGKAIDBF1YWjFVAhQIFFEaB1Y9G15KKxFVYxcUFVsEC01kBRESA1UKMUMbBkNVDQRRL3BLehVQWEMQUlhBHlZOBUAPDWN9ahdeKXIFAlQSKiYePRYiG1kLDEYrGVRWPlZEJTcMehVQWEMQUlhBVxBOQmEbHUdRPBdcYw0FAlQSOwxeHFhcV1ccA1A8Kh93JDVcJDcMBHAGHQ1ESDsOGV4LAUZGCURWKQJZIjxKXhteUWkQUlhBVxBOQhJOTxEYalYQJDRCHloEWDBFAA4IAVECTGEaDkVdZBdeOTslAlQSWBdYFxZBBVUaF0AAT1RWLnwQbXJCUBVQWEMQUlhBVxBOFlMdBB9PKx9EZWJMQABZckMQUlhBVxBOQhJOTxEYalZiKD8NBFADVgVZAB1JVWMfF1scAnJZJBVVIXBLehVQWEMQUlhBVxBOQhJOTxFrPhdEPnwHA1YRCAZUNQoAFUNOXxI9G1BMOVhVPjEDAFAUPxFREAtBXBBfaBJOTxEYalYQbXJCUFAeHEo6UlhBVxBOQhILAVUyalYQbTcOA1AZHkNeHQxBARAPDFZOPERKPB9GLD5ML1ICGQFzHRYPV0QGB1xkTxEYalYQbXIxBUcGERVRHlY+EEIPAHEBAV8CDh9DLj0MHlATDEsZSVgyAkIYC0QPAx9nLQRRLxENHltQRUNeGxRrVxBOQlcACztdJBI6R39PUHEVGRdYUhsOAl4aB0BkPVRVJQJVPnwBH1seHQBEWlolElEaChBCT1dNJBVEJD0MWBxQKxdRBgtPE1UPFlodTwwYGQJROSFMFFARDAtDUlNBRhALDFZHZTsVZ1bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fM6X1VBTx5OL3MtJ3h2D1ZxGAYtPXQkMSx+Uprh4xAvF0YBT2JTIxpcbREKFVYbck4dUpr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/zsVZ1ZkJTdCA1ACDgZCUhwOEkNUQhI9BFhUJhVYKDEJJUUUGRdVSDEPAV8FB3ECBlRWPl5AITMbFUdcWARVHB0TFkQBEB5ODkNfOV86YH9CB10VCgYQEwoGBBACDV0FHBFUIx1VbSlCBEwAHUMNUloCHkINDldMExNMOBNRKT8LHFlSVENSHQ0PE1EcG2EHFVQYd1Z+YXIWEUcXHRcfAhcSHkQHDVxBDFRWPhNCbW9CJBlQVk0eUgVrWh1ONloLT1JUIxNeOXIPBUYEWBFVBg0TGRAPQlwbAlNdOFZZI3I5QBteST4QBhAAAxACA1wKHBFRJAVZKTdCBF0VWARCFx0PV0oBDFdkQhwYKRNeOTcQFVFQFw0QJlgWHkQGQloPA1cVPR9UOTpCEloFFgdRAAEyHkoLTQBAZRwVQFsdbQEWAlQEHQRJSFgTElEKQkYGChFMKwRXKCZCFlwVFAcQFAoOGhAPEFUdTxlPL1ZEPytCFUMVChoQERcMGl8AQlwPAlQRZHwdYHIrFhUHHUNTExZGAxAIC1wKT1hMZlZWLD4OUFcRGwgQBhdBFhAdFlMaBlIYPBdcODdCBF0VWBZDFwpBFFEAQkYbAVQWQBpfLjMOUHgRGwtZHB1BShAVQmEaDkVdaksQNlhCUBVQGRZEHSsKHlwCAVoLDFoYd1ZWLD4RFRl6WEMQUhkUA189CVsCA1JQLxVbCTcOEUxQRUMAXnJBVxBOBFMCA1NZKR1mLD4XFRVNWFMeR1RBVxBOTx9OAF9UM1ZFPjcGUEIYHQ0QHBdBA1EcBVcaT1dRLxpUbTsRUFweWAJCFQtrVxBOQlYLDURfGgRZIyZCUBVNWAVRHgsEWxBOQh9DT0FKIxhEPnIDAlIDWAxeER1BAFgLDBIaAFZfJhNURy8fej9dVUN+PSwkTRA8DVACAEkYLhlVPnIsP2FQGQ9cHQ9BBVUPBlsACBFKLFh/IxEOGVAeDCpeBBcKEhBGFUAHG1QVJRhcNHtMehhdWDRVUhsAGRcaQkEPGVQYPh5VbT0QGVIZFgJcUhAAGVQCB0BAT3heagJYKHIFEVgVXxAQJzFBBFUaERIHGx0YJQNCPnIVGVkcWBFVAhQAFFVOC0ZkQhwYYhdeKXIUGVYVWBVVAAsAXh5ONVMaDFlcJREQJycRBBUCHU5RAggNHlUdQl0bHUIYLwBVPytCQBtFC0NHGwwJGEUaQlEGClJTIxhXY1gOH1YRFENvGhkPE1wLEHMNG1hOL1YNbTQDHEYVcg9fERkNV28CA0EaK1RaPxFkJD8HUAhQSGk6X1VBI0IHB0FOCkddOA8QLj0PHVoeWA1RHx1BEV8cQkYGChEaPhdCKjcWUEUfCwpEGxcPVRBBQhANCl9MLwQSbTQLFVkUWApeUhkTEENAaF4BDFBUahBFIzEWGVoeWAZIBgoAFEQ6A0AJCkUQKwRXPntoUBVQWApWUgwYB1VGA0AJHBgYNEsQbyYDElkVWkNEGh0PV0ILFkccARFWIxoQKDwGehVQWEMdX1glHkILAUZOAURVLwRZLnIEGVAcHBA6UlhBV1YBEBIxQxFTah9ebTsSEVwCC0tLeFhBVxBOQhJOTUVZOBFVOXBOUBcEGRFXFwwxGEMHFlsBARMUalRAIiELBFwfFkEcUloCEl4aB0BMQxEaKRNeOTcQIFoDWk86UlhBVxBOQhJMCklILxVEKDZAXBVSCAZCFB0CA2ABEVsaBl5WaFoQbzoLBGUfCwpEGxcPVRxOQFwLClVUL1QcR3JCUBVQWEMQUAIOGVUtB1waCkMaZlYSLjsQE1kVOwZeBh0TVRxOQF8HC0FXIxhEb35CUkMRFBZVUFRrVxBOQk9HT1VXQFYQbXJCUBVQFAxTExRBARBTQlMcCEJjISs6bXJCUBVQWENZFFgVDkALSkRHTwwFalReOD8AFUdSWBdYFxZBBVUaF0AAT0cYLxhUR3JCUBUVFgc6UlhBVx1DQmEBAlRMIxtVPnIMFUYEHQcQGxYSHlQLQlNOTUtXJBMSbT0QUBcSFxZeFhkTDhJOFlMMA1QyalYQbTQNAhUvVENbUhEPV1keA1scHBlDalRKIjwHUhlQWgFfBxYFFkIXQB5OTUJTIxpcLjoHE15SVEMSARMIG1wtClcNBBMYN18QKT1oUBVQWEMQUlgNGFMPDhIdGlMYd1ZRPzURK14tckMQUlhBVxBOC1ROG0hIL15DODBLUAhNWEFEExoNEhJOFloLATsYalYQbXJCUBVQWENWHQpBKBxOCQBOBl8YIwZRJCARWE5QWgBVHAwEBRJCQhAeAEJRPh9fI3BOUBcEGRFXFwxDWxBMD1sKH15RJAISbS9LUFEfckMQUlhBVxBOQhJOTxEYalZZK3IWCUUVUBBFECMKRW1HQg9TTxNWPxtSKCBAUEEYHQ0QAB0VAkIAQkEbDWpTeCsQKDwGehVQWEMQUlhBVxBOQlcACzsYalYQbXJCUFAeHGkQUlhBEl4KaBJOTxFKLwJFPzxCHlwccgZeFnJrWh1OMkALG0VBZwZCJDwWAxURWBdREBQEV0QBQkYGChFbJRhDIj4HUB0fFgYQHh0XElxOBlcLHxgyJhlTLD5CFkAeGxdZHRZBE0UDEnMcCEIQKwRXPntoUBVQWApWUgwYB1VGA0AJHBgYNEsQbyYDElkVWkNEGh0PV0AcC1waRxNjE0R7bRYDHlEJJUNDGRENGxANClcNBBFZOBFDd3BOUFQCHxAZSVgTEkQbEFxOCl9cQFYQbXISAlweDEsSKSFTPBAqA1wKFmwYd0sNbSEJGVkcWABYFxsKV1EcBUFOUgwFaF86bXJCUFMfCkNbXlgXV1kAQkIPBkNLYhdCKiFLUFEfckMQUlhBVxBOC1ROG0hIL15GZHJfTRVSDAJSHh1DV0QGB1xkTxEYalYQbXJCUBVQCBFZHAxJVRBOQB5OBB0YaEsQNnBLehVQWEMQUlhBVxBOQlQBHRFTeFoQO2BCGVtQCAJZAAtJARlOBl1OH0NRJAIYb3JCUBVQWEEcUhNTWxBMXxBCT0cKY1ZVIzZoUBVQWEMQUlhBVxBOEkAHAUUQaFYQMHBLehVQWEMQUlhBElwdBzhOTxEYalYQbXJCUBUACgpeBlBDVxBMThIFQxEad1QcbSROUBdYWk0eBgEREhgYSxxATRgaY3wQbXJCUBVQWAZeFnJBVxBOB1wKZVRWLnw6IT0BEVlQHhZeEQwIGF5ODUccPFpRJhpzJTcBG30RFgdcFwpJB1wPG1ccQxFfLxhVPzMWH0dcWAJCFQtIfRBOQhJDQhF8LxRFKnISAlweDEMYHRYEWkMGDUZOH1RKagJfKjUOFRUEF0NRBBcIExAdElMDRjsYalYQJDRCPVQTEApeF1YyA1EaBxwKClNNLSZCJDwWUFQeHEMYBhECHBhHQh9OMF1ZOQJ0KDAXF2EZFQYZUkZBRhAaClcAZREYalYQbXJCL1kRCxd0FxoUEGQHD1dOUhFMIxVbZXtoUBVQWEMQUlgFAl0eI0AJHBlZOBFDZFhCUBVQHQ1UeHJBVxBOC1ROAV5MajtRLjoLHlBeKxdRBh1PFkUaDWEFBl1UKR5VLjlCBF0VFmkQUlhBVxBOQh9DT2NdPgNCIzsMFxUeFxdYGxYGV10PCVcdT0VQL1ZDKCAUFUdXC0MKOxYXGFsLIV4HCl9MagJYPz0VUNfw7ENSBwxBAFVOClMYChFWJXwQbXJCUBVQWE4dUg8ADhAaDRIIAENPKwRUbSYNUEEYHUNfABEGHl4PDhIGDl9cJhNCbXowH1ccFxsQFBcTFVkKERIcClBcIxhXbR0MM1kZHQ1EOxYXGFsLSxxkTxEYalYQbXJPXRUjF0NZFFgYGEVOFVMAGxFMIhMQPzcFBVkRCkNlO1gDFlMFThIaGkNWagJYKHIWH1IXFAYQHR4HV1EABhIcCltXIxgeR3JCUBVQWEMQAB0VAkIAaBJOTxFdJBI6R3JCUBUZHkN9ExsJHl4LTGEaDkVdZBdFOT0xG1wcFABYFxsKM1UCA0tOUREIagJYKDxoUBVQWEMQUlgVFkMFTEUPBkUQBxdTJTsMFRsjDAJEF1YAAkQBMVkHA11bIhNTJhYHHFQJUWkQUlhBEl4KaDhOTxEYZ1sQCzsQA0FQDBFJSFgTEkQbEFxOG1ldagJRPzUHBBUEEAYQAR0TAVUcQlsaHFRULFZDKDwWUEADckMQUlgNGFMPDhIaDkNfLwIQcHIHCEECGQBEJhkTEFUaSlMcCEIRQFYQbXILFhUEGRFXFwxBA1gLDBIcCkVNOBgQOTMQF1AEWAZeFnJrVxBOQh9DT3dZJhpSLDEJUB0fFg9JUg0SElROFVoLARFWJVZELCAFFUFQHgpVHhxBEV8bDFZOBl8YKwRXPntoUBVQWBFVBg0TGRAjA1EGBl9dZCVELCYHXlMRFA9SExsKIVECF1dkCl9cQHxcIjEDHBUWDQ1TBhEOGRAHDEEaDl1UAhdeKT4HAh1ZckMQUlgNGFMPDhIcCREFaiNEJD4RXkcVCwxcBB0xFkQGShA8CkFUIxVROTcGI0EfCgJXF1YkAVUAFkFAPFpRJhpTJTcBG2AAHAJEF1pIfRBOQhIHCRFWJQIQPzRCH0dQFgxEUgoHTXkdIxpMPVRVJQJVCycME0EZFw0SW1gVH1UAQkALG0RKJFZWLD4RFRUVFgc6UlhBVx1DQmU8JmV9Zzl+AQtYUFsVDgZCUgoEFlROEFRAIF97Jh9VIyYrHkMfEwY6UlhBV0IITH0ALF1RLxhEBDwUH14VWF4QHQ0TJFsHDl4tB1RbIT5RIzYOFUd6WEMQUicJFl4KDlccLlJMIwBVbW9CBEcFHWkQUlhBBVUaF0AAT0VKPxM6KDwGej8cFwBRHlgHAl4NFlsBARFLPhdCOQUDBFYYHAxXWlFrVxBOQlsIT3xZKR5ZIzdML0IRDABYFhcGV0QGB1xOHVRMPwRebTcMFD9QWEMQPxkCH1kABxwxGFBMKR5UIjVCTRUEGRBbXAsRFkcASlQbAVJMIxleZXtoUBVQWEMQUlgWH1kCBxIjDlJQIxhVYwEWEUEVVgJFBhcyHFkCDlEGClJTahlCbR8DE10ZFgYeIQwAA1VABlcMGlZoOB9eOXIGHz9QWEMQUlhBVxBOQhJDQhFqL1tHPzsWFRUEEAYQGhkPE1wLEBIeCkNRJRJZLjMOHExQEQ0QERkSEhAaCldOCFBVL1FDbQcrUEcVVRBVBlgIAx5kQhJOTxEYalYQbXJCXRhQLwYQERkPUEROAVoLDFoYPR5fbT0VHkZQERcQkPj1V0cLQlgbHEUYJQBVPyUQGUEVVmkQUlhBVxBOQhJOTxFRJAVELD4OOFQeHA9VAFBIfRBOQhJOTxEYalYQbSYDA15eDwJZBlBQWQBHaBJOTxEYalYQKDwGehVQWEMQUlhBOlENClsACh9nPRdELjoGH1JQRUNeGxRrVxBOQlcACxgyLxhUR1gEBVsTDApfHFgsFlMGC1wLQUJdPjdFOT0xG1wcFABYFxsKX0ZHaBJOTxF1KxVYJDwHXmYEGRdVXBkUA189CVsCA1JQLxVbbW9CBj9QWEMQGx5BARAaClcAT1hWOQJRIT4qEVsUFAZCWlFaV0MaA0AaOFBMKR5UIjVKWRUVFgc6FxYFfToIF1wNG1hXJFZ9LDEKGVsVVhBVBjwEFUUJMkAHAUUQPF86bXJCUHgRGwtZHB1PJEQPFldAC1RaPxFgPzsMBBVNWBU6UlhBV1kIQkROG1ldJFZZIyEWEVkcMAJeFhQEBRhHWRIdG1BKPiFROTEKFFoXUEoQFxYFfVUABjhkQhwYqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgck4dUkFPV3E7Nn1OP3h7ASNgR39PUNfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr05zoCDVEPAxF5PwJfHTsBG0AAWF4QCVgyA1EaBxJTT0oYOANeIzsMFxVNWAVRHgsEWxAcA1wJChEFakcCYXILHkEVChVRHlhcVwBAVxITT0wyLANeLiYLH1tQORZEHSgIFFsbEhwdG1BKPl4ZR3JCUBUZHkNxBwwOJ1kNCUceQWJMKwJVYyAXHlsZFgQQBhAEGRAcB0YbHV8YLxhUR3JCUBUxDRdfIhECHEUeTGEaDkVdZARFIzwLHlJQRUNEAA0EfRBOQhI7G1hUOVhcIj0SWFMFFgBEGxcPXxlOEFcaGkNWajdFOT0yGVYbDRMeIQwAA1VAC1waCkNOKxoQKDwGXD9QWEMQUlhBV1YbDFEaBl5WYl8QPzcWBUceWCJFBhcxHlMFF0JAPEVZPhMePycMHlweH0NVHBxNV1YbDFEaBl5WYl86bXJCUBVQWEMQUlhBG18NA15OMB0YIgRAbW9CJUEZFBAeFBEPE30XNl0BARkRQFYQbXJCUBVQWEMQUhEHV14BFhIGHUEYPh5VI3IQFUEFCg0QFxYFfRBOQhJOTxEYalYQbTQNAhUvVENZBh0MV1kAQlseDlhKOV5iIj0PXlIVDCpEFxUSXxlHQlYBZREYalYQbXJCUBVQWEMQUlgIERA7FlsCHB9cIwVELDwBFR0YChMeIhcSHkQHDVxCT1hMLxsePz0NBBsgFxBZBhEOGRlOXg9OLkRMJSZZLjkXABsjDAJEF1YTFl4JBxIaB1RWQFYQbXJCUBVQWEMQUlhBVxBOQhJOQhwYHRdcJnINBlACWBdYF1gIA1UDQkAPG1ldOFZEJTMMUFEZCgZTBlgVElwLEl0cGxFMJVZROz0LFBUDCAZVFlgHG1EJaBJOTxEYalYQbXJCUBVQWEMQUlhBH0IeTHEoHVBVL1YNbREkAlQdHU1eFw9JHkQLDxwcAF5MZCZfPjsWGVoeWEgQJB0CA18cURwACkYQeloQf35CQBxZckMQUlhBVxBOQhJOTxEYalYQbXJCI0ERDBAeGwwEGkM+C1EFClUYd1ZjOTMWAxsZDAZdASgIFFsLBhJFTwAyalYQbXJCUBVQWEMQUlhBVxBOQhIaDkJTZAFRJCZKQBtBTUo6UlhBVxBOQhJOTxEYalYQbTcMFD9QWEMQUlhBVxBOQhILAVUyalYQbXJCUBUVFgcZeB0PEzoIF1wNG1hXJFZxOCYNIFwTExZAXAsVGEBGSxIvGkVXGh9TJicSXmYEGRdVXAoUGV4HDFVOUhFeKxpDKHIHHlF6ck4dUpr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/zsVZ1YBfXxCPXomPS51PCxBX0MPBFdOHVBWLRNDdnIFEVgVWAtRAVgAV0MLEEQLHRxLIxJVbSESFVAUWABYFxsKXjpDTxKM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MJoHFoTGQ8QPxcXEl0LDEZOUhFDaiVELCYHUAhQA2kQUlhBAFECCWEeClRcaksQfGdOUF8FFRNgHQ8EBRBTQgdeQxFRJBB6OD8SUAhQHgJcAR1NV14BAV4HHxEFahBRISEHXD9QWEMQFBQYVw1OBFMCHFQUahBcNAESFVAUWF4QR0hNV1EAFlsvKXoYd1ZEPycHXBUDGRVVFigOBBBTQlwHAx0yalYQbTAbAFQDCzBAFx0FNFEeQg9OCVBUORMcbX9PUFwWWBZDFwpBAFEAFkFOB1hfIhNCbSYKEVtQKyJ2NycsNmgxMWIrKnUyN1oQEjENHltQRUNLD1gcfToCDVEPAxFePxhTOTsNHhURCBNcCzAUGlEADVsKRxgyalYQbT4NE1QcWDwcUidNV1gbDxJTT2RMIxpDYzQLHlE9ATdfHRZJXgtOC1ROAV5Mah5FIHIWGFAeWBFVBg0TGRALDFZkTxEYah5FIHw1EVkbKxNVFxxBShAjDUQLAlRWPlhjOTMWFRsHGQ9bIQgEElRkQhJOT0FbKxpcZTQXHlYEEQxeWlFBH0UDTHgbAkFoJQFVP3JfUHgfDgZdFxYVWWMaA0YLQVtNJwZgIiUHAhUVFgcZeFhBVxAeAVMCAxlePxhTOTsNHh1ZWAtFH1Y0BFUkF18eP15PLwQQcHIWAkAVWAZeFlFrEl4KaFQbAVJMIxlebR8NBlAdHQ1EXAsEA2cPDlk9H1RdLl5GZFhCUBVQDkMNUgwOGUUDAFccR0cRahlCbWNXehVQWENZFFgPGEROL10YClxdJAIeHiYDBFBeGhpAEwsSJEALB1YtDkEYKxhUbSRCThUzFw1WGx9PJHEoJ20jLmlnGSZ1CBZCBF0VFkNGUkVBNF8ABFsJQWJ5DDNvABM6L2YgPSZ0Uh0PEzpOQhJOIl5OLxtVIyZMI0ERDAYeBRkNHGMeB1cKTwwYPHwQbXJCEUUAFBp4BxUAGV8HBhpHZVRWLnxWODwBBFwfFkN9HQ4EGlUAFhwdCkVyPxtAHT0VFUdYDkoQPxcXEl0LDEZAPEVZPhMeJycPAGUfDwZCUkVBA18AF18MCkMQPF8QIiBCRQVLWAJAAhQYP0UDA1wBBlUQY1ZVIzZoFkAeGxdZHRZBOl8YB18LAUUWORNEBDwEOkAdCEtGW3JBVxBOL10YClxdJAIeHiYDBFBeEQ1WOA0MBxBTQkRkTxEYah9WbSRCEVsUWA1fBlgsGEYLD1cAGx9nKRleI3wLHlM6DQ5AUgwJEl5kQhJOTxEYalZ9IiQHHVAeDE1vERcPGR4HDFQkGlxIaksQGCEHAnweCBZEIR0TAVkNBxwkGlxIGBNBODcRBA8zFw1eFxsVX1YbDFEaBl5WYl86bXJCUBVQWEMQUlhBHlZODF0aT3xXPBNdKDwWXmYEGRdVXBEPEXobD0JOG1ldJFZCKCYXAltQHQ1UeFhBVxBOQhJOTxEYahpfLjMOUGpcWDwcUhAUGhBTQmcaBl1LZBBZIzYvCWEfFw0YW3JBVxBOQhJOTxEYalZZK3IKBVhQDAtVHFgJAl1UIVoPAVZdGQJROTdKNVsFFU14BxUAGV8HBmEaDkVdHg9AKHwoBVgAEQ1XW1gEGVRkQhJOTxEYalZVIzZLehVQWENVHgsEHlZODF0aT0cYKxhUbR8NBlAdHQ1EXCcCGF4ATFsACXtNJwYQOToHHj9QWEMQUlhBV30BFFcDCl9MZClTIjwMXlweHilFHwhbM1kdAV0AAVRbPl4ZdnIvH0MVFQZeBlY+FF8ADBwHAVdyPxtAbW9CHlwcckMQUlgEGVRkB1wKZVdNJBVEJD0MUHgfDgZdFxYVWUMLFnwBDF1ROl5GZFhCUBVQNQxGFxUEGURAMUYPG1QWJBlTITsSUAhQDmkQUlhBHlZOFBIPAVUYJBlEbR8NBlAdHQ1EXCcCGF4ATFwBDF1ROlZEJTcMehVQWEMQUlhBOl8YB18LAUUWFRVfIzxMHloTFApAUkVBJUUAMVccGVhbL1hjOTcSAFAUQiBfHBYEFERGBEcADEVRJRgYZFhCUBVQWEMQUlhBVxAHBBIAAEUYBxlGKD8HHkFeKxdRBh1PGV8NDlseT0VQLxgQPzcWBUceWAZeFnJBVxBOQhJOTxEYalZcIjEDHBUTEAJCUkVBO18NA14+A1BBLwQeDjoDAlQTDAZCSVgIERAADUZODFlZOFZEJTcMUEcVDBZCHFgEGVRkQhJOTxEYalYQbXJCFloCWDwcUghBHl5OC0IPBkNLYhVYLCBYN1AEPAZDER0PE1EAFkFGRhgYLhk6bXJCUBVQWEMQUlhBVxBOQlsIT0ECAwVxZXAgEUYVKAJCBlpIV1EABhIeQXJZJDVfIT4LFFBQDAtVHFgRWXMPDHEBA11RLhMQcHIEEVkDHUNVHBxrVxBOQhJOTxEYalYQKDwGehVQWEMQUlhBEl4KSzhOTxEYLxpDKDsEUFsfDENGUhkPExAjDUQLAlRWPlhvLj0MHhseFwBcGwhBA1gLDDhOTxEYalYQbR8NBlAdHQ1EXCcCGF4ATFwBDF1ROkx0JCEBH1seHQBEWlFaV30BFFcDCl9MZClTIjwMXlsfGw9ZAlhcV14HDjhOTxEYLxhURzcMFD8cFwBRHlgHAl4NFlsBARFLPhdCORQOCR1ZckMQUlgNGFMPDhIxQxFQOAYcbToXHRVNWDZEGxQSWVYHDFYjFmVXJRgYZGlCGVNQFgxEUhATBxABEBIAAEUYIgNdbSYKFVtQCgZEBwoPV1UABjhOTxEYJhlTLD5CEkNQRUN5HAsVFl4NBxwACkYQaDRfKSs0FVkfGwpEC1pITBAMFBwjDkl+JQRTKHJfUGMVGxdfAEtPGVUZSgMLVh0JL08cfDdbWQ5QGhUeJB0NGFMHFktOUhFuLxVEIiBRXlsVD0sZSVgDAR4+A0ALAUUYd1ZYPyJoUBVQWA9fERkNV1IJQg9OJl9LPhdeLjdMHlAHUEFyHRwYMEkcDRBHVBFaLVh9LCo2H0cBDQYQT1g3ElMaDUBdQV9dPV4BKGtOQVBJVFJVS1FaV1IJTGJOUhEJL0ILbTAFXmURCgZeBlhcV1gcEjhOTxEYBxlGKD8HHkFeJwBfHBZPEVwXIGRCT3xXPBNdKDwWXmoTFw1eXB4NDnIpQg9ODUcUahRXR3JCUBUYDQ4eIhQAA1YBEF89G1BWLlYNbSYQBVB6WEMQUjUOAVUDB1waQW5bJRheYzQOCWAAHAJEF1hcV2IbDGELHUdRKRMeHzcMFFACKxdVAggEEwotDVwAClJMYhBFIzEWGVoeUEo6UlhBVxBOQhIHCRFWJQIQAD0UFVgVFhceIQwAA1VABF4XT0VQLxgQPzcWBUceWAZeFnJBVxBOQhJOT11XKRdcbTEDHRVNWBRfABMSB1ENBxwtGkNKLxhEDjMPFUcRckMQUlhBVxBODl0NDl0YJ1YNbQQHE0EfClAeHB0WXxlkQhJOTxEYalZZK3I3A1ACMQ1ABwwyEkIYC1ELVXhLARNJCT0VHh01FhZdXDMEDnMBBldAOBgYalYQbXJCUBUEEAZeUhVBShADQhlODFBVZDV2PzMPFRs8FwxbJB0CA18cQlcACzsYalYQbXJCUFwWWDZDFwooGUAbFmELHUdRKRMKBCEpFUw0FxReWj0PAl1AKVcXLF5cL1hjZHJCUBVQWEMQUgwJEl5ODxJTT1wYZ1ZTLD9MM3MCGQ5VXDQOGFs4B1EaAEMYLxhUR3JCUBVQWEMQGx5BIkMLEHsAH0RMGRNCOzsBFQ85CyhVCzwOAF5GJ1wbAh9zLw9zIjYHXnRZWEMQUlhBVxBOFloLARFVaksQIHJPUFYRFU1zNAoAGlVAMFsJB0VuLxVEIiBCFVsUckMQUlhBVxBOC1ROOkJdOD9ePScWI1ACDgpTF0IoBHsLG3YBGF8QDxhFIHwpFUwzFwdVXDxIVxBOQhJOTxEYPh5VI3IPUAhQFUMbUhsAGh4tJEAPAlQWGB9XJSY0FVYEFxEQFxYFfRBOQhJOTxEYIxAQGCEHAnweCBZEIR0TAVkNBwgnHHpdMzJfOjxKNVsFFU17FwEiGFQLTGEeDlJdY1YQbXJCBF0VFkNdUkVBGhBFQmQLDEVXOEUeIzcVWAVcWFIcUkhIV1UABjhOTxEYalYQbTsEUGADHRF5HAgUA2MLEEQHDFQCAwV7KCsmH0IeUCZeBxVPPFUXIV0KCh90LxBEHjoLFkFZWBdYFxZBGhBTQl9OQhFuLxVEIiBRXlsVD0sAXlhQWxBeSxILAVUyalYQbXJCUBUZHkNdXDUAEF4HFkcKChEGakYQOToHHhUdWF4QH1Y0GVkaQhhOIl5OLxtVIyZMI0ERDAYeFBQYJEALB1ZOCl9cQFYQbXJCUBVQGhUeJB0NGFMHFktOUhFVQFYQbXJCUBVQGgQeMT4TFl0LQg9ODFBVZDV2PzMPFT9QWEMQFxYFXjoLDFZkA15bKxoQKycME0EZFw0QAQwOB3YCGxpHZREYalZWIiBCLxlQE0NZHFgIB1EHEEFGFBNeJg9lPTYDBFBSVEFWHgEjIRJCQFQCFnN/aAsZbTYNehVQWEMQUlhBG18NA15ODBEFajtfOzcPFVsEVjxTHRYPLFszaBJOTxEYalYQJDRCExUEEAZeeFhBVxBOQhJOTxEYah9WbSYbAFAfHktTW1hcShBMMHA2PFJKIwZEDj0MHlATDApfHFpBA1gLDBINVXVRORVfIzwHE0FYUUNVHgsEV1NUJlcdG0NXM14ZbTcMFD9QWEMQUlhBVxBOQhIjAEddJxNeOXw9E1oeFjhbL1hcV14HDjhOTxEYalYQbTcMFD9QWEMQFxYFfRBOQhICAFJZJlZvYXI9XBUYDQ4QT1g0A1kCERwIBl9cBw9kIj0MWBx6WEMQUhEHV1gbDxIaB1RWah5FIHwyHFQEHgxCHysVFl4KQg9OCVBUORMQKDwGelAeHGlWBxYCA1kBDBIjAEddJxNeOXwRFUE2FBoYBFFBOl8YB18LAUUWGQJROTdMFlkJWF4QBENBHlZOFBIaB1RWagVELCAWNlkJUEoQFxQSEhAdFl0eKV1BYl8QKDwGUFAeHGlWBxYCA1kBDBIjAEddJxNeOXwRFUE2FBpjAh0EExgYSxIjAEddJxNeOXwxBFQEHU1WHgEyB1ULBhJTT0VXJANdLzcQWENZWAxCUk1RV1UABjgIGl9bPh9fI3IvH0MVFQZeBlYSEkQvDEYHLndzYgAZR3JCUBU9FxVVHx0PAx49FlMaCh9ZJAJZDBQpUAhQDmkQUlhBHlZOFBIPAVUYJBlEbR8NBlAdHQ1EXCcCGF4ATFMAG1h5DD0QOToHHj9QWEMQUlhBV30BFFcDCl9MZClTIjwMXlQeDApxNDNBShAiDVEPA2FUKw9VP3wrFFkVHFlzHRYPElMaSlQbAVJMIxleZXtoUBVQWEMQUlhBVxBOC1ROAV5MajtfOzcPFVsEVjBEEwwEWVEAFlsvKXoYPh5VI3IQFUEFCg0QFxYFfRBOQhJOTxEYalYQbSIBEVkcUAVFHBsVHl8AShtOOVhKPgNRIQcRFUdKOwJABg0TEnMBDEYcAF1ULwQYZGlCJlwCDBZRHi0SEkJUIV4HDFp6PwJEIjxQWGMVGxdfAEpPGVUZShtHT1RWLl86bXJCUBVQWENVHBxIfRBOQhILA0JdIxAQIz0WUENQGQ1UUjUOAVUDB1waQW5bJRheYzMMBFwxPigQBhAEGTpOQhJOTxEYajtfOzcPFVsEVjxTHRYPWVEAFlsvKXoCDh9DLj0MHlATDEsZSVgsGEYLD1cAGx9nKRleI3wDHkEZOSV7UkVBGVkCaBJOTxFdJBI6KDwGelMFFgBEGxcPV30BFFcDCl9MZAVROzcyH0ZYUWkQUlhBG18NA15OMB0YIgRAbW9CJUEZFBAeFBEPE30XNl0BARkRcVZZK3IKAkVQDAtVHFgsGEYLD1cAGx9rPhdEKHwREUMVHDNfAVhcV1gcEhw+AEJRPh9fI2lCAlAEDRFeUgwTAlVOB1wKZVRWLnxWODwBBFwfFkN9HQ4EGlUAFhwcClJZJhpgIiFKWT9QWEMQGx5BOl8YB18LAUUWGQJROTdMA1QGHQdgHQtBA1gLDBI7G1hUOVhEKD4HAFoCDEt9HQ4EGlUAFhw9G1BML1hDLCQHFGUfC0oLUgoEA0UcDBIaHURdahNeKVgHHlF6NAxTExQxG1EXB0BALFlZOBdTOTcQMVEUHQcKMRcPGVUNFhoIGl9bPh9fI3pLehVQWENEEwsKWUcPC0ZGXx8OY00QLCISHEw4DQ5RHBcIExhHaBJOTxFRLFZ9IiQHHVAeDE1jBhkVEh4IDktOG1ldJFZDOTMQBHMcAUsZUh0PEzoLDFZHZTsVZ1bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fPS5+iD4qCM96KM+qHa3+bS2MKA5aWS7fM6X1VBRgFAQmQnPGR5BiU6YH9CkqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xfVwBAVMCT2dROQNRISFCTRULWDBEEwwEVw1OGRIIGl1UKARZKjoWUAhQHgJcAR1NV14BJF0JTwwYLBdcPjdCDRlQJwFRERMUBxBTQkkTT0wyJhlTLD5CFkAeGxdZHRZBFVENCUceI1hfIgJZIzVKWT9QWEMQGx5BGVUWFho4BkJNKxpDYw0AEVYbDRMZUgwJEl5OEFcaGkNWahNeKVhCUBVQLgpDBxkNBB4xAFMNBERIZDRCJDUKBFsVCxAQUlhBShAiC1UGG1hWLVhyPzsFGEEeHRBDeFhBVxA4C0EbDl1LZClSLDEJBUVeOw9fERM1Hl0LQhJOTxEFajpZKjoWGVsXViBcHRsKI1kDBzhOTxEYHB9DODMOAxsvGgJTGQ0RWXcCDVAPA2JQKxJfOiFCTRU8EQRYBhEPEB4pDl0MDl1rIhdUIiURehVQWENmGwsUFlwdTG0MDlJTPwYeCz0FNVsUWEMQUlhBVxBTQn4HCFlMIxhXYxQNF3AeHGkQUlhBIVkdF1MCHB9nKBdTJicSXnMfHzBEEwoVVxBOQhJOUhF0IxFYOTsMFxs2FwRjBhkTAzoLDFZkCURWKQJZIjxCJlwDDQJcAVYSEkQoF14CDUNRLR5EZSRLehVQWENmGwsUFlwdTGEaDkVdZBBFIT4AAlwXEBcQT1gXTBAMA1EFGkF0IxFYOTsMFx1ZckMQUlgIERAYQkYGCl8YBh9XJSYLHlJeOhFZFRAVGVUdERJTTwIDajpZKjoWGVsXViBcHRsKI1kDBxJTTwAMcVZ8JDUKBFweH013HhcDFlw9ClMKAEZLaksQKzMOA1B6WEMQUh0NBFVkQhJOTxEYalZ8JDUKBFweH01yABEGH0QAB0EdTwwYHB9DODMOAxsvGgJTGQ0RWXIcC1UGG19dOQUQIiBCQT9QWEMQUlhBV3wHBVoaBl9fZDVcIjEJJFwdHUMQT1g3HkMbA14dQW5aKxVbOCJMM1kfGwhkGxUEV18cQgNaZREYalYQbXJCPFwXEBdZHB9PMFwBAFMCPFlZLhlHPnJfUGMZCxZRHgtPKFIPAVkbHx9/JhlSLD4xGFQUFxRDUgZcV1YPDkELZREYalZVIzZoFVsUcgVFHBsVHl8AQmQHHERZJgUePjcWPlo2FwQYBFFrVxBOQmQHHERZJgUeHiYDBFBeFgx2HR9BShAYWRIMDlJTPwZ8JDUKBFweH0sZeFhBVxAHBBIYT0VQLxgQATsFGEEZFgQeNBcGMl4KQg9OXlQOcVZ8JDUKBFweH012HR8yA1EcFhJTTwBdfHwQbXJCFVkDHUN8Gx8JA1kABRwoAFZ9JBIQcHI0GUYFGQ9DXCcDFlMFF0JAKV5fDxhUbT0QUARASFMLUjQIEFgaC1wJQXdXLSVELCAWUAhQLgpDBxkNBB4xAFMNBERIZDBfKgEWEUcEWAxCUkhBEl4KaFcACzsyZ1sQr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvagkO3xlaX+gKf+jaSoqOOgr8fykqDgmvageFVMVwFcTBI7JhHayuIQIT0DFBU/GhBZFhEAGWUHQho3XXoRahdeKXIABVwcHENEGh1BAFkABl0ZZRwVapSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6IGl4pr059L78tD7/9Ot2pSl3bD34Nfl6GlAABEPAxhGQGk3XXplajpfLDYLHlJQNwFDGxwIFl47CxIIAEMYbwUQY3xMUhxKHgxCHxkVX3MBDFQHCB9/Czt1EhwjPXBZUWk6HhcCFlxOLlsMHVBKM1oQGToHHVA9GQ1RFR0TWxA9A0QLIlBWKxFVP1gOH1YRFENfGS0oVw1OElEPA10QLANeLiYLH1tYUWkQUlhBO1kMEFMcFhEYalYQbW9CHFoRHBBEABEPEBgJA18LVXlMPgZ3KCZKM1oeHgpXXC0oKGIrMn1OQR8YaDpZLyADAkxeFBZRUFFIXxlkQhJOT2VQLxtVADMMEVIVCkMNUhQOFlQdFkAHAVYQLRddKGgqBEEAPwZEWjsOGVYHBRw7Jm5qDyZ/bXxMUBcRHAdfHAtOI1gLD1cjDl9ZLRNCYz4XERdZUUsZeFhBVxA9A0QLIlBWKxFVP3JCTRUcFwJUAQwTHl4JSlUPAlQCAgJEPRUHBB0zFw1WGx9PInkxMHc+IBEWZFYSLDYGH1sDVzBRBB0sFl4PBVccQV1NK1QZZHpLelAeHEo6Gx5BGV8aQl0FOngYJQQQIz0WUHkZGhFRAAFBA1gLDDhOTxEYPRdCI3pAK2xCM0N4Bxo8V3YPC14LCxFMJVZcIjMGUHoSCwpUGxkPIllAQnMMAENMIxhXY3BLehVQWENvNVY4RXsxJnMgK2hnAiNyEh4tMXE1PEMNUhYIGwtOEFcaGkNWQBNeKVhoHFoTGQ8QPQgVHl8AER5OO15fLRpVPnJfUHkZGhFRAAFPOEAaC10AHB0YBh9SPzMQCRskFwRXHh0SfXwHAEAPHUgWDBlCLjchGFATEwFfClhcV1YPDkELZTtUJRVRIXIEBVsTDApfHFgvGEQHBEtGG1hMJhMcbTYHA1ZcWAZCAFFrVxBOQn4HDUNZOA8KAz0WGVMJUBg6UlhBVxBOQhI6BkVUL1YQbXJCUBVNWAZCAFgAGVROShArHUNXOFbSzfBCUhVeVkNEGwwNEhlODUBOG1hMJhMcR3JCUBVQWEMQNh0SFEIHEkYHAF8Yd1ZUKCEBUFoCWEESXnJBVxBOQhJOT2VRJxMQbXJCUBVQWF4QRlRrVxBOQk9HZVRWLnw6IT0BEVlQLwpeFhcWVw1OLlsMHVBKM0xzPzcDBFAnEQ1UHQ9JDDpOQhJOO1hMJhMQbXJCUBVQWEMQUlhcVxIqA1wKFhZLaiFfPz4GUBWS+MEQUiFTPBAmF1BOT0caalgebRENHlMZH01jMSooJ2QxNHc8QzsYalYQCz0NBFACWEMQUlhBVxBOQhJTTxNheD0QHjEQGUUEWCFRERNTNVENCRJOjbGaalYSbXxMUHYfFgVZFVYmNn0rPXwvInQUQFYQbXIsH0EZHhpjGxwEVxBOQhJOTwwYaCRZKjoWUhl6WEMQUisJGEctF0EaAFx7PwRDIiBCTRUEChZVXnJBVxBOIVcAG1RKalYQbXJCUBVQWEMNUgwTAlVCaBJOTxF5PwJfHjoNBxVQWEMQUlhBVw1OFkAbCh0yalYQbQAHA1wKGQFcF1hBVxBOQhJOUhFMOANVYVhCUBVQOwxCHB0TJVEKC0cdTxEYalYNbWNSXD8NUWk6HhcCFlxONlMMHBEFag06bXJCUGYFChVZBBkNVw1ONVsAC15PcDdUKQYDEh1SKxZCBBEXFlxMThJOTUJQIxNcKXBLXD9QWEMQPxkCH1kAB0FOUhFvIxhUIiVYMVEULAJSWlosFlMGC1wLHBMUalYSOiAHHlYYWkoceFhBVxAnFlcDHBEYalYNbQULHlEfD1lxFhw1FlJGQHsaClxLaFoQbXJCUBcAGQBbEx8EVRlCaBJOTxFoJhdJKCBCUBVNWDRZHBwOAAovBlY6DlMQaCZcLCsHAhdcWEMQUloUBFUcQBtCZREYalZ9JCEBUBVQWEMNUi8IGVQBFQgvC1VsKxQYbx8LA1ZSVEMQUlhBVxIHDFQBTRgUQFYQbXIhH1sWEQRDUlhcV2cHDFYBGAt5LhJkLDBKUnYfFgVZFQtDWxBOQhAKDkVZKBdDKHBLXD9QWEMQIR0VA1kABUFOUhFvIxhUIiVYMVEULAJSWloyEkQaC1wJHBMUalYSPjcWBFweHxASW1RrVxBOQnEcClVRPgUQbW9CJ1weHAxHSDkFE2QPABpMLENdLh9EPnBOUBVQWgtVEwoVVRlCaE9kZRwVapSkzbD28Nfk+ENkMzpBRhCM4qZOPGRqHD9mDB5CkqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4QBpfLjMOUGYFCjdSCjRBShA6A1AdQWJNOABZOzMOSnQUHC9VFAw1FlIMDUpGRjtUJRVRIXIxBUckDwpDBh0FVw1OMUccO1NABkxxKTY2EVdYWjdHGwsVElROJ2E+TRgyJhlTLD5CI0ACNgxEGx4YVxBTQmEbHWVaMjoKDDYGJFQSUEF+HQwIEVkLEBBHZTtrPwRkOjsRBFAUQiJUFjQAFVUCSklOO1RAPlYNbXAqGVIYFApXGgwSV1UYB0AXT2VPIwVEKDZCJFofFkNZHFgVH1VOAUccHVRWPlZCIj0PUEIZDAsQHBkMEhBFQlYHHEVZJBVVY3BOUHEfHRBnABkRVw1OFkAbChFFY3xjOCA2B1wDDAZUSDkFE3QHFFsKCkMQY3xjOCA2B1wDDAZUSDkFE2QBBVUCChkaDyVgGSULA0EVHEEcUgNBI1UWFhJTTxNsPR9DOTcGUHAjKEEcUjwEEVEbDkZOUhFeKxpDKH5CM1QcFAFRERNBShArMWJAHFRMHgFZPiYHFBUNUWljBwo1AFkdFlcKVXBcLiJfKjUOFR1SPTBgJg8IBEQLBnYHHEUaZlZLbQYHCEFQRUMSIRAOABAKC0EaDl9bL1QcbRYHFlQFFBcQT1gVBUULTjhOTxEYCRdcITADE15QRUNWBxYCA1kBDBoYRhF9GSYeHiYDBFBeDBRZAQwEE3QHEUYPAVJdaksQO3IHHlFQBUo6IQ0TI0cHEUYLCwt5LhJkIjUFHFBYWiZjIisJGEchDF4XLF1XORMSYXIZUGEVABcQT1hDP1kKBxIHCRFMJRkQKzMQUhlQPAZWEw0NAxBTQlQPA0JdZnwQbXJCJFofFBdZAlhcVxIhDF4XT0NdJBJVP3InI2VQHgxCUh0PA1kaC1cdT0ZRPh5ZI3IhHFoDHUNiExYGEh5MTjhOTxEYCRdcITADE15QRUNWBxYCA1kBDBoYRhF9GSYeHiYDBFBeCwtfBTcPG0ktDl0dChEFagAQKDwGUEhZcjBFACwWHkMaB1ZULlVcGRpZKTcQWBc1KzNzHhcSEmIPDFULTR0YMVZkKCoWUAhQWiBcHQsEV0IPDFULTR0YDhNWLCcOBBVNWFUAXlgsHl5OXxJcXx0YBxdIbW9CQgVAVENiHQ0PE1kABRJTTwEUaiVFKzQLCBVNWEEQAQxDWzpOQhJOLFBUJhRRLjlCTRUWDQ1TBhEOGRgYSxIrPGEWGQJROTdME1kfCwZiExYGEhBTQkROCl9cagsZRwEXAmEHERBEFxxbNlQKLlMMCl0QaCJHJCEWFVFQGwxcHQpDXgovBlYtAF1XOCZZLjkHAh1SPTBgJg8IBEQLBnEBA15KaFoQNlhCUBVQPAZWEw0NAxBTQnc9Px9rPhdEKHwWB1wDDAZUMRcNGEJCQmYHG11daksQbwYVGUYEHQcQNysxV1MBDl0cTR0yalYQbREDHFkSGQBbUkVBEUUAAUYHAF8QKV8QCAEyXmYEGRdVXAwWHkMaB1YtAF1XOFYNbTFCFVsUWB4ZeHIyAkIgDUYHCUgCCxJUATMAFVlYA0NkFwAVVw1OQGIBH0IYK1ZCKDZCElQeFgZCUhYEFkJOFloLT0VXOlZfK3IbH0ACWBBTAB0EGRAZClcAT1AYHgFZPiYHFBUVFhdVAAtBB0IBGlsDBkVBZFQcbRYNFUYnCgJAUkVBA0IbBxITRjtrPwR+IiYLFkxKOQdUNhEXHlQLEBpHZWJNODhfOTsECQ8xHAdkHR8GG1VGQHwBG1heIxNCb35CCxUkHRtEUkVBVWQZC0EaClUYGgRfNTsPGUEJWC1fBhEHHlUcQB5OK1ReKwNcOXJfUFMRFBBVXlgiFlwCAFMNBBEFaiVFPyQLBlQcVhBVBjYOA1kIC1ccT0wRQCVFPxwNBFwWAVlxFhwyG1kKB0BGTX9XPh9WJDcQIlQeHwYSXlgaV2QLGkZOUhEaHgRZKjUHAhUCGQ1XF1pNV3QLBFMbA0UYd1YDeH5CPVweWF4QQ0hNV30PGhJTTwAKeloQHz0XHlEZFgQQT1hRWxA9F1QIBkkYd1YSbSEWUhl6WEMQUjsAG1wMA1EFTwwYLANeLiYLH1tYDkoQIQ0TAVkYA15APEVZPhMeIz0WGVMZHRFiExYGEhBTQkROCl9cagsZR1gOH1YRFENjBwo1FUg8Qg9OO1BaOVhjOCAUGUMRFFlxFhwzHlcGFmYPDVNXMl4ZRz4NE1QcWDBFADkPA1kpEFMMTwwYGQNCGTAaIg8xHAdkExpJVXEAFltDKENZKFQZRz4NE1QcWDBFADsOE1UdQhJOTwwYGQNCGTAaIg8xHAdkExpJVXMBBlcdTRgyQCVFPxMMBFw3CgJSSDkFE3wPAFcCR0oYHhNIOXJfUBcxDRdfHxkVHlMPDl4XT0JJPx9CIH8BEVsTHQ9DUg8JEl5OAxI6GFhLPhNUbTUQEVcDWBpfB1ZBJEUcFFsYDl0YJh9WKCEDBlACVkEcUjwOEkM5EFMeTwwYPgRFKHIfWT8jDRFxHAwIMEIPAAgvC1V8IwBZKTcQWBx6KxZCMxYVHnccA1BULlVcHhlXKj4HWBcxFhdZNQoAFRJCQklOO1RAPlYNbXAjBUEfWDBBBxETGh0tA1wNCl0YJRgQKiADEhdcWCdVFBkUG0ROXxIIDl1LL1o6bXJCUGEfFw9EGwhBShBMJFscCkIYPh5VbQETBVwCFSJSGxQIA0ktA1wNCl0YOBNdIiYHUEEYHUNdHRUEGUROG10bT1ZdPlZXPzMAElAUVkEceFhBVxAtA14CDVBbIVYNbQEXAkMZDgJcXAsEA3EAFlspHVBaagsZR1gxBUczFwdVAUIgE1QiA1ALAxlDaiJVNSZCTRVSKgZUFx0MV1kAT1UPAlQYKRlUKCFMUHcFEQ9EXxEPV1wHEUZOHVReOBNDJTcRUFoTGwJDGxcPFlwCGxxMQxF8JRNDGiADABVNWBdCBx1BChlkMUccLF5cLwUKDDYGNFwGEQdVAFBIfWMbEHEBC1RLcDdUKRAXBEEfFktLUiwED0ROXxJMPVRcLxNdbRMuPBUSDQpcBlUIGRANDVYLHBMUajBFIzFCTRUWDQ1TBhEOGRhHaBJOTxFeJQQQEn5CE1oUHUNZHFgIB1EHEEFGLF5WLB9XYxEtNHAjUUNUHXJBVxBOQhJOT2NdJxlEKCFMGVsGFwhVWloiGFQLJ0QLAUUaZlZTIjYHWT9QWEMQUlhBV0QPEVlAGFBRPl4AY2ZLehVQWENVHBxrVxBOQnwBG1heM14SDj0GFUZSVEMSJgoIElROQBJAQREbCRleKzsFXnY/PCZjUlZPVxJOAV0KCkIWaF86KDwGUEhZcjBFADsOE1UdWHMKC3hWOgNEZXAhBUYEFw5zHRwEVRxOGRI6CklMaksQbxEXA0EfFUNTHRwEVRxOJlcIDkRUPlYNbXBAXBUgFAJTFxAOG1QLEBJTTxNbJRJVbToHAlBSVENzExQNFVENCRJTT1dNJBVEJD0MWBxQHQ1UUgVIfWMbEHEBC1RLcDdUKRAXBEEfFktLUiwED0ROXxJMPVRcLxNdbTEXA0EfFUNTHRwEVRxOJEcADBEFahBFIzEWGVoeUEo6UlhBV1wBAVMCT1JXLhMQcHItAEEZFw1DXDsUBEQBD3EBC1QYKxhUbR0SBFwfFhAeMQ0SA18DIV0KCh9uKxpFKHINAhVSWmkQUlhBHlZOAV0KChEFd1YSb3IWGFAeWC1fBhEHDhhMIV0KChMUalR1ICIWCRdcWBdCBx1ITBAcB0YbHV8YLxhUR3JCUBUiHQ5fBh0SWVkAFF0FChkaCRlUKBcUFVsEWk8QERcFEhlVQnwBG1heM14SDj0GFRdcWEFkABEEEwpOQBJAQRFbJRJVZFgHHlFQBUo6eFVMV9L64tD679OsylZkDBBCQhWS+PcQPzkiP3kgJ2FOjaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhfVwBAVMCT3xZKR58bW9CJFQSC019ExsJHl4LEQgvC1V0LxBECiANBUUSFxsYUDUAFFgHDFdOKmJoaFoQbyUQFVsTEEEZeDUAFFgiWHMKC31ZKBNcZSlCJFAIDEMNUlopHlcGDlsJB0VLahNGKCAbUFgRGwtZHB1BAFkaChIHG0IYKRldPT4HBFwfFkMVXFpNV3QBB0E5HVBIaksQOSAXFRUNUWl9ExsJOwovBlYqBkdRLhNCZXtoPVQTEC8KMxwFI18JBV4LRxN9GSZ9LDEKGVsVWk8QCVg1EkgaQg9OTXxZKR5ZIzdCNWYgWk8QNh0HFkUCFhJTT1dZJgVVYXIhEVkcGgJTGVhcV3U9MhwdCkV1KxVYJDwHUEhZci5RERAtTXEKBn4PDVRUYlR9LDEKGVsVWABfHhcTVRlUI1YKLF5UJQRgJDEJFUdYWiZjIjUAFFgHDFctAF1XOFQcbSloUBVQWCdVFBkUG0ROXxIrPGEWGQJROTdMHVQTEApeFzsOG18cThI6BkVUL1YNbXAvEVYYEQ1VUj0yJxANDV4BHRMUQFYQbXIhEVkcGgJTGVhcV1YbDFEaBl5WYhUZbRcxIBsjDAJEF1YMFlMGC1wLLF5UJQQQcHIBUFAeHENNW3JrG18NA15OIlBbIiQQcHI2EVcDVi5RERAIGVUdWHMKC2NRLR5ECiANBUUSFxsYUDkUA19OEVkHA10YKR5VLjlAXBVSEwZJUFFrOlENCmBULlVcBhdSKD5KCxUkHRtEUkVBVWILA1YdT0VQL1ZDKCAUFUdXC0NEEwoGEkROBEABAhFMIhMQPjkLHFldGwtVERNBFkIJERIPAVUYOBNEOCAMAxUZDE0QJRkVFFgKDVVOHVQVIxhDOTMOHEZQEQUQBhAEV1cPD1dOHVRLLwJDbTsWXhdcWCdfFws2BVEeQg9OG0NNL1ZNZFgvEVYYKllxFhwlHkYHBlccRxgyBxdTJQBYMVEULAxXFRQEXxIvF0YBPFpRJhpzJTcBGxdcWBgQJh0ZAxBTQhAvGkVXaiVbJD4OUHYYHQBbUFRBM1UIA0cCGxEFahBRISEHXD9QWEMQJhcOG0QHEhJTTxN5PwJfYCIDA0YVC0NTGwoCG1VOA1wKT0VKLxdUIDsOHBUDEwpcHlgCH1UNCUFODUgYOBNEOCAMGVsXWBdYF1gSEkIYB0BJHBFXPRgQOTMQF1AEWBVRHg0EWRJCaBJOTxF7KxpcLzMBGxVNWC5RERAIGVVAEVcaLkRMJSVbJD4OE10VGwgQD1FrOlENCmBULlVcGRpZKTcQWBc2GQ9cEBkCHGYPDkcLTR0YMVZkKCoWUAhQWiVRHhQDFlMFQkQPA0Rdal5ZK3IMHxUEGRFXFwxBHl5OA0AJHBgaZlZ0KDQDBVkEWF4QQlZUWxAjC1xOUhEIZEYcbR8DCBVNWFIeQlRBJV8bDFYHAVYYd1YCYVhCUBVQLAxfHgwIBxBTQhAhAV1BagNDKDZCGVNQDwYQERkPUEROA0caABxcLwJVLiZCBF0VWBdRAB8EAx5ONkAXTwEWeVYfbWJMRRVfWFMeRVgIERAHFhIDBkJLLwUeb35oUBVQWCBRHhQDFlMFQg9OCURWKQJZIjxKBhxQNQJTGhEPEh49FlMaCh9eKxpcLzMBG2MRFBZVUkVBARALDFZOEhgyBxdTJQBYMVEUKw9ZFh0TXxI9CVsCA3JQLxVbCTcOEUxSVENLUiwED0ROXxJMPVRLOhlePjdCFFAcGRoSXlglElYPF14aTwwYeloQADsMUAhQSE0AXlgsFkhOXxJfQQQUaiRfODwGGVsXWF4QQFRBJEUIBFsWTwwYaFZDb35oUBVQWDdfHRQVHkBOXxJMP1BNORMQLzcEH0cVWAJeAQ8EBVkABRxOXxEFah9ePiYDHkFeWk86UlhBV3MPDl4MDlJTaksQKycME0EZFw0YBFFBOlENClsACh9rPhdEKHwDBUEfKwhZHhQCH1UNCXYLA1BBaksQO3IHHlFQBUo6PxkCH2JUI1YKK1hOIxJVP3pLengRGwtiSDkFE2QBBVUCChkaDhNSODUxG1wcFCBYFxsKVRxOGRI6CklMaksQb6L94K5QPAZSBx9bV0AcC1waT1BKLQUQOT1CE1oeCwxcF1pNV3QLBFMbA0UYd1ZWLD4RFRl6WEMQUiwOGFwaC0JOUhEaGgRZIyYRUEEYHUNDGRENGx0NClcNBBFZOBFDbXoSAlADC0N2S1gVGBAdB1dHQRFtORMQOToLAxUfFgBVUgwOV1wLA0AAT0VQL1ZELCAFFUFQHgpVHhxBGVEDBx5OG1ldJFZEOCAMUFoWHk0SXnJBVxBOIVMCA1NZKR0QcHIvEVYYEQ1VXAsEA3QLAEcJP0NRJAIQMHtoPVQTEDEKMxwFNUUaFl0AR0oYHhNIOXJfUBciHU5ZHAsVFlwCQloBAFoYJBlHb35oUBVQWDdfHRQVHkBOXxJMKV5KKRMQPzdPEUUAFBoQGx5BHkROEUYBH0FdLlZHIiAJGVsXWAJWBh0TV1FOEFcdH1BPJFgSYVhCUBVQPhZeEVhcV1YbDFEaBl5WYl86bXJCUBVQWEN9ExsJHl4LTEELG3BNPhljJjsOHFYYHQBbWh4AG0MLSwlOG1BLIVhHLDsWWAVeSFYZSVgsFlMGC1wLQUJdPjdFOT0xG1wcFABYFxsKX0QcF1dHZREYalYQbXJCPloEEQVJWloyHFkCDhItB1RbIVQcbXAwFRgYFwxbFxxPVRlkQhJOT1RWLlZNZFhoXRhQmvewkOzhlaTuQmYvLRELapSw2XIrJHA9K0PS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5vhrG18NA15OJkVVBlYNbQYDEkZeMRdVHwtbNlQKLlcIG3ZKJQNALz0aWBc5DAZdUj0yJxJCQhAeDlJTKxFVb3toOUEdNFlxFhwtFlILDhoVT2VdMgIQcHJAOFwXEA9ZFRAVBBALFFccFhFIIxVbLDAOFRUZDAZdUhEPV0QGBxINGkNKLxhEbSANH1heWk8QNhcEBGccA0JOUhFMOANVbS9LenwEFS8KMxwFM1kYC1YLHRkRQD9EIB5YMVEULAxXFRQEXxIrMWInG1RVaFoQNnI2FU0EWF4QUDEVEl1OJ2E+TR0YDhNWLCcOBBVNWAVRHgsEWxAtA14CDVBbIVYNbRcxIBsDHRd5Bh0MV01HaHsaAn0CCxJUATMAFVlYWipEFxVBFF8CDUBMRgt5LhJzIj4NAmUZGwhVAFBDMmM+K0YLAnJXJhlCb35CCz9QWEMQNh0HFkUCFhJTT3RrGlhjOTMWFRsZDAZdMRcNGEJCQmYHG11daksQbxsWFVhQPTBgUhsOG18cQB5kTxEYajVRIT4AEVYbWF4QFA0PFEQHDVxGDBgYDyVgYwEWEUEVVgpEFxUiGFwBEBJTT1IYLxhUbS9Lej8cFwBRHlgoA108Qg9OO1BaOVh5OTcPAw8xHAdiGx8JA3ccDUceDV5AYlRxOCYNUEUZGwhFAlpNVxIdA0QLTRgyAwJdH2gjFFE8GQFVHlAaV2QLGkZOUhEaHRdcJiFCBFpQFgZRABoYV1kaB18dT1BWLlZXPzMAAxUEEAZdXFgzFl4JBxIHHBFbJRhDKCAUEUEZDgYQEAFBE1UIA0cCGx8aZlZ0IjcRJ0cRCEMNUgwTAlVOHxtkJkVVGExxKTYmGUMZHAZCWlFrPkQDMAgvC1VsJRFXITdKUnQFDAxgGxsKAkBMThIVT2VdMgIQcHJAMUAEF0NgGxsKAkBODFcPHVNBah9EKD8RUhlQPAZWEw0NAxBTQlQPA0JdZnwQbXJCM1QcFAFRERNBShAIF1wNG1hXJF5GZHILFhUGWBdYFxZBNkUaDWIHDFpNOlhDOTMQBB1ZWAZcAR1BNkUaDWIHDFpNOlhDOT0SWBxQHQ1UUh0PExATSzgnG1xqcDdUKQEOGVEVCksSIhECHEUeMFMACFQaZlZLbQYHCEFQRUMSIhECHEUeQkAPAVZdaFoQCTcEEUAcDEMNUklTWxAjC1xOUhENZlZ9LCpCTRVISE8QIBcUGVQHDFVOUhEIZlZjODQEGU1QRUMSUgsVVRxkQhJOT3JZJhpSLDEJUAhQHhZeEQwIGF5GFBtOLkRMJSZZLjkXABsjDAJEF1YTFl4JBxJTT0cYLxhUbS9LenwEFTEKMxwFJFwHBlccRxNoIxVbOCIrHkEVChVRHlpNV0tONlcWGxEFalRzJTcBGxUZFhdVAA4AGxJCQnYLCVBNJgIQcHJSXgBcWC5ZHFhcVwBAUB5OIlBAaksQeH5CIloFFgdZHB9BShBcThI9GldeIw4QcHJAUEZSVGkQUlhBNFECDlAPDFoYd1ZWODwBBFwfFktGW1ggAkQBMlsNBERIZCVELCYHXlweDAZCBBkNVw1OFBILAVUYN186R39PUNfk+IGk8pr19xA6I3BOWxHayuIQHR4jKXAiWIGk8pr199L64tD679OsypSkzbD28Nfk+IGk8pr199L64tD679OsypSkzbD28Nfk+IGk8pr199L64tD679OsypSkzbD28Nfk+IGk8pr199L64tD679OsypSkzbD28Nfk+IGk8pr199L64tD679OsypSkzbD28Nfk+IGk8pr199L64tD679OsypSkzbD28Nfk+IGk8pr199L64tD679OsypSkzbD28Nfk+GlcHRsAGxA+DkA6DUl0aksQGTMAAxsgFAJJFwpbNlQKLlcIG2VZKBRfNXpLelkfGwJcUjUOAVU6A1BOUhFoJgRkLyouSnQUHDdREFBDOl8YB18LAUUaY3xcIjEDHBUmERBkExpBVw1OMl4cO1NABkxxKTY2EVdYWjVZAQ0AG0NMSzhkIl5OLyJRL2gjFFE8GQFVHlAaV2QLGkZOUhEaqOyQbRUDHVBQEAJDUhlBBFUcFFccQkJRLhMQPiIHFVFQGwtVERNPV3QLBFMbA0VLagVELCtCBVsUHREQBhAEV0QGEFcdB15ULlgSYXImH1ADLxFRAlhcV0QcF1dOEhgyBxlGKAYDEg8xHAd0Gw4IE1UcShtkIl5OLyJRL2gjFFEjFApUFwpJVWcPDlk9H1RdLlQcbSlCJFAIDEMNUlo2FlwFQmEeClRcaFoQCTcEEUAcDEMNUklUWxAjC1xOUhEJf1oQADMaUAhQSlEcUioOAl4KC1wJTwwYeloQHicEFlwIWF4QUFgSA0UKER0dTR0yalYQbQYNH1kEERMQT1hDJFEIBxIcDl9fL1ZZPnIXABUEF0MSUlZPV3MBDFQHCB9rCzB1Eh8jKGojKCZ1NlhPWRBMTBIpDlxdahJVKzMXHEFQERAQQ01PVRxkQhJOT3JZJhpSLDEJUAhQNQxGFxUEGURAEVcaOFBUISVAKDcGUEhZci5fBB01FlJUI1YKO15fLRpVZXAgCUURCxBjAh0EE3MPEhBCT0oYHhNIOXJfUBcxFA9fBVgTHkMFGxIdH1RdLgUQZWxQQhxSVEN0Fx4AAlwaQg9OCVBUORMcbQALA14JWF4QBgoUEhxkQhJOT2VXJRpEJCJCTRVSLQ1cHRsKBBAaCldOHF1RLhNCbTMAH0MVWFECXFgsFklOFkAHCFZdOFZDPTcHFBUWFAJXXFpNfRBOQhItDl1UKBdTJnJfUFMFFgBEGxcPX0ZHaBJOTxEYalYQAD0UFVgVFhceIQwAA1VAAEseDkJLGQZVKDYhEUVQRUNGeFhBVxBOQhJOBlcYBQZEJD0MAxsnGQ9bIQgEElROA1wKT35IPh9fIyFMJ1QcEzBAFx0FWX0PGhIaB1RWQFYQbXJCUBVQWEMQUlVMV38MEVsKBlBWHx8QKT0HA1tXDENVCggOBFVOBksADlxRKVZDITsGFUdQFQJISVgUBFUcQl8bHEUYOBMdPjcWUEMRFBZVUhUAGUUPDl4XZREYalYQbXJCFVsUckMQUlgEGVROHxtkIl5OLyJRL2gjFFEjFApUFwpJVXobD0I+AEZdOFQcbSlCJFAIDEMNUlorAl0eQmIBGFRKaFoQCTcEEUAcDEMNUk1RWxAjC1xOUhENeloQADMaUAhQSlMAXlgzGEUABlsACBEFakYcbREDHFkSGQBbUkVBOl8YB18LAUUWORNEBycPAGUfDwZCUgVIfX0BFFc6DlMCCxJUGT0FF1kVUEF5HB4rAl0eQB5OFBFsLw5EbW9CUnweHgpeGwwEV3obD0JMQxF8LxBROD4WUAhQHgJcAR1NV3MPDl4MDlJTaksQAD0UFVgVFhceAR0VPl4IKEcDHxFFY3x9IiQHJFQSQiJUFiwOEFcCBxpMIV5bJh9Ab35CUE5QLAZIBlhcVxIgDVECBkEaZlYQbXJCUBVQPAZWEw0NAxBTQlQPA0JdZlZzLD4OElQTE0MNUjUOAVUDB1waQUJdPjhfLj4LABUNUWl9HQ4EI1EMWHMKC3VRPB9UKCBKWT89FxVVJhkDTXEKBmYBCFZUL14SCz4bUhlQA0NkFwAVVw1OQHQCFhMUajJVKzMXHEFQRUNWExQSEhxOMFsdBEgYd1ZEPycHXD9QWEMQJhcOG0QHEhJTTxN0Ix1VIStCBFpQDBFZFR8EBRAPDEYHQlJQLxdEbTsEUEADHQcQERkTElwLEUECFh8aZnwQbXJCM1QcFAFRERNBShAjDUQLAlRWPlhDKCYkHExQBUo6PxcXEmQPAAgvC1VrJh9UKCBKUnMcATBAFx0FVRxOGRI6CklMaksQbxQOCRUDCAZVFlpNV3QLBFMbA0UYd1YFfX5CPVweWF4QQ0hNV30PGhJTTwMIeloQHz0XHlEZFgQQT1hRWxAtA14CDVBbIVYNbR8NBlAdHQ1EXAsEA3YCG2EeClRcagsZRx8NBlAkGQEKMxwFM1kYC1YLHRkRQDtfOzc2EVdKOQdUJhcGEFwLShAvAUVRCzB7b35CCxUkHRtEUkVBVXEAFltDLndzaFoQCTcEEUAcDEMNUgwTAlVCaBJOTxFsJRlcOTsSUAhQWiFcHRsKBBAaCldOXQEVJx9eOCYHUFwUFAYQGRECHB5MThItDl1UKBdTJnJfUHgfDgZdFxYVWUMLFnMAG1h5DD0QMHtoPVoGHQ5VHAxPBFUaI1waBnB+AV5EPycHWT89FxVVJhkDTXEKBnYHGVhcLwQYZFgvH0MVLAJSSDkFE3IbFkYBARlDaiJVNSZCTRVSKwJGF1gCAkIcB1waT0FXOR9EJD0MUhlQPhZeEVhcV1YbDFEaBl5WYl8QJDRCPVoGHQ5VHAxPBFEYB2IBHBkRagJYKDxCPloEEQVJWloxGENMThA9DkddLlgSZHIHHEYVWC1fBhEHDhhMMl0dTR0aBBkQLjoDAhdcDBFFF1FBEl4KQlcACxFFY3x9IiQHJFQSQiJUFjoUA0QBDBoVT2VdMgIQcHJAIlATGQ9cUgsAAVUKQkIBHFhMIxleb35CNkAeG0MNUh4UGVMaC10ARxgYIxAQAD0UFVgVFhceAB0CFlwCMl0dRxgYPh5VI3IsH0EZHhoYUCgOBBJCQGALDFBUJhNUY3BLUFAcCwYQPBcVHlYXShA+AEIaZlR+IiYKGVsXWBBRBB0FVRwaEEcLRhFdJBIQKDwGUEhZcmlmGws1FlJUI1YKI1BaLxoYNnI2FU0EWF4QUC8OBVwKQl4HCFlMIxhXbXlCAFkRAQZCUj0yJx5MThIqAFRLHQRRPXJfUEECDQYQD1FrIVkdNlMMVXBcLjJZOzsGFUdYUWlmGws1FlJUI1YKO15fLRpVZXAkBVkcGhFZFRAVVRxOGRI6CklMaksQbxQXHFkSCgpXGgxDWxAqB1QPGl1MaksQKzMOA1BcWCBRHhQDFlMFQg9OOVhLPxdcPnwRFUE2DQ9cEAoIEFgaQk9HZWdROSJRL2gjFFEkFwRXHh1JVX4BJF0JTR0YalYQbXIZUGEVABcQT1hDJVUDDUQLT1dXLVQcbRYHFlQFFBcQT1gHFlwdBx5OLFBUJhRRLjlCTRUmERBFExQSWUMLFnwBKV5fagsZRwQLA2ERGllxFhwlHkYHBlccRxgyHB9DGTMASnQUHDdfFR8NEhhMJ2E+P11ZMxNCb35CUE5QLAZIBlhcVxI+DlMXCkMYDyVgb35CNFAWGRZcBlhcV1YPDkELQxF7KxpcLzMBGxVNWCZjIlYSEkQ+DlMXCkMYN186GzsRJFQSQiJUFjQAFVUCShA+A1BBLwQQLj0OH0dSUVlxFhwiGFwBEGIHDFpdOF4SCAEyIFkRAQZCMRcNGEJMThIVZREYalZ0KDQDBVkEWF4QNysxWWMaA0YLQUFUKw9VPxENHFoCVENkGwwNEhBTQhA+A1BBLwQQCAEyUFYfFAxCUFRrVxBOQnEPA11aKxVbbW9CFkAeGxdZHRZJFBlOJ2E+QWJMKwJVYyIOEUwVCiBfHhcTVw1OARILAVUYN186Rz4NE1QcWDNcACwDD2JOXxI6DlNLZCZcLCsHAg8xHAdiGx8JA2QPAFABFxkRQBpfLjMOUGEAKgxfH1hcV2ACEGYMF2MCCxJUGTMAWBciFwxdUiwxBBJHaF4BDFBUaiJAHT4QAxVNWDNcACwDD2JUI1YKO1BaYlRgITMbFUdQLDMSW3JrI0A8DV0DVXBcLjpRLzcOWE5QLAZIBlhcVxI6B14LH15KPlZRPz0XHlFQDAtVUhsUBUILDEZOHV5XJ1gSYXImH1ADLxFRAlhcV0QcF1dOEhgyHgZiIj0PSnQUHCdZBBEFEkJGSzg6H2NXJRsKDDYGMkAEDAxeWgNBI1UWFhJTTxPazOQQCD4HBlQEFxESXlgnAl4NQg9OCURWKQJZIjxKWT9QWEMQHhcCFlxOEhJTT2NXJRseKjcWNVkVDgJEHQoxGENGSzhOTxEYIxAQPXIWGFAeWDZEGxQSWUQLDlceAENMYgYQZnI0FVYEFxEDXBYEABheTgZCXxgRcVZ+IiYLFkxYWjdgUFRDlbb8QncCCkdZPhlCb3toUBVQWAZcAR1BOV8aC1QXRxNsGlQcbxwNUFAcHRVRBhcTVRwaEEcLRhFdJBI6KDwGUEhZcjdAIBcOGgovBlYsGkVMJRgYNnI2FU0EWF4QUJrn5RAgB1McCkJMahtRLjoLHlBSVEN2BxYCVw1OBEcADEVRJRgYZFhCUBVQFAxTExRBKBxOCkAeTwwYHwJZISFMFlweHC5JJhcOGRhHaBJOTxFRLFZeIiZCGEcAWBdYFxZBOV8aC1QXRxNsGlQcbxwNUFYYGRESXgwTAlVHWRIcCkVNOBgQKDwGehVQWENcHRsAGxAMB0EaQxFaLlYNbTwLHBlQFQJEGlYJAlcLaBJOTxFeJQQQEn5CHRUZFkNZAhkIBUNGMF0BAh9fLwJ9LDEKGVsVC0sZW1gFGDpOQhJOTxEYahpfLjMOUFFQRUNlBhENBB4KC0EaDl9bL15YPyJMIFoDERdZHRZNV11AEF0BGx9oJQVZOTsNHhx6WEMQUlhBVxAHBBIKTw0YKBIQOToHHhUSHEMNUhxaV1ILEUZOUhFVahNeKVhCUBVQHQ1UeFhBVxAHBBIMCkJMagJYKDxCJUEZFBAeBh0NEkABEEZGDVRLPlhCIj0WXmUfCwpEGxcPVxtONFcNG15KeVheKCVKQBlEVFMZW0NBOV8aC1QXRxNsGlQcb7Dk4hVSVk1SFwsVWV4PD1dHZREYalZVISEHUHsfDApWC1BDI2BMThAgABFVKxVYJDwHUhkEChZVW1gEGVRkB1wKT0wRQCJAHz0NHQ8xHAdyBwwVGF5GGRI6CklMaksQb7Dk4hU+HQJCFwsVV1kaB19MQxF+PxhTbW9CFkAeGxdZHRZJXjpOQhJOA15bKxoQEn5CGEcAWF4QJwwIG0NABFsAC3xBHhlfI3pLehVQWENZFFgPGEROCkAeT0VQLxgQAz0WGVMJUEFkIlpNVX4BQlEGDkMaZgJCODdLSxUCHRdFABZBEl4KaBJOTxFUJRVRIXIAFUYEVENSFlhcV14HDh5OAlBMIlhYODUHehVQWENWHQpBKBxOCxIHARFROhdZPyFKIlofFU1XFwwoA1UDERpHRhFcJXwQbXJCUBVQWA9fERkNV1ROXxI7G1hUOVhUJCEWEVsTHUtYAAhPJ18dC0YHAF8Uah8ePz0NBBsgFxBZBhEOGRlkQhJOTxEYalZZK3IGUAlQGgcQBhAEGRAMBhJTT1UDahRVPiZCTRUZWAZeFnJBVxBOB1wKZREYalZZK3IAFUYEWBdYFxZBIkQHDkFAG1RULwZfPyZKElADDE1CHRcVWWABEVsaBl5Wal0QGzcBBFoCS01eFw9JRxxdTgJHRgoYBBlEJDQbWBckKEEcUJrn5RBMTBwMCkJMZBhRIDdLehVQWENVHgsEV34BFlsIFhkaHiYSYXAsHxUZDAZdAVpNA0IbBxtOCl9cQBNeKXIfWT96FAxTExRBEUUAAUYHAF8YLRNEHT4DCVACNgJdFwtJXjpOQhJOA15bKxoQIicWUAhQAx46UlhBV1YBEBIxQxFIah9ebTsSEVwCC0tgHhkYEkIdWHULG2FUKw9VPyFKWRxQHAw6UlhBVxBOQhIHCRFIaggNbR4NE1QcKA9RCx0TV0QGB1xOG1BaJhMeJDwRFUcEUAxFBlRBBx4gA18LRhFdJBI6bXJCUFAeHGkQUlhBHlZOQV0bGxEFd1YAbSYKFVtQDAJSHh1PHl4dB0AaR15NPloQb3oMH1sVUUEZUh0PEzpOQhJOHVRMPwRebT0XBD8VFgc6JggxG0IdWHMKC31ZKBNcZSlCJFAIDEMNUlo1ElwLEl0cGxFMJVZRIz0WGFACWBNcEwEEBRAHDBIaB1QYORNCOzcQXhdcWCdfFws2BVEeQg9OG0NNL1ZNZFg2AGUcChAKMxwFM1kYC1YLHRkRQCJAHT4QAw8xHAd0ABcRE18ZDBpMO0FoJhdJKCBAXBULWDdVCgxBShBMMl4PFlRKaFoQGzMOBVADWF4QFR0VJ1wPG1ccIVBVLwUYZH5CNFAWGRZcBlhcVxJGDF0AChgaZlZzLD4OElQTE0MNUh4UGVMaC10ARxgYLxhUbS9LemEAKA9CAUIgE1QsF0YaAF8QMVZkKCoWUAhQWjFVFAoEBFhODlsdGxMUajBFIzFCTRUWDQ1TBhEOGRhHaBJOTxFRLFZ/PSYLH1sDVjdAIhQADlUcQlMACxF3OgJZIjwRXmEAKA9RCx0TWWMLFmQPA0RdOVZEJTcMUHoADApfHAtPI0A+DlMXCkMCGRNEGzMOBVADUARVBigNFkkLEHwPAlRLYl8ZbTcMFD8VFgcQD1FrI0A+DkAdVXBcLjRFOSYNHh0LWDdVCgxBShBMNlcCCkFXOAIQOT1CA1AcHQBEFxxDWxAoF1wNTwwYLANeLiYLH1tYUWkQUlhBG18NA15OAREFajlAOTsNHkZeLBNgHhkYEkJOA1wKT35IPh9fIyFMJEUgFAJJFwpPIVECF1dkTxEYalsdbR4NH15QEQ0QOxYmFl0LMl4PFlRKOVZWIiBCBF0VEREQBhcOGTpOQhJOA15bKxoQOiFCTRUnFxFbAQgAFFVUJFsAC3dROAVEDjoLHFFYWipeNRkMEmACA0sLHUIaY3wQbXJCGVNQDxAQBhAEGTpOQhJOTxEYahpfLjMOUFhQRUNHAUInHl4KJFscHEV7Ih9cKXoMWT9QWEMQUlhBV1wBAVMCT1lKOlYNbT9CEVsUWA4KNBEPE3YHEEEaLFlRJhIYbxoXHVQeFwpUIBcOA2APEEZMRjsYalYQbXJCUFwWWAtCAlgVH1UAQmcaBl1LZAJVITcSH0cEUAtCAlYxGEMHFlsBARETaiBVLiYNAgZeFgZHWkpNRxxeSxtVT0NdPgNCI3IHHlF6WEMQUh0PEzpOQhJOIV5MIxBJZXA2IBdcWEFgHhkYEkJODF0aT1hWZxFRIDdAXBUEChZVW3IEGVROHxtkZRwVapSkzbD28Nfk+ENkMzpBQhCM4qZOInhrCVbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LWS7OPS5viD47CM9rKM+7Ha3vbS2dKA5LV6FAxTExRBOlkdAX5OUhFsKxRDYx8LA1ZKOQdUPh0HA3ccDUceDV5AYlR3LD8HUBNQKxdRBgtDWxBMC1wIABMRQDtZPjEuSnQUHC9REB0NX0tONlcWGxEFalR3LD8HUFweHgwQExYFV1wHFFdOHFRLOR9fI3IRBFQEC00SXlglGFUdNUAPHxEFagJCODdCDRx6NQpDETRbNlQKJlsYBlVdOF4ZRx8LA1Y8QiJUFjQAFVUCShpMP11ZKRMKbXcRUhxKHgxCHxkVX3MBDFQHCB9/Czt1EhwjPXBZUWl9GwsCOwovBlYiDlNdJl4YbwIOEVYVWCp0SFhEExJHWFQBHVxZPl5zIjwEGVJeKC9xMT0+PnRHSzgjBkJbBkxxKTYmGUMZHAZCWlFrG18NA15OA1NUBxdTJXJCUAhQNQpDETRbNlQKLlMMCl0QaDtRLjoLHlADWABfHwgNEkQLBghOXxMRQBpfLjMOUFkSFCpEFxUSVxBTQn8HHFJ0cDdUKR4DElAcUEF5Bh0MBBAeC1EFClUYalYQbWhCQBdZcg9fERkNV1wMDnUcDlNLalYNbR8LA1Y8QiJUFjQAFVUCShApHVBaOVZVPjEDAFAUWEMQUkJBRxJHaF4BDFBUahpSIRYHEUEYC0MNUjUIBFMiWHMKC31ZKBNcZXAmFVQEEBAQUlhBVxBOQhJOTwsYelQZRz4NE1QcWA9SHi0RA1kDBxJTT3xRORV8dxMGFHkRGgZcWlo0B0QHD1dOTxEYalYQbXJCUA9QSFMKQkhbRwBMSzgjBkJbBkxxKTYmGUMZHAZCWlFrOlkdAX5ULlVcCANEOT0MWE5QLAZIBlhcVxI8B0ELGxFLPhdEPnBOUHMFFgAQT1gHAl4NFlsBARkRaiVELCYRXkcVCwZEWlFaV34BFlsIFhkaGQJROSFAXBciHRBVBlZDXhALDFZOEhgyQBpfLjMOUHgZCwBiUkVBI1EMERwjBkJbcDdUKQALF10EPxFfBwgDGEhGQGELHUddOFQcbXAVAlAeGwsSW3IsHkMNMAgvC1V0KxRVIXoZUGEVABcQT1hDJVUEDVsAT15Kah5fPXIWHxURWAVCFwsJV0MLEEQLHR8aZlZ0IjcRJ0cRCEMNUgwTAlVOHxtkIlhLKSQKDDYGNFwGEQdVAFBIfX0HEVE8VXBcLjRFOSYNHh0LWDdVCgxBShBMMFcEAFhWagJYJCFCA1ACDgZCUFRrVxBOQnQbAVIYd1ZWODwBBFwfFksZUh8AGlVUJVcaPFRKPB9TKHpAJFAcHRNfAAwyEkIYC1ELTRgCHhNcKCINAkFYOwxeFBEGWWAiI3ErMHh8ZlZ8IjEDHGUcGRpVAFFBEl4KQk9HZXxRORVidxMGFHcFDBdfHFAaV2QLGkZOUhEaGRNCOzcQUF0fCEMYABkPE18DSxBCZREYalZ2ODwBUAhQHhZeEQwIGF5GSzhOTxEYalYQbRwNBFwWAUsSOhcRVRxOQGELDkNbIh9eKnxMXhdZckMQUlhBVxBOFlMdBB9LOhdHI3oEBVsTDApfHFBIfRBOQhJOTxEYalYQbT4NE1QcWDdjUkVBEFEDBwgpCkVrLwRGJDEHWBckHQ9VAhcTA2MLEEQHDFQaY3wQbXJCUBVQWEMQUlgNGFMPDhImG0VIGRNCOzsBFRVNWARRHx1bMFUaMVccGVhbL14SBSYWAGYVChVZER1DXjpOQhJOTxEYalYQbXIOH1YRFENfGVRBBVUdQg9OH1JZJhoYKycME0EZFw0YW3JBVxBOQhJOTxEYalYQbXJCAlAEDRFeUh8AGlVUKkYaH3ZdPl4YbzoWBEUDQkwfFRkMEkNAEF0MA15AZBVfIH0UQRoXGQ5VAVdEEx8dB0AYCkNLZSZFLz4LEwoDFxFEPQoFEkJTI0ENSV1RJx9EcGNSQBdZQgVfABUAAxgtDVwIBlYWGjpxDhc9OXFZUWkQUlhBVxBOQhJOTxFdJBIZR3JCUBVQWEMQUlhBV1kIQlwBGxFXIVZEJTcMUHsfDApWC1BDP18eQB5MJ0VMOjFVOXIEEVwcHQceUFQVBUULSwlOHVRMPwRebTcMFD9QWEMQUlhBVxBOQhICAFJZJlZfJmBOUFERDAIQT1gRFFECDhoIGl9bPh9fI3pLUEcVDBZCHFgpA0QeMVccGVhbL0x6Hh0sNFATFwdVWgoEBBlOB1wKRjsYalYQbXJCUBVQWENZFFgPGERODVlcT15KahhfOXIGEUERWAxCUhYOAxAKA0YPQVVZPhcQOToHHhU+FxdZFAFJVXgBEhBCTXNZLlZCKCESH1sDHU0SXgwTAlVHWRIcCkVNOBgQKDwGehVQWEMQUlhBVxBOQlQBHRFnZlZDPyRCGVtQERNRGwoSX1QPFlNAC1BMK18QKT1oUBVQWEMQUlhBVxBOQhJOT1heagVCO3wSHFQJEQ1XUhkPExAdEERAAlBAGhpRNDcQAxURFgcQAQoXWUACA0sHAVYYdlZDPyRMHVQIKA9RCx0TBBBDQgNODl9cagVCO3wLFBUORUNXExUEWXoBAHsKT0VQLxg6bXJCUBVQWEMQUlhBVxBOQhJOTxFsGUxkKD4HAFoCDDdfIhQAFFUnDEEaDl9bL15zIjwEGVJeKC9xMT0+PnRCQkEcGR9RLloQAT0BEVkgFAJJFwpITBAcB0YbHV8yalYQbXJCUBVQWEMQUlhBV1UABjhOTxEYalYQbXJCUBUVFgc6UlhBVxBOQhJOTxEYBBlEJDQbWBc4FxMSXlovGBAdB0AYCkMYLBlFIzZMUhkEChZVW3JBVxBOQhJOT1RWLl86bXJCUFAeHENNW3JrWh1OLlsYChFNOhJROTdCHFofCGlEEwsKWUMeA0UAR1dNJBVEJD0MWBx6WEMQUg8JHlwLQkYPHFoWPRdZOXpTWRUUF2kQUlhBVxBOQkINDl1UYhBFIzEWGVoeUEo6UlhBVxBOQhJOTxEYIxAQITAOPVQTEEMQUhkPExACAF4jDlJQZCVVOQYHCEFQWENEGh0PV1wMDn8PDFkCGRNEGTcaBB1SNQJTGhEPEkNOAV0DH11dPhNUd3JAUBteWDBEEwwSWV0PAVoHAVRLDhleKHtCFVsUckMQUlhBVxBOQhJOT1heahpSIRsWFVgDWENRHBxBG1ICK0YLAkIWGRNEGTcaBBVQDAtVHFgNFVwnFlcDHAtrLwJkKCoWWBc5DAZdAVgRHlMFB1ZOTxEYakwQb3JMXhUjDAJEAVYIA1UDEWIHDFpdLl8QKDwGehVQWEMQUlhBVxBOQlsIT11aJjFCLDARUBURFgcQHhoNMEIPAEFAPFRMHhNIOXJCBF0VFkNcEBQmBVEMEQg9CkVsLw5EZXAlAlQSC0NVARsAB1UKQhJOTwsYaFYeY3IxBFQEC01VARsAB1UKJUAPDUIRahNeKVhCUBVQWEMQUlhBVxAHBBICDV18LxdEJSFCEVsUWA9SHjwEFkQGERw9CkVsLw5EbSYKFVtQFAFcNh0AA1gdWGELG2VdMgIYbxYHEUEYC0MQUlhBVxBOQhJOVREaalgebQEWEUEDVgdVEwwJBBlOB1wKZREYalYQbXJCUBVQWApWUhQDG2UeFlsDChFZJBIQITAOJUUEEQ5VXCsEA2QLGkZOG1ldJFZcLz43AEEZFQYKIR0VI1UWFhpMOkFMIxtVbXJCUBVQWEMQUlhbVxJOTBxOPEVZPgUeOCIWGVgVUEoZUh0PEzpOQhJOTxEYahNeKXtoUBVQWAZeFnIEGVRHaDhDQhHa3vbS2dKA5LVQLCJyUkBBlbD6QnE8KnVxHiUQr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4QBpfLjMOUHYCNEMNUiwAFUNAIUALC1hMOUxxKTYuFVMEPxFfBwgDGEhGQHMMAERMagJYJCFCOEASWk8QUBEPEV9MSzgtHX0CCxJUATMAFVlYA0NkFwAVVw1OQHYPAVVBbQUQGj0QHFFQmuOkUiFTPBAmF1BMQxF8JRNDGiADABVNWBdCBx1BChlkIUAiVXBcLjpRLzcOWE5QLAZIBlhcVxI9F0AYBkdZJltWIjEXA1AUWAtFEFZBMmM+ThIPAUVRZxFCLDBOUEYbEQ9cXxsJElMFThIPGkVXagZZLjkXABtSVEN0HR0SIEIPEhJTT0VKPxMQMHtoM0c8QiJUFjwIAVkKB0BGRjt7ODoKDDYGPFQSHQ8YWloyFEIHEkZOGVRKOR9fI3JYUBADWkoKFBcTGlEaSnEBAVdRLVhjDgArIGEvLiZiW1FrNEIiWHMKC31ZKBNcZXA3ORUcEQFCEwoYVxBOQhJUT35aOR9UJDMMJVxSUWlzADRbNlQKLlMMCl0QaCN5bTMXBF0fCkMQUlhBVwpOOwAFT2JbOB9AOXIgEVYbSiFRERNDXjotEH5ULlVcBhdSKD5KWBcjGRVVUh4OG1QLEBJOTxECalNDb3tYFloCFQJEWjsOGVYHBRw9Lmd9FSR/AgZLWT96FAxTExRBNEI8Qg9OO1BaOVhzPzcGGUEDQiJUFioIEFgaJUABGkFaJQ4YbwYDEhU3DQpUF1pNVxIDDVwHG15KaF86DiAwSnQUHC9REB0NX0tONlcWGxEFalRhODsBGxUCHQVVAB0PFFVOgLL6T0ZQKwIQKDMBGBUEGQEQFhcEBApMThIqAFRLHQRRPXJfUEECDQYQD1FrNEI8WHMKC3VRPB9UKCBKWT8zCjEKMxwFO1EMB15GFBFsLw5EbW9CUtfw2kNjBwoXHkYPDhKM76UYHgFZPiYHFBU1KzMcUhYOA1kIC1ccQxFZJAJZYDUQEVdcWABfFh0SWRJCQnYBCkJvOBdAbW9CBEcFHUNNW3IiBWJUI1YKI1BaLxoYNnI2FU0EWF4QUJrh1RAjA1EGBl9dOVbSzcZCPVQTEApeF1gkJGBOA1wKT1BNPhkQPjkLHFldGwtVERNPVRxOJl0LHGZKKwYQcHIWAkAVWB4ZeDsTJQovBlYiDlNdJl5LbQYHCEFQRUMSkPjDV3kaB18dT9O43lZ5OTcPUHAjKENRHBxBFkUaDRIeBlJTPwYeb35CNFoVCzRCEwhBShAaEEcLT0wRQDVCH2gjFFE8GQFVHlAaV2QLGkZOUhEaqPaSbQIOEUwVCkPS8uxBOl8YB18LAUUUahBcNH5CHloTFApAXlgTGF8DTUICDkhdOFZkHSFMUhlQPAxVAS8TFkBOXxIaHURdagsZRxEQIg8xHAd8ExoEGxgVQmYLF0UYd1YSr9LAUHgZCwAQkPj1V3wHFFdOHEVZPgUcbSEHAkMVCkNCFxIOHl5BCl0eQRMUajJfKCE1AlQAWF4QBgoUEhATSzgtHWMCCxJUATMAFVlYA0NkFwAVVw1OQNDuzRF7JRhWJDURUNfw7ENjEw4EWFwBA1ZOH0NdORNEbSIQH1MZFAZDXFpNV3QBB0E5HVBIaksQOSAXFRUNUWlzACpbNlQKLlMMCl0QMVZkKCoWUAhQWoGw0FgyEkQaC1wJHBHayuIQGBtCAEcVHhAcUhkCA1kBDBIGAEVTLw9DYXIWGFAdHU0SXlglGFUdNUAPHxEFagJCODdCDRx6ck4dUpr199L64tD67xFsCzQQenKA8KFQKyZkJjEvMGNOgKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmveweBQOFFECQmELG30Yd1ZkLDARXmYVDBdZHB8STXEKBn4LCUV/OBlFPTANCB1SMQ1EFwoHFlMLQB5OTVxXJB9EIiBAWT8jHRd8SDkFE3wPAFcCR0oYHhNIOXJfUBcmERBFExRBB0ILBFccCl9bLwUQKz0QUEEYHUNdFxYUV1kaEVcCCR8aZlZ0IjcRJ0cRCEMNUgwTAlVOHxtkPFRMBkxxKTYmGUMZHAZCWlFrJFUaLggvC1VsJRFXITdKUmYYFxRzBwsVGF0tF0AdAEMaZlZLbQYHCEFQRUMSMQ0SA18DQnEbHUJXOFQcbRYHFlQFFBcQT1gVBUULTjhOTxEYCRdcITADE15QRUNWBxYCA1kBDBoYRhF0IxRCLCAbXmYYFxRzBwsVGF0tF0AdAEMYd1ZGbTcMFBUNUWljFwwtTXEKBn4PDVRUYlRzOCARH0dQOwxcHQpDXgovBlYtAF1XOCZZLjkHAh1SOxZCARcTNF8CDUBMQxFDQFYQbXImFVMRDQ9EUkVBNF8ABFsJQXB7CTN+GX5CJFwEFAYQT1hDNEUcEV0cT3JXJhlCb35oUBVQWCBRHhQDFlMFQg9OCURWKQJZIjxKExxQNApSABkTDgo9B0YtGkNLJQRzIj4NAh0TUUNVHBxBChlkMVcaIwt5LhJ0Pz0SFFoHFksSPBcVHlYXMVsKChMUag0QGzMOBVADWF4QCVhDO1UIFhBCTxNqIxFYOXBCDRlQPAZWEw0NAxBTQhA8BlZQPlQcbQYHCEFQRUMSPBcVHlYHAVMaBl5WagVZKTdAXD9QWEMQMRkNG1IPAVlOUhFePxhTOTsNHh0GUUN8GxoTFkIXWGELG39XPh9WNAELFFBYDkoQFxYFV01HaGELG30CCxJUCSANAFEfDw0YUC0oJFMPDldMQxFDaiBRIScHAxVNWBgQUE9UUhJCQANeXxQaZlQBf2dHUhlSSVYAV1pBChxOJlcIDkRUPlYNbXBTQAVVWk8QJh0ZAxBTQhA7JhFrKRdcKHBOehVQWENzExQNFVENCRJTT1dNJBVEJD0MWENZWC9ZEAoABUlUMVcaK2FxGRVRITdKBFoeDQ5SFwpJAQoJEUcMRxMdb1Qcb3BLWRxQHQ1UUgVIfWMLFn5ULlVcDh9GJDYHAh1ZcjBVBjRbNlQKLlMMCl0QaDtVIydCO1AJGgpeFlpITXEKBnkLFmFRKR1VP3pAPVAeDShVCxoIGVRMThIVZREYalZ0KDQDBVkEWF4QMRcPEVkJTGYhKHZ0Dyl7CAtOUHsfLSoQT1gVBUULThI6CklMaksQbwYNF1IcHUN9FxYUVRxkHxtkPFRMBkxxKTYmGUMZHAZCWlFrJFUaLggvC1V6PwJEIjxKCxUkHRtEUkVBVWUADl0PCxFwPxQSYXImH0ASFAZzHhECHBBTQkYcGlQUQFYQbXI2H1ocDApAUkVBVWILD10YCkIYPh5VbQcrUFQeHENUGwsCGF4AB1EaHBFdPBNCNCYKGVsXVkEceFhBVxAoF1wNTwwYLANeLiYLH1tYUWkQUlhBVxBOQnc9Px9LLwJkOjsRBFAUUAVRHgsEXgtOJ2E+QUJdPjtRLjoLHlBYHgJcAR1ITBArMWJAHFRMAwJVIHoEEVkDHUoLUj0yJx4dB0Y+A1BBLwQYKzMOA1BZckMQUlhBVxBOC1ROKmJoZClTIjwMXlgREQ0QBhAEGRArMWJAMFJXJBgeIDMLHg80ERBTHRYPElMaShtOCl9cQFYQbXJCUBVQNQxGFxUEGURAEVcaKV1BYhBRISEHWQ5QNQxGFxUEGURAEVcaIV5bJh9AZTQDHEYVUVgQPxcXEl0LDEZAHFRMAxhWBycPAB0WGQ9DF1FaV30BFFcDCl9MZAVVORMMBFwxPigYFBkNBFVHaBJOTxEYalYQJDRCI0ACDgpGExRPKFMBDFxOG1ldJFZjOCAUGUMRFE1vERcPGQoqC0ENAF9WLxVEZXtCFVsUckMQUlhBVxBOC1ROPERKPB9GLD5ML1sfDApWCz8UHhAaClcAT2JNOABZOzMOXmoeFxdZFAEmAllUJlcdG0NXM14ZbTcMFD9QWEMQUlhBV28pTGtcJG58Czh0FA0qJXcvNCxxNj0lVw1ODFsCZREYalYQbXJCPFwSCgJCC0I0GVwBA1ZGRjsYalYQKDwGUEhZcmlcHRsAGxA9B0Y8TwwYHhdSPnwxFUEEEQ1XAUIgE1Q8C1UGG3ZKJQNALz0aWBcxGxdZHRZBP18aCVcXHBMUalRbKCtAWT8jHRdiSDkFE3wPAFcCR0oYHhNIOXJfUBchDQpTGVgKEkkdQlQBHRFXJBMdPjoNBBURGxdZHRYSWRJCQnYBCkJvOBdAbW9CBEcFHUNNW3IyEkQ8WHMKC3VRPB9UKCBKWT8jHRdiSDkFE3wPAFcCRxNsLxpVPT0QBBUEF0NVHh0XFkQBEBBHVXBcLj1VNAILE14VCksSOhcVHFUXJ14LGRMUag06bXJCUHEVHgJFHgxBShBMJRBCT3xXLhMQcHJAJFoXHw9VUFRBI1UWFhJTTxN9JhNGLCYNAhdcckMQUlgiFlwCAFMNBBEFahBFIzEWGVoeUAJTBhEXEhlkQhJOTxEYalZZK3IDE0EZDgYQBhAEGTpOQhJOTxEYalYQbXIOH1YRFENAUkVBJV8BDxwJCkV9JhNGLCYNAmUfC0sZeFhBVxBOQhJOTxEYah9WbSJCBF0VFkNlBhENBB4aB14LH15KPl5AbXlCJlATDAxCQVYPEkdGUh5aQwERY00QAz0WGVMJUEF4HQwKEklMThCM6aMYDxpVOzMWH0dSUUNVHBxrVxBOQhJOTxFdJBI6bXJCUFAeHENNW3IyEkQ8WHMKC31ZKBNcZXA2FVkVCAxCBlgVGBAAB1McCkJMahtRLjoLHlBSUVlxFhwqEkk+C1EFCkMQaD5fOTkHCXgRGwsSXlgafRBOQhIqCldZPxpEbW9CUn1SVEN9HRwEVw1OQGYBCFZUL1QcbQYHCEFQRUMSPxkCH1kABxBCZREYalZzLD4OElQTE0MNUh4UGVMaC10AR1BbPh9GKHtoUBVQWEMQUlgIERAADUZODlJMIwBVbSYKFVtQCgZEBwoPV1UABjhOTxEYalYQbT4NE1QcWDwcUhATBxBTQmcaBl1LZBBZIzYvCWEfFw0YW0NBHlZODF0aT1lKOlZEJTcMUEcVDBZCHFgEGVRkQhJOTxEYalZcIjEDHBUSHRBEXlgDExBTQlwHAx0YJxdEJXwKBVIVckMQUlhBVxBOBF0cT24UahsQJDxCGUURERFDWioOGF1ABVcaIlBbIh9eKCFKWRxQHAw6UlhBVxBOQhJOTxEYJhlTLD5CFBVNWDZEGxQSWVQHEUYPAVJdYh5CPXwyH0YZDApfHFRBGh4cDV0aQWFXOR9EJD0MWT9QWEMQUlhBVxBOQhIHCRFcakoQLzZCBF0VFkNSFlhcV1RVQlALHEUYd1ZdbTcMFD9QWEMQUlhBV1UABjhOTxEYalYQbTsEUFcVCxcQBhAEGRA7FlsCHB9MLxpVPT0QBB0SHRBEXAoOGERAMl0dBkVRJRgQZnI0FVYEFxEDXBYEABheTgZCXxgRcVZ+IiYLFkxYWitfBhMEDhJCQNDo/REaZFhSKCEWXlsRFQYZUh0PEzpOQhJOCl9cagsZRwEHBGdKOQdUPhkDElxGQGYBCFZUL1ZkOjsRBFAUWCZjIlpITXEKBnkLFmFRKR1VP3pAOFoEEwZJNysxVRxOGThOTxEYDhNWLCcOBBVNWEFkUFRBOl8KBxJTTxNsJRFXITdAXBUkHRtEUkVBVXU9MhBCZREYalZzLD4OElQTE0MNUh4UGVMaC10AR1BbPh9GKHtoUBVQWEMQUlgIERAPAUYHGVQYPh5VI1hCUBVQWEMQUlhBVxACDVEPAxFOaksQIz0WUHAjKE1jBhkVEh4aFVsdG1RcQFYQbXJCUBVQWEMQUj0yJx4dB0Y6GFhLPhNUZSRLehVQWEMQUlhBVxBOQlsIT2VXLRFcKCFMNWYgLBRZAQwEExAaClcAT2VXLRFcKCFMNWYgLBRZAQwEEwo9B0Y4Dl1NL15GZHIHHlF6WEMQUlhBVxBOQhJOIV5MIxBJZXAqH0EbHRoSXlhDI0cHEUYLCxF9GSYQb3JMXhVYDkNRHBxBVX8gQBIBHREaBTB2b3tLehVQWEMQUlhBEl4KaBJOTxFdJBIQMHtoI1AEKllxFhwtFlILDhpMPVRbKxpcbSEDBlAUWBNfAVpITXEKBnkLFmFRKR1VP3pAOFoEEwZJIB0CFlwCQB5OFDsYalYQCTcEEUAcDEMNUlozVRxOL10KChEFalRkIjUFHFBSVENkFwAVVw1OQGALDFBUJlQcR3JCUBUzGQ9cEBkCHBBTQlQbAVJMIxleZTMBBFwGHUoQGx5BFlMaC0QLT0VQLxgQAD0UFVgVFhceAB0CFlwCMl0dRxgDajhfOTsECR1SMAxEGR0YVRxMMFcNDl1ULxIeb3tCFVsUWAZeFlgcXjpkLlsMHVBKM1hkIjUFHFA7HRpSGxYFVw1OLUIaBl5WOVh9KDwXO1AJGgpeFnJrWh1OgKbujaW4qOKwbQYKFVgVWEgQIRkXEhAPBlYBAUIYqOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwmvewkOzhlaTugKbujaW4qOKwr8bikqHwcgpWUiwJEl0LL1MADlZdOFZRIzZCI1QGHS5RHBkGEkJOFloLATsYalYQGToHHVA9GQ1RFR0TTWMLFn4HDUNZOA8YATsAAlQCAUo6UlhBV2MPFFcjDl9ZLRNCdwEHBHkZGhFRAAFJO1kMEFMcFhgyalYQbQEDBlA9GQ1RFR0TTXkJDF0cCmVQLxtVHjcWBFweHxAYW3JBVxBOMVMYCnxZJBdXKCBYI1AEMQReHQoEPl4KB0oLHBlDalR9KDwXO1AJGgpeFlpBChlkQhJOT2VQLxtVADMMEVIVClljFwwnGFwKB0BGLF5WLB9XYwEjJnAvKix/JlFrVxBOQmEPGVR1KxhRKjcQSmYVDCVfHhwEBRgtDVwIBlYWGTdmCA0hNnIjUWkQUlhBJFEYB38PAVBfLwQKDycLHFEzFw1WGx8yElMaC10AR2VZKAUeDj0MFlwXC0o6UlhBV2QGB18LIlBWKxFVP2gjAEUcATdfJhkDX2QPAEFAPFRMPh9eKiFLehVQWENAERkNGxgIF1wNG1hXJF4ZbQEDBlA9GQ1RFR0TTXwBA1YvGkVXJhlRKRENHlMZH0sZUh0PExlkB1wKZTsVZ1ZjOTMQBBUEEAYQNysxV1wBDUJOR1hMahleIStCAlAeHAZCAVgEGVEMDlcKT1JZPhNXIiALFUZZciZjIlYSA1EcFhpHZTt2JQJZKytKUmxCM0N4BxpDWxBMLl0PC1RcahBfP3JAUBteWCBfHB4IEB4pI38rMH95BzMQY3xCUhtQKBFVAQtBJVkJCkYtG0NUagJfbSYNF1IcHU0SW3IRBVkAFhpGTWpheD1tbR4NEVEVHENWHQpBUkNOSmICDlJdAxIQaDZLXhdZQgVfABUAAxgtDVwIBlYWDTd9CA0sMXg1VENzHRYHHldAMn4vLHRnAzIZZFg='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, antiSpy = { kick = true, halt = true } })
