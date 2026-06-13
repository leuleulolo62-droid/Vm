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

local __k = 'UnaDOxitLDtguaS5UjMbV5lk'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
