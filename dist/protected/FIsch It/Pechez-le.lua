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

local __k = 'DtixeGDcW35kaVzKlKQiR9pV'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
