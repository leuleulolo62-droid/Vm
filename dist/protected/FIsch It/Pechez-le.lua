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

local __k = 'ZisWh6XqAxtUSHMNf9YLgAXV'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
