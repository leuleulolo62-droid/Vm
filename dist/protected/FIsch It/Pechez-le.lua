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

local __k = 'pr6OCODCXOKzlHFXBQLi3Yes'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
