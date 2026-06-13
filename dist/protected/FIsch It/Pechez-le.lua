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
				-- crash the tamperer's client (retaliation / fallback if kick is blocked):
				-- allocate faster than GC can reclaim (refs kept) -> OOM. Runs in its own
				-- thread so it isn't cancelled by cleanup.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(1048576, 0)
							else
								sink[#sink + 1] = string.rep("\0", 1048576)
							end
						end
					end
					if sp then pcall(sp, crasher) else pcall(crasher) end
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

local __k = '3bjujDQWv4FBE50lBegxV19v'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
