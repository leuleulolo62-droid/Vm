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

local __k = 'YjO94zHdvDYlpTQK7S62Qf3y'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
