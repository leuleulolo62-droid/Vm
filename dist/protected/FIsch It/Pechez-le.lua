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

local __k = 'RMwloqV9GREi8rTjIDUlWPng'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-uTSsVd6AGDDM
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, watermark = 'Y2k-uTSsVd6AGDDM', neuterAC = true, antiSpy = { kick = true, halt = true } })
