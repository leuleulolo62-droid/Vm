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

local __k = '4CCyO0Qy0fVJ7j2HEAZIFev8'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, antiSpy = { kick = true, halt = true } })
