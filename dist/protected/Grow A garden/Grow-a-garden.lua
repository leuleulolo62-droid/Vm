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

local __k = 'ZMONiDxqZYMjB3MBU1PCabil'
local __p = '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axNnYiZBIiYABklGei8uPQxOHR8+U0cMN10uNjxePmM0FgAAKWMoKx0XEBQ5MiEPMRtkSHURcGMNDQoNNm0jPUl5WD01OiwGEl8sOzBDagUIDA0qMz88OiosER0+cW8GJ1IpJydCJCIVEUtFUG1vbkktHlE2Km0eKlYjSHURcGNBQklMNiIsLwVkCxl6ZG0GMQkLKztVFioTER0vMiQjKkFmKxk/OiYGJ0Bva18RcGNBQklMeiQpbhosWAUyPCNKMFY5NydfcDcOER0eMyMoZhosVic7NTgPaxMoLDE7cGNBQgwCPkdvbklkChQuLD8EYhFgYF9UPidraERBeq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPyUdHbxN+bHVjFQ4uNiw/UGBibovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0jkhLTZQPGMzBwQDLig8blRkA1EFOiwJKlZtf3VKLW9BPQwaPyM7PUl5WB8zNW0XSDkhLTZQPGMHFwcPLiQgIEkhDhQ0LT5CazltYnUROSVBMAwBNTkqPUcbHQc/NzkZYlIjJnVjNS4OFgwfdBIqOAwqDAJ0CSwYJ105YiFZNS1BEAwYLz8hbjshFR4uPD5EHVY7JztFI2MEDA1mem1vbjshFR4uPD5EHVY7JztFI2NcQjwYMyE8YBshCx42Lyg6I0clahZePiUIBUcpDAgBGjobKDAOEWRgYhNtYidUJDYTDEk+PyAgOgw3Vi4/LygENkBHJztVWkkHFwcPLiQgIEkWHRw1LSgZbFQoNn1aNTpIaElMem0mKEkWHRw1LSgZbGwuIzZZNRgKBxAxeiwhKkkWHRw1LSgZbGwuIzZZNRgKBxAxdB0uPAwqDFEuMSgEYkEoNiBDPmMzBwQDLig8YDYnGRIyPBYBJ0oQYjBfNElBQklMNiIsLwVkFhA3PG1XYnAiLDNYN20zJyQjDggcFQIhASx6Nj9KKVY0SHURcGMNDQoNNm0qOEl5WBQsPCMeMRtkeXVYNmMPDR1MPztvOgEhFlEoPDkfMF1tLDxdcCYPBmNMem1vIgYnGR16K21XYlY7eBNYPicnCxsfLg4nJwUgUB87NChDSBNtYnVYNmMTQh0EPyNvHAwpFwU/KmM1IVIuKjBqOyYYP0lRej9vKwcgclF6eW0YJ0c4MDsRIkkEDA1mUCs6IAowER40eR8PL1w5JyYfNioTB0EHPzRjbkdqVlhQeW1KYl8iITRdcDFBX0k+PyAgOgw3VhY/LWUBJ0pkeXVYNmMPDR1MKG07JgwqWAM/LTgYLBMrIzlCNWMEDA1mem1vbgUrGxA2eSwYJUBtf3VFMSENB0ccOy4kZkdqVlhQeW1KYl8iITRdcCwKQlRMKi4uIgVsHgQ0OjkDLV1la3VDagUIEAw/Pz85KxtsDBA4NShEN109IzZaeCITBRpAenxjbgg2HwJ0N2RDYlYjJnw7cGNBQhsJLjg9IEkrE3s/NylgSFU4LDZFOSwPQjsJNyI7KxpqER8sNiYPalgoO3kRfm1PS2NMem1vIgYnGR16K21XYmEoLzpFNTBPBQwYciYqN0B/WBg8eSMFNhM/YiFZNS1BEAwYLz8hbg8lFAI/eSgEJjltYnURPCwCAwVMOz8oPUl5WAU7OyEPbEMsIT4Zfm1PS2NMem1vIgYnGR16KygZN185MXUMcDhBEgoNNiFnKBwqGwUzNiNCaxM/JyFEIi1BEFMlNDsgJQwXHQMsPD9CNlIvLjAfJS0RAwoHciw9KRpoWEB2eSwYJUBjLHwYcCYPBkBMJ0dvbklkERd6NyIeYkEoMSBdJDA6UzRMLiUqIEk2HQUvKyNKJFIhMTARNS0FaElMem07LwsoHV8oPCAFNFZlMDBCJS8VEUVMa2RFbklkWAM/LTgYLBM5MCBUfGMVAwsAP2M6IBklGxpyKygZN185MXw7NS0FaGNBd22t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN1gbx5tdnsRFgIzL0k+Hx4AAjwQMT4UeWUMK10pYiVdMToEEE4feiI4IAwgWBc7KyBKK11tNTpDOzARAwoJc0diY0mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16NHLjpSMS9BJAgeN21ybhI5ch01OiwGYmwrIydcfGM+DggfLh8qPQYoDhR6ZG0EK19hYmU7WiUUDAoYMyIhbi8lChx0KygZLV87J30YWmNBQkkFPG0QKAg2FVE7NylKHVUsMDgfACITBwcYeiwhKkkwERIxcWRKbxMSLjRCJBEEEQYALChvcklxWAUyPCNKMFY5NydfcBwHAxsBeighKmNkWFF6NSIJI19tJDRDPTBBX0k7NT8kPRklGxRgHyQEJnUkMCZFEysIDg1EeAsuPARmUXt6eW1KK1VtLDpFcCUAEAQfejknKwdkChQuLD8EYl0kLnVUPidrQklMeisgPEkbVFE8eSQEYlo9IzxDI2sHAxsBKXcIKx0HEBg2PT8PLBtka3VVP0lBQklMem1vbgUrGxA2eSQHMhNwYjMLFioPBi8FKD47DQEtFBVyewQHMlw/NjRfJGFIaElMem1vbklkFB45OCFKJlI5I3UMcCoMEkkNNClvJwQ0QjczNyksK0E+NhZZOS8FSksoOzkubEBOWFF6eW1KYhMhLTZQPGMOFQcJKG1ybg0lDBB6OCMOYlcsNjQLFioPBi8FKD47DQEtFBVyewIdLFY/YHw7cGNBQklMem0mKEkrDx8/K20LLFdtLSJfNTFPNAgALyhvc1RkNB45OCE6LlI0JycfHiIMB0kYMighRElkWFF6eW1KYhNtYgpXMTEMQlRMPHZvEQUlCwUIPD4FLkUoYmgRJCoCCUFFUG1vbklkWFF6eW1KYkEoNiBDPmM+BAgeN0dvbklkWFF6eSgEJjltYnURNS0FaAwCPkdFY0RkOR02eT0GI105YjheNCYNEUkDNG07JgxkHhAoNEcMN10uNjxePmMnAxsBdCoqOjkoGR8uKmVDSBNtYnVdPyAADkkKenBvCAg2FV8oPD4FLkUoanwKcCoHQgcDLm0pbh0sHR96KygeN0EjYi5McCYPBmNMem1vIgYnGR16MCAaYg5tJG93OS0FJAAeKTkMJgAoHFl4ECAaLUE5IztFcmpaQgAKeiMgOkktFQF6LSUPLBM/JyFEIi1BGRRMPyMrRElkWFE2Ni4LLhM9LjRfJDBBX0kFNz11CAAqHDczKz4eAVskLjEZchMNAwcYKRIfJhA3ERI7NW9DSBNtYnVYNmMPDR1MKiEuIB03WAUyPCNKMl8sLCFCcH5BCwQcYAsmIA0CEQMpLQ4CK18pandhPCIPFhpOc20qIA1OWFF6eSQMYl0iNnVBPCIPFhpMLiUqIEk2HQUvKyNKOU5tJztVWmNBQkkePzk6PAdkCB07NzkZeHQoNhZZOS8FEAwCcmRFKwcgcnt3dG0rLl9tMDxBNWNOQgENKDsqPR0lGh0/eT0GI105MV9XJS0CFgADNG0JLxspVhY/LR8DMlYdLjRfJDBJS2NMem1vIgYnGR16NjgeYg5tOSg7cGNBQg8DKG0QYkk0WBg0eSQaI1o/MX13MTEMTA4JLh0jLwcwC1lzcG0OLTltYnURcGNBQgAKej11BxoFUFMXNikPLhFkYiFZNS1rQklMem1vbklkWFF6dGBKDlwiKXVXPzFBBBsZMzk8bkZkCAM1ND0eMRMkLCZYNCZBEgUNNDlvIwYgHR1QeW1KYhNtYnURcGNBDgYPOyFvKBsxEQUpeXBKMgkLKztVFioTER0vMiQjKkFmPgMvMDkZYBpHYnURcGNBQklMem1vJw9kHgMvMDkZYkclJzs7cGNBQklMem1vbklkWFF6eSsFMBMSbnVXImMIDEkFKiwmPBpsHgMvMDkZeHQoNhZZOS8FEAwCcmRmbg0rWAU7OyEPbFojMTBDJGsOFx1Aeis9Z0khFhVQeW1KYhNtYnURcGNBBwUfP0dvbklkWFF6eW1KYhNtYnURfW5BMgUNNDk8bh4tDBk1LDlKJEE4KyERNiwNBgweKW0iLxBkCxg9NywGYkEkMjBfNTASQh8FO20uOh02ERMvLShgYhNtYnURcGNBQklMem1vbgAiWAFgHigeA0c5MDxTJTcESks+Mz0qbEBkRUx6LT8fJxM5KjBfcDcAAAUJdCQhPQw2DFk1LDlGYkNkYjBfNElBQklMem1vbklkWFE/NylgYhNtYnURcGMEDA1mem1vbgwqHHt6eW1KMFY5NydfcCwUFmMJNClFRA8xFhIuMCIEYnUsMDgfNyYVMRkNLSMfIRpsUXt6eW1KLlwuIzkRNmNcQi8NKCBhPAw3Fx0sPGVDeRMkJHVfPzdBBEkYMighbhshDAQoN20EK19tJztVWmNBQkkANS4uIkk3CFFneStQBFojJhNYIjAVIQEFNilnbDo0GQY0Bh0FK105YHwRPzFBBFMqMyMrCAA2CwUZMSQGJhtvATBfJCYTPTkDMyM7bEBOWFF6eSQMYkA9YjRfNGMSElMlKQxnbCslCxQKOD8eYBptNj1UPmMTBx0ZKCNvPRlqKB4pMDkDLV1tJztVWiYPBmNmPDghLR0tFx96HywYLx0qJyFyNS0VBxtEc0dvbklkFB45OCFKJBNwYhNQIi5PEAwfNSE5K0FtQ1EzP20ELUdtJHVFOCYPQhsJLjg9IEkqER16PCMOSBNtYnVdPyAADkkfKm1ybg9+Phg0PQsDMEA5AT1YPCdJQCoJNDkqPDYUFxg0LW9DSBNtYnVYNmMSEkkNNClvPRl+MQIbcW8oI0AoEjRDJGFIQh0EPyNvPAwwDQM0eT4abGMiMTxFOSwPQgwCPkdvbklkChQuLD8EYnUsMDgfNyYVMRkNLSMfIRpsUXs/NylgSB5gYrekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5ykdiY0lxVlEJDQw+ETlgb3XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz91FIgYnGR16CjkLNkBtf3VKcDMNAwcYPylvc0l0VFEyOD8cJ0A5JzERbWNRTkkfNSErblRkSF16OyIfJVs5YmgRYG9BEQwfKSQgIDowGQMueXBKNlouKX0YcD5rBBwCOTkmIQdkKwU7LT5EMFY+JyEZeWMyFggYKWM/IggqDBQ+dW05NlI5MXtZMTEXBxoYPyljbjowGQUpdz4FLldhYgZFMTcSTAsDLyonOkl5WEF2aWFabgN2YgZFMTcSTBoJKT4mIQcXDBAoLW1XYkckIT4ZeWMEDA1mPDghLR0tFx96CjkLNkBjNyVFOS4ESkBmem1vbgUrGxA2eT5KfxMgIyFZfiUNDQYecjkmLQJsUVF3eR4eI0c+bCZUIzAIDQc/Liw9OkBOWFF6eSEFIVIhYj0RbWMMAx0EdCsjIQY2UAJ6dm1ZdAN9a24RI2NcQhpMd20nbkNkS0dqaUdKYhNtLjpSMS9BD0lReiAuOgFqHh01Nj9CMRNiYmMBeXhBQkkfenBvPUlpWBx6c21ccjltYnURIiYVFxsCej47PAAqH188Nj8HI0dlYHABYidbR1lePndqflsgWl16MWFKLx9tMXw7NS0FaGNBd22t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN1gbx5tdHsRERY1LUkrGx8LCydOVVx6u9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChWi8OAQgAegw6OgYDGQM+PCNKfxM2YgZFMTcEQlRMIUdvbklkGQQuNh0GI105YnURcH5BBAgAKShjbhkoGR8uCigPJhNtYnURbWMPCwVAem0/IggqDDU/NSwTYhNtf3UBfnZNaElMem0uOx0rMBAoLygZNhNtf3VXMS8SB0VMMiw9OAw3DDg0LSgYNFIhYmgRY21RTmNMem1vLxwwFzI1NSEPIUdtYmgRNiINEQxAei4gIgUhGwUTNzkPMEUsLnUMcHdPUkVmem1vbggxDB4JPCEGYhNtYnUMcCUADhoJdm08KwUoMR8uPD8cI19tYmgRY3NNaElMem0uOx0rLxAuPD9KYhNtf3VXMS8SB0VMLSw7KxsNFgU/KzsLLhNwYmMBfElBQklMOzg7ITosFwc/NW1KYg5tJDRdIyZNQhoENTsqIiAqDBQoLywGYg5tc2UdcDAJDR8JNgYqKxlkRVEhJGFgYhNtYj9YJDcEEElMem1vbkl5WAUoLChGSE4wSF9dPyAADkkKLyMsOgArFlEwMDlCNBptMDBFJTEPQigZLiIILxsgHR90CjkLNlZjKDxFJCYTQggCPm0aOgAoC18wMDkeJ0FlNHkRYG1QUEBMNT9vOEkhFhVQU2BHYnUkLDERMWMJBwUIej4qKw1kDB41NW0IOxMjIzhUWi8OAQgAeis6IAowER40eSsDLFceJzBVBCwODkECOyAqZ2NkWFF6NSIJI19tIT1QImNcQiUDOSwjHgUlARQodw4CI0EsISFUIklBQklMNiIsLwVkGhA5Mj0LIVhtf3V9PyAADjkAOzQqPFMCER8+HyQYMUcOKjxdNGtDIAgPMT0uLQJmUXt6eW1KLlwuIzkRNjYPAR0FNSNvPgAnE1kqOD8PLEdkSHURcGNBQklMPCI9bjZoWAV6MCNKK0MsKydCeDMAEAwCLncIKx0HEBg2PT8PLBtka3VVP0lBQklMem1vbklkWFEzP20eeHo+A30TBCwODktFejknKwdOWFF6eW1KYhNtYnURcGNBQgUDOSwjbg9kRVEuYwoPNnI5NidYMjYVB0FOPG9mRElkWFF6eW1KYhNtYnURcGMIBEkKenBybgclFRR6LSUPLBM/JyFEIi1BFkkJNClFbklkWFF6eW1KYhNtYnURcCoHQh1CFCwiK1MiER8+cW80YBNjbHVfMS4ES0kYMighbhshDAQoN20eYlYjJl8RcGNBQklMem1vbklkWFF6MCtKNh0DIzhUaiUIDA1EeGgUHQwhHFQHe2RKI10pYn1Ffg0ADwxWNiI4KxtsUUs8MCMOal0sLzALPCwWBxtEc2Fvf0VkDAMvPGRDYkclJzsRIiYVFxsCejlvKwcgclF6eW1KYhNtYnURcCYPBmNMem1vbklkWBQ0PUdKYhNtJztVWmNBQkkePzk6PAdkUBIyOD9KI10pYiVYMyhJAQENKGRmbgY2WFk4OC4BMlIuKXVQPidBEgAPMWUtLwovCBA5MmRDSFYjJl87NjYPAR0FNSNvDxwwFzY7KykPLB0oMyBYIBAEBw1ENCwiK0BOWFF6eSQMYl0iNnVfMS4EQh0EPyNvPAwwDQM0eSsLLkAoYjBfNElBQklMNiIsLwVkDB41NW1XYlUkLDFiNSYFNgYDNmUhLwQhUXt6eW1KK1VtLDpFcDcODQVMLiUqIEk2HQUvKyNKJFIhMTARNS0FaElMem0jIQolFFE5MSwYYg5tDjpSMS8xDggVPz9hDQElChA5LSgYSBNtYnVYNmMVDQYAdB0uPAwqDFEkZG0JKlI/YiFZNS1rQklMem1vbkkwFx42dx0LMFYjNnUMcCAJAxtmem1vbklkWFEuOD4BbEQsKyEZYG1QS2NMem1vKwcgclF6eW0YJ0c4MDsRJDEUB2MJNClFRA8xFhIuMCIEYnI4Njp2MTEFBwdCKTkuPB0FDQU1CSELLEdla18RcGNBCw9MGzg7IS4lChU/N2M5NlI5J3tQJTcOMgUNNDlvOgEhFlEoPDkfMF1tJztVWmNBQkktLzkgCQg2HBQ0dx4eI0cobDREJCwxDggCLm1ybh02DRRQeW1KYmY5KzlCfi8ODRlEPDghLR0tFx9ycG0YJ0c4MDsROioVSigZLiIILxsgHR90CjkLNlZjMjlQPjclBwUNI2RvKwcgVHt6eW1KYhNtYjNEPiAVCwYCcmRvPAwwDQM0eQwfNlwKIydVNS1PMR0NLihhLxwwFyE2OCMeYlYjJnkRNjYPAR0FNSNnZ2NkWFF6eW1KYhNtYnVdPyAADkkfPygrblRkOQQuNgoLMFcoLHtiJCIVB0ccNiwhOjohHRVQeW1KYhNtYnURcGNBCw9MNCI7bhohHRV6Nj9KMVYoJnUMbWNDQEkYMighbhshDAQoN20PLFdHYnURcGNBQklMem1vJw9kFh4ueQwfNlwKIydVNS1PBxgZMz0cKwwgUAI/PClDYkclJzsRIiYVFxsCeighKmNkWFF6eW1KYhNtYnUcfWMyBwcIeixvPgUlFgV6KygbN1Y+NnVQJGMAQhkDKSQ7JwYqWBg0KiQOJxMiNycRNiITD2NMem1vbklkWFF6eW0GLVAsLnVSNS0VBxtMZ20JLxspVhY/LQ4PLEcoMH0YWmNBQklMem1vbklkWBg8eSMFNhMuJztFNTFBFgEJNG09Kx0xCh96PCMOSBNtYnURcGNBQklMemBibjo0ChQ7PW0aLlIjNiYRIiIPBgYBNjRvLxsrDR8+eTkCJxMuJztFNTFrQklMem1vbklkWFF6NSIJI19tKDxFJCYTOklRemUiLx0sVgM7NykFLxtkYngRYG1US0lGen5/RElkWFF6eW1KYhNtYjleMyINQgMFLjkqPDNkRVFyNCweKh0/IztVPy5JS0lBen1he0BkUlFpaUdKYhNtYnURcGNBQkkANS4uIkk0FwJ6ZG0JJ105JycRe2M3BwoYNT98YAchD1kwMDkeJ0EVbnUBfGMLCx0YPz8VZ2NkWFF6eW1KYhNtYnVjNS4OFgwfdCsmPAxsWiE2OCMeYB9tMjpCfGMSBwwIc0dvbklkWFF6eW1KYhMeNjRFI20RDggCLigrblRkKwU7LT5EMl8sLCFUNGNKQlhmem1vbklkWFE/NylDSFYjJl9XJS0CFgADNG0OOx0rPxAoPSgEbEA5LSVwJTcOMgUNNDlnZ0kFDQU1HiwYJlYjbAZFMTcETAgZLiIfIggqDFFneSsLLkAoYjBfNElrBBwCOTkmIQdkOQQuNgoLMFcoLHtCJCITFigZLiIHLxsyHQIucWRgYhNtYjxXcAIUFgYrOz8rKwdqKwU7LShEI0Y5LR1QIjUEER1MLiUqIEk2HQUvKyNKJ10pSHURcGMgFx0DHSw9KgwqViIuODkPbFI4Njp5MTEXBxoYenBvOhsxHXt6eW1KF0ckLiYfPCwOEkEKLyMsOgArFllzeT8PNkY/LHVwJTcOJQgePighYDowGQU/dyULMEUoMSF4PjcEEB8NNm0qIA1oclF6eW1KYhNtJCBfMzcIDQdEc209Kx0xCh96GDgeLXQsMDFUPm0yFggYP2MuOx0rMBAoLygZNhMoLDEdcCUUDAoYMyIhZkBOWFF6eW1KYhNtYnURNiwTQjZAej0jLwcwWBg0eSQaI1o/MX13MTEMTA4JLh0jLwcwC1lzcG0OLTltYnURcGNBQklMem1vbklkERd6NyIeYnI4Njp2MTEFBwdCCTkuOgxqGQQuNgULMEUoMSERJCsEDEkePzk6PAdkHR8+U21KYhNtYnURcGNBQklMem0jIQolFFE1Mm1XYmEoLzpFNTBPCwcaNSYqZksMGQMsPD4eYB9tMjlQPjdIaElMem1vbklkWFF6eW1KYhMkJHVeO2MVCgwCeh47Lx03Vhk7KzsPMUcoJnUMcBAVAx0fdCUuPB8hCwU/PW1BYgJtJztVWmNBQklMem1vbklkWFF6eW0eI0AmbCJQOTdJUkdcb2RFbklkWFF6eW1KYhNtJztVWmNBQklMem1vKwcgUXs/NylgJEYjISFYPy1BIxwYNQouPA0hFl8pLSIaA0Y5LR1QIjUEER1Ec20OOx0rPxAoPSgEbGA5IyFUfiIUFgYkOz85KxowWEx6PywGMVZtJztVWkkHFwcPLiQgIEkFDQU1HiwYJlYjbCZFMTEVIxwYNQ4gIgUhGwVycEdKYhNtKzMRETYVDS4NKCkqIEcXDBAuPGMLN0ciATpdPCYCFkkYMighbhshDAQoN20PLFdHYnURcAIUFgYrOz8rKwdqKwU7LShEI0Y5LRZePC8EAR1MZ207PBwhclF6eW0/NlohMXtdPywRSg8ZNC47JwYqUFh6KygeN0EjYhREJCwmAxsIPyNhHR0lDBR0OiIGLlYuNhxfJCYTFAgAeighKkVOWFF6eW1KYhMrNztSJCoODEFFej8qOhw2FlEbLDkFBVI/JjBffhAVAx0JdCw6OgYHFx02PC4eYlYjJnkRNjYPAR0FNSNnZ2NkWFF6eW1KYhNtYnUcfWM2AwUHeiI5KxtkChgqPG0MMEYkNiYRIyxBFgEJI20uOx0rVRI1NSEPIUdHYnURcGNBQklMem1vIgYnGR16BmFKKkE9YmgRBTcIDhpCPSg7DQElCllzU21KYhNtYnURcGNBQgAKeiMgOkksCgF6LSUPLBM/JyFEIi1BBwcIUG1vbklkWFF6eW1KYl8iITRdcCwTCw4FNCwjblRkEAMqdw4sMFIgJ18RcGNBQklMem1vbkkiFwN6BmFKJEFtKzsROTMACxsfcgsuPARqHxQuCyQaJ2MhIztFI2tIS0kINUdvbklkWFF6eW1KYhNtYnUROSVBDAYYegw6OgYDGQM+PCNEEUcsNjAfMTYVDSoDNiEqLR1kDBk/N20IMFYsKXVUPidrQklMem1vbklkWFF6eW1KYlorYjNDagoSI0FOGCw8KzklCgV4cG0eKlYjSHURcGNBQklMem1vbklkWFF6eW1KKkE9bBZ3IiIMB0lReg4JPAgpHV80PDpCJEFjEjpCOTcIDQdMcW0ZKwowFwNpdyMPNRt9bnUCfGNRS0Bmem1vbklkWFF6eW1KYhNtYnURcGMVAxoHdDouJx1sSF9qYWRgYhNtYnURcGNBQklMem1vbgwoCxQzP20MMAkEMRQZcg4OBgwAeGRvLwcgWBcodx0YK14sMCxhMTEVQh0EPyNFbklkWFF6eW1KYhNtYnURcGNBQkkEKD1hDS82GRw/eXBKAXU/IzhUfi0EFUEKKGMfPAApGQMjCSwYNh0dLSZYJCoODElHehsqLR0rCkJ0NygdagNhYmYdcHNIS2NMem1vbklkWFF6eW1KYhNtYnURcDcAEQJCLSwmOkF0VkFicEdKYhNtYnURcGNBQklMem1vKwcgclF6eW1KYhNtYnURcCYPBmNMem1vbklkWFF6eW0CMENjARNDMS4EQlRMNT8mKQAqGR1QeW1KYhNtYnVUPidIaAwCPkcpOwcnDBg1N20rN0ciBTRDNCYPTBoYNT0OOx0rOx42NSgJNhtkYhREJCwmAxsIPyNhHR0lDBR0ODgeLXAiLjlUMzdBX0kKOyE8K0khFhVQUysfLFA5KzpfcAIUFgYrOz8rKwdqCwU7KzkrN0ciETBdPGtIaElMem0mKEkFDQU1HiwYJlYjbAZFMTcETAgZLiIcKwUoWAUyPCNKMFY5NydfcCYPBmNMem1vDxwwFzY7KykPLB0eNjRFNW0AFx0DCSgjIkl5WAUoLChgYhNtYgBFOS8STAUDNT1nKBwqGwUzNiNCaxM/JyFEIi1BIxwYNQouPA0hFl8JLSweJx0+JzldGS0VBxsaOyFvKwcgVHt6eW1KYhNtYjNEPiAVCwYCcmRvPAwwDQM0eQwfNlwKIydVNS1PMR0NLihhLxwwFyI/NSFKJ10pbnVXJS0CFgADNGVmRElkWFF6eW1KYhNtYgdUPSwVBxpCPCQ9K0FmKxQ2NQsFLVdva18RcGNBQklMem1vbkkXDBAuKmMZLV8pYmgRAzcAFhpCKSIjKklvWEBQeW1KYhNtYnVUPidIaAwCPkcpOwcnDBg1N20rN0ciBTRDNCYPTBoYNT0OOx0rKxQ2NWVDYnI4Njp2MTEFBwdCCTkuOgxqGQQuNh4PLl9tf3VXMS8SB0kJNClFRA8xFhIuMCIEYnI4Njp2MTEFBwdCKTkuPB0FDQU1DiweJ0Fla18RcGNBCw9MGzg7IS4lChU/N2M5NlI5J3tQJTcONQgYPz9vOgEhFlEoPDkfMF1tJztVWmNBQkktLzkgCQg2HBQ0dx4eI0cobDREJCw2Ax0JKG1ybh02DRRQeW1KYmY5KzlCfi8ODRlEPDghLR0tFx9ycG0YJ0c4MDsRETYVDS4NKCkqIEcXDBAuPGMdI0coMBxfJCYTFAgAeighKkVOWFF6eW1KYhMrNztSJCoODEFFej8qOhw2FlEbLDkFBVI/JjBffhAVAx0JdCw6OgYTGQU/K20PLFdhYjNEPiAVCwYCcmRFbklkWFF6eW1KYhNtEDBcPzcEEUcFNDsgJQxsWiY7LSgYBVI/JjBfI2FIaElMem1vbklkHR8+cEcPLFdHJCBfMzcIDQdMGzg7IS4lChU/N2MZNlw9AyBFPxQAFgwecmRvDxwwFzY7KykPLB0eNjRFNW0AFx0DDSw7KxtkRVE8OCEZJxMoLDE7Wm5MQov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6Ht3dG1dbBMMFwF+cBApLTlMuM3bbgsxAQJ6LiULNlY7JycWI2MAFAgFNiwtIgxkFx96OG0JLV0rKzJEIiIDDgxMMyM7KxsyGR1QdGBKoKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxaAUDOSwjbigxDB4JMSIaYg5tOXViJCIVB0lRejZFbklkWAI/PCkkI14oMXURcH5BGRRAeiw6OgYXHRQ+Km1XYlUsLiZUfElBQklMPSguPCclFRQpeW1KfxM2P3kRMTYVDS4JOz9vblRkHhA2KihGSBNtYnVUNyQvAwQJKW1vbkl5WAondW0LN0ciBzJWI2NBX0kKOyE8K0VOWFF6eS4FMV4oNjxSI2NBQlRMPCwjPQxoclF6eW0DLEcoMCNQPGNBQklRenhhfkVOWFF6eSgcJ105ET1eIGNBQlRMPCwjPQxoclF6eW0EK1QlNnURcGNBQklReisuIhohVHt6eW1KNkEsNDBdOS0GQklMZ20pLwU3HV1QJDBgSFU4LDZFOSwPQigZLiIcJgY0VgIuOD8eahpHYnURcCoHQigZLiIcJgY0Vi4oLCMEK10qYiFZNS1BEAwYLz8hbgwqHHt6eW1KA0Y5LQZZPzNPPRsZNCMmIA5kRVEuKzgPSBNtYnVkJCoNEUcANSI/Zg8xFhIuMCIEahptMDBFJTEPQigZLiIcJgY0ViIuODkPbFojNjBDJiINQgwCPmFFbklkWFF6eW0MN10uNjxePmtIQhsJLjg9IEkFDQU1CiUFMh0SMCBfPioPBUkJNCljbg8xFhIuMCIEahpHYnURcGNBQklMem1vIgYnGR16Km1XYnI4NjpiOCwRTDoYOzkqRElkWFF6eW1KYhNtYjxXcDBPAxwYNR4qKw03WAUyPCNgYhNtYnURcGNBQklMem1vbg8rClEFdW0EYlojYjxBMSoTEUEfdD4qKw0KGRw/KmRKJlxHYnURcGNBQklMem1vbklkWFF6eW04J14iNjBCfiUIEAxEeA86NzohHRV4dW0EazltYnURcGNBQklMem1vbklkWFF6eR4eI0c+bDdeJSQJFklReh47Lx03VhM1LCoCNhNmYmQ7cGNBQklMem1vbklkWFF6eW1KYhM5IyZafjQACx1EamN+Z2NkWFF6eW1KYhNtYnURcGNBBwcIUG1vbklkWFF6eW1KYlYjJl8RcGNBQklMem1vbkktHlEpdywfNlwKJzRDcDcJBwdmem1vbklkWFF6eW1KYhNtYjNeImM+TkkCeiQhbgA0GRgoKmUZbFQoIyd/MS4EEUBMPiJFbklkWFF6eW1KYhNtYnURcGNBQkk+PyAgOgw3VhczKyhCYHE4OxJUMTFDTkkCc0dvbklkWFF6eW1KYhNtYnURcGNBQjoYOzk8YAsrDRYyLW1XYmA5IyFCfiEOFw4ELm1kblhOWFF6eW1KYhNtYnURcGNBQklMem07LxovVgY7MDlCch18a18RcGNBQklMem1vbklkWFF6PCMOSBNtYnURcGNBQklMeighKmNkWFF6eW1KYhNtYnVYNmMSTAgZLiIKKQ43WAUyPCNgYhNtYnURcGNBQklMem1vbg8rClEFdW0EYlojYjxBMSoTEUEfdCgoKSclFRQpcG0OLTltYnURcGNBQklMem1vbklkWFF6eR8PL1w5JyYfNioTB0FOGDg2HgwwPRY9e2FKLBpHYnURcGNBQklMem1vbklkWFF6eW05NlI5MXtTPzYGCh1MZ20cOggwC184NjgNKkdtaXUAWmNBQklMem1vbklkWFF6eW1KYhNtNjRCO20WAwAYcn1hf0BOWFF6eW1KYhNtYnURcGNBQgwCPkdvbklkWFF6eW1KYhMoLDE7cGNBQklMem1vbklkERd6KmMPNFYjNgZZPzNBQkkYMighbjshFR4uPD5EJFo/J30TEjYYJx8JNDkcJgY0WlhheR8PL1w5JyYfNioTB0FOGDg2Cwg3DBQoCjkFIVhva3VUPidrQklMem1vbklkWFF6MCtKMR0jKzJZJGNBQklMem07JgwqWCM/NCIeJ0BjJDxDNWtDIBwVFCQoJh0BDhQ0LR4CLUNva3VUPidrQklMem1vbklkWFF6MCtKMR05MDRHNS8IDA5Mem07JgwqWCM/NCIeJ0BjJDxDNWtDIBwVDj8uOAwoER89e2RKJ10pSHURcGNBQklMPyMrZ2MhFhVQPzgEIUckLTsRETYVDToENT1hPR0rCFlzeQwfNlweKjpBfhwTFwcCMyMoblRkHhA2KihKJ10pSF8cfWOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/lOVVx6YWNKA2YZDXVhFRcyaERBeq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPyUcGLVAsLnVwJTcOMgwYKW1ybhJkKwU7LShKfxM2SHURcGMAFx0DCSgjIjkhDAJ6ZG0MI18+J3kRIyYNDjkJLgQhOgw2DhA2eXBKcQNhSHURcGMSBwUACig7AwAqORY/eXBKcx9tb3gRIyYNDkkcPzk8bhArDR89PD9KNlssLHVFOCoSaBQRUEcpOwcnDBg1N20rN0ciEjBFI20SBwUAGyEjZkBOWFF6eR8PL1w5JyYfNioTB0FOCSgjIigoFCE/LT5IazkoLDE7WiUUDAoYMyIhbigxDB4KPDkZbEA5IydFeGprQklMeiQpbigxDB4KPDkZbGw/NztfOS0GQh0EPyNvPAwwDQM0eSgEJjltYnURETYVDTkJLj5hERsxFh8zNypKfxM5MCBUWmNBQkk5LiQjPUcoFx4qcSsfLFA5KzpfeGpBEAwYLz8hbigxDB4KPDkZbGA5IyFUfjAEDgU8PzkGIB0hCgc7NW0PLFdhSHURcGNBQklMPDghLR0tFx9ycG0YJ0c4MDsRETYVDTkJLj5hERsxFh8zNypKJ10pbnVXJS0CFgADNGVmRElkWFF6eW1KYhNtYjxXcAIUFgY8Pzk8YDowGQU/dywfNlweJzldACYVEUkYMighRElkWFF6eW1KYhNtYnURcGNMT0k/Pz85KxtpCxg+PG0OJ1AkJjBCa2MWB0kGLz47bg8tChR6LSUPYkAoLjkcMS8NQgAKejg8KxtkDxA0LT5KIEYhKV8RcGNBQklMem1vbklkWFF6CygHLUcoMXtXOTEESks/PyEjDwUoKBQuKm9DSBNtYnURcGNBQklMeighKmNkWFF6eW1KYlYjJnw7NS0FaA8ZNC47JwYqWDAvLSI6J0c+bCZFPzNJS0ktLzkgHgwwC18FKzgELFojJXUMcCUADhoJeighKmNOVVx6GiIOJ0BHJCBfMzcIDQdMGzg7ITkhDAJ0KygOJ1YgATpVNTBJDAYYMys2Z2NkWFF6PyIYYmxhYjZeNCZBCwdMMz0uJxs3UDI1NysDJR0ODRF0A2pBBgZmem1vbklkWFEIPCAFNlY+bDNYIiZJQCoAOyQiLwsoHTI1PShIbhMuLTFUeUlBQklMem1vbgAiWB81LSQMOxM5KjBfcC0OFgAKI2VtDQYgHVN2eW8+MFooJm8RcmNPTEkPNSkqZ0khFhVQeW1KYhNtYnVFMTAKTB4NMzlnfkdwUXt6eW1KJ10pSDBfNElrT0RMuNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKU2BHYgpjYhh+BgYsJyc4UGBibovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0jkhLTZQPGMsDR8JNyghOkl5WAp6CjkLNlZtf3VKWmNBQkkbOyEkHRkhHRV6ZG1Ych9tKCBcIBMOFQweenBve1loWBg0PwcfL0Ntf3VXMS8SB0VMNCIsIgA0WEx6PywGMVZhSHURcGMHDhBMZ20pLwU3HV16PyETEUMoJzERbWNZUkVMOyM7JygCM1FneTkYN1ZhYj1YJCEOGklRen9jRElkWFEpODsPJmMiMXUMcC0IDkVmJ2FvEQorFh96ZG0RPxMwSF9dPyAADkkKLyMsOgArFlE7KT0GO3s4LzRfPyoFSkBmem1vbgUrGxA2eRJGYmxhYj1EPWNcQjwYMyE8YA4hDDIyOD9CawhtKzMRPiwVQgEZN207JgwqWAM/LTgYLBMoLDE7cGNBQgEZN2MYLwUvKwE/PClKfxMALSNUPSYPFkc/Liw7K0czGR0xCj0PJ1dHYnURcDMCAwUAcis6IAowER40cWRKKkYgbB9EPTMxDR4JKG1ybiQrDhQ3PCMebGA5IyFUfikUDxk8NToqPEkhFhVzU21KYhM9ITRdPGsHFwcPLiQgIEFtWBkvNGM/MVYHNzhBACwWBxtMZ207PBwhWBQ0PWRgJ10pSDNEPiAVCwYCegAgOAwpHR8udz4PNmQsLj5iICYEBkEac20CIR8hFRQ0LWM5NlI5J3tGMS8KMRkJPylvc0kwFx8vNC8PMBs7a3VeImNTUlJMOz0/IhAMDRw7NyIDJhtkYjBfNEkHFwcPLiQgIEkJFwc/NCgENh0+JyF7JS4RMgYbPz9nOEBkNR4sPCAPLEdjESFQJCZPCBwBKh0gOQw2WEx6LSIEN14vJycZJmpBDRtMb310bgg0CB0jETgHI10iKzEZeWMEDA1mPDghLR0tFx96FCIcJ14oLCEfIyYVKgAYOCI3Zh9tclF6eW0nLUUoLzBfJG0yFggYP2MnJx0mFwl6ZG0eLV04LzdUImsXS0kDKG19RElkWFE2Ni4LLhMSbnVZIjNBX0k5LiQjPUcjHQUZMSwYahpHYnURcCoHQgEeKm07JgwqWBkoKWM5K0koYmgRBiYCFgYeaWMhKx5sDl16L2FKNBptJztVWiYPBmMKLyMsOgArFlEXNjsPL1YjNntCNTcoDA8mLyA/Zh9tclF6eW0nLUUoLzBfJG0yFggYP2MmIA8ODRwqeXBKNDltYnUROSVBFEkNNClvIAYwWDw1LygHJ105bApSPy0PTAACPAc6IxlkDBk/N0dKYhNtYnURcA4OFAwBPyM7YDYnFx80dyQEJHk4LyURbWM0EQweEyM/Ox0XHQMsMC4PbHk4LyVjNTIUBxoYYA4gIAchGwVyPzgEIUckLTsZeUlBQklMem1vbklkWFEzP20ELUdtDzpHNS4EDB1CCTkuOgxqER88EzgHMhM5KjBfcDEEFhweNG0qIA1OWFF6eW1KYhNtYnURPCwCAwVMBWFvEUVkEAQ3eXBKF0ckLiYfNyYVIQENKGVmRElkWFF6eW1KYhNtYjxXcCsUD0kYMighbgExFUsZMSwEJVYeNjRFNWskDBwBdAU6IwgqFxg+CjkLNlYZOyVUfgkUDxkFNCpmbgwqHHt6eW1KYhNtYjBfNGprQklMeigjPQwtHlE0NjlKNBMsLDERHSwXBwQJNDlhEQorFh90MCMMCEYgMnVFOCYPaElMem1vbklkNR4sPCAPLEdjHTZePi1PCwcKEDgiPlMAEQI5NiMEJ1A5anwKcA4OFAwBPyM7YDYnFx80dyQEJHk4LyURbWMPCwVmem1vbgwqHHs/NylgJEYjISFYPy1BLwYaPyAqIB1qCxQuFyIJLlo9aiMYWmNBQkkhNTsqIwwqDF8JLSweJx0jLTZdOTNBX0kaUG1vbkktHlEseSwEJhMjLSERHSwXBwQJNDlhEQorFh90NyIJLlo9YiFZNS1rQklMem1vbkkJFwc/NCgENh0SITpfPm0PDQoAMz1vc0kWDR8JPD8cK1AobAZFNTMRBw1WGSIhIAwnDFk8LCMJNloiLH0YWmNBQklMem1vbklkWBg8eSMFNhMALSNUPSYPFkc/Liw7K0cqFxI2MD1KNlsoLHVDNTcUEAdMPyMrRElkWFF6eW1KYhNtYjleMyINQgoEOz9vc0kIFxI7NR0GI0ooMHtyOCITAwoYPz90bgAiWB81LW0JKlI/YiFZNS1BEAwYLz8hbgwqHHt6eW1KYhNtYnURcGMHDRtMBWFvPkktFlEzKSwDMEBlIT1QInkmBx0oPz4sKwcgGR8uKmVDaxMpLV8RcGNBQklMem1vbklkWFF6MCtKMgkEMRQZcgEAEQw8Oz87bEBkGR8+eT1EAVIjATpdPCoFB0kYMighbhlqOxA0GiIGLlopJ3UMcCUADhoJeighKmNkWFF6eW1KYhNtYnVUPidrQklMem1vbkkhFhVzU21KYhMoLiZUOSVBDAYYejtvLwcgWDw1LygHJ105bApSPy0PTAcDOSEmPkkwEBQ0U21KYhNtYnURHSwXBwQJNDlhEQorFh90NyIJLlo9eBFYIyAODAcJOTlnZ1JkNR4sPCAPLEdjHTZePi1PDAYPNiQ/blRkFhg2U21KYhMoLDE7NS0FaAUDOSwjbg8xFhIuMCIEYkA5IydFFi8YSkBmem1vbgUrGxA2eRJGYls/MnkRODYMQlRMDzkmIhpqHxQuGiULMBtkeXVYNmMPDR1MMj8/bgY2WB81LW0CN15tNj1UPmMTBx0ZKCNvKwcgclF6eW0GLVAsLnVTJmNcQiACKTkuIAohVh8/LmVIAFwpOwNUPCwCCx0VeGR0bgsyVjw7IQsFMFAoYmgRBiYCFgYeaWMhKx5sSRRjdXwPex98J2wYa2MDFEc6PyEgLQAwAVFneRsPIUciMGYfPiYWSkBXei85YDklChQ0LW1XYls/Ml8RcGNBDgYPOyFvLA5kRVETNz4eI10uJ3tfNTRJQCsDPjQINxsrWlhheS8NbH4sOgFeIjIUB0lRehsqLR0rCkJ0NygdagIoe3kANXpNUwxVc3ZvLA5qKFFneXwPdghtIDIfACITBwcYenBvJhs0clF6eW0nLUUoLzBfJG0+AQYCNGMpIhAGLl16FCIcJ14oLCEfDyAODAdCPCE2DC5kRVE4L2FKIFRHYnURcCsUD0c8Niw7KAY2FSIuOCMOYg5tNidENUlBQklMFyI5KwQhFgV0Bi4FLF1jJDlIBTMFAx0JenBvHBwqKxQoLyQJJx0fJztVNTEyFgwcKigrdCorFh8/OjlCJEYjISFYPy1JS2NMem1vbklkWBg8eSMFNhMALSNUPSYPFkc/Liw7K0ciFAh6LSUPLBM/JyFEIi1BBwcIUG1vbklkWFF6NSIJI19tITRccH5BFQYeMT4/LwohVjIvKz8PLEcOIzhUIiJrQklMem1vbkkoFxI7NW0HYg5tFDBSJCwTUUcCPzpnZ2NkWFF6eW1KYlorYgBCNTEoDBkZLh4qPB8tGxRgED4hJ0oJLSJfeAYPFwRCESg2DQYgHV8NcG1KYhNtYnURcDcJBwdMN21ybgRkU1E5OCBEAXU/IzhUfg8ODQI6Py47IRtkHR8+U21KYhNtYnUROSVBNxoJKAQhPhwwKxQoLyQJJwkEMR5UKQcOFQdEHyM6I0cPHQgZNikPbGBkYnURcGNBQklMLiUqIEkpWEx6NG1HYlAsL3tyFjEADwxCFiIgJT8hGwU1K20PLFdHYnURcGNBQkkFPG0aPQw2MR8qLDk5J0E7KzZUagoSKQwVHiI4IEEBFgQ3dwYPO3AiJjAfEWpBQklMem1vbkkwEBQ0eSBKfxMgYngRMyIMTCoqKCwiK0cWERYyLRsPIUciMHVUPidrQklMem1vbkktHlEPKigYC109NyFiNTEXCwoJYAQ8BQw9PB4tN2UvLEYgbB5UKQAOBgxCHmRvbklkWFF6eW0eKlYjYjgRbWMMQkJMOSwiYCoCChA3PGM4K1QlNgNUMzcOEEkJNClFbklkWFF6eW0DJBMYMTBDGS0RFx0/Pz85JwohQjgpEigTBlw6LH10PjYMTCIJIw4gKgxqKwE7OihDYhNtYnVFOCYPQgRMZ20ibkJkLhQ5LSIYcR0jJyIZYG9BU0VMamRvKwcgclF6eW1KYhNtKzMRBTAEECACKjg7HQw2Dhg5PHcjMXgoOxFeJy1JJwcZN2MEKxAHFxU/dwEPJEceKjxXJGpBFgEJNG0iblRkFVF3eRsPIUciMGYfPiYWSllAenxjblltWBQ0PUdKYhNtYnURcCoHQgRCFywoIAAwDRU/eXNKchM5KjBfcC5BX0kBdBghJx1kUlEXNjsPL1YjNntiJCIVB0cKNjQcPgwhHFE/NylgYhNtYnURcGMDFEc6PyEgLQAwAVFneSBgYhNtYnURcGMDBUcvHD8uIwxkRVE5OCBEAXU/IzhUWmNBQkkJNClmRAwqHHs2Ni4LLhMrNztSJCoODEkfLiI/CAU9UFhQeW1KYlUiMHVufGMKQgACeiQ/LwA2C1kheysGO2Y9JjRFNWFNQA8AIw8ZbEVmHh0jGwpIPxptJjo7cGNBQklMem0jIQolFFE5eXBKD1w7JzhUPjdPPQoDNCMUJTROWFF6eW1KYhMkJHVScDcJBwdmem1vbklkWFF6eW1KK1VtNixBNSwHSgpFenBybksWOikJOj8DMkcOLTtfNSAVCwYCeG07JgwqWBJgHSQZIVwjLDBSJGtIQgwAKShvLVMAHQIuKyITahptJztVWmNBQklMem1vbklkWDw1LygHJ105bApSPy0POQIxenBvIAAoclF6eW1KYhNtJztVWmNBQkkJNClFbklkWB01OiwGYmxhYgodcCsUD0lRehg7JwU3VhY/LQ4CI0Fla18RcGNBCw9MMjgibh0sHR96MTgHbGMhIyFXPzEMMR0NNClvc0kiGR0pPG0PLFdHJztVWiUUDAoYMyIhbiQrDhQ3PCMebEAoNhNdKWsXS0khNTsqIwwqDF8JLSweJx0rLiwRbWMXWUkFPG05bh0sHR96KjkLMEcLLiwZeWMEDhoJej47IRkCFAhycG0PLFdtJztVWiUUDAoYMyIhbiQrDhQ3PCMebEAoNhNdKRARBwwIcjtmbiQrDhQ3PCMebGA5IyFUfiUNGzocPygrblRkDB40LCAIJ0FlNHwRPzFBWllMPyMrRA8xFhIuMCIEYn4iNDBcNS0VTBoJLgwhOgAFPjpyL2RgYhNtYhheJiYMBwcYdB47Lx0hVhA0LSQrBHhtf3VHWmNBQkkFPG05bggqHFE0NjlKD1w7JzhUPjdPPQoDNCNhLwcwETAcEm0eKlYjSHURcGNBQklMFyI5KwQhFgV0Bi4FLF1jIztFOQInKUlRegEgLQgoKB07ICgYbHopLjBVagAODAcJOTlnKBwqGwUzNiNCazltYnURcGNBQklMem0mKEkqFwV6FCIcJ14oLCEfAzcAFgxCOyM7JygCM1EuMSgEYkEoNiBDPmMEDA1mem1vbklkWFF6eW1KMlAsLjkZNjYPAR0FNSNnZ0kSEQMuLCwGF0AoMG9yMTMVFxsJGSIhOhsrFB0/K2VDeRMbKydFJSINNxoJKHcMIgAnEzMvLTkFLAFlFDBSJCwTUEcCPzpnZ0BkHR8+cEdKYhNtYnURcCYPBkBmem1vbgwoCxQzP20ELUdtNHVQPidBLwYaPyAqIB1qJxI1NyNEI105KxR3G2MVCgwCUG1vbklkWFF6FCIcJ14oLCEfDyAODAdCOyM7JygCM0seMD4JLV0jJzZFeGpaQiQDLCgiKwcwVi45NiMEbFIjNjxwFghBX0kCMyFFbklkWBQ0PUcPLFdHJCBfMzcIDQdMFyI5KwQhFgV0KiwcJ2MiMX0YWmNBQkkANS4uIkkbVFEyKz1KfxMYNjxdI20GBx0vMiw9ZkB/WBg8eSUYMhM5KjBfcA4OFAwBPyM7YDowGQU/dz4LNFYpEjpCcH5BChscdB0gPQAwER40Ym0YJ0c4MDsRJDEUB0kJNClFKwcgchcvNy4eK1wjYhheJiYMBwcYdD8qLQgoFCE1KmVDSBNtYnVYNmMsDR8JNyghOkcXDBAuPGMZI0UoJgVeI2MVCgwCehg7JwU3VgU/NSgaLUE5ahheJiYMBwcYdB47Lx0hVgI7LygOElw+a24RIiYVFxsCejk9OwxkHR8+UygEJjkBLTZQPBMNAxAJKGMMJgg2GRIuPD8rJlcoJm9yPy0PBwoYcis6IAowER40cWRgYhNtYiFQIyhPFQgFLmV/YF9tQ1E7KT0GO3s4LzRfPyoFSkBmem1vbgAiWDw1LygHJ105bAZFMTcETA8AI207JgwqWAIuOD8eBF80anwRNS0FaElMem0mKEkJFwc/NCgENh0eNjRFNW0JCx0ONTVvMFRkSlEuMSgEYn4iNDBcNS0VTBoJLgUmOgsrAFkXNjsPL1YjNntiJCIVB0cEMzktIRFtWBQ0PUcPLFdkSF8cfWOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/lOVVx6aH1EYmcIDhBhHxE1MWNBd22t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN1gLlwuIzkRBCYNBxkDKDk8blRkAwxQNSIJI19tJCBfMzcIDQdMPCQhKicUO1k0OCAPazltYnURPCwCAwVMND0sPUl5WCY1KyYZMlIuJ293OS0FJAAeKTkMJgAoHFl4Fx0pERFkSHURcGMIBEkCNTlvIBknC1EuMSgEYkEoNiBDPmMPCwVMPyMrRElkWFE0OCAPYg5tLDRcNXkNDR4JKGVmRElkWFE8Nj9KHR9tLHVYPmMIEggFKD5nIBknC0sdPDkpKlohJidUPmtIS0kINUdvbklkWFF6eSQMYl1jDDRcNXkNDR4JKGVmdA8tFhVyNywHJx9tc3kRJDEUB0BMLiUqIGNkWFF6eW1KYhNtYnVYNmMPWCAfG2VtAwYgHR14cG0eKlYjSHURcGNBQklMem1vbklkWFEzP20EbGM/KzhQIjoxAxsYejknKwdkChQuLD8EYl1jEidYPSITGzkNKDlhHgY3EQUzNiNKJ10pSHURcGNBQklMem1vbklkWFE2Ni4LLhM9YmgRPnknCwcIHCQ9PR0HEBg2PRoCK1AlCyZweGEjAxoJCiw9OktoWAUoLChDSBNtYnURcGNBQklMem1vbkktHlEqeTkCJ11tMDBFJTEPQhlCCiI8Jx0tFx96PCMOSBNtYnURcGNBQklMeigjPQwtHlE0YwQZAxtvADRCNRMAEB1Oc207JgwqclF6eW1KYhNtYnURcGNBQkkePzk6PAdkFl8KNj4DNloiLF8RcGNBQklMem1vbkkhFhVQeW1KYhNtYnVUPidrQklMeighKmMhFhVQNSIJI19tJCBfMzcIDQdMPCQhKj4rCh0+cSMLL1ZkSHURcGMPAwQJenBvIAgpHUs2NjoPMBtkSHURcGMHDRtMBWFvKkktFlEzKSwDMEBlFTpDOzARAwoJYAoqOi0hCxI/NykLLEc+anwYcCcOaElMem1vbklkERd6PWMkI14oeDleJyYTSkBWPCQhKkEqGRw/dW1bbhM5MCBUeWMVCgwCUG1vbklkWFF6eW1KYlorYjELGTAgSksuOz4qHgg2DFNzeTkCJ11tMDBFJTEPQg1CCiI8Jx0tFx96PCMOSBNtYnURcGNBQklMeiQpbg1+MQIbcW8nLVcoLncYcCIPBkkIdB09JwQlCggKOD8eYkclJzsRIiYVFxsCeilhHhstFRAoIB0LMEdjEjpCOTcIDQdMPyMrRElkWFF6eW1KJ10pSHURcGMEDA1mPyMrRA8xFhIuMCIEYmcoLjBBPzEVEUcAMz47ZkBOWFF6eT8PNkY/LHVKWmNBQklMem1vNUkqGRw/eXBKYH40YjNQIi5BShocOzohZ0toWFF6PigeYg5tJCBfMzcIDQdEc209Kx0xCh96HywYLx0qJyFiICIWDDkDKWVmbgwqHFEndUdKYhNtYnURcDhBDAgBP21ybksJAVE8OD8HYhsuJztFNTFIQEVMeioqOkl5WBcvNy4eK1wjanwRIiYVFxsCegsuPARqHxQuGigENlY/anwRNS0FQhRAUG1vbklkWFF6Im0EI14oYmgRchAEBw1MKSUgPkkKKDJ4dW1KYhNtJTBFcH5BBBwCOTkmIQdsUVEoPDkfMF1tJDxfNA0xIUFOKSgqKkttWB4oeSsDLFcDEhYZcjAAD0tFeighKkk5VHt6eW1KYhNtYi4RPiIMB0lRem8IKwg2WAIyNj1KDGMOYHkRcGNBQg4JLm1ybg8xFhIuMCIEahptMDBFJTEPQg8FNCkBHipsWhY/OD9IaxMiMHVXOS0FLDkvcm87IQRmUVE/NylKPx9HYnURcGNBQkkXeiMuIwxkRVF4CSgeYlYqJXVCOCwRQEVMem1vbkkjHQV6ZG0MN10uNjxePmtIQhsJLjg9IEkiER8+Fx0pahEoJTITeWMOEEkKMyMrADkHUFMqPDlIaxMoLDERLW9rQklMem1vbkk/WB87NChKfxNvATpCPSYVCwpMKSUgPktoWFF6eW0NJ0dtf3VXJS0CFgADNGVmbhshDAQoN20MK10pDAVyeGECDRoBPzkmLUttWBQ0PW0XbjltYnURcGNBQhJMNCwiK0l5WFMJPCEGYkkiLDATfGNBQklMem1vbg4hDFFneSsfLFA5KzpfeGpBEAwYLz8hbg8tFhUNNj8GJhtvMTBdPGFIQgwCPm0yYmNkWFF6eW1KYkhtLDRcNWNcQks4KCw5KwUtFhZ6NCgYIVssLCETfCQEFklReis6IAowER40cWRKMFY5NydfcCUIDA0iCg5nbB02GQc/NSQEJRFkYjpDcCUIDA0iCg5nbAQhChIyOCMeYBptJztVcD5NaElMem1vbklkA1E0OCAPYg5tYBhQOS8DDRFOdm1vbklkWFF6eW1KJVY5YmgRNjYPAR0FNSNnZ2NkWFF6eW1KYhNtYnVdPyAADkkKenBvCAg2FV8oPD4FLkUoanwKcCoHQg9MLiUqIGNkWFF6eW1KYhNtYnURcGNBDgYPOyFvI0l5WBdgHyQEJnUkMCZFEysIDg1EeAAuJwUmFwl4cEdKYhNtYnURcGNBQklMem1vJw9kFVE7NylKLx0dMDxcMTEYMggeLm07JgwqWAM/LTgYLBMgbAVDOS4AEBA8Oz87YDkrCxguMCIEYlYjJl8RcGNBQklMem1vbklkWFF6MCtKLxM5KjBfcC8OAQgAej1vc0kpQjczNyksK0E+NhZZOS8FNQEFOSUGPShsWjM7Kig6I0E5YHkRJDEUB0BXeiQpbhlkDBk/N20YJ0c4MDsRIG0xDRoFLiQgIEkhFhV6PCMOSBNtYnURcGNBQklMeighKmNkWFF6eW1KYlYjJnVMfElBQklMem1vbhJkFhA3PG1XYhEKIydVNS1BIQYFNG0cJgY0Wl16eSoPNhNwYjNEPiAVCwYCcmRvPAwwDQM0eSsDLFcaLSddNGtDJQgePighDQYtFlNzeSgEJhMwbl8RcGNBQklMejZvIAgpHVFneW85J1A/JyERHyEDG0kJNDk9N0toWBY/LW1XYlU4LDZFOSwPSkBMKCg7OxsqWBczNyk9LUEhJn0TAyYCEAwYFS8tN0ttWBQ0PW0XbjltYnURLUkEDA1mPDghLR0tFx96DSgGJ0MiMCFCfiQOSgcNNyhmRElkWFE8Nj9KHR9tJ3VYPmMIEggFKD5nGgwoHQE1KzkZbF8kMSEZeWpBBgZmem1vbklkWFEzP20PbF0sLzARbX5BDAgBP207JgwqclF6eW1KYhNtYnURcC8OAQgAej1vc0khVhY/LWVDSBNtYnURcGNBQklMeiQpbhlkDBk/N20/NlohMXtFNS8EEgYeLmU/bkJkLhQ5LSIYcR0jJyIZYG9BVkVMamRmdUk2HQUvKyNKNkE4J3VUPidrQklMem1vbkkhFhVQeW1KYlYjJl8RcGNBEAwYLz8hbg8lFAI/UygEJjlHb3gRstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfrPzUmuTKu9j6oKbdoMChstbxgPz8uNjfRERpWEBrd208C2AYAxliWm5MQov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6Hs2Ni4LLhMbKyZEMS8SQlRMIW0cOggwHVFneTZKJEYhLjdDOSQJFklReisuIhohVFE0NgsFJRNwYjNQPDAEQhRAehItLwovDQF6ZG0RPxMwSDleMyINQg8ZNC47JwYqWBM7OiYfMn8kJT1FOS0GSkBmem1vbgAiWB8/ITlCFFo+NzRdI20+AAgPMTg/Z0kwEBQ0eT8PNkY/LHVUPidrQklMehsmPRwlFAJ0Bi8LIVg4MntzIioGCh0CPz48bklkWEx6FSQNKkckLDIfEjEIBQEYNCg8PWNkWFF6DyQZN1IhMXtuMiICCRwcdA4jIQovLBg3PG1KYhNtf3V9OSQJFgACPWMMIgYnEyUzNChgYhNtYgNYIzYADhpCBS8uLQIxCF8dNSIII18eKjRVPzQSQlRMFiQoJh0tFhZ0HiEFIFIhET1QNCwWEWNMem1vGAA3DRA2KmM1IFIuKSBBfgUOBSwCPm1vbklkWFF6ZG0mK1QlNjxfN20nDQ4pNClFbklkWCczKjgLLkBjHTdQMygUEkcqNSocOgg2DFF6eW1KYg5tDjxWODcIDA5CHCIoHR0lCgVQPCMOSFU4LDZFOSwPQj8FKTguIhpqCxQuHzgGLlE/KzJZJGsXS2NMem1vGAA3DRA2KmM5NlI5J3tXJS8NABsFPSU7blRkDkp6OywJKUY9DjxWODcIDA5Ec0dvbklkERd6L20eKlYjYhlYNysVCwcLdA89Jw4sDB8/Kj5KfxN+eXV9OSQJFgACPWMMIgYnEyUzNChKfxN8dm4RHCoGCh0FNCphCQUrGhA2CiULJlw6MXUMcCUADhoJUG1vbkkhFAI/U21KYhNtYnURHCoGCh0FNCphDBstHxkuNygZMRNwYgNYIzYADhpCBS8uLQIxCF8YKyQNKkcjJyZCcCwTQlhmem1vbklkWFEWMCoCNlojJXtyPCwCCT0FNyhvblRkLhgpLCwGMR0SIDRSOzYRTCoANS4kGgApHVE1K21bdjltYnURcGNBQiUFPSU7JwcjVjY2Ni8LLmAlIzFeJzBBX0k6Mz46LwU3Vi44OC4BN0NjBTleMiINMQENPiI4PUk6RVE8OCEZJzltYnURNS0FaAwCPkcpOwcnDBg1N208K0A4IzlCfjAEFicDHCIoZh9tclF6eW08K0A4IzlCfhAVAx0JdCMgCAYjWEx6L3ZKIFIuKSBBHCoGCh0FNCpnZ2NkWFF6MCtKNBM5KjBfcA8IBQEYMyMoYC8rHzQ0PW1XYgIodG4RHCoGCh0FNCphCAYjKwU7KzlKfxN8J2M7cGNBQgwAKShvAgAjEAUzNypEBFwqBztVcH5BNAAfLywjPUcbGhA5MjgabHUiJRBfNGMOEEldan1/dUkIERYyLSQEJR0LLTJiJCITFklRehsmPRwlFAJ0Bi8LIVg4Mnt3PyQyFggeLm0gPEl0WBQ0PUcPLFdHSHgccKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3ovR6JPPya//0tHY0rekwKH08ov5yq/a3mNpVVFra2NKF3ptoNWlcC8OAw1MFS88Jw0tGR8PMG1CGwEGa3VQPidBABwFNilvOgEhWAYzNykFNTlgb3XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz92t2/mm7eG4zN2I16Ov18XTxdOD9/mOz91FPhstFgVycW8xGwEGH3V9PyIFCwcLegItPQAgERA0DCRKJFw/YnBCcG1PTEtFYCsgPAQlDFkZNiMMK1RjBRR8FRwvIyQpc2RFRAUrGxA2eQEDIEEsMCwdcBcJBwQJFywhLw4hCl16CiwcJ34sLDRWNTFrDgYPOyFvIQIRMVFneT0JI18hajNEPiAVCwYCcmRFbklkWD0zOz8LMEptYnURcGNcQgUDOyk8OhstFhZyPiwHJwkFNiFBFyYVSioDNCsmKUcRMS4IHB0lYh1jYnd9OSETAxsVdCE6L0ttUVlzU21KYhMZKjBcNQ4ADAgLPz9vc0koFxA+KjkYK10qajJQPSZbKh0YKgoqOkEHFx88MCpEF3oSEBBhH2NPTElOOykrIQc3VyUyPCAPD1IjIzJUIm0NFwhOc2RnZ2NkWFF6CiwcJ34sLDRWNTFBQlRMNiIuKhowChg0PmUNI14oeB1FJDMmBx1EGSIhKAAjViQTBh8vEnxtbHsRciIFBgYCKWIcLx8hNRA0OCoPMB0hNzQTeWpJS2MJNClmRAAiWB81LW0FKWYEYjpDcC0OFkkgMy89Lxs9WAUyPCNgYhNtYiJQIi1JQDI1aAZvBhwmJVEcOCQGJ1dtNjoRPCwABkkjOD4mKgAlFiQzd20rIFw/NjxfN21DS2NMem1vES5qIUMRBgorBWwFFxduHAwgJiwoenBvIAAoQ1EoPDkfMF1HJztVWkkNDQoNNm0APh0tFx8pdW0+LVQqLjBCcH5BLgAOKCw9N0cLCAUzNiMZbhMBKzdDMTEYTD0DPSojKxpONBg4KywYOx0LLSdSNQAJBwoHOCI3blRkHhA2KihgSF8iITRdcCUUDAoYMyIhbicrDBg8IGUeK0chJ3kRNCYSAUVMPz89Z2NkWFF6FSQIMFI/O29/PzcIBBBEIUdvbklkWFF6eRkDNl8oYnURcGNBQlRMPz89bggqHFFyewgYMFw/Yrex8mNDQkdCejkmOgUhUVE1K20eK0chJ3k7cGNBQklMem0LKxonChgqLSQFLBNwYjFUIyBBDRtMeG9jRElkWFF6eW1KFlogJ3URcGNBQklMZ217YmNkWFF6JGRgJ10pSF9dPyAADkk7MyMrIR5kRVEWMC8YI0E0eBZDNSIVBz4FNCkgOUE/clF6eW0+K0chJ3URcGNBQklMem1vblRkWjYoNjpKIxMKIydVNS1BQovs+G1vF1sPWDkvO21KNBFtbHsREywPBAALdB4MHCAULC4MHB9GSBNtYnV3PywVBxtMem1vbklkWFF6eXBKYGp/CXViMzEIEh1MGCwsJVsGGRIxeW2IwpFtYncRfm1BIQYCPCQoYC4FNTQFFwwnBx9HYnURcA0OFgAKIx4mKgxkWFF6eW1KfxNvEDxWODdDTmNMem1vHQErDzIvKjkFL3A4MCZeImNcQh0eLyhjRElkWFEZPCMeJ0FtYnURcGNBQklMenBvOhsxHV1QeW1KYnI4NjpiOCwWQklMem1vbklkRVEuKzgPbjltYnURAiYSCxMNOCEqbklkWFF6eW1XYkc/NzAdWmNBQkkvNT8hKxsWGRUzLD5KYhNtYmgRYXNNaBRFUEcjIQolFFEOOC8ZYg5tOV8RcGNBJQgePighbklkRVENMCMOLUR3AzFVBCIDSksrOz8rKwdmVFF6eW8ZI0UoYHwdWmNBQkk/MiI/bklkWFFneRoDLFciNW9wNCc1AwtEeB4nIRlmVFF6eW1KYEMsIT5QNyZDS0Vmem1vbjkhDAJ6eW1KYg5tFTxfNCwWWCgIPhkuLEFmKBQuKm9GYhNtYnUTOCYAEB1Oc2FFbklkWCE2ODQPMBNtYmgRByoPBgYbYAwrKj0lGll4CSELO1Y/YHkRcGNDFxoJKG9mYmNkWFF6FCQZIRNtYnURbWM2CwcINTp1Dw0gLBA4cW8nK0AuYHkRcGNBQksbKCghLQFmUV1QeW1KYnAiLDNYNzBBQlRMDSQhKgYzQjA+PRkLIBtvATpfNioGEUtAem1tKggwGRM7KihIax9HYnURcBAEFh0FNCo8blRkLxg0PSIdeHIpJgFQMmtDMQwYLiQhKRpmVFF4KigeNlojJSYTeW9rQklMeg49Kw0tDAJ6eXBKFVojJjpGagIFBj0NOGVtDRshHBguKm9GYhNvKztXP2FITmMRUEdiY0mm7PG4zc2I1rNtFhRzcHJBgOn4egoOHC0BNlG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PFQNSIJI19tBTFfBCEZLklRehkuLBpqPxAoPSgEeHIpJhlUNjc1AwsONTVnZ2MoFxI7NW0tJl0dLjRfJGNcQi4INBktNiV+ORU+DSwIahEMNyFecBMNAwcYeGRFIgYnGR16HikEClI/NDBCJGNcQi4INBktNiV+ORU+DSwIahEFIydHNTAVQkZMGSIjIgwnDFNzU0ctJl0dLjRfJHkgBg0gOy8qIkE/WCU/ITlKfxNvATpfJCoPFwYZKSE2bhkoGR8uKm0eKlZtMTBdNSAVBw1MKSgqKkklGwM1Kj5KO1w4MHVeJy0EBkkKOz8iYEtoWDU1PD49MFI9YmgRJDEUB0kRc0cIKgcUFBA0LXcrJlcJKyNYNCYTSkBmHSkhHgUlFgVgGCkOC109NyEZchMNAwcYCSgqKiclFRR4dW0RYmcoOiERbWNDMQwJPm0hLwQhWFk/ISwJNhpvbnV1NSUAFwUYenBvbColCgM1LW9GYmMhIzZUOCwNBgweenBvbColCgM1LWFKEUc/IyJTNTETG0VMdGNhbEVOWFF6eRkFLV85KyURbWNDNhAcP207JgxkCxQ/PW0EI14oYjRCcCoVQggcKiguPBpkER96ICIfMBMkLCNUPjcOEBBMcjomOgErDQV6Ah4PJ1cQa3sTfElBQklMGSwjIgslGxp6ZG0MN10uNjxePmsXS0ktLzkgCQg2HBQ0dx4eI0cobCVdMS0VMQwJPm1ybh9kHR8+eTBDSHI4Njp2MTEFBwdCCTkuOgxqCB07Nzk5J1YpYmgRcgAAEBsDLm9FRC4gFiE2OCMeeHIpJgFeNyQNB0FOGzg7ITkoGR8ue2FKORMZJy1FcH5BQCgZLiJvHgUlFgV6cSALMUcoMHwTfGMlBw8NLyE7blRkHhA2KihGSBNtYnVlPywNFgAcenBvbDo0ChQ7PT5KMVYoJiYRIiIPBgYBNjRvLwo2FwIpeTQFN0FtJDRDPWMRDgYYdG9jRElkWFEZOCEGIFIuKXUMcCUUDAoYMyIhZh9tWBg8eTtKNlsoLHVwJTcOJQgePighYBowGQMuGDgeLWMhIztFeGpBBwUfP20OOx0rPxAoPSgEbEA5LSVwJTcOMgUNNDlnZ0khFhV6PCMOYk5kSBJVPhMNAwcYYAwrKjooERU/K2VIEl8sLCF1NS8AG0tAejZvGgw8DFFneW86LlIjNnVYPjcEEB8NNm9jbi0hHhAvNTlKfxN9bGAdcA4IDElRen1hf0VkNRAieXBKdx9tEDpEPicIDA5MZ219YkkXDRc8MDVKfxNvYiYTfElBQklMDiIgIh0tCFFneW8+K14oYjdUJDQEBwdMPywsJkk0FBA0LWNIbjltYnUREyINDgsNOSZvc0kiDR85LSQFLBs7a3VwJTcOJQgePighYDowGQU/dz0GI105BjBdMTpBX0kaeighKkk5UXsdPSM6LlIjNm9wNCc1DQ4LNihnbCMtDAU/K29GYkhtFjBJJGNcQks+OyMrIQQtAhR6LSQHK10qMXcdcAcEBAgZNjlvc0kwCgQ/dUdKYhNtFjpePDcIEklRem8OKg03WLPraH9PYkEsLDFePS0EERpMKSJvOgEhWAE7LTkPMF1tKyZfdzdBEgwePCgsOgU9WAM1OyIeK1BjYHk7cGNBQioNNiEtLwovWEx6PzgEIUckLTsZJmpBIxwYNQouPA0hFl8JLSweJx0nKyFFNTFBX0kaeighKkk5UXtQHikEClI/NDBCJHkgBg0gOy8qIkE/WCU/ITlKfxNvAyBFP24JAxsaPz47bhstCBR6KSELLEc+YjRfNGMWAwUHeiI5KxtkHAM1KT0PJhMrMCBYJGMVDUkcMy4kbgAwWAQqd29GYnciJyZmIiIRQlRMLj86K0k5UXsdPSMiI0E7JyZFagIFBi0FLCQrKxtsUXsdPSMiI0E7JyZFagIFBj0DPSojK0FmOQQuNgULMEUoMSETfGMaQj0JIjlvc0lmOQQuNm0iI0E7JyZFcDMNAwcYKW9jbi0hHhAvNTlKfxMrIzlCNW9rQklMehkgIQUwEQF6ZG1IAVIhLiYRJCsEQgENKDsqPR1kChQ3NjkPYlwjYjBHNTEYQhkAOyM7bgYqWAg1LD9KJFI/L3sTfElBQklMGSwjIgslGxp6ZG0MN10uNjxePmsXS0kFPG05bh0sHR96GDgeLXQsMDFUPm0SFggeLgw6OgYMGQMsPD4eahptJzlCNWMgFx0DHSw9KgwqVgIuNj0rN0ciCjRDJiYSFkFFeighKkkhFhV6JGRgBVcjCjRDJiYSFlMtPikcIgAgHQNyewULMEUoMSF4PjcEEB8NNm9jbhJkLBQiLW1XYhEFIydHNTAVQgACLig9OAgoWl16HSgMI0YhNnUMcHBNQiQFNG1yblhoWDw7IW1XYgV9bnVjPzYPBgACPW1yblhoWCIvPysDOhNwYncRI2FNaElMem0MLwUoGhA5Mm1XYlU4LDZFOSwPSh9Fegw6OgYDGQM+PCNEEUcsNjAfOCITFAwfLgQhOgw2DhA2eXBKNBMoLDERLWprJQ0CEiw9OAw3DEsbPSkuK0UkJjBDeGprJQ0CEiw9OAw3DEsbPSk+LVQqLjAZcgIUFgYvNSEjKwowWl16Im0+J0s5YmgRcgIUFgZMDSwjJUQHFx02PC4eYkEkMjATfGMlBw8NLyE7blRkHhA2KihGSBNtYnVlPywNFgAcenBvbD4lFBopeSIcJ0FtJzRSOGMTCxkJeis9OwAwWAI1eSQeYlI4NjocICoCCRpMLz1hbEVOWFF6eQ4LLl8vIzZacH5BBBwCOTkmIQdsDlh6MCtKNBM5KjBfcAIUFgYrOz8rKwdqCwU7KzkrN0ciATpdPCYCFkFFeigjPQxkOQQuNgoLMFcoLHtCJCwRIxwYNQ4gIgUhGwVycG0PLFdtJztVcD5IaC4INAUuPB8hCwVgGCkOEV8kJjBDeGEiDQUAPy47BwcwHQMsOCFIbhM2YgFUKDdBX0lOGSIjIgwnDFEzNzkPMEUsLncdcAcEBAgZNjlvc0lwVFEXMCNKfxN8bnV8MTtBX0laamFvHAYxFhUzNypKfxN8bnViJSUHCxFMZ21tbhpmVHt6eW1KAVIhLjdQMyhBX0kKLyMsOgArFlkscG0rN0ciBTRDNCYPTDoYOzkqYAorFB0/OjkjLEcoMCNQPGNcQh9MPyMrbhRtcns2Ni4LLhMKJjtlMjszQlRMDiwtPUcDGQM+PCNQA1cpEDxWODc1AwsONTVnZ2MoFxI7NW0tJl0eJzldcH5BJQ0CDi83HFMFHBUOOC9CYGAoLjkRf2M2Ax0JKG9mRAUrGxA2eQoOLGA5IyFCcH5BJQ0CDi83HFMFHBUOOC9CYH8kNDARMywUDB0JKD5tZ2NOPxU0CigGLgkMJjF9MSEEDkEXehkqNh1kRVF4GDgeLR4+JzldI2MJBwUIeisgIQ1kGR8+eToLNlY/MXVQPC9BGwYZKG0/IggqDAJ6NiNKNlogJydCfmFNQi0DPz4YPAg0WEx6LT8fJxMwa192NC0yBwUAYAwrKi0tDhg+PD9CazkKJjtiNS8NWCgIPhkgKQ4oHVl4GDgeLWAoLjkTfGMaQj0JIjlvc0lmOQQuNm05J18hYjNePydDTkkoPysuOwUwWEx6PywGMVZhSHURcGM1DQYALiQ/blRkWjczKygZYkclJ3VCNS8NQhsJNyI7K0dkKwU7NylKLFYsMHVFOCZBMQwANm0BHipqWl1QeW1KYnAsLjlTMSAKQlRMPDghLR0tFx9yL2RKK1VtNHVFOCYPQigZLiIILxsgHR90KjkLMEcMNyFeAyYNDkFFeigjPQxkOQQuNgoLMFcoLHtCJCwRIxwYNR4qIgVsUVE/NylKJ10pYigYWgQFDDoJNiF1Dw0gKx0zPSgYahEeJzldGS0VBxsaOyFtYkk/WCU/ITlKfxNvETBdPGMIDB0JKDsuIktoWDU/PywfLkdtf3UCYG9BLwACenBve0VkNRAieXBKdAN9bnVjPzYPBgACPW1yblloWCIvPysDOhNwYncRI2FNaElMem0MLwUoGhA5Mm1XYlU4LDZFOSwPSh9Fegw6OgYDGQM+PCNEEUcsNjAfIyYNDiACLig9OAgoWEx6L20PLFdtP3w7FycPMQwANncOKg0AEQczPSgYahpHBTFfAyYNDlMtPikbIQ4jFBRyewwfNlwaIyFUImFNQhJMDig3Okl5WFMbLDkFYmQsNjBDcCQAEA0JND5tYkkAHRc7LCEeYg5tJDRdIyZNaElMem0bIQYoDBgqeXBKYHAsLjlCcDcJB0k7OzkqPDArDQMdOD8OJ10+YidUPSwVB0dMGCIgPR03WBYoNjoeKh1vbl8RcGNBIQgANi8uLQJkRVE8LCMJNloiLH1HeWMIBEkaejknKwdkOQQuNgoLMFcoLHtCJCITFigZLiIYLx0hCllzeSgGMVZtAyBFPwQAEA0JNGM8OgY0OQQuNhoLNlY/anwRNS0FQgwCPm0yZ2MDHB8JPCEGeHIpJgZdOScEEEFODSw7KxsNFgU/KzsLLhFhYi4RBCYZFklRem8YLx0hClEzNzkPMEUsLncdcAcEBAgZNjlvc0lySF16FCQEYg5tc2UdcA4AGklRent/fkVkKh4vNykDLFRtf3UBfGMyFw8KMzVvc0lmWAJ4dUdKYhNtATRdPCEAAQJMZ20pOwcnDBg1N2UcaxMMNyFeFyITBgwCdB47Lx0hVgY7LSgYC105JydHMS9BX0kaeighKkk5UXsdPSM5J18heBRVNAcIFAAIPz9nZ2MDHB8JPCEGeHIpJhdEJDcODEEXehkqNh1kRVF4CigGLhMrLTpVcA0uNUtAegs6IApkRVE8LCMJNloiLH0YcBEEDwYYPz5hKAA2HVl4CigGLnUiLTETeXhBLAYYMys2ZksXHR02e2FKYHUkMDBVfmFIQgwCPm0yZ2MDHB8JPCEGeHIpJhdEJDcODEEXehkqNh1kRVF4DiweJ0FtDBpmcm9BQklMegs6IApkRVE8LCMJNloiLH0YcBEEDwYYPz5hJwcyFxo/cW89I0coMBJQIicEDBpOc3ZvAAYwERcjcW89I0coMHcdcGEnCxsJPmNtZ0khFhV6JGRgSF8iITRdcC8DDjkAOyM7Kw1kWFFneQoOLGA5IyFCagIFBiUNOCgjZksUFBA0LSgOYhNteHUBcmprDgYPOyFvIgsoMBAoLygZNlYpYmgRFycPMR0NLj51Dw0gNBA4PCFCYHssMCNUIzcEBklWen1tZ2MoFxI7NW0GIF8PLSBWODdBQklMZ20IKgcXDBAuKncrJlcBIzdUPGtDMQEDKm0tOxA3WEt6aW9DSF8iITRdcC8DDjoDNilvbklkWFFneQoOLGA5IyFCagIFBiUNOCgjZksXHR02eS4LLl8+eHUBcmprDgYPOyFvIgsoLQEuMCAPYhNtYmgRFycPMR0NLj51Dw0gNBA4PCFCYGY9NjxcNWNBQklWen1/dFl0QkFqe2RgBVcjESFQJDBbIw0IHiQ5Jw0hCllzUwoOLGA5IyFCagIFBisZLjkgIEE/WCU/ITlKfxNvEDBCNTdBER0NLj5tYkkCDR85eXBKJEYjISFYPy1JS0k/Liw7PUc2HQI/LWVDeRMDLSFYNjpJQDoYOzk8bEVkWiM/KigebBFkYjBfNGMcS2Nmd2BvrP3EmuXau9nqYmcMAHUDcKHh9kk/EgIfbovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2UcGLVAsLnViODM1ABEgenBvGggmC18JMSIaeHIpJhlUNjc1AwsONTVnZ2MoFxI7NW05KkMeJzBVI2NcQjoEKhktNiV+ORU+DSwIahEeJzBVI2NHQi4JOz9tZ2MoFxI7NW05KkMIJTJCcGNcQjoEKhktNiV+ORU+DSwIahEIJTJCcGVBJx8JNDk8bEBOciIyKR4PJ1c+eBRVNA8AAAwAcjZvGgw8DFFneW8rN0cibzdEKTBBEQwJPm0uIA1kHxQ7K20ZKlw9YiZFPyAKQgYCeixvOgApHQN0eQwOJhMuLThcMW4SBxkNKCw7Kw1kFhA3PD5EYB9tBjpUIxQTAxlMZ207PBwhWAxzUx4CMmAoJzFCagIFBi0FLCQrKxtsUXsJMT05J1YpMW9wNCcoDBkZLmVtHQwhHD87NCgZYB9tOXVlNTsVQlRMeB4qKw03WAU1eS8fOxFhYhFUNiIUDh1MZ21tDQg2Ch4udR4eMFI6IDBDIjpNIAUZPy8qPBs9VCU1NCweLRFhSHURcGMxDggPPyUgIg0hClFneW8JLV4gI3hCNTMAEAgYPylvIAgpHQJ4dUdKYhNtFjpePDcIEklRem8MIQQpGVwpPD0LMFI5JzERPCoSFkkDPG08KwwgWB87NCgZYkciYiVEIiAJAxoJejonKwdkER96KjkFIVhjYHk7cGNBQioNNiEtLwovWEx6PzgEIUckLTsZJmprQklMem1vbkkFDQU1CiUFMh0eNjRFNW0SBwwIFCwiKxpkRVEhJEdKYhNtYnURcCUOEEkCeiQhbh0rCwUoMCMNakVkeDJcMTcCCkFOARNjE0JmUVE+NkdKYhNtYnURcGNBQkkANS4uIkk3WEx6N3cHI0cuKn0TDmYSSEFCd2RqPUNgWlhQeW1KYhNtYnURcGNBCw9MKW0xc0lmWlEuMSgEYkcsIDlUfioPEQweLmUOOx0rKxk1KWM5NlI5J3tCNSYFLAgBPz5jbhptWBQ0PUdKYhNtYnURcCYPBmNMem1vKwcgWAxzUx4CMmAoJzFCagIFBj0DPSojK0FmOQQuNg8fO2AoJzFCcm9BGUk4PzU7blRkWjAvLSJKAEY0YiZUNScSQEVMHigpLxwoDFFneSsLLkAobl8RcGNBIQgANi8uLQJkRVE8LCMJNloiLH1HeWMgFx0DCSUgPkcXDBAuPGMLN0ciETBUNDBBX0kaYW0mKEkyWAUyPCNKA0Y5LQZZPzNPER0NKDlnZ0khFhV6PCMOYk5kSAZZIBAEBw0fYAwrKi0tDhg+PD9CazkeKiViNSYFEVMtPikGIBkxDFl4HigLMH0sLzBCcm9BGUk4PzU7blRkWjY/OD9KNlxtICBIcm9BJgwKOzgjOkl5WFMNODkPMFojJXVyMS1NNhsDLSgjbEVOWFF6eR0GI1AoKjpdNCYTQlRMeC4gIwQlVQI/KSwYI0coJnVfMS4EEUtAUG1vbkkHGR02OywJKRNwYjNEPiAVCwYCcjtmRElkWFF6eW1KA0Y5LQZZPzNPMR0NLihhKQwlCj87NCgZYg5tOSg7cGNBQklMem0pIRtkFlEzN20eLUA5MDxfN2sXS1MLNyw7LQFsWioEdRBBYBptJjo7cGNBQklMem1vbklkFB45OCFKMRNwYjsLPSIVAQFEeBNqPUNsVlxzfD5AZhFkSHURcGNBQklMem1vbgAiWAJ6J3BKYBFtNj1UPmMVAwsAP2MmIBohCgVyGDgeLWAlLSUfAzcAFgxCPSguPCclFRQpdW0ZaxMoLDE7cGNBQklMem0qIA1OWFF6eSgEJhMwa19iODMyBwwIKXcOKg0QFxY9NShCYHI4NjpzJTomBwgeeGFvNUkQHQkueXBKYHI4NjoREjYYQg4JOz9tYkkAHRc7LCEeYg5tJDRdIyZNaElMem0MLwUoGhA5Mm1XYlU4LDZFOSwPSh9Fegw6OgYXEB4qdx4eI0cobDREJCwmBwgeenBvOFJkERd6L20eKlYjYhREJCwyCgYcdD47LxswUFh6PCMOYlYjJnVMeUkyChk/PygrPVMFHBUeMDsDJlY/anw7AysRMQwJPj51Dw0gKx0zPSgYahEeKjpBGS0VBxsaOyFtYkk/WCU/ITlKfxNvET1eIGMCCgwPMW0mIB0hCgc7NW9GYncoJDREPDdBX0lZdm0CJwdkRVFrdW0nI0ttf3UHYG9BMAYZNCkmIA5kRVFrdW05N1UrKy0RbWNDQhpOdkdvbklkOxA2NS8LIVhtf3VXJS0CFgADNGU5Z0kFDQU1CiUFMh0eNjRFNW0IDB0JKDsuIkl5WAd6PCMOYk5kSF9iODMkBQ4fYAwrKiUlGhQ2cTZKFlY1NnUMcGEgFx0Ddy86NxpkCBQueSgNJUBtIztVcDcTCw4LPz88bgwyHR8udiMDJVs5bSFDMTUEDgACPWAiKxsnEBA0LW0ZKlw9MXsTfGMlDQwfDT8uPkl5WAUoLChKPxpHET1BFSQGEVMtPikLJx8tHBQocWRgEVs9BzJWI3kgBg0lND06OkFmPRY9FywHJ0BvbnVKcBcEGh1MZ21tCw4jC1EuNm0IN0pvbnV1NSUAFwUYenBvbCorFRw1N20vJVRvbl8RcGNBMgUNOSgnIQUgHQN6ZG1IIVwgLzQcIyYRAxsNLigrbgwjH1E0OCAPMRFhSHURcGMiAwUAOCwsJUl5WBcvNy4eK1wjaiMYWmNBQklMem1vDxwwFyIyNj1EEUcsNjAfNSQGLAgBPz5vc0k/BXt6eW1KYhNtYjNeImMPQgACejkgPR02ER89cTtDeFQgIyFSOGtDOTdAB2ZtZ0kgF3t6eW1KYhNtYnURcGMNDQoNNm08blRkFks3ODkJKhtvHHBCemtPT0BJKWdrbEBOWFF6eW1KYhNtYnUROSVBEUkSZ21tbEkwEBQ0eTkLIF8obDxfIyYTFkEtLzkgHQErCF8JLSweJx0oJTJ/MS4EEUVMKWRvKwcgclF6eW1KYhNtJztVWmNBQkkJNClvM0BOKxkqHCoNMQkMJjFlPyQGDgxEeAw6OgYGDQgfPioZYB9tOXVlNTsVQlRMeAw6OgZkOgQjeSgNJUBvbnV1NSUAFwUYenBvKAgoCxR2U21KYhMOIzldMiICCUlReis6IAowER40cTtDYnI4NjpiOCwRTDoYOzkqYAgxDB4fPioZYg5tNG4ROSVBFEkYMighbigxDB4JMSIabEA5IydFeGpBBwcIeighKkk5UXsJMT0vJVQ+eBRVNAcIFAAIPz9nZ2MXEAEfPioZeHIpJgFeNyQNB0FOHzsqIB0XEB4qe2FKORMZJy1FcH5BQCgZLiJvDBw9WDQsPCMeYkAlLSUTfGMlBw8NLyE7blRkHhA2KihGSBNtYnVlPywNFgAcenBvbCsxAQJ6PDsPLEdgMT1eIGMSFgYPMW1pbiwlCwU/K20ZNlwuKXVGOCYPQggPLiQ5K0dmVHt6eW1KAVIhLjdQMyhBX0kKLyMsOgArFlkscG0rN0ciET1eIG0yFggYP2MqOAwqDCIyNj1KfxM7eXVYNmMXQh0EPyNvDxwwFyIyNj1EMUcsMCEZeWMEDA1MPyMrbhRtciIyKQgNJUB3AzFVBCwGBQUJcm8BJw4sDCIyNj1IbhM2YgFUKDdBX0lOGzg7IUkGDQh6FyQNKkdtMT1eIGFNQi0JPCw6Ih1kRVE8OCEZJx9HYnURcAAADgUOOy4kblRkHgQ0OjkDLV1lNHwRETYVDToENT1hHR0lDBR0NyQNKkdtf3VHa2MIBEkaejknKwdkOQQuNh4CLUNjMSFQIjdJS0kJNClvKwcgWAxzUx4CMnYqJSYLEScFNgYLPSEqZksQChAsPCEDLFQAJydSOGFNQhJMDig3Okl5WFMbLDkFYnE4O3VlIiIXBwUFNCpvAww2Gxk7NzlIbhMJJzNQJS8VQlRMPCwjPQxoclF6eW0pI18hIDRSO2NcQg8ZNC47JwYqUAdzeQwfNlweKjpBfhAVAx0JdDk9Lx8hFBg0Pm1XYkV2YjxXcDVBFgEJNG0OOx0rKxk1KWMZNlI/Nn0YcCYPBkkJNClvM0BOch01OiwGYmAlMgcRbWM1AwsfdB4nIRl+ORU+CyQNKkcKMDpEICEOGkFOCzgmLQJkGRIuMCIEMRFhYndaNTpDS2M/Mj0ddCggHD07OygGakhtFjBJJGNcQkshOyM6LwVkFx8/dD4CLUdtMT1eIGMAAR0FNSM8YEtoWDU1PD49MFI9YmgRJDEUB0kRc0ccJhkWQjA+PQkDNFopJycZeUkyChk+YAwrKisxDAU1N2URYmcoOiERbWNDIBwVegwDAkk3HRQ+Km1CJEEiL3VdOTAVS0tAegs6IApkRVE8LCMJNloiLH0YWmNBQkkKNT9vEUVkFlEzN20DMlIkMCYZETYVDToENT1hHR0lDBR0KigPJn0sLzBCeWMFDUk+PyAgOgw3VhczKyhCYHE4OwZUNSdDTkkCc3ZvOgg3E18tOCQeagNjc3wRNS0FaElMem0BIR0tHghyex4CLUNvbnUTBDEIBw1MODg2JwcjWAI/PCkZbBFkSDBfNGMcS2M/Mj0ddCggHDMvLTkFLBs2YgFUKDdBX0lOGDg2bigINFE9PCwYYhsrMDpccC8IER1FeGFvCBwqG1FneSsfLFA5KzpfeGprQklMeisgPEkbVFE0eSQEYlo9IzxDI2sgFx0DCSUgPkcXDBAuPGMNJ1I/DDRcNTBIQg0Deh8qIwYwHQJ0PyQYJxtvACBIFyYAEEtAeiNmdUkwGQIxdzoLK0dlcnsAeWMEDA1mem1vbicrDBg8IGVIEVsiMncdcGE1EAAJPm0tOxAtFhZ6PigLMB1va19UPidBH0BmCSU/HFMFHBUYLDkeLV1lOXVlNTsVQlRMeA86N0kFND16PCoNMRNlJCdePWMNCxoYc29jbi8xFhJ6ZG0MN10uNjxePmtIaElMem0pIRtkJ116N20DLBMkMjRYIjBJIxwYNR4nIRlqKwU7LShEJ1QqDDRcNTBIQg0Deh8qIwYwHQJ0PyQYJxtvACBIACYVJw4LeGFvIEB/WAU7KiZENVIkNn0BfnJIQgwCPkdvbklkNh4uMCsTahEeKjpBcm9BQD0eMygrbgsxARg0Pm0PJVQ+bHcYWiYPBkkRc0ccJhkWQjA+PQkDNFopJycZeUkyChk+YAwrKisxDAU1N2URYmcoOiERbWNDMAwIPygibigINFE4LCQGNh4kLHVSPycEEUtAUG1vbkkQFx42LSQaYg5tYAFDOSYSQgwaPz82bgIqFwY0eSwJNlo7J3VSPycEQg8eNSBvOgEhWBMvMCEeb1ojYjlYIzdPQEVmem1vbi8xFhJ6ZG0MN10uNjxePmtIQigZLiIfKx03VgM/PSgPL3AiJjBCeA0OFgAKI2RvKwcgWAxzUx4CMmF3AzFVGS0RFx1EeA46PR0rFTI1PShIbhM2YgFUKDdBX0lOGTg8OgYpWBI1PShIbhMJJzNQJS8VQlRMeG9jbjkoGRI/MSIGJlY/YmgRchcYEgxMO20sIQ0hVl90e2FKAVIhLjdQMyhBX0kKLyMsOgArFllzeSgEJhMwa19iODMzWCgIPg86Oh0rFlkheRkPOkdtf3UTAiYFBwwBei46PR0rFVE5NikPYB9tBCBfM2NcQg8ZNC47JwYqUFhQeW1KYl8iITRdcCAOBgxMZ20APh0tFx8pdw4fMUciLxZeNCZBAwcIegI/OgArFgJ0GjgZNlwgATpVNW03AwUZP20gPElmWnt6eW1KK1VtITpVNWNcX0lOeG07JgwqWD81LSQMOxtvATpVNWFNQkspNz07N0toWAUoLChDeRM/JyFEIi1BBwcIUG1vbkkWHRw1LSgZbFUkMDAZcgANAwABOy8jKyorHBR4dW0JLVcoa24RHiwVCw8Vcm8MIQ0hWl16exkYK1YpeHUTcG1PQgoDPihmRAwqHFEncEdgbx5toMGxstfhgP3sehkODEl3WJPazW06B2ceYrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14mMANS4uIkkUHQUWeXBKFlIvMXthNTcSWCgIPgEqKB0DCh4vKS8FOhtvETBdPGNHQiQNNCwoK0toWFMyPCwYNhFkSAVUJA9bIw0IFiwtKwVsA1EOPDUeYg5tYAZUPC9BEgwYKW0mIEkmDR0xeSIYYlwjJ3hCOCwVTEkuP20sLxshHgQ2eToDNlttETBdPGMgLiVNeGFvCgYhCyYoOD1KfxM5MCBUcD5IaDkJLgF1Dw0gPBgsMCkPMBtkSAVUJA9bIw0IDiIoKQUhUFMbLDkFEVYhLgVUJDBDTkkXehkqNh1kRVF4GDgeLRMeJzldcAItLkk8Pzk8bkEoFx4qcG9GYncoJDREPDdBX0kKOyE8K0VkKhgpMjRKfxM5MCBUfElBQklMDiIgIh0tCFFneW86J0EkLTFYMyINDhBMPCQ9KxpkKxQ2NQwGLmMoNiYfcBYSB0kbMzknbgolChR0e2FgYhNtYhZQPC8DAwoHenBvKBwqGwUzNiNCNBptAyBFPxMEFhpCCTkuOgxqGQQuNh4PLl8dJyFCcH5BFFJMMytvOEkwEBQ0eQwfNlwdJyFCfjAVAxsYcmRvKwcgWBQ0PW0XazkdJyF9agIFBjoAMykqPEFmKxQ2NR0PNnojNjBDJiINQEVMIW0bKxEwWEx6ex4PLl9gMjBFcCoPFgweLCwjbEVkPBQ8ODgGNhNwYmYBfGMsCwdMZ216YkkJGQl6ZG1ccgNhYgdeJS0FCwcLenBvfkVkKwQ8PyQSYg5tYHVCcm9rQklMeg4uIgUmGRIxeXBKJEYjISFYPy1JFEBMGzg7ITkhDAJ0CjkLNlZjMTBdPBMEFiACLig9OAgoWEx6L20PLFdtP3w7ACYVLlMtPikLJx8tHBQocWRgElY5Dm9wNCcjFx0YNSNnNUkQHQkueXBKYGAoLjkREQ8tQhkJLj5vACYTWl16HSIfIF8oATlYMyhBX0kYKDgqYmNkWFF6DSIFLkckMnUMcGEuDAxBKSUgOkkXHR02eQwmDh1tBjpEMi8ETwoAMy4kbh0rWBI1NysDMF5jYHk7cGNBQi8ZNC5vc0kiDR85LSQFLBtkYhREJCwxBx0fdD4qIgUFFB1ycHZKDFw5KzNIeGExBx0feGFvbDohFB0bNSFKJFo/JzEfcmpBBwcIejBmRGMoFxI7NW06J0cfYmgRBCIDEUc8Pzk8dCggHCMzPiUeBUEiNyVTPztJQCwdLyQ/bk9kOh41KjlIbhNvKTBIcmprMgwYCHcOKg0IGRM/NWURYmcoOiERbWNDLwgCLywjbhkhDFE/KDgDMkBtIztVcCEODRoYejk9Jw4jHQMpeWUoJ1ZtATpdPy0YTkkhLzkuOgArFlEXOC4CK10obnVUJCBITEtAegkgKxoTChAqeXBKNkE4J3VMeUkxBx0+YAwrKi0tDhg+PD9CazkdJyFjagIFBisZLjkgIEE/WCU/ITlKfxNvFidYNyQEEEkhLzkuOgArFlEXOC4CK10oYHkRFjYPAUlReis6IAowER40cWRKEFYgLSFUI20HCxsJcm8fKx0JDQU7LSQFLH4sIT1YPiYyBxsaMy4qETsBWlh6PCMOYk5kSAVUJBFbIw0IGDg7OgYqUAp6DSgSNhNwYndkIyZBMgwYeh0gOwosWl16eW1KYhNtYnURcGMnFwcPenBvKBwqGwUzNiNCaxMfJzheJCYSTA8FKChnbDkhDCE1LC4CF0AoYHwRNS0FQhRFUB0qOjt+ORU+GzgeNlwjai4RBCYZFklRem8aPQxkPhAzKzRKDFY5YHkRcGNBQklMem1vbkkCDR85eXBKJEYjISFYPy1JS0k+PyAgOgw3VhczKyhCYHUsKydIHiYVIwoYMzsuOgwgWlh6PCMOYk5kSAVUJBFbIw0IGDg7OgYqUAp6DSgSNhNwYndkIyZBJAgFKDRvHRwpFR40PD9IbhNtYnURcGMnFwcPenBvKBwqGwUzNiNCaxMfJzheJCYSTA8FKChnbC8lEQMjCjgHL1wjJydwMzcIFAgYPyltZ0khFhV6JGRgElY5EG9wNCcjFx0YNSNnNUkQHQkueXBKYGY+J3VhNTdBLAgBP20dKxsrFB0/K29GYhNtYhNEPiBBX0kKLyMsOgArFllzeR8PL1w5JyYfNioTB0FOCig7AAgpHSM/KyIGLlY/AzZFOTUAFgwIeGRvKwcgWAxzU0dHbxOv1tXTxMOD9ulMDgwNbl1kmvHOeR0mA2oIEHXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tXTxMOD9umOzs2t2umm7PG4zc2I1rOv1tU7PCwCAwVMCiE9Ggs8NFFneRkLIEBjEjlQKSYTWCgIPgEqKB0QGRM4NjVCazkhLTZQPGMsDR8JDiwtblRkKB0oDS8SDgkMJjFlMSFJQCQDLCgiKwcwWlhQNSIJI19tFDxCBCIDQklReh0jPD0mAD1gGCkOFlIvandnOTAUAwUfeGRFRCQrDhQOOC9QA1cpDjRTNS9JGUk4PzU7blRkWiIqPCgObhMnNzhBcCIPBkkBNTsqIwwqDFEyPCEaJ0E+bHVjNW4AEhkAMyg8bgYqWAM/Kj0LNV1jYHkRFCwEET4eOz1vc0kwCgQ/eTBDSH4iNDBlMSFbIw0IHiQ5Jw0hCllzUwAFNFYZIzcLEScFMQUFPig9ZksTGR0xCj0PJ1dvbnVKcBcEGh1MZ21tGQgoE1EJKSgPJhFhYhFUNiIUDh1MZ219fkVkNRg0eXBKcwVhYhhQKGNcQltcamFvHAYxFhUzNypKfxN9bnViJSUHCxFMZ21tbhowDRUpdj5IbjltYnURBCwODh0FKm1ybksDGRw/eSkPJFI4LiEROTBBUFlCeGFvDQgoFBM7OiZKfxMALSNUPSYPFkcfPzkYLwUvKwE/PClKPxpHDzpHNRcAAFMtPikcIgAgHQNyewcfL0MdLSJUImFNQhJMDig3Okl5WFMQLCAaYmMiNTBDcm9BJgwKOzgjOkl5WERqdW0nK11tf3UEYG9BLwgUenBvfVl0VFEINjgEJlojJXUMcHNNQioNNiEtLwovWEx6FCIcJ14oLCEfIyYVKBwBKh0gOQw2WAxzUwAFNFYZIzcLEScFNgYLPSEqZksNFhcQLCAaYB9tYnVKcBcEGh1MZ21tBwciER8zLShKCEYgMncdcAcEBAgZNjlvc0kiGR0pPGFKAVIhLjdQMyhBX0khNTsqIwwqDF8pPDkjLFUHNzhBcD5IaCQDLCgbLwt+ORU+DSINJV8oand/PyANCxlOdm1vbkk/WCU/ITlKfxNvDDpSPCoRQEVMem1vbklkWDU/PywfLkdtf3VXMS8SB0VMGSwjIgslGxp6ZG0nLUUoLzBfJG0SBx0iNS4jJxlkBVhQFCIcJ2csIG9wNCclCx8FPig9ZkBONR4sPBkLIAkMJjFlPyQGDgxEeAsjN0toWFF6eW1KYkhtFjBJJGNcQksqNjRtYkkAHRc7LCEeYg5tJDRdIyZNQj0DNSE7JxlkRVF4Dgw5BhNmYgZBMSAETSU/MiQpOktoWDI7NSEII1AmYmgRHSwXBwQJNDlhPQwwPh0jeTBDSH4iNDBlMSFbIw0ICSEmKgw2UFMcNTQ5MlYoJncdcGMaQj0JIjlvc0lmPh0jeR4aJ1YpYHkRFCYHAxwALm1yblF0VFEXMCNKfxN8cnkRHSIZQlRMbn1/YkkWFwQ0PSQEJRNwYmUdcAAADgUOOy4kblRkNR4sPCAPLEdjMTBFFi8YMRkJPylvM0BONR4sPBkLIAkMJjF1OTUIBgwecmRFAwYyHSU7O3crJlcZLTJWPCZJQCgCLiQOCCJmVFF6eTZKFlY1NnUMcGEgDB0FdwwJBUtoWDU/PywfLkdtf3VFIjYETkk4NSIjOgA0WEx6ew8GLVAmMXVFOCZBUFlBNyQhbgAgFBR6MiQJKR1vbnVyMS8NAAgPMW1ybiQrDhQ3PCMebEAoNhRfJCogJCJMJ2RFAwYyHRw/NzlEMVY5AztFOQInKUEYKDgqZ2MJFwc/DSwIeHIpJhFYJioFBxtEc0cCIR8hLBA4YwwOJmAhKzFUImtDKgAYOCI3bEVkWFF6Im0+J0s5YmgRcgsIFgsDIm08JxMhWl16HSgMI0YhNnUMcHFNQiQFNG1ybltoWDw7IW1XYgF9bnVjPzYPBgACPW1yblloWCIvPysDOhNwYncRIzcUBhpOdkdvbklkLB41NTkDMhNwYndzOSQGBxtMKCIgOkk0GQMueXBKNVopJycRMywNDgwPLiQgIEk2GRUzLD5EYB9tATRdPCEAAQJMZ20CIR8hFRQ0LWMZJ0cFKyFTPztBH0BmFyI5Kz0lGksbPSkuK0UkJjBDeGprLwYaPxkuLFMFHBUYLDkeLV1lOXVlNTsVQlRMeB4uOAxkGwQoKygENhM9LSZYJCoODEtAegs6IApkRVE8LCMJNloiLH0YcCoHQiQDLCgiKwcwVgI7Lyg6LUBla3VFOCYPQicDLiQpN0FmKB4pe2FIEVI7JzEfcmpBBwUfP20BIR0tHghyex0FMRFhYBtecCAJAxtOdjk9OwxtWBQ0PW0PLFdtP3w7HSwXBz0NOHcOKg0GDQUuNiNCORMZJy1FcH5BQDsJOSwjIkk3GQc/PW0aLUAkNjxePmFNQi8ZNC5vc0kiDR85LSQFLBtkYjxXcA4OFAwBPyM7YBshGxA2NR0FMRtkYiFZNS1BLAYYMys2ZksUFwJ4dW84J1AsLjlUNG1DS0kJNj4qbicrDBg8IGVIElw+YHkTHiwVCgACPW08Lx8hHFN2LT8fJxptJztVcCYPBkkRc0dFGAA3LBA4YwwOJn8sIDBdeDhBNgwULm1ybksTFwM2PW0GK1QlNjxfN21DTkkoNSg8GRslCFFneTkYN1ZtP3w7BioSNggOYAwrKi0tDhg+PD9CazkbKyZlMSFbIw0IDiIoKQUhUFMcLCEGIEEkJT1Fcm9BGUk4PzU7blRkWjcvNSEIMFoqKiETfGMlBw8NLyE7blRkHhA2KihGYnAsLjlTMSAKQlRMDCQ8OwgoC18pPDksN18hICdYNysVQhRFUBsmPT0lGksbPSk+LVQqLjAZcg0OJAYLeGFvbklkWFEheRkPOkdtf3UTAiYMDR8JeisgKUtoWDU/PywfLkdtf3VXMS8SB0VMGSwjIgslGxp6ZG08K0A4IzlCfjAEFicDHCIobhRtcns2Ni4LLhMdLidlMjszQlRMDiwtPUcUFBAjPD9QA1cpEDxWODc1AwsONTVnZ2MoFxI7NW0+MmMCCyYRcGNBX0k8Nj8bLBEWQjA+PRkLIBtvDzRBcBMuKxpOc0cjIQolFFEOKR0GI0ooMCYRbWMxDhs4ODUddCggHCU7O2VIEl8sOzBDcBcxQEBmUBk/HiYNC0sbPSkmI1EoLn1KcBcEGh1MZ21tAQchVRI2MC4BYkcoLjBBPzEVEUdMFB0MbgclFRQpeSwYJxMrNy9LKW4MAx0PMigrbgAqWAY1KyYZMlIuJ3sTfGMlDQwfDT8uPkl5WAUoLChKPxpHFiVhHwoSWCgIPgkmOAAgHQNycEcMLUFtHXkRNWMIDEkFKiwmPBpsLBQ2PD0FMEc+bDlYIzdJS0BMPiJFbklkWB01OiwGYl0sLzARbWMETAcNNyhFbklkWCUqCQIjMQkMJjFzJTcVDQdEIW0bKxEwWEx6e6/s0BNvYnsfcC0ADwxAegs6IApkRVE8LCMJNloiLH0YWmNBQklMem1vJw9kFh4ueRkPLlY9LSdFI20GDUECOyAqZ0kwEBQ0eQMFNlorO30TBBNDTkkCOyAqbkdqWFN6NyIeYlUiNztVcm9BFhsZP2RFbklkWFF6eW0PLkAoYhteJCoHG0FODh1tYklmmvfIeW9KbB1tLDRcNWpBBwcIUG1vbkkhFhV6JGRgJ10pSF9dPyAADkkKLyMsOgArFlE9PDk6LlI0Jyd/MS4EEUFFUG1vbkkoFxI7NW0FN0dtf3VKLUlBQklMPCI9bjZoWAF6MCNKK0MsKydCeBMNAxAJKD51CQwwKB07ICgYMRtka3VVP0lBQklMem1vbgAiWAF6J3BKDlwuIzlhPCIYBxtMLiUqIEkwGRM2PGMDLEAoMCEZPzYVTkkcdAMuIwxtWBQ0PUdKYhNtJztVWmNBQkkFPG1sIRwwWExneX1KNlsoLHVFMSENB0cFND4qPB1sFwQudW1Ial0iLDAYcmpBBwcIUG1vbkk2HQUvKyNKLUY5SDBfNEk1EjkAOzQqPBp+ORU+FSwIJ19lOXVlNTsVQlRMeBkqIgw0FwMueTkFYlw5KjBDcDMNAxAJKD5vJwdkDBk/eT4PMEUoMHsTfGMlDQwfDT8uPkl5WAUoLChKPxpHFiVhPCIYBxsfYAwrKi0tDhg+PD9CazkZMgVdMToEEBpWGykrChsrCBU1LiNCYGc9EjlQKSYTQEVMIW0bKxEwWEx6ex0GI0ooMHcdcBUADhwJKW1ybg4hDCE2ODQPMH0sLzBCeGpNQi0JPCw6Ih1kRVF4cSMFLFZkYHkREyINDgsNOSZvc0kiDR85LSQFLBtkYjBfNGMcS2M4Kh0jLxAhCgJgGCkOAEY5NjpfeDhBNgwULm1ybksWHRcoPD4CYl8kMSETfGMnFwcPenBvKBwqGwUzNiNCazltYnUROSVBLRkYMyIhPUcQCCE2ODQPMBMsLDERHzMVCwYCKWMbPjkoGQg/K2M5J0cbIzlENTBBFgEJNG0APh0tFx8pdxkaEl8sOzBDahAEFj8NNjgqPUEjHQUKNSwTJ0EDIzhUI2tIS0kJNClFKwcgWAxzUxkaEl8sOzBDI3kgBg0uLzk7IQdsA1EOPDUeYg5tYAFUPCYRDRsYejkgbhohFBQ5LSgOYB9tBCBfM2NcQg8ZNC47JwYqUFhQeW1KYl8iITRdcC1BX0kjKjkmIQc3ViUqCSELO1Y/YjRfNGMuEh0FNSM8YD00KB07ICgYbGUsLiBUWmNBQkkANS4uIkk0WEx6N20LLFdtEjlQKSYTEVMqMyMrCAA2CwUZMSQGJhsja18RcGNBCw9MKm0uIA1kCF8ZMSwYI1A5JycRJCsEDGNMem1vbklkWB01OiwGYls/MnUMcDNPIQENKCwsOgw2QjczNyksK0E+NhZZOS8FSkskLyAuIAYtHCM1Njk6I0E5YHw7cGNBQklMem0mKEksCgF6LSUPLBMYNjxdI20VBwUJKiI9OkEsCgF0CSIZK0ckLTsRe2M3BwoYNT98YAchD1lodW1abhN9a3wRNS0FaElMem0qIA1OHR8+eTBDSDlgb3XTxMOD9umOzs1vGigGWER6u83+Yn4EERYRstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3sUCEgLQgoWDwzKi4mYg5tFjRTI20sCxoPYAwrKiUhHgUdKyIfMlEiOn0TFyIMB0lKeg46PBshFhIje2FKYFojJDoTeUksCxoPFncOKg0IGRM/NWURYmcoOiERbWNDJQgBP20mIA8rWBA0PW0TLUY/YjlYJiZBMQEJOSYjKxpkGhA2OCMJJx1vbnV1PyYSNRsNKm1ybh02DRR6JGRgD1o+IRkLEScFJgAaMykqPEFtcjwzKi4meHIpJhlQMiYNSkFOCiEuLQx+WFQpe2RQJFw/LzRFeAAODA8FPWMIDyQBJz8bFAhDazkAKyZSHHkgBg0gOy8qIkFsWiE2OC4PYnoJeHUUNGFIWA8DKCAuOkEHFx88MCpEEn8MARBuGQdIS2MhMz4sAlMFHBUWOC8PLhtlYBZDNSIVDRtWemg8bEB+Hh4oNCweanAiLDNYN20iMCwtDgIdZ0BONRgpOgFQA1cpBjxHOScEEEFFUCEgLQgoWB04NR4CJ0ttf3V8OTACLlMtPikDLwshFFl4CiUPIVghJyYLcG5DS2NmNiIsLwVkNRgpOh9KfxMZIzdCfg4IEQpWGykrHAAjEAUdKyIfMlEiOn0TAyYTFAweeGFvbB42HR85MW9DSH4kMTZjagIFBiUNOCgjZhJkLBQiLW1XYhEfJz9eOS1BFgEFKW08KxsyHQN6Nj9KKlw9YiFecCJBBBsJKSVvPhwmFBg5eT4PMEUoMHsTfGMlDQwfDT8uPkl5WAUoLChKPxpHDzxCMxFbIw0IHiQ5Jw0hCllzUwADMVAfeBRVNAEUFh0DNGU0bj0hAAV6ZG1IEFYnLTxfcDcJCxpMKSg9OAw2Wl1QeW1KYnU4LDYRbWMHFwcPLiQgIEFtWBY7NChQBVY5ETBDJioCB0FODigjKxkrCgUJPD8cK1AoYHwLBCYNBxkDKDlnDQYqHhg9dx0mA3AIHRx1fGMtDQoNNh0jLxAhClh6PCMOYk5kSBhYIyAzWCgIPg86Oh0rFlkheRkPOkdtf3UTAyYTFAweeiUgPklsChA0PSIHaxFhSHURcGMnFwcPenBvKBwqGwUzNiNCazltYnURcGNBQicDLiQpN0FmMB4qe2FKYGAoIydSOCoPBUdCdG9mRElkWFF6eW1KNlI+KXtCICIWDEEKLyMsOgArFllzU21KYhNtYnURcGNBQgUDOSwjbj0XWEx6PiwHJwkKJyFiNTEXCwoJcm8bKwUhCB4oLR4PMEUkITATeUlBQklMem1vbklkWFE2Ni4LLhMFNiFBAyYTFAAPP21ybg4lFRRgHigeEVY/NDxSNWtDKh0YKh4qPB8tGxR4cEdKYhNtYnURcGNBQkkANS4uIkkrE116KygZYg5tMjZQPC9JBBwCOTkmIQdsUXt6eW1KYhNtYnURcGNBQklMKCg7OxsqWBY7NChQCkc5MhJUJGtJQAEYLj08dEZrHxA3PD5EMFwvLjpJfiAOD0Yaa2IoLwQhC15/PWIZJ0E7JydCfxMUAAUFOXI8IRswNwM+PD9XA0AuZDlYPSoVX1hcam9mdA8rChw7LWUpLV0rKzIfAA8gISwzEwlmZ2NkWFF6eW1KYhNtYnVUPidIaElMem1vbklkWFF6eSQMYl0iNnVeO2MVCgwCegMgOgAiAVl4ESIaYB9vCiFFIAQEFkkKOyQjKw1qWl0uKzgPawhtMDBFJTEPQgwCPkdvbklkWFF6eW1KYhMhLTZQPGMOCVtAeikuOghkRVEqOiwGLhsrNztSJCoODEFFej8qOhw2FlESLTkaEVY/NDxSNXkrMSYiHigsIQ0hUAM/KmRKJ10pa18RcGNBQklMem1vbkktHlE0NjlKLVh/YjpDcC0OFkkIOzkubgY2WB81LW0OI0csbDFQJCJBFgEJNG0BIR0tHghyewUFMhFhYBdQNGMTBxocNSM8K0dmVAUoLChDeRM/JyFEIi1BBwcIUG1vbklkWFF6eW1KYlUiMHVufGMSEB9MMyNvJxklEQMpcSkLNlJjJjRFMWpBBgZmem1vbklkWFF6eW1KYhNtYjxXcDATFEccNiw2JwcjWBA0PW0ZMEVjLzRJAC8AGwweKW0uIA1kCwMsdz0GI0okLDIRbGMSEB9CNyw3HgUlARQoKm1HYgJtIztVcDATFEcFPm0xc0kjGRw/dwcFIHopYiFZNS1rQklMem1vbklkWFF6eW1KYhNtYnVlA3k1BwUJKiI9Oj0rKB07OigjLEA5IztSNWsiDQcKMyphHiUFOzQFEAlGYkA/NHtYNG9BLgYPOyEfIgg9HQNzYm0YJ0c4MDs7cGNBQklMem1vbklkWFF6eSgEJjltYnURcGNBQklMem0qIA1OWFF6eW1KYhNtYnURHiwVCw8Vcm8HIRlmVFMUNm0ZJ0E7JycRNiwUDA1CeGE7PBwhUXt6eW1KYhNtYjBfNGprQklMeighKkk5UXtQdGBKDlo7J3VEICcAFgwfUDkuPQJqCwE7LiNCJEYjISFYPy1JS2NMem1vOQEtFBR6LSwZKR06IzxFeHJIQg0DUG1vbklkWFF6KS4LLl9lJCBfMzcIDQdEc0dvbklkWFF6eW1KYhMkJHVdMi8xDggCLigrbklkGR8+eSEILmMhIztFNSdPMQwYDig3OklkWAUyPCNKLlEhEjlQPjcEBlM/PzkbKxEwUFMKNSwENlYpYnURamNDQkdCeh47Lx03VgE2OCMeJ1dkYjBfNElBQklMem1vbklkWFEzP20GIF8FIydHNTAVBw1MOyMrbgUmFDk7KzsPMUcoJntiNTc1BxEYejknKwdkFBM2ESwYNFY+NjBVahAEFj0JIjlnbCElCgc/KjkPJhN3YncRfm1BMR0NLj5hJgg2DhQpLSgOaxMoLDE7cGNBQklMem1vbklkERd6NS8GAFw4JT1FcGNBQggCPm0jLAUGFwQ9MTlEEVY5FjBJJGNBQkkYMighbgUmFDM1LCoCNgkeJyFlNTsVSks/MiI/bgsxAQJ6Y21IYh1jYgZFMTcSTAsDLyonOkBkHR8+U21KYhNtYnURcGNBQgAKeiEtIjorFBV6eW1KYhMsLDERPCENMQYAPmMcKx0QHQkueW1KYhNtNj1UPmMNAAU/NSErdDohDCU/ITlCYGAoLjkRMyINDhpWem9vYEdkKwU7LT5EMVwhJnwRNS0FaElMem1vbklkWFF6eSQMYl8vLgBBJCoMB0lMem0uIA1kFBM2DD0eK14obAZUJBcEGh1Mem1vOgEhFlE2OyE/MkckLzALAyYVNgwULmVtGxkwERw/eW1KYgltYHUffmMyFggYKWM6Ph0tFRRycGRKJ10pSHURcGNBQklMem1vbgAiWB04NR4CJ0ttYnURcGMADA1MNi8jHQEhAF8JPDk+J0s5YnURcGNBFgEJNG0jLAUXEBQiYx4PNmcoOiEZchAJBwoHNig8dElmWF90eRgeK18+bDJUJBAJBwoHNig8ZkBtWBQ0PUdKYhNtYnURcCYPBkBmem1vbgwqHHs/NylDSDlgb3XTxMOD9umOzs1vGigGWEl6u83+YnAfBxF4BBBBgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxstfhgP3suNnPrP3EmuXau9nqoKfNoMGxWi8OAQgAeg49Akl5WCU7Oz5EAUEoJjxFI3kgBg0gPys7CRsrDQE4NjVCYHIvLSBFcDcJCxpMEjgtbEVkWhg0PyJIazkOMBkLEScFLggOPyFnNUkQHQkueXBKYHQ/LSIRMWMmAxsIPyNvrOnQWChoEm0iN1FvbnV1PyYSNRsNKm1ybh02DRR6JGRgAUEBeBRVNA8AAAwAcjZvGgw8DFFneW8rYlAhJzRffGMHFwUAI20sOxowFxwzIywILlZtJTRDNCYPTwgZLiIiLx0tFx96MTgIbBFhYhFeNTA2EAgcenBvOhsxHVEncEcpMH93AzFVFCoXCw0JKGVmRCo2NEsbPSkmI1EoLn0ZchACEAAcLm05Kxs3ER40eXdKZ0Bva29XPzEMAx1EGSIhKAAjViIZCwQ6FmwbBwcYeUkiECVWGykrAggmHR1yexgjYl8kICdQIjpBQklMendvAQs3ERUzOCM/KxFkSBZDHHkgBg0gOy8qIkFmLTh6ODgeKlw/YnURcGNBWEk1aCZvHQo2EQEueQ8LIVh/ADRSO2FIaCoeFncOKg0IGRM/NWVCYGAsNDARNiwNBgweem1vblNkXQJ4cHcMLUEgIyEZEywPBAALdB4OGCwbKj4VDWRDSDkhLTZQPGMiEDtMZ20bLws3VjIoPCkDNkB3AzFVAioGCh0rKCI6PgsrAFl4DSwIYnQ4KzFUcm9BQAQDNCQ7IRtmUXsZKx9QA1cpDjRTNS9JGUk4PzU7blRkWiAvMC4BYkEoJDBDNS0CB0mO2tlvOQElDFE/OC4CYkcsIHVVPyYSWEtAegkgKxoTChAqeXBKNkE4J3VMeUkiEDtWGykrCgAyERU/K2VDSHA/EG9wNCctAwsJNmU0bj0hAAV6ZG1IoLPvYhJQIicEDEmO2tlvDxwwF1EqNSwENhNiYj1QIjUEER1MdW0sIQUoHRIueWJKMVYhLnUecDQAFgwedG9jbi0rHQINKywaYg5tNidENWMcS2MvKB91Dw0gNBA4PCFCORMZJy1FcH5BQIvs+G0cJgY0WJPazW0rN0cibzdEKWMSBwwIKWFvKQwlCl16PCoNMR9tJyNUPjcSTkkPNSkqPUdmVFEeNigZFUEsMnUMcDcTFwxMJ2RFDRsWQjA+PQELIFYhai4RBCYZFklRem+tzstkKBQuKm2IwqdtETBdPGMRBx0fdm0iOx0lDBg1N20HI1AlKztUfGMDDQYfLj5hbEVkPB4/KhoYI0Ntf3VFIjYEQhRFUA49HFMFHBUWOC8PLhs2YgFUKDdBX0lOuM3tbjkoGQg/K22IwqdtDzpHNS4EDB1AeisjN0VkFh45NSQabhM5JzlUICwTFhpAejsmPRwlFAJ0e2FKBlwoMQJDMTNBX0kYKDgqbhRtcjIoC3crJlcBIzdUPGsaQj0JIjlvc0lmmvH4eQADMVBtoNWlcBAJBwoHNig8Ykk3HQMsPD9KMFYnLTxffysOEkdOdm0LIQw3LwM7KW1XYkc/NzARLWprIRs+YAwrKiUlGhQ2cTZKFlY1NnUMcGGD4stMGSIhKAAjC1G42dlKEVI7J3pdPyIFQhkePz4qOkk0Ch48MCEPMR1vbnV1PyYSNRsNKm1ybh02DRR6JGRgAUEfeBRVNA8AAAwAcjZvGgw8DFFneW+IwpFtETBFJCoPBRpMuM3bbjwNWAEoPCsZbhMsISFYPy1BCgYYMSg2PUVkDBk/NChEYB9tBjpUIxQTAxlMZ207PBwhWAxzU0dHbxOv1tXTxMOD9ulMDgwNbl5kmvHOeR4vFmcEDBJicKH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wjkhLTZQPGMyBx0genBvGggmC18JPDkeK10qMW9wNCctBw8YHT8gOxkmFwlyewQENlY/JDRSNWFNQksBNSMmOgY2WlhQCigeDgkMJjF9MSEEDkEXehkqNh1kRVF4DyQZN1IhYiVDNSUEEAwCOSg8bg8rClEuMShKL1YjN3VYJDAEDg9CeGFvCgYhCyYoOD1KfxM5MCBUcD5IaDoJLgF1Dw0gPBgsMCkPMBtkSAZUJA9bIw0IDiIoKQUhUFMJMSIdAUY+NjpcEzYTEQYeeGFvNUkQHQkueXBKYHA4MSFePWMiFxsfNT9tYkkAHRc7LCEeYg5tNidENW9rQklMeg4uIgUmGRIxeXBKJEYjISFYPy1JFEBMFiQtPAg2AV8JMSIdAUY+NjpcEzYTEQYeenBvOEkhFhV6JGRgEVY5Dm9wNCctAwsJNmVtDRw2Cx4oeQ4FLlw/YHwLEScFIQYANT8fJwovHQNyew4fMEAiMBZePCwTQEVMIUdvbklkPBQ8ODgGNhNwYhZePiUIBUctGQ4KAD1oWCUzLSEPYg5tYBZEIjAOEEkvNSEgPEtoclF6eW0pI18hIDRSO2NcQg8ZNC47JwYqUBJzeQEDIEEsMCwLAyYVIRweKSI9DQYoFwNyOmRKJ10pYigYWhAEFiVWGykrChsrCBU1LiNCYH0iNjxXKRAIBgxOdm00bj8lFAQ/Km1XYkhtYBlUNjdDTklOCCQoJh1mWAx2eQkPJFI4LiERbWNDMAALMjltYkkQHQkueXBKYH0iNjxXOSAAFgADNG08Jw0hWl1QeW1KYnAsLjlTMSAKQlRMPDghLR0tFx9yL2RKDlovMDRDKXkyBx0iNTkmKBAXERU/cTtDYlYjJnVMeUkyBx0gYAwrKi02FwE+NjoEahEYCwZSMS8EQEVMIW0ZLwUxHQJ6ZG0RYhF6d3ATfGFQUllJeGFtf1txXVN2e3xfchZvYigdcAcEBAgZNjlvc0lmSUFqfG9GYmcoOiERbWNDNyBMCS4uIgxmVHt6eW1KAVIhLjdQMyhBX0kKLyMsOgArFlkscG0mK1E/IydIahAEFi08Ex4sLwUhUAU1NzgHIFY/aiMLNzAUAEFOf2htYktmUVhzeSgEJhMwa19iNTctWCgIPgkmOAAgHQNycEc5J0cBeBRVNA8AAAwAcm8CKwcxWDo/IC8DLFdva29wNCcqBxA8My4kKxtsWjw/NzghJ0ovKztVcm9BGUkoPysuOwUwWEx6GiIEJFoqbAF+FwQtJzYnHxRjbicrLTh6ZG0eMEYobnVlNTsVQlRMeBkgKQ4oHVEXPCMfYBMwa19iNTctWCgIPgkmOAAgHQNycEc5J0cBeBRVNAEUFh0DNGU0bj0hAAV6ZG1IF10hLTRVcAsUAEtAegkgOwsoHTI2MC4BYg5tNidENW9rQklMehkgIQUwEQF6ZG1IEFYgLSNUI2MVCgxMDwRvLwcgWBUzKi4FLF0oISFCcCYXBxsVLiUmIA5qWl1QeW1KYnU4LDYRbWMHFwcPLiQgIEFtWC4ddxRYCWwKAxJuGBYjPSUjGwkKCkl5WB8zNXZKDlovMDRDKXk0DAUDOylnZ0khFhV6JGRgSF8iITRdcBAEFjtMZ20bLws3ViI/LTkDLFQ+eBRVNBEIBQEYHT8gOxkmFwlyewwJNloiLHV5PzcKBxAfeGFvbAIhAVNzUx4PNmF3AzFVHCIDBwVEIW0bKxEwWEx6exwfK1AmYj5UKTBBBAYeeiIhK0Q3EB4ueSwJNloiLCYfcm9BJgYJKRo9LxlkRVEuKzgPYk5kSAZUJBFbIw0IHiQ5Jw0hCllzUx4PNmF3AzFVHCIDBwVEeB4qIgVkHh41PW9DeHIpJh5UKRMIAQIJKGVtBgYwExQjCigGLhFhYi47cGNBQi0JPCw6Ih1kRVF4Hm9GYn4iJjARbWNDNgYLPSEqbEVkLBQiLW1XYhEeJzldcm9rQklMeg4uIgUmGRIxeXBKJEYjISFYPy1JAwoYMzsqZ0ktHlE7OjkDNFZtNj1UPmMzBwQDLig8YA8tChRyex4PLl8LLTpVcmpaQicDLiQpN0FmMB4uMigTYB9vETBdPG1DS0kJNClvKwcgWAxzUx4PNmF3AzFVHCIDBwVEeBouOgw2WBY7KykPLEBva29wNCcqBxA8My4kKxtsWjk1LSYPO2QsNjBDcm9BGWNMem1vCgwiGQQ2LW1XYhEFYHkRHSwFB0lRem8bIQ4jFBR4dW0+J0s5YmgRchQAFgweeGFFbklkWDI7NSEII1AmYmgRNjYPAR0FNSNnLwowEQc/cG0DJBMsISFYJiZBFgEJNG0dKwQrDBQpdyQENFwmJ30TByIVBxsrOz8rKwc3WlhheQMFNlorO30TGCwVCQwVeGFtGQgwHQN0e2RKJ10pYjBfNGMcS2M/PzkddCggHD07OygGahEZLTJWPCZBIxwYNW0fIggqDFNzYwwOJngoOwVYMygEEEFOEiI7JQw9KB07NzlIbhM2SHURcGMlBw8NLyE7blRkWiF4dW0nLVcoYmgRchcOBQ4AP29jbj0hAAV6ZG1IEl8sLCETfElBQklMGSwjIgslGxp6ZG0MN10uNjxePmsAAR0FLChmRElkWFF6eW1KK1VtIzZFOTUEQh0EPyNFbklkWFF6eW1KYhNtKzMRETYVDS4NKCkqIEcXDBAuPGMLN0ciEjlQPjdBFgEJNG0OOx0rPxAoPSgEbEA5LSVwJTcOMgUNNDlnZ1JkNh4uMCsTahEFLSFaNTpDTks8NiwhOkkLPjd4cEdKYhNtYnURcGNBQkkJNj4qbigxDB4dOD8OJ11jMSFQIjcgFx0DCiEuIB1sUUp6FyIeK1U0and5PzcKBxBOdm8fIggqDFEVF29DYlYjJl8RcGNBQklMeighKmNkWFF6PCMOYk5kSAZUJBFbIw0IFiwtKwVsWiM/OiwGLhM+IyNUNGMRDRpOc3cOKg0PHQgKMC4BJ0FlYB1eJCgEGzsJOSwjIktoWApQeW1KYncoJDREPDdBX0lOCG9jbiQrHBR6ZG1IFlwqJTlUcm9BNgwULm1ybksWHRI7NSFIbjltYnUREyINDgsNOSZvc0kiDR85LSQFLBssISFYJiZIQgAKeiwsOgAyHVEuMSgEYn4iNDBcNS0VTBsJOSwjIjkrC1lzYm0kLUckJCwZcgsOFgIJI29jbDshGxA2NSgObBFkYjBfNGMEDA1MJ2RFRCUtGgM7KzREFlwqJTlUGyYYAAACPm1ybiY0DBg1Nz5ED1YjNx5UKSEIDA1mUGBibovQ+JPO2a/+whMZKjBcNWNKQjoNLChvLw0gFx8pea/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0KH14ov42q/bzovQ+JPO2a/+wtHZwrel0EkIBEk4MigiKyQlFhA9PD9KI10pYgZQJiYsAwcNPSg9bh0sHR9QeW1KYmclJzhUHSIPAw4JKHccKx0IERMoOD8Tan8kICdQIjpIaElMem0cLx8hNRA0OCoPMAkeJyF9OSETAxsVcgEmLBslCghzU21KYhMeIyNUHSIPAw4JKHcGKQcrChQOMSgHJ2AoNiFYPiQSSkBmem1vbjolDhQXOCMLJVY/eAZUJAoGDAYePwQhKgw8HQJyIm1ID1YjNx5UKSEIDA1OejBmRElkWFEOMSgHJ34sLDRWNTFbMQwYHCIjKgw2UDI1NysDJR0eAwN0DxEuLT1FUG1vbkkXGQc/FCwEI1QoMG9iNTcnDQUIPz9nDQYqHhg9dx4rFHYSARN2A2prQklMeh4uOAwJGR87PigYeHE4KzlVEywPBAALCSgsOgArFlkOOC8ZbHAiLDNYNzBIaElMem0bJgwpHTw7NywNJ0F3AyVBPDo1DT0NOGUbLws3ViI/LTkDLFQ+a18RcGNBEgoNNiFnKBwqGwUzNiNCaxMeIyNUHSIPAw4JKHcDIQggOQQuNiEFI1cOLTtXOSRJS0kJNClmRAwqHHtQFyIeK1U0andoYghBKhwOeGFvbCUrGRU/PW0MLUFtYHUffmMiDQcKMyphCSgJPS4UGAAvYh1jYncfcBMTBxofeh8mKQEwOwUoNW0eLRM5LTJWPCZPQEBmKj8mIB1sUFMBAH8hHxMBLTRVNSdBBAYeemg8bkEUFBA5PAQOYhYpa3sTeXkHDRsBOzlnDQYqHhg9dworD3YSDBR8FW9BIQYCPCQoYDkIOTIfBgQuaxpH'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
