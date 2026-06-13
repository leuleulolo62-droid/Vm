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

local __k = 'AQjXOzbS06QPhS0wB6EGRUsK'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, antiSpy = { kick = true, halt = true } })
