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

local __k = 'tKitjcHHYlKr1YoJbauNdS1l'
local __p = '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GHlFahERBysFNxFGVCkIBw9pLSY9ZkEURDcMPgsOG24xJ1gAB2UOER4wIC06BycXQnFGQEJBVW4IPFINGGsFB0peaAQ2DyoeYTUOMwcTTwgNPVUqHTkaACkLISQ9RGkeVDgLLxASAS8QIBNFfmtJVEoKLmg1H2sGWTwBQEJBVW5EcxFMGCQKFQZDOyB5UWseQmMpIwwFMycWIEUvHCIFEEJBGyA8DyAeVCpNY2hBVW5EcxFMVCIPVBkLaDwxCSVSQzwbPxAPVToLIEUeHSUOXBkLZh44AD4XGHkKJAZrVW5Ec1QCEEFJVEpDOi0tGTkcEXtCaGgEGypuWRxBVKn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/EFfHHlcZEIzMAMrB3Q/fmZEVIj22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/Knnobv62oD05azxw9P55Kn85Ij22KrM/KnnoVMDJQEAGW42NlwDAC4aVFdDM2gGDyoRWTxPd0IaCGJEDFQaESUdB0peaCYwAGsPO1MDJQEAGW4CJl8PACIGGkoGPi03GDhaGFNPakJBHChEAVQBGz8MB0Q8LT48Aj8BETgBLkIzECMLJ1QfWhQMAg8NPDt3PCoAVDcbahYJECBEIVQYATkHVDgGJSctCThcbjwZLwwVBm4BPVVmVGtJVDgGJSctCThcbjwZLwwVBm5Zc2QY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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-0bpLF61hiK2t
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, watermark = 'Y2k-0bpLF61hiK2t', neuterAC = true, antiSpy = { kick = true, halt = true } })
