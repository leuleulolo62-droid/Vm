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

local __k = 'RnsDEtThBnKwuEo4aSTxzIfU'
local __p = 'f0MoH0+Wwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/55ZGVUdC8QIRxXNGUodTMXETZaaYTVxk5THXc/dCAXLGtXA3RBBE9jdFhaaUZ1ck5TZGVUdEhiTmtXVWVPFEFzfAsTJwE5N0MVLSkRdAo3BycTXE9PFEFzBAoVLRM2JgccKmgFIQkuBz8OVSQaQA5+MxkILQM7cgYGJmUSOxpiPicWFiAmUEFiZk5CcVJja1tFd3FEYl5iRh8fEGUoVRM3MRZaDgc4N0d5ZGVUdD0LVGtXVWUgVhI6MBEbJzM8ckYqdg5UBwswBzsDVQcOVwphFhkZIk9fck5TZBYALQQnVGs6GiEKRg9zOh0VJ0YMYCVfZDYZOwc2BmsDAiAKWhJ/dB4PJQp1IQ8FIWoAPA0vC2sEADUfWxMnXnJaaUZ1Azs6Bw5UBzwDPB9Xl8X7FBEyJwwfaQ87JgFTJSsNdDotDCcYDWUKTAQwIQwVO0Y0PApTNjAaemJITmtXVQMKVRUmJh0JaU5ichoSJjZdbmJiTmtXVWWNtMNzExkILQM7ck5TZKf0wEgDGz8YVTUDVQ8ndFdaIQcnJAsAMGVbdAstAicSFjFPG0EgPBcMLAp1MQIWJSsBJGJiTmtXVWWNtMNzBxAVOUZ1ck5TZKf0wEgDGz8YVScaTUEgMR0eOkZ6cgkWJTdUe0gnCSwEVWpPVw4gOR0OIAUmfk4BITYAOwspTj8eGCAdPkFzdFhaaYTV8E4jITEHdEhiTmtXl8X7FCkyIBsSaQMyNR1fZCAFIQEyQTgSGSlPRAQnJ1RaKAEwcgwcKzYAJ0RiCCoBGjcGQARzOR8XPWx1ck5TZGWW1MpiPicWDCAdFEFzdJr63UYCMwIYFzURMQxiQWs9ACgfFE5zHRYcAxM4Ik5cZAsbNwQrHmtYVQMDTUF8dDkUPQ94Eyg4ZGpUADgxZGtXVWVPFIPT9lg3IBU2ck5TZGVUtujWTgceAyBPZwk2NxMWLBV5ch0HJTEHeEgxCzkBEDdPXA4jewofIwk8PGRTZGVUdEig7ulXNioBUgg0J1haaYTVxk4gJTMRGQksDywSB2UfRgQgMQxaOgo6Jh15ZGVUdEhijMvVVRYKQBU6Oh8JaUa30vpTEQxUJBonCDhXXmUOVxU6OxZaIQkhOQsKN2VfdBwqCyYSVTUGVwo2JnJwaUZ1cisFITcNdAQtATtXHSQcFAgnJ1gVPgh1OwAHITcCNQRiHSceESAdGkEWIh0IMEYmNw0HLSoadA06HicWHCscFAgnJx0WL0hfsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qQzsIWGQaImUrE0YbXAAoMgQoaykGFic2BicRFypTMC0ROmJiTmtXAiQdWklxDyFIAkYdJwwuZAQYJg0jCjJXGSoOUAQ3dJr63UY2MwIfZAkdNhojHDJNICsDWwA3fFFaLw8nIRpdZmx+dEhiTjkSATAdWms2OhxwFiF7C1w4GwI1EzcKOwkoOQoucCQXdEVaPRQgN2R5KCoXNQRiPicWDCAdR0FzdFhaaUZ1ck5TeWUTNQUnVAwSARYKRhc6Nx1SazY5MxcWNjZWfWIuASgWGWU9URE/PRsbPQMxARocNiQTMUh/TiwWGCBVcwQnBx0IPw82N0ZRFiAEOAEhDz8SERYbWxMyMx1YYGw5PQ0SKGUmIQYRCzkBHCYKFEFzdFhaaUZocgkSKSBOEw02PS4FAywMUUlxBg0UGgMnJAcQIWddXgQtDSobVRIARgogJBkZLEZ1ck5TZGVUdFViCSoaEH8oURUAMQoMIAUwekwkKzcfJxgjDS5VXE8DWwIyOFgvOgMnGwADMTEnMRo0BygSVWVSFAYyOR1ADgMhAQsBMiwXMUBgOzgSBwwBRBQnBx0IPw82N0xaTikbNwkuTgceEi0bXQ80dFhaaUZ1ck5TZHhUMwkvC3EwEDE8URMlPRsfYUQZOwkbMCwaM0prZCcYFiQDFDc6JgwPKAoAIQsBZGVUdEhiTnZXEiQCUVsUMQwpLBQjOw0WbGciPRo2GyobIDYKRkN6XhQVKgc5ciIcJyQYBAQjFy4FVWVPFEFzdEVaGQo0KwsBN2s4OwsjAhsbFDwKRmtZPR5aJwkhcgkSKSBOHRsOASoTECFHHUEnPB0UaQE0PwtdCCoVMA0mVBwWHDFHHUE2OhxwQ0t4cozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/kFaWGVeGkEQGzY8ACFff0NTptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nfykAVwA/dDsVJwA8NU5OZD4JXistAC0eEmsodSwWCzY7BCN1clNTZgIGOx9iD2swFDcLUQ9xXjsVJwA8NUAjCAQ3ETcLKmtXVXhPBVNlbEBOf19gZF1HdHNCXistAC0eEmssZiQSADcoaUZ1clNTZhEcMUgFDzkTECtPcwA+MVpwCgk7NAcUahY3BiESOhQhMBdPCUFxZVZKZ1Z3WC0cKiMdM0YXJxQlMBUgFEFzdEVaaw4hJh4AfmpbJgk1QCweAS0aVhQgMQoZJgghNwAHaiYbOUcbXCAkFjcGRBURNRsReyQ0MQVcCycHPQwrDyUiHGoCVQg9e1pwCgk7NAcUahY1Ai0dPAQ4IWVPCUFxEwoVPicSMxwXIStWXistAC0eEms8dTcWCzs8DjV1clNTZgIGOx8DKSoFESABGwI8Oh4TLhV3WC0cKiMdM0YWIQwwOQAwfyQKdEVaazQ8NQYHByoaIBotAml9NioBUgg0ejk5CiMbBk5TZGVUaUgBAScYB3ZBUhM8OSo9C05lfk5BdXVYdFpwV2J9f2hCFCYyOR1aLBAwPBoAZCkdIg1iGyUTEDdPZgQjOBEZKBIwNj0HKzcVMw1sKSoaEAAZUQ8nJ3I5JggzOwldARMxGjwRMRs2IQ1PCUFxBh0KJQ82MxoWIBYAOxojCS5ZMiQCUSQlMRYOOkRfWENeZA4aOx8sTjkSGCobUUE/MRkcaQg0PwsAZG0CMRorCCISEWUJRg4+dAwSLEY5OxgWZCIVOQ1rZAgYGyMGU08BETU1HSMGclNTP09UdEhiPicWGzFPFEFzdFhaaUZ1ck5TZHhUdjguDyUDKhcqFk1ZdFhaaS40IBgWNzFUdEhiTmtXVWVPFEFudFoyKBQjNx0HFiAZOxwnTGd9VWVPFDYyIB0IDgcnNgsdN2VUdEhiTmtKVWc4VRU2JiEVPBQSMxwXISsHdkRITmtXVQMKRhU6OBEALBR1ck5TZGVUdEh/TmkxEDcbXQ06Lh0IGgMnJAcQIRomEUpuZGtXVWU8UQ0/EhcVLUZ1ck5TZGVUdEhiU2tVJiADWCc8OxwlGyN3fmRTZGVUBw0uAhsSAWVPFEFzdFhaaUZ1clNTZhYROAQSCz8oJwBNGGtzdFhaGgM5Pi8fKBURIBtiTmtXVWVPFFxzdisfJQoUPgIjITEHCzoHTGd9VWVPFCMmLSsfLAJ1ck5TZGVUdEhiTmtKVWctQRgAMR0eGhI6MQVRaE9UdEhiLD4OMiAORkFzdFhaaUZ1ck5TZHhUdio3FwwSFDc8QA4wP1pWQ0Z1ck4xMTwkMRwHCSxXVWVPFEFzdFhadEZ3EBsKFCAAEQ8lTGd9VWVPFCMmLTwbIAosAQsWIBYcOxhiTmtKVWctQRgXNREWMDUwNwogLCoEBxwtDSBVWU9PFEFzFg0DDBAwPBogLCoEdEhiTmtXVXhPFiMmLT0MLAghAQYcNBYAOwspTGd9VWVPFCMmLSwIKBAwPgcdI2VUdEhiTmtKVWctQRgHJhkMLAo8PAk+ITcXPAksGhgfGjU8QA4wP1pWQ0Z1ck4xMTwzNRomCyU0GiwBZwk8JFhadEZ3EBsKAyQGMA0sLSQeGxYHWxEAIBcZIkR5WE5TZGU2IREMBywfAQAZUQ8nBxAVOUZ1b05RBjANGgElBj8yAyABQDI7OwgpPQk2OUxfTmVUdEgAGzIyFDYbURMAIBcZIkZ1ck5TeWVWFh07KyoEASAdZxU8NxNYZWx1ck5TBjANFwcxAy4DHCYmQAQ+dFhaaVt1cCwGPQYbJwUnGiIUPDEKWUN/XlhaaUYXJxcwKzYZMRwrDQgFFDEKFEFzaVhYCxMsEQEAKSAAPQsBHCoDEGdDPkFzdFg4PB8WPR0eITEdNy4nACgSVWVPCUFxFg0DCgkmPwsHLSYyMQYhC2lbf2VPFEERIQEoLAQ8IBobZGVUdEhiTmtXSGVNdhQqBh0YIBQhOkxfTmVUdEgEDz0YBywbUSgnMRVaaUZ1ck5TeWVWEgk0ATkeASAwfRU2OVpWQ0Z1ck41JTMbJgE2Cx8YGilPFEFzdFhadEZ3FA8FKzcdIA0WASQbJyACWxU2dlRwaUZ1cj4WMDYnMRo0BygSVWVPFEFzdFhHaUQFNxoAFyAGIgEhC2lbf2VPFEESNwwTPwMFNxogITcCPQsnTmtXSGVNdQInPQ4fGQMhAQsBMiwXMUpuZGtXVWU/URUWMx8pLBQjOw0WZGVUdEhiU2tVJSAbcQY0Bx0IPw82N0xfTmVUdEgBAioeGCQNWAQQOxwfaUZ1ck5TeWVWFwQjByYWFykKdw43MSsfOxA8MQtRaE9UdEhiLygUEDUbZAQnExEcPUZ1ck5TZHhUdikhDS4HARUKQCY6MgxYZWx1ck5TFCkVOhwRCy4TNCsGWUFzdFhaaVt1cD4fJSsABw0nCgoZHCgOQAg8OlpWQ0Z1ck4wKykYMQs2LycbNCsGWUFzdFhadEZ3EQEfKCAXICkuAgoZHCgOQAg8OlpWQ0Z1ck4nNjw8NRo0CzgDNyQcXwQndFhadEZ3BhwKDCQGIg0xGgkWBi4KQEN/XgVwQ0t4ci0cICAHdEAhASYaACsGQBh+PxYVPgh5chwWIjcRJwAnCmsFECIaWAAhOAFaKx91NgsFN2x+FwcsCCIQWwYgcCQAdEVaMmx1ck5TZg87DUpuTmkgPQAhfTIEFS4/cER5ckwkDAA6HTsVLx0yTWdDFEMEHD00ADUCEzg2c2dYdEoEPAQkIQArFk1ZdFhaaUQTHSlRaGVWAyEQKw9VWWVNczMcAzk9BikRcEJTZgImGz9gQmtVJwA8cTVxeFhYHyMHCyw2FhctdkRITmtXVWcteC4cGSFYZUZ3HyE8CnRWeEhgXwY+OWdDFENiGTE2BS8aHExfZGcmFSEMTGdXVwsqY0N/XgVwQ0t4cozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/kFaWGVdGkEGADE2Gmx4f06R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9t9GSoMVQ1zAQwTJRV1b04IOU9+Mh0sDT8eGitPYRU6OAtUOwMmPQIFIRUVIABqHioDHWxlFEFzdBQVKgc5cg0GNmVJdA8jAy59VWVPFAc8JlgJLAF1OwBTNCQAPFIlAyoDFi1HFjoNcVYnYkR8cgocTmVUdEhiTmtXHCNPWg4ndBsPO0YhOgsdZDcRIB0wAGsZHClPUQ83XlhaaUZ1ck5TJzAGdFViDT4FTwMGWgUVPQoJPSU9OwIXbDYRM0FITmtXVSABUGtzdFhaOwMhJxwdZCYBJmInAC99fyMaWgInPRcUaTMhOwIAaiIRICsqDzlfXE9PFEFzOBcZKAp1MQYSNmVJdCQtDSobJSkOTQQhejsSKBQ0MRoWNk9UdEhiBy1XGyobFAI7NQpaPQ4wPE4BITEBJgZiACIbVSABUGtzdFhaJQk2MwJTLDcEdFViDSMWB38pXQ83EhEIOhIWOgcfIG1WHB0vDyUYHCE9Ww4nBBkIPUR8WE5TZGUYOwsjAmsfAChPCUEwPBkIcyA8PAo1LTcHICsqBycTOiMsWAAgJ1BYARM4MwAcLSFWfWJiTmtXHCNPXBMjdBkULUY9JwNTMC0ROkgwCz8CBytPVwkyJlRaIRQlfk4bMShUMQYmZGtXVWUdURUmJhZaJw85WAsdIE9+Mh0sDT8eGitPYRU6OAtUPQM5Nx4cNjFcJAcxR0FXVWVPWA4wNRRaFkp1OhwDZHhUARwrAjhZEiAbdwkyJlBTQ0Z1ck4aImUcJhhiDyUTVTUAR0EnPB0UaQ4nIkAwAjcVOQ1iU2s0MzcOWQR9Oh0NYRY6IUdIZDcRIB0wAGsDBzAKFAQ9MHJaaUZ1IAsHMTcadA4jAjgSfyABUGtZMg0UKhI8PQBTETEdOBtsAiQYBW0IURUaOgwfOxA0PkJTNjAaOgEsCWdXEytGPkFzdFgOKBU+fB0DJTIafA43ACgDHCoBHEhZdFhaaUZ1ck4ELCwYMUgwGyUZHCsIHEhzMBdwaUZ1ck5TZGVUdEhiAiQUFClPWwp/dB0IO0Zoch4QJSkYfA4sR0FXVWVPFEFzdFhaaUY8NE4dKzFUOwNiGiMSG2UYVRM9fFohEFQeD04fKyoEbkhgTmVZVTEARxUhPRYdYQMnIEdaZCAaMGJiTmtXVWVPFEFzdFgWJgU0Pk4XMGVJdBw7Hi5fEiAbfQ8nMQoMKAp8clNOZGcSIQYhGiIYG2dPVQ83dB8fPS87JgsBMiQYfEFiATlXEiAbfQ8nMQoMKApfck5TZGVUdEhiTmtXASQcX08kNREOYQIhe2RTZGVUdEhiTi4ZEU9PFEFzMRYeYGwwPAp5TiMBOgs2ByQZVRAbXQ0gehITPRIwIEYRJTYReEgxHjkSFCFGPkFzdFgJORQwMwpTeWUHJBonDy9XGjdPBE9iYXJaaUZ1IAsHMTcadAojHS5XXmVHWQAnPFYIKAgxPQNbbWVedFpiQ2tGXGVFFBIjJh0bLUZ/cgwSNyB+MQYmZEERACsMQAg8OlgvPQ85IUAUITEnPA0hBScSBm1GPkFzdFgWJgU0Pk4fN2VJdCQtDSobJSkOTQQhbj4TJwITOxwAMAYcPQQmRmkbECQLURMgIBkOOkR8WE5TZGUdMkguHWsDHSABPkFzdFhaaUZ1PgEQJSlUJwBiU2sbBn8pXQ83EhEIOhIWOgcfIG1WBwAnDSAbEDZNHWtzdFhaaUZ1cgcVZDYcdBwqCyVXByAbQRM9dAwVOhInOwAUbDYcej4jAj4SXGUKWgVZdFhaaQM7NmRTZGVUJg02GzkZVWdCFms2OhxwQ0t4cozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/kFaWGVcGkEBETU1HSMGWENeZKfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5U8DWwIyOFgoLAs6JgsAZHhUL0gdDSoUHSBPCUEoKVRaFgMjNwAHN2VJdAYrAmsKf08DWwIyOFgcPAg2JgccKmURIg0sGjhfXE9PFEFzPR5aGwM4PRoWN2srMR4nAD8EVSQBUEEBMRUVPQMmfDEWMiAaIBtsPioFECsbFBU7MRZaOwMhJxwdZBcROQc2CzhZKiAZUQ8nJ1gfJwJfck5TZBcROQc2CzhZKiAZUQ8nJ1hHaTMhOwIAajcRJwcuGC4nFDEHHCI8Oh4TLkgQBCs9EBYrBCkWJmJ9VWVPFBM2IA0IJ0YHNwMcMCAHejcnGC4ZATZlUQ83XnIcPAg2JgccKmUmMQUtGi4EWyIKQEk4MQFTQ0Z1ck4aImUmMQUtGi4EWxoMVQI7MSMRLB8Icg8dIGUmMQUtGi4EWxoMVQI7MSMRLB8IfD4SNiAaIEg2Bi4ZVTcKQBQhOlgoLAs6JgsAahoXNQsqCxAcEDwyFAQ9MHJaaUZ1PgEQJSlUOgkvC2tKVQYAWgc6M1YoDCsaBisgHy4RLTViATlXHiAWPkFzdFgWJgU0Pk4WMmVJdA00CyUDBm1GD0E6MlgUJhJ1NxhTMC0ROkgwCz8CBytPWgg/dB0ULWx1ck5TKCoXNQRiHGtKVSAZDic6Ohw8IBQmJi0bLSkQfAYjAy5ef2VPFEE6MlgIaRI9NwBTFiAZOxwnHWUoFiQMXAQIPx0DFEZochxTISsQXkhiTmsFEDEaRg9zJnIfJwJfWAgGKiYAPQcsThkSGCobURJ9MhEILE4+NxdfZGtaekFITmtXVSkAVwA/dApadEYHNwMcMCAHeg8nGmMcEDxGD0E6MlgUJhJ1IE4HLCAadBonGj4FG2UJVQ0gMVgfJwJfck5TZCkbNwkuTioFEjZPCUEnNRoWLEglMw0YbGtaekFITmtXVSkAVwA/dBcRaVt1Ig0SKClcMh0sDT8eGitHHUEhbj4TOwMGNxwFITdcIAkgAi5ZACsfVQI4fBkILhV5cl9fZCQGMxtsAGJeVSABUEhZdFhaaRQwJhsBKmUbP2InAC99fyMaWgInPRcUaTQwPwEHITZaPQY0ASASXS4KTU1zelZUYGx1ck5TKCoXNQRiHGtKVRcKWQ4nMQtULgMhegUWPWxPdAEkTiUYAWUdFBU7MRZaOwMhJxwdZCMVOBsnTi4ZEU9PFEFzOBcZKAp1MxwUN2VJdBwjDCcSWzUOVwp7elZUYGx1ck5TKCoXNQRiHC4EACkbR0FudANaOQU0PgJbIjAaNxwrASVfXGUdURUmJhZaO1wcPBgcLyAnMRo0CzlfASQNWAR9IRYKKAU+eg8BIzZYdFluTioFEjZBWkh6dB0ULU91L2RTZGVUPQ5iACQDVTcKRxQ/IAsheDt1JgYWKmUGMRw3HCVXEyQDRwRzMRYeQ0Z1ck4HJScYMUYwCyYYAyBHRgQgIRQOOkp1Y0d5ZGVUdBonGj4FG2UbRhQ2eFgOKAQ5N0AGKjUVNwNqHC4EACkbR0hZMRYeQ2x4f06R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9t9WGhPAE9zEjkoBEYHFz08CBAgHScMTmMRHCsLFBE/NQEfO0EmcgEEKiAQdA4jHCZXHCtPQw4hPwsKKAUwe2ReaWWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NVlWA4wNRRaDwcnP05OZD4JXgQtDSobVRoJVRM+eFglJQcmJjwWNyoYIg1iU2sZHClDFFFZXh4PJwUhOwEdZAMVJgVsHC4EGikZUUl6XlhaaUY8NE4sIiQGOUgjAC9XKiMORgx9BBkILAghcg8dIGUAPQspRmJXWGUwWAAgICofOgk5JAtTeGVBdBwqCyVXByAbQRM9dCccKBQ4cgsdIE9UdEhiAiQUFClPUgAhOQtadEYCPRwYNzUVNw14KCIZEQMGRhInFxATJQJ9cCgSNihWfWJiTmtXHCNPWg4ndB4bOwsmchobIStUJg02GzkZVSsGWEE2OhxwaUZ1cggcNmUreEgkTiIZVSwfVQghJ1AcKBQ4IVQ0ITE3PAEuCjkSG21GHUE3O3JaaUZ1ck5TZCkbNwkuTiIaBWVSFAdpEhEULSA8IB0HBy0dOAxqTAIaBSodQAA9IFpTQ0Z1ck5TZGVUOAchDydXESQbVUFudBEXOUY0PApTLSgEbi4rAC8xHDccQCI7PRQeYUQRMxoSZmx+dEhiTmtXVWUDWwIyOFgVPggwIE5OZCEVIAliDyUTVSEOQABpEhEULSA8IB0HBy0dOAxqTAQAGyAdFkhZdFhaaUZ1ck4aImUbIwYnHGsWGyFPWxY9MQpUHwc5JwtTeXhUGAchDycnGSQWURN9GhkXLEYhOgsdTmVUdEhiTmtXVWVPFD41NQoXaVt1NFVTGykVJxwQCzgYGTMKFFxzIBEZIk58WE5TZGVUdEhiTmtXVTcKQBQhOlglLwcnP2RTZGVUdEhiTi4ZEU9PFEFzMRYeQwM7NmR5aWhUFQQuTjsbFCsbFAw8MB0WOkY6PE4HLCBUMgkwA0ERACsMQAg8Olg8KBQ4fAkWMBUYNQY2HWNef2VPFEE/OxsbJUYzclNTAiQGOUYwCzgYGTMKHEhodBEcaQg6Jk4VZDEcMQZiHC4DADcBFBoudB0ULWx1ck5TKCoXNQRiByYHVXhPUlsVPRYeDw8nIRowLCwYMEBgJyYHGjcbVQ8ndlFBaQ8zcgAcMGUdORhiGiMSG2UdURUmJhZaMht1NwAXTmVUdEguASgWGWUfWAA9IAtadEY8Px5JAiwaMC4rHDgDNi0GWAV7digWKAghITEjLDwHPQsjAmlef2VPFEE6MlgUJhJ1IgISKjEHdBwqCyVXBSkOWhUgdEVaIAslaCgaKiEyPRoxGggfHCkLHEMDOBkUPRV3e04WKiF+dEhiTiIRVSsAQEEjOBkUPRV1JgYWKmUGMRw3HCVXDjhPUQ83XlhaaUYnNxoGNitUJAQjAD8ETwIKQCI7PRQeOwM7ekd5ISsQXmJvQ2s2GSlPRggjMVhVaQ40IBgWNzEVNgQnTjsbFCsbR2s1IRYZPQ86PE41JTcZeg8nGhkeBSA/WAA9IAtSYGx1ck5TKCoXNQRiAT4DVXhPTxxZdFhaaQA6IE4saGUEdAEsTiIHFCwdR0kVNQoXZwEwJj4fJSsAJ0BrR2sTGk9PFEFzdFhaaQ8zch5JDTY1fEoPAS8SGWdGFBU7MRZwaUZ1ck5TZGVUdEhiQ2ZXOSoAX0E1OwpaLxQgOxoAZGpUJBotAzsDBmUGWhI6MB1aOQo0PBpTKSoQMQRITmtXVWVPFEFzdFhaJQk2MwJTIjcBPRwxTnZXBX8pXQ83EhEIOhIWOgcfIG1WEho3Bz8EV2xlFEFzdFhaaUZ1ck5TLSNUMho3Bz8EVTEHUQ9ZdFhaaUZ1ck5TZGVUdEhiTi0YB2UwGEE1JlgTJ0Y8Ig8aNjZcMho3Bz8ETwIKQCI7PRQeOwM7ekdaZCEbdBwjDCcSWywBRwQhIFAVPBJ5cggBbWUROgxITmtXVWVPFEFzdFhaLAomN2RTZGVUdEhiTmtXVWVPFEFzeVVaGQo0PBoAZDIdIAAtGz9XEzcaXRVzMhcWLQMnIU4eJTxUJwElACobVTcGRAQ9MQsJaRA8M04SMDEGPQo3Gi59VWVPFEFzdFhaaUZ1ck5TZCwSdBh4KS4DNDEbRggxIQwfYUQHOx4WZmxUaVViGjkCEGUbXAQ9dAwbKwowfAcdNyAGIEAtGz9bVTVGFAQ9MHJaaUZ1ck5TZGVUdEgnAC99VWVPFEFzdFgfJwJfck5TZCAaMGJiTmtXByAbQRM9dBcPPWwwPAp5TiMBOgs2ByQZVQMORgx9Mx0OGhY0JQAjKzZcfWJiTmtXGSoMVQ1zMlhHaSA0IANdNiAHOwQ0C2NeTmUGUkE9OwxaL0YhOgsdZDcRIB0wAGsZHClPUQ83XlhaaUY5PQ0SKGUHJEh/Ti1NMywBUCc6JgsOCg48PgpbZhYENR8sMRsYHCsbFkhzOwpaL1wTOwAXAiwGJxwBBiIbEW1NdwQ9IB0IFjY6OwAHZmx+dEhiTiIRVTYfFAA9MFgJOVwcIS9bZgcVJw0SDzkDV2xPQAk2OlgILBIgIABTNzVaBAcxBz8eGitPUQ83Xh0ULWxfNBsdJzEdOwZiKCoFGGsIURUQMRYOLBR9e2RTZGVUOAchDydXE2VSFCcyJhVUOwMmPQIFIW1db0grCGsZGjFPUkEnPB0UaRQwJhsBKmUaPQRiCyUTf2VPFEE/OxsbJUYmIk5OZCNOEgEsCg0eBzYbdwk6OBxSayUwPBoWNhokOwEsGmlef2VPFEE6MlgJOUY0PApTNzVOHRsDRmk1FDYKZAAhIFpTaRI9NwBTNiAAIRosTjgHWxUARwgnPRcUaQM7NmRTZGVUJg02GzkZVQMORgx9Mx0OGhY0JQAjKzZcfWInAC99f2hCFIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwmReaWVBekgROgojJk9CGUGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/55KCoXNQRiPT8WATZPCUEodAgWKAghNwpTeWVEeEgqDzkBEDYbUQVzaVhKZUYmPQIXZHhUZERiDCQCEi0bFFxzZFRaOgMmIQccKhYANRo2TnZXASwMX0l6dAVwLxM7MRoaKytUBxwjGjhZByAcURV7fVgpPQchIUADKCQaIA0mQmskASQbR087NQoMLBUhNwpfZBYANRwxQDgYGSFDFDInNQwJZwQ6JwkbMGVJdFhuXmdHWXVUFDInNQwJZxUwIR0aKysnIAkwGmtKVTEGVwp7fVgfJwJfNBsdJzEdOwZiPT8WATZBQREnPRUfYU9fck5TZCkbNwkuTjhXSGUCVRU7eh4WJgknehoaJy5cfUhvThgDFDEcGhI2JwsTJggGJg8BMGx+dEhiTicYFiQDFAlzaVgXKBI9fAgfKyoGfBtiQWtEQ3VfHVpzJ1hHaRV1f04bZG9UZ15yXkFXVWVPWA4wNRRaJEZocgMSMC1aMgQtATlfBmVAFFdjfUNaaUYmclNTN2VZdAViRGtBRU9PFEFzJh0OPBQ7ch0HNiwaM0YkATkaFDFHFkRjZhxAbFZnNlRWdHcQdkRiBmdXGGlPR0hZMRYeQ2x4f06R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9t9WGhPAk9zFS0uBkYSEzw3AQt+eUVijN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDXhQVKgc5ci8GMCozNRomCyVXSGUUFDInNQwfaVt1KWRTZGVUNR02ARsbFCsbFEFzdEVaLwc5IQtfZDUYNQY2PS4SEWVPFEFzaVgUIAp5ck4DKCQaICwnAioOVWVPCUFjek1WQ0Z1ck4SMTEbHAkwGC4EAWVPCUE1NRQJLEp1Og8BMiAHICEsGi4FAyQDFFxzZ1ZKZWx1ck5TJTAAOystAicSFjFPFFxzMhkWOgN5cg0cKCkRNxwLAD8SBzMOWEFudExUeUpfck5TZCQBIAcRCycbVWVPFEFudB4bJRUwfk4AISkYHQY2CzkBFClPFFxzZ0hWQ0Z1ck4SMTEbAwk2CzlXVWVPCUE1NRQJLEp1JQ8HITc9OhwnHD0WGWVSFFdjeHJaaUZ1MxsHKxYcOx4nAmtXVXhPUgA/Jx1WaRU9PRgWKAwaIA0wGCobVXhPBVF/dAsSJhAwPiUWITVUaUg5E2d9VWVPFAs6IAwfO0Z1ck5TZGVJdBwwGy5bfzgSPms/OxsbJUYzJwAQMCwbOkgoBz9fA2xPRgQnIQoUaScgJgE0JTcQMQZsPT8WASBBXggnIB0IaQc7Nk4mMCwYJ0YoBz8DEDdHQk1zZFZLe091PRxTMmUROgxIZGZaVQMGWgVzNVgSLAoxch0WISFUIActAmsVDGUBVQw2XhQVKgc5cggGKiYAPQcsTi0eGyE8UQQ3ABcVJU47MwMWbU9UdEhiAiQUFClPVwkyJlhHaSo6MQ8fFCkVLQ0wQAgfFDcOVxU2JnJaaUZ1PgEQJSlUNgkhBTsWFi5PCUEfOxsbJTY5MxcWNn8yPQYmKCIFBjEsXAg/MFBYCwc2OR4SJy5WfWJiTmtXGSoMVQ1zMg0UKhI8PQBTNCwXP0AyDzkSGzFGPkFzdFhaaUZ1NAEBZBpYdBxiByVXHDUOXRMgfAgbOwM7JlQ0ITE3PAEuCjkSG21GHUE3O3JaaUZ1ck5TZGVUdEgrCGsDTwwcdUlxABcVJUR8chobISt+dEhiTmtXVWVPFEFzdFhaaQo6MQ8fZCNUaUg2VAwSAQQbQBM6Ng0OLE53NExaTmVUdEhiTmtXVWVPFEFzdFgTL0YzclNOZCsVOQ1iGiMSG2UdURUmJhZaPUYwPAp5ZGVUdEhiTmtXVWVPFEFzdBEcaRJ7HA8eIX8SPQYmRmkpV2VBGkE9NRUfYEYhOgsdZDcRIB0wAGsDVSABUGtzdFhaaUZ1ck5TZGVUdEhiBy1XAWshVQw2bh4TJwJ9cEsoFyARME0fTGJXFCsLFEknejYbJANvPgEEITdcfVIkByUTXSsOWQRpOBcNLBR9e0JTdWlUIBo3C2JeVTEHUQ9zJh0OPBQ7chpTISsQXkhiTmtXVWVPFEFzdB0ULWx1ck5TZGVUdA0sCkFXVWVPUQ83XlhaaUYnNxoGNitUfAsqDzlXFCsLFBE6NxNSKg40IEdaZCoGdEAgDygcBSQMX0EyOhxaOQ82OUYRJSYfJAkhBWJefyABUGtZMg0UKhI8PQBTBTAAOy8jHC8SG2sKRRQ6JCsfLAJ9PA8eIWx+dEhiTiIRVSsAQEE9NRUfaRI9NwBTNiAAIRosTi0WGTYKFAQ9MHJaaUZ1PgEQJSlUIActAmtKVSMGWgUAMR0eHQk6PkYdJSgRfWJiTmtXHCNPWg4ndAwVJgp1JgYWKmUGMRw3HCVXEyQDRwRzMRYeQ0Z1ck4fKyYVOEghBioFVXhPeA4wNRQqJQcsNxxdBy0VJgkhGi4Ff2VPFEE6MlgOJgk5fD4SNiAaIEg8U2sUHSQdFBU7MRZwaUZ1ck5TZGUAOwcuQBsWByABQEFudBsSKBRfck5TZGVUdEg2DzgcWzIOXRV7ZFZLYGx1ck5TISsQXkhiTmsFEDEaRg9zIAoPLGwwPAp5TiMBOgs2ByQZVQQaQA4UNQoeLAh7IRoSNjE1IRwtPicWGzFHHWtzdFhaIAB1ExsHKwIVJgwnAGUkASQbUU8yIQwVGQo0PBpTMC0ROkgwCz8CBytPUQ83XlhaaUYUJxocAyQGMA0sQBgDFDEKGgAmIBcqJQc7Jk5OZDEGIQ1ITmtXVRAbXQ0gehQVJhZ9NBsdJzEdOwZqR2sFEDEaRg9zPhEOYScgJgE0JTcQMQZsPT8WASBBRA0yOgw+LAo0K0dTISsQeGJiTmtXVWVPFAcmOhsOIAk7ekdTNiAAIRosTgoCASooVRM3MRZUGhI0JgtdJTAAOzguDyUDVSABUE1zMg0UKhI8PQBbbU9UdEhiTmtXVWVPFEE/OxsbJUYmNwsXZHhUFR02AQwWByEKWk8AIBkOLEglPg8dMBYRMQxITmtXVWVPFEFzdFhaIAB1PAEHZDYRMQxiATlXBiAKUEFuaVhYa0YhOgsdZDcRIB0wAGsSGyFlFEFzdFhaaUZ1ck5TLSNUOgc2TgoCASooVRM3MRZULBcgOx4gISAQfBsnCy9eVTEHUQ9zJh0OPBQ7cgsdIE9UdEhiTmtXVWVPFEF+eVgpLAgxcg9TNCkVOhxiHC4GACAcQEEyIFgbaRY6IQcHLSoadAEsHSITEGUAQRNzMhkIJGx1ck5TZGVUdEhiTmsbGiYOWEEwMRYOLBR1b041JTcZeg8nGggSGzEKRkl6XlhaaUZ1ck5TZGVUdAEkTiUYAWUMUQ8nMQpaPQ4wPE4BITEBJgZiCyUTf2VPFEFzdFhaaUZ1ckNeZBYEJg0jCmsHGSQBQBJzJhkULQk4PhdTJTcbIQYmTj8fEGUMUQ8nMQpwaUZ1ck5TZGVUdEhiAiQUFClPXggnIB0IEUZockYeJTEcehojAC8YGG1GFExzZFZPYEZ/cl1DTmVUdEhiTmtXVWVPFA08NxkWaQw8JhoWNh9UaUhqAyoDHWsdVQ83OxVSYEZ4cl5dcWxUfkhxXkFXVWVPFEFzdFhaaUY5PQ0SKGUEOxtiU2sUECsbURNzf1gsLAUhPRxAaisRI0AoBz8DEDc3GEFjeFgQIBIhNxwpbU9UdEhiTmtXVWVPFEEBMRUVPQMmfAgaNiBcdjguDyUDV2lPRA4geFgJLAMxe2RTZGVUdEhiTmtXVWU8QAAnJ1YKJQc7JgsXZHhUBxwjGjhZBSkOWhU2MFhRaVdfck5TZGVUdEgnAC9efyABUGs1IRYZPQ86PE4yMTEbEwkwCi4ZWzYbWxESIQwVGQo0PBpbbWU1IRwtKSoFESABGjInNQwfZwcgJgEjKCQaIEh/Ti0WGTYKFAQ9MHJwLxM7MRoaKytUFR02AQwWByEKWk8gIBkIPScgJgE7JTcCMRs2RmJ9VWVPFAg1dDkPPQkSMxwXIStaBxwjGi5ZFDAbWykyJg4fOhJ1JgYWKmUGMRw3HCVXECsLPkFzdFg7PBI6FQ8BICAaejs2Dz8SWyQaQA4bNQoMLBUhclNTMDcBMWJiTmtXIDEGWBJ9OBcVOU4zJwAQMCwbOkBrTjkSATAdWkESIQwVDgcnNgsdahYANRwnQCMWBzMKRxUaOgwfOxA0Pk4WKiFYXkhiTmtXVWVPUhQ9NwwTJgh9e04BITEBJgZiLz4DGgIORgU2OlYpPQchN0ASMTEbHAkwGC4EAWUKWgV/dB4PJwUhOwEdbGx+dEhiTmtXVWVPFEFzMhcIaTl5ch4fJSsAdAEsTiIHFCwdR0kVNQoXZwEwJj4fJSsAJ0BrR2sTGk9PFEFzdFhaaUZ1ck5TZGVUPQ5iACQDVQQaQA4UNQoeLAh7ARoSMCBaNR02AQMWBzMKRxVzIBAfJ0YnNxoGNitUMQYmZGtXVWVPFEFzdFhaaUZ1ck4fKyYVOEgtBWtKVRcKWQ4nMQtUIAgjPQUWbGc8NRo0CzgDV2lPRA0yOgxTQ0Z1ck5TZGVUdEhiTmtXVWUGUkE8P1gOIQM7cj0HJTEHegAjHD0SBjEKUEFudCsOKBImfAYSNjMRJxwnCmtcVXRPUQ83XlhaaUZ1ck5TZGVUdEhiTmsDFDYEGhYyPQxSeUhlZ0d5ZGVUdEhiTmtXVWVPUQ83XlhaaUZ1ck5TISsQfWInAC99EzABVxU6OxZaCBMhPSkSNiEROkYxGiQHNDAbWykyJg4fOhJ9e04yMTEbEwkwCi4ZWxYbVRU2ehkPPQkdMxwFITYAdFViCCobBiBPUQ83XnIcPAg2JgccKmU1IRwtKSoFESABGhInNQoOCBMhPS0cKCkRNxxqR0FXVWVPXQdzFQ0OJiE0IAoWKmsnIAk2C2UWADEAdw4/OB0ZPUYhOgsdZDcRIB0wAGsSGyFlFEFzdDkPPQkSMxwXIStaBxwjGi5ZFDAbWyI8OBQfKhJ1b04HNjARXkhiTmsiASwDR08/OxcKYQAgPA0HLSoafEFiHC4DADcBFCAmIBc9KBQxNwBdFzEVIA1sDSQbGSAMQCg9IB0IPwc5cgsdIGl+dEhiTmtXVWUJQQ8wIBEVJ058chwWMDAGOkgDGz8YMiQdUAQ9eisOKBIwfA8GMCo3OwQuCygDVSABUE1zMg0UKhI8PQBbbU9UdEhiTmtXVWVPFEF+eVgtKAo+cgEFITdUJgEyC2sRBzAGQBJzJxdaPQ4wK04SMTEbeQstAicSFjFlFEFzdFhaaUZ1ck5TKCoXNQRiMWdXHTcfFFxzAQwTJRV7NQsHBy0VJkBrZGtXVWVPFEFzdFhaaQ8zcgAcMGUcJhhiGiMSG2UdURUmJhZaLAgxWE5TZGVUdEhiTmtXVSkAVwA/dBcIIAE8PA8fZHhUPBoyQAgxByQCUWtzdFhaaUZ1ck5TZGUSOxpiMWdXEzdPXQ9zPQgbIBQmeigSNihaMw02PCIHEBUDVQ8nJ1BTYEYxPWRTZGVUdEhiTmtXVWVPFEFzPR5aJwkhci8GMCozNRomCyVZJjEOQAR9NQ0OJiU6PgIWJzFUIAAnAGsVByAOX0E2OhxwaUZ1ck5TZGVUdEhiTmtXVSwJFAchbjEJCE53EA8AIRUVJhxgR2sDHSABPkFzdFhaaUZ1ck5TZGVUdEhiTmtXHTcfGiIVJhkXLEZoci01NiQZMUYsCzxfEzdBZA4gPQwTJgh1eU4lISYAOxpxQCUSAm1fGEFgeFhKYE9fck5TZGVUdEhiTmtXVWVPFEFzdFgOKBU+fBkSLTFcZEZyVmJ9VWVPFEFzdFhaaUZ1ck5TZCAYJw0rCGsRB38mRyB7djUVLQM5cEdTJSsQdA4wQBsFHCgORhgDNQoOaRI9NwB5ZGVUdEhiTmtXVWVPFEFzdFhaaUY9IB5dBwMGNQUnTnZXNgMdVQw2ehYfPk4zIEAjNiwZNRo7PioFAWs/WxI6IBEVJ0Z+cjgWJzEbJltsAC4AXXVDFFJ/dEhTYGx1ck5TZGVUdEhiTmtXVWVPFEFzdAwbOg17JQ8aMG1Eelh6R0FXVWVPFEFzdFhaaUZ1ck5TISsQXkhiTmtXVWVPFEFzdB0ULWx1ck5TZGVUdEhiTmsfBzVBdychNRUfaVt1PRwaIywaNQRITmtXVWVPFEE2OhxTQwM7NmQVMSsXIAEtAGs2ADEAcwAhMB0UZxUhPR4yMTEbFwcuAi4UAW1GFCAmIBc9KBQxNwBdFzEVIA1sDz4DGgYAWA02NwxadEYzMwIAIWUROgxIZC0CGyYbXQ49dDkPPQkSMxwXIStaJxwjHD82ADEAZwQ/OFBTQ0Z1ck4aImU1IRwtKSoFESABGjInNQwfZwcgJgEgISkYdBwqCyVXByAbQRM9dB0ULWx1ck5TBTAAOy8jHC8SG2s8QAAnMVYbPBI6AQsfKGVJdBwwGy59VWVPFDQnPRQJZwo6PR5bIjAaNxwrASVfXGUdURUmJhZaCBMhPSkSNiEROkYRGioDEGscUQ0/HRYOLBQjMwJTISsQeGJiTmtXVWVPFAcmOhsOIAk7ekdTNiAAIRosTgoCASooVRM3MRZUGhI0JgtdJTAAOzsnAidXECsLGEE1IRYZPQ86PEZaTmVUdEhiTmtXVWVPFDM2ORcOLBV7NAcBIW1WBw0uAg0YGiFNHWtzdFhaaUZ1ck5TZGUnIAk2HWUEGikLFFxzBwwbPRV7IQEfIGVfdFlITmtXVWVPFEE2OhxTQwM7NmQVMSsXIAEtAGs2ADEAcwAhMB0UZxUhPR4yMTEbBw0uAmNeVQQaQA4UNQoeLAh7ARoSMCBaNR02ARgSGSlPCUE1NRQJLEYwPAp5TiMBOgs2ByQZVQQaQA4UNQoeLAh7IRoSNjE1IRwtOSoDEDdHHWtzdFhaIAB1ExsHKwIVJgwnAGUkASQbUU8yIQwVHgchNxxTMC0ROkgwCz8CBytPUQ83XlhaaUYUJxocAyQGMA0sQBgDFDEKGgAmIBctKBIwIE5OZDEGIQ1ITmtXVRAbXQ0gehQVJhZ9NBsdJzEdOwZqR2sFEDEaRg9zFQ0OJiE0IAoWKmsnIAk2C2UAFDEKRig9IB0IPwc5cgsdIGl+dEhiTmtXVWUJQQ8wIBEVJ058chwWMDAGOkgDGz8YMiQdUAQ9eisOKBIwfA8GMCojNRwnHGsSGyFDFAcmOhsOIAk7ekd5ZGVUdEhiTmtXVWVPZgQ+OwwfOkg8PBgcLyBcdj8jGi4FMiQdUAQ9J1pTQ0Z1ck5TZGVUMQYmR0ESGyFlUhQ9NwwTJgh1ExsHKwIVJgwnAGUEASofdRQnOy8bPQMnekdTBTAAOy8jHC8SG2s8QAAnMVYbPBI6BQ8HITdUaUgkDycEEGUKWgVZXlVXaYTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxGJvQ2tAW2UuYTUcdCsyBjZ1sO7nZCcBLRtiGSMWASAZURN0J1gbPwc8Pg8RKCBUOwZiD2sUGisJXQYmJhkYJQN1OwAHITcCNQRIQ2ZXl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qQwo6MQ8fZAQBIAcRBiQHVXhPT0EAIBkOLEZochV5ZGVUdBsnCy85FCgKR0FzdEVaMht5cg8GMConMQ0mHWtKVSMOWBI2eHJaaUZ1NQsSNgsVOQ0xTmtXSGUUSU1zNQ0OJiEwMxxTZHhUMgkuHS5bf2VPFEE2Mx80KAswIU5TZGVJdBM/QmsWADEAcQY0J1hadEYzMwIAIWl+dEhiTigYBigKQAgwJ1haaVt1NA8fNyBYXkhiTmseGzEKRhcyOFhaaUZocltddGl+dEhiTi4BECsbZwk8JFhaaVt1NA8fNyBYXkhiTmsZHCIHQEFzdFhaaUZocggSKDYReGJiTmtXATcOQgQ/PRYdaUZ1b04VJSkHMURIEzZ9fyMaWgInPRcUaScgJgEgLCoEehs2DzkDXWxlFEFzdBEcaScgJgEgLCoEejcwGyUZHCsIFBU7MRZaOwMhJxwdZCAaMGJiTmtXNDAbWzI7OwhUFhQgPAAaKiJUaUg2HD4Sf2VPFEEGIBEWOkg5PQEDbCMBOgs2ByQZXWxPRgQnIQoUaScgJgEgLCoEejs2Dz8SWywBQAQhIhkWaQM7NkJ5ZGVUdEhiTmsRACsMQAg8OlBTaRQwJhsBKmU1IRwtPSMYBWswRhQ9OhEULkYwPApfZCMBOgs2ByQZXWxlFEFzdFhaaUZ1ck5TKCoXNQRiHWtKVQQaQA4APBcKZzUhMxoWTmVUdEhiTmtXVWVPFAg1dAtUKBMhPT0WISEHdBwqCyV9VWVPFEFzdFhaaUZ1ck5TZCMbJkgdQmsZVSwBFAgjNREIOk4mfB0WISE6NQUnHWJXESplFEFzdFhaaUZ1ck5TZGVUdEhiTmslECgAQAQgeh4TOwN9cCwGPRYRMQxgQmsZXE9PFEFzdFhaaUZ1ck5TZGVUdEhiThgDFDEcGgM8IR8SPUZocj0HJTEHegotGywfAWVEFFBZdFhaaUZ1ck5TZGVUdEhiTmtXVWUbVRI4eg8bIBJ9YkBCbU9UdEhiTmtXVWVPFEFzdFhaLAgxWE5TZGVUdEhiTmtXVSABUGtzdFhaaUZ1ck5TZGUdMkgxQCoCASooUQAhdAwSLAhfck5TZGVUdEhiTmtXVWVPFAc8JlglZUY7cgcdZCwENQEwHWMEWyIKVRMdNRUfOk91NgF5ZGVUdEhiTmtXVWVPFEFzdFhaaUYHNwMcMCAHeg4rHC5fVwcaTSY2NQpYZUY7e2RTZGVUdEhiTmtXVWVPFEFzdFhaaTUhMxoAaicbIQ8qGmtKVRYbVRUgehoVPAE9Jk5YZHR+dEhiTmtXVWVPFEFzdFhaaUZ1ck4HJTYfeh8jBz9fRWteHWtzdFhaaUZ1ck5TZGVUdEhiCyUTf2VPFEFzdFhaaUZ1cgsdIE9UdEhiTmtXVWVPFEE6MlgJZwcgJgE2IyIHdBwqCyV9VWVPFEFzdFhaaUZ1ck5TZCMbJkgdQmsZVSwBFAgjNREIOk4mfAsUIwsVOQ0xR2sTGk9PFEFzdFhaaUZ1ck5TZGVUdEhiThkSGCobURJ9MhEILE53EBsKFCAAEQ8lTGdXG2xlFEFzdFhaaUZ1ck5TZGVUdEhiTmskASQbR08xOw0dIRJ1b04gMCQAJ0YgAT4QHTFPH0FiXlhaaUZ1ck5TZGVUdEhiTmtXVWVPQAAgP1YNKA8hel5ddWx+dEhiTmtXVWVPFEFzdFhaaQM7NmRTZGVUdEhiTmtXVWUKWgVZdFhaaUZ1ck5TZGVUPQ5iHWUSAyABQDI7OwhaaUYhOgsdZBcROQc2CzhZEywdUUlxFg0DDBAwPBogLCoEdkF5ThkSGCobURJ9MhEILE53EBsKASQHIA0wPT8YFi5NHUE2OhxwaUZ1ck5TZGVUdEhiBy1XBmsBXQY7IFhaaUZ1ck4HLCAadDonAyQDEDZBUgghMVBYCxMsHAcULDExIg0sGhgfGjVNHUE2OhxwaUZ1ck5TZGVUdEhiBy1XBmsbRgAlMRQTJwF1ck4HLCAadDonAyQDEDZBUgghMVBYCxMsBhwSMiAYPQYlTGJXECsLPkFzdFhaaUZ1NwAXbU8ROgxICD4ZFjEGWw9zFQ0OJjU9PR5dNzEbJEBrTgoCASo8XA4jeicIPAg7OwAUZHhUMgkuHS5XECsLPmt+eViY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dV+eUViVmVXNBA7e0EDESwpQ0t4cozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/kEbGiYOWEESIQwVGQMhIU5OZD5UBxwjGi5XSGUUPkFzdFgbPBI6AQsfKBURIBtiU2sRFCkcUU1zJx0WJTYwJicdMCAGIgkuTnZXRnVDPkFzdFgJLAo5AgsHCSwaFQ8nTnZXRGlPGUxzJx0WJUYlNxoAZDwbIQYlCzlXAS0OWkEnPBEJQxsoWGQVMSsXIAEtAGs2ADEAZAQnJ1YJLAo5EwIfbGx+dEhiThkSGCobURJ9MhEILE53AQsfKAQYODgnGjhVXE8KWgVZXh4PJwUhOwEdZAQBIAcSCz8EWzYbVRMnfFFwaUZ1cgcVZAQBIAcSCz8EWxodQQ89PRYdaRI9NwBTNiAAIRosTi4ZEU9PFEFzFQ0OJjYwJh1dGzcBOgYrACxXSGUbRhQ2XlhaaUYAJgcfN2sYOwcyRi0CGyYbXQ49fFFaOwMhJxwdZAQBIAcSCz8EWxYbVRU2egsfJQoFNxo6KjERJh4jAmsSGyFDPkFzdFhaaUZ1NBsdJzEdOwZqR2sFEDEaRg9zFQ0OJjYwJh1dGzcBOgYrACxXECsLGEE1IRYZPQ86PEZaTmVUdEhiTmtXVWVPFAg1dDkPPQkFNxoAahYANRwnQCoCASo8UQ0/BB0OOkYhOgsdTmVUdEhiTmtXVWVPFEFzdFhXZEYGNxwFITdZJwEmC2sTECYGUAQgb1gNLEY/Jx0HZCMdJg1iGiMSVTYKWA1+NRQWaQ8zchsAITdUIwksGjhXFzADX2tzdFhaaUZ1ck5TZGVUdEhiPC4aGjEKR081PQofYUQGNwIfBSkYBA02HWlef2VPFEFzdFhaaUZ1cgsdIE9UdEhiTmtXVSABUEhZMRYeQwAgPA0HLSoadCk3GiQnEDEcGhInOwhSYEYUJxocFCAAJ0YdHD4ZGywBU0FudB4bJRUwcgsdIE9+eUViLSQTEDZlUhQ9NwwTJgh1ExsHKxURIBtsHC4TECACdw43MQtSJwkhOwgKbU9UdEhiCCQFVRpDFAI8MB1aIAh1Ox4SLTcHfCstAC0eEmsseyUWB1FaLQlfck5TZGVUdEgQCyYYASAcGgc6Jh1SayU5MwceJScYMSstCi5VWWUMWwU2fXJaaUZ1ck5TZCwSdAYtGiIRDGUbXAQ9dBYVPQ8zK0ZRByoQMUpuTmkjBywKUFtzdlhUZ0Y2PQoWbWUROgxITmtXVWVPFEEnNQsRZxE0OxpbdGtAfWJiTmtXECsLPgQ9MHJwZEt1sPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SZGZaVXxBFCwcAj03DCgBWENeZKfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5U8DWwIyOFg3JhAwPwsdMGVJdBNiPT8WASBPCUEoXlhaaUYiMwIYFzURMQxiU2tFRWlPXhQ+JCgVPgMnclNTcXVYdAEsCAECGDVPCUE1NRQJLEp1PAEQKCwEdFViCCobBiBDPkFzdFgcJR91b04VJSkHMURiCCcOJjUKUQVzaVhCeUp1MwAHLQQyH0h/Tj8FACBDFAk6IBoVMUZoclxfTmVUdEgxDz0SERUAR0FudBYTJUpfL0JTGyYbOgZiU2sMCGUSPms/OxsbJUYzJwAQMCwbOkgjHjsbDA0aWQA9OxEeYU9fck5TZCkbNwkuThRbVRpDFAkmOVhHaTMhOwIAaiIRICsqDzlfXH5PXQdzOhcOaQ4gP04HLCAadBonGj4FG2UKWgVZdFhaaQ4gP0AkJSkfBxgnCy9XSGUiWxc2OR0UPUgGJg8HIWsDNQQpPTsSECFlFEFzdAgZKAo5eggGKiYAPQcsRmJXHTACGismOQgqJhEwIE5OZAgbIg0vCyUDWxYbVRU2ehIPJBYFPRkWNmUROgxrZGtXVWUfVwA/OFAcPAg2JgccKm1ddAA3A2UiBiAlQQwjBBcNLBR1b04HNjARdA0sCmJ9ECsLPgcmOhsOIAk7ciMcMiAZMQY2QDgSARIOWAoAJB0fLU4je04+KzMROQ0sGmUkASQbUU8kNRQRGhYwNwpTeWUAOwY3AykSB20ZHUE8JlhIeV11Mx4DKDw8IQUjACQeEW1GFAQ9MHIcPAg2JgccKmU5Ox4nAy4ZAWscURUZIRUKGQkiNxxbMmxUGQc0CyYSGzFBZxUyIB1UIxM4Ij4cMyAGdFViGiQZACgNURN7IlFaJhR1Z15IZCQEJAQ7Jj4aFCsAXQV7fVgfJwJfNBsdJzEdOwZiIyQBECgKWhV9Jx0OAQ8hMAELbDNdXkhiTms6GjMKWQQ9IFYpPQchN0AbLTEWOxBiU2sDGisaWQM2JlAMYEY6IE5BTmVUdEguASgWGWUwGEE7JghadEYAJgcfN2sTMRwBBioFXWxlFEFzdBEcaQ4nIk4HLCAadAAwHmUkHD8KFFxzAh0ZPQknYUAdITJcIkRiGGdXA2xPUQ83Xh0ULWwzJwAQMCwbOkgPAT0SGCABQE8gMQwzJwAfJwMDbDNdXkhiTms6GjMKWQQ9IFYpPQchN0AaKiM+IQUyTnZXA09PFEFzPR5aP0Y0PApTKioAdCUtGC4aECsbGj4wOxYUZw87NCQGKTVUIAAnAEFXVWVPFEFzdDUVPwM4NwAHahoXOwYsQCIZEw8aWRFzaVgvOgMnGwADMTEnMRo0BygSWw8aWREBMQkPLBUhaC0cKisRNxxqCD4ZFjEGWw97fXJaaUZ1ck5TZGVUdEgrCGsZGjFPeQ4lMRUfJxJ7ARoSMCBaPQYkJD4aBWUbXAQ9dAofPRMnPE4WKiF+dEhiTmtXVWVPFEFzOBcZKAp1DUJTG2lUPB0vTnZXIDEGWBJ9Mx0OCg40IEZaTmVUdEhiTmtXVWVPFAg1dBAPJEYhOgsdZC0BOVIBBioZEiA8QAAnMVA/JxM4fCYGKSQaOwEmPT8WASA7TRE2ejIPJBY8PAlaZCAaMGJiTmtXVWVPFAQ9MFFwaUZ1cgsfNyAdMkgsAT9XA2UOWgVzGRcMLAswPBpdGyYbOgZsByURPzACREEnPB0UQ0Z1ck5TZGVUGQc0CyYSGzFBawI8OhZUIAgzGBseNH8wPRshASUZECYbHEhodDUVPwM4NwAHahoXOwYsQCIZEw8aWRFzaVgUIApfck5TZCAaMGInAC99EzABVxU6OxZaBAkjNwMWKjFaJw02ICQUGSwfHBd6XlhaaUYYPRgWKSAaIEYRGioDEGsBWwI/PQhadEYjWE5TZGUdMkg0TioZEWUBWxVzGRcMLAswPBpdGyYbOgZsACQUGSwfFBU7MRZwaUZ1ck5TZGU5Ox4nAy4ZAWswVw49OlYUJgU5Ox5TeWUmIQYRCzkBHCYKGjInMQgKLAJvEQEdKiAXIEAkGyUUASwAWkl6XlhaaUZ1ck5TZGVUdAEkTiUYAWUiWxc2OR0UPUgGJg8HIWsaOwsuBztXAS0KWkEhMQwPOwh1NwAXTmVUdEhiTmtXVWVPFA08NxkWaQU9MxxTeWU4OwsjAhsbFDwKRk8QPBkIKAUhNxxIZCwSdAYtGmsUHSQdFBU7MRZaOwMhJxwdZCAaMGJiTmtXVWVPFEFzdFgcJhR1DUJTNGUdOkgrHioeBzZHVwkyJkI9LBIRNx0QISsQNQY2HWNeXGULW2tzdFhaaUZ1ck5TZGVUdEhiBy1XBX8mRyB7djobOgMFMxwHZmxUNQYmTjtZNiQBdw4/OBEeLEYhOgsdZDVaFwksLSQbGSwLUUFudB4bJRUwcgsdIE9UdEhiTmtXVWVPFEE2OhxwaUZ1ck5TZGUROgxrZGtXVWUKWBI2PR5aJwkhchhTJSsQdCUtGC4aECsbGj4wOxYUZwg6MQIaNGUAPA0sZGtXVWVPFEFzGRcMLAswPBpdGyYbOgZsACQUGSwfDiU6JxsVJwgwMRpbbX5UGQc0CyYSGzFBawI8OhZUJwk2PgcDZHhUOgEuZGtXVWUKWgVZMRYeQwo6MQ8fZCMBOgs2ByQZVTYbVRMnEhQDYU9fck5TZCkbNwkuThRbVS0dRE1zPA0XaVt1BxoaKDZaMw02LSMWB21GD0E6MlgUJhJ1OhwDZCoGdAYtGmsfAChPQAk2OlgILBIgIABTISsQXkhiTmsbGiYOWEExIlhHaS87IRoSKiYRegYnGWNVNyoLTTc2OBcZIBIscEdIZCcCeiUjFg0YByYKFFxzAh0ZPQknYUAdITJcZQ17QnoSTGleUVh6b1gYP0gDNwIcJywALUh/Th0SFjEARlJ9Oh0NYU9ucgwFahUVJg0sGmtKVS0dRGtzdFhaJQk2MwJTJiJUaUgLADgDFCsMUU89MQ9SayQ6Nhc0PTcbdkF5TikQWwgOTDU8JgkPLEZocjgWJzEbJltsAC4AXXQKDU1iMUFWeANse1VTJiJaBEh/TnoSQX5PVgZ9BBkILAghclNTLDcEXkhiTms6GjMKWQQ9IFYlKgk7PEAVKDw2AkRiIyQBECgKWhV9CxsVJwh7NAIKBgJUaUggGGdXFyJlFEFzdBAPJEgFPg8HIioGOTs2DyUTVXhPQBMmMXJaaUZ1HwEFISgROhxsMSgYGytBUg0qAQgeKBIwclNTFjAaBw0wGCIUEGs9UQ83MQopPQMlIgsXfgYbOgYnDT9fEzABVxU6OxZSYGx1ck5TZGVUdAEkTiUYAWUiWxc2OR0UPUgGJg8HIWsSOBFiGiMSG2UdURUmJhZaLAgxWE5TZGVUdEhiAiQUFClPVwA+dEVaPgknOR0DJSYReis3HDkSGzEsVQw2JhlwaUZ1ck5TZGUYOwsjAmsaVXhPYgQwIBcIekg7NxlbbU9UdEhiTmtXVSwJFDQgMQozJxYgJj0WNjMdNw14Jzg8EDwrWxY9fD0UPAt7GQsKByoQMUYVR2tXVWVPFEFzdAwSLAh1P05OZChUf0ghDyZZNgMdVQw2ejQVJg0DNw0HKzdUMQYmZGtXVWVPFEFzPR5aHBUwICcdNDAABw0wGCIUEH8mRyo2LTwVPgh9FwAGKWs/MREBAS8SWxZGFEFzdFhaaUZ1JgYWKmUZdFViA2taVSYOWU8QEgobJAN7HgEcLxMRNxwtHGsSGyFlFEFzdFhaaUY8NE4mNyAGHQYyGz8kEDcZXQI2bjEJAgMsFgEEKm0xOh0vQAASDAYAUAR9FVFaaUZ1ck5TZGUAPA0sTiZXSGUCFExzNxkXZyUTIA8eIWsmPQ8qGh0SFjEARkE2OhxwaUZ1ck5TZGUdMkgXHS4FPCsfQRUAMQoMIAUwaCcADyANEAc1AGMyGzACGio2LTsVLQN7FkdTZGVUdEhiTmsDHSABFAxzaVgXaU11MQ8eagYyJgkvC2UlHCIHQDc2NwwVO0YwPAp5ZGVUdEhiTmseE2U6RwQhHRYKPBIGNxwFLSYRbiExJS4OMSoYWkkWOg0XZy0wKy0cICBaBxgjDS5eVWVPFEEnPB0UaQt1b04eZG5UAg0hGiQFRmsBURZ7ZFRaeEp1YkdTISsQXkhiTmtXVWVPXQdzAQsfOy87IhsHFyAGIgEhC3E+Bg4KTSU8IxZSDAggP0A4ITw3OwwnQAcSEzE8XAg1IFFaPQ4wPE4eZHhUOUhvTh0SFjEARlJ9Oh0NYVZ5cl9fZHVddA0sCkFXVWVPFEFzdBEcaQt7Hw8UKiwAIQwnTnVXRWUbXAQ9dBVadEY4fDsdLTFUfkgPAT0SGCABQE8AIBkOLEgzPhcgNCARMEgnAC99VWVPFEFzdFgYP0gDNwIcJywALUh/TiZ9VWVPFEFzdFgYLkgWFBwSKSBUaUghDyZZNgMdVQw2XlhaaUYwPApaTiAaMGIuASgWGWUJQQ8wIBEVJ0YmJgEDAikNfEFITmtXVSMARkEMeFgRaQ87cgcDJSwGJ0A5TC0bDBAfUAAnMVpWawA5KywlZmlWMgQ7LAxVCGxPUA5ZdFhaaUZ1ck4fKyYVOEghTnZXOCoZUQw2OgxUFgU6PAAoLxh+dEhiTmtXVWUGUkEwdAwSLAhfck5TZGVUdEhiTmtXHCNPQBgjMRccYQV8clNOZGcmFjARDTkeBTEsWw89MRsOIAk7cE4HLCAadAt4KiIEFioBWgQwIFBTaQM5IQtTJ38wMRs2HCQOXWxPUQ83XlhaaUZ1ck5TZGVUdCUtGC4aECsbGj4wOxYUEg0IclNTKiwYXkhiTmtXVWVPUQ83XlhaaUYwPAp5ZGVUdAQtDSobVRpDFD5/dBAPJEZocjsHLSkHeg8nGggfFDdHHWtzdFhaIAB1OhseZDEcMQZiBj4aWxUDVRU1OwoXGhI0PApTeWUSNQQxC2sSGyFlUQ83Xh4PJwUhOwEdZAgbIg0vCyUDWzYKQCc/LVAMYEYYPRgWKSAaIEYRGioDEGsJWBhzaVgMckY8NE4FZDEcMQZiHT8WBzEpWBh7fVgfJRUwch0HKzUyOBFqR2sSGyFPUQ83Xh4PJwUhOwEdZAgbIg0vCyUDWzYKQCc/LSsKLAMxehhaZAgbIg0vCyUDWxYbVRU2eh4WMDUlNwsXZHhUIAcsGyYVEDdHQkhzOwpacVZ1NwAXTiMBOgs2ByQZVQgAQgQ+MRYOZxUwJi8dMCw1EiNqGGJ9VWVPFCw8Ih0XLAghfD0HJTERegksGiI2Mw5PCUElXlhaaUY8NE4FZCQaMEgsAT9XOCoZUQw2OgxUFgU6PABdJSsAPSkEJWsDHSABPkFzdFhaaUZ1HwEFISgROhxsMSgYGytBVQ8nPTk8AkZociIcJyQYBAQjFy4FWwwLWAQ3bjsVJwgwMRpbIjAaNxwrASVfXE9PFEFzdFhaaUZ1ck4aImUaOxxiIyQBECgKWhV9BwwbPQN7MwAHLQQyH0g2Bi4ZVTcKQBQhOlgfJwJfck5TZGVUdEhiTmtXBSYOWA17Mg0UKhI8PQBbbWUiPRo2GyobIDYKRlsQNQgOPBQwEQEdMDcbOAQnHGNeTmU5XRMnIRkWHBUwIFQwKCwXPyo3Gj8YG3dHYgQwIBcIe0g7NxlbbWxUMQYmR0FXVWVPFEFzdB0ULU9fck5TZCAYJw0rCGsZGjFPQkEyOhxaBAkjNwMWKjFaCwstACVZFCsbXSAVH1gOIQM7WE5TZGVUdEhiIyQBECgKWhV9CxsVJwh7MwAHLQQyH1IGBzgUGisBUQInfFFBaSs6JAseISsAejchASUZWyQBQAgSEjNadEY7OwJ5ZGVUdA0sCkESGyFlUhQ9NwwTJgh1HwEFISgROhxsHSoBEBUAR0l6XlhaaUY5PQ0SKGUreEgqHDtXSGU6QAg/J1YdLBIWOg8BbGxPdAEkTiMFBWUbXAQ9dDUVPwM4NwAHahYANRwnQDgWAyALZA4gdEVaIRQlfD4cNywAPQcsVWsFEDEaRg9zIAoPLEYwPAp5ISsQXg43ACgDHCoBFCw8Ih0XLAghfBwWJyQYODgtHWNef2VPFEE6Mlg3JhAwPwsdMGsnIAk2C2UEFDMKUDE8J1gOIQM7cjsHLSkHehwnAi4HGjcbHCw8Ih0XLAghfD0HJTERehsjGC4TJSocHVpzJh0OPBQ7choBMSBUMQYmZC4ZEU8jWwIyOCgWKB8wIEAwLCQGNQs2Czk2ESEKUFsQOxYULAUheggGKiYAPQcsRmJ9VWVPFBUyJxNUPgc8JkZDanNdb0gjHjsbDA0aWQA9OxEeYU9fck5TZCwSdCUtGC4aECsbGjInNQwfZwA5K04HLCAadBs2DzkDMykWHEhzMRYeQ0Z1ck4aImU5Ox4nAy4ZAWs8QAAnMVYSIBI3PRZTOnhUZkg2Bi4ZVQgAQgQ+MRYOZxUwJiYaMCcbLEAPAT0SGCABQE8AIBkOLEg9OxoRKz1ddA0sCkESGyFGPmt+eViY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dV+eUViX3tZVREqeCQDGyouGmx4f06R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9t9GSoMVQ1zAB0WLBY6IBoAZHhULxVIAiQUFClPUhQ9NwwTJgh1NAcdIAskF0AsDyYSXE9PFEFzOBcZKAp1PB4QN2VJdD8tHCAEBSQMUVsVPRYeDw8nIRowLCwYMEBgIBs0JmdGPkFzdFgTL0Y7PRpTKjUXJ0g2Bi4ZVTcKQBQhOlgUIAp1NwAXTmVUdEgsDyYSVXhPWgA+MUIWJhEwIEZaTmVUdEgkATlXKmlPWkE6OlgTOQc8IB1bKjUXJ1IFCz80HSwDUBM2OlBTYEYxPWRTZGVUdEhiTiIRVStBegA+MUIWJhEwIEZafiMdOgxqACoaEGlPBU1zIAoPLE91JgYWKk9UdEhiTmtXVWVPFEE6MlgUcy8mE0ZRCSoQMQRgR2sDHSABPkFzdFhaaUZ1ck5TZGVUdEgrCGsZWxUdXQwyJgEqKBQhchobIStUJg02GzkZVStBZBM6ORkIMDY0IBpdFCoHPRwrASVXECsLPkFzdFhaaUZ1ck5TZGVUdEguASgWGWUfFFxzOkI8IAgxFAcBNzE3PAEuChwfHCYHfRISfFo4KBUwAg8BMGdYdBwwGy5ef2VPFEFzdFhaaUZ1ck5TZGUdMkgyTj8fECtPRgQnIQoUaRZ7AgEALTEdOwZiCyUTf2VPFEFzdFhaaUZ1cgsfNyAdMkgsVAIENG1NdgAgMSgbOxJ3e04HLCAaXkhiTmtXVWVPFEFzdFhaaUYnNxoGNitUOkYSATgeASwAWmtzdFhaaUZ1ck5TZGUROgxITmtXVWVPFEE2OhxwaUZ1cgsdIE8ROgxIAiQUFClPUhQ9NwwTJgh1NAcdIBIbJgQmRiUWGCBGPkFzdFgUKAswclNTKiQZMVIuATwSB21GPkFzdFgcJhR1DUJTIGUdOkgrHioeBzZHYw4hPwsKKAUwaCkWMAERJwsnAC8WGzEcHEh6dBwVQ0Z1ck5TZGVUPQ5iCmU5FCgKDg08Ix0IYU9vNAcdIG0aNQUnQmtGWWUbRhQ2fVgOIQM7WE5TZGVUdEhiTmtXVSwJFAVpHQs7YUQXMx0WFCQGIEprTj8fECtPRgQnIQoUaQJ7AgEALTEdOwZiCyUTf2VPFEFzdFhaaUZ1cgcVZCFOHRsDRmk6GiEKWEN6dBkULUYxfD4BLSgVJhESDzkDVTEHUQ9zJh0OPBQ7cgpdFDcdOQkwFxsWBzFBZA4gPQwTJgh1NwAXTmVUdEhiTmtXECsLPkFzdFgfJwJfNwAXTiMBOgs2ByQZVREKWAQjOwoOOkg5Ox0HbGx+dEhiTjkSATAdWkEoXlhaaUZ1ck5TP2UaNQUnTnZXVwgWFAcyJhVaYRUlMxkdbWdYdEhiCS4DVXhPUhQ9NwwTJgh9e04BITEBJgZiKCoFGGsIURUAJBkNJzY6IUZaZCAaMEg/QkFXVWVPFEFzdANaJwc4N05OZGc5LUgkDzkaVW0MUQ8nMQpTa0p1cgkWMGVJdA43ACgDHCoBHEhzJh0OPBQ7cigSNihaMw02LS4ZASAdHEhzMRYeaRt5WE5TZGVUdEhiFWsZFCgKFFxzdisfLAJ1IQYcNGU6BCtgQmtXVWVPUwQndEVaLxM7MRoaKytcfUgwCz8CBytPUgg9MDYqCk53IQsWIGdddAcwTi0eGyEhZCJ7dgsbJER8cgsdIGUJeGJiTmtXVWVPFBpzOhkXLEZockw0ISQGdBsqATtXOxUsFk1zdFhaaQEwJk5OZCMBOgs2ByQZXWxPRgQnIQoUaQA8PAo9FAZcdg8nDzlVXGUARkE1PRYeBzYWekwHKyhWfUgnAC9XCGllFEFzdFhaaUYucgASKSBUaUhgPi4DVSAIU0EgPBcKa0p1ck5TZGUTMRxiU2sRACsMQAg8OlBTaRQwJhsBKmUSPQYmIBs0XWcKUwZxfVgVO0YzOwAXChU3fEoyCz9VXGUKWgVzKVRwaUZ1ck5TZGUPdAYjAy5XSGVNdw4gOR0OIAV1IQYcNGdYdEhiTmsQEDFPCUE1IRYZPQ86PEZaZDcRIB0wAGsRHCsLejEQfFoZJhU4NxoaJ2dddA0sCmsKWU9PFEFzdFhaaR11PA8eIWVJdEoRCycbVT8AWgRxeFhaaUZ1ck5TZCIRIEh/Ti0CGyYbXQ49fFFaOwMhJxwdZCMdOgwVATkbEW1NRwQ/OFpTaQM7Nk4OaE9UdEhiTmtXVT5PWgA+MVhHaUQBIA8FISkdOg9iAy4FFi0OWhVxeB8fPUZocggGKiYAPQcsRmJXByAbQRM9dB4TJwIbAi1bZjEGNR4nAiIZEmdGFA4hdB4TJwIbAi1bZigRJgsqDyUDV2xPUQ83dAVWQ0Z1ck5TZGVUL0gsDyYSVXhPFiwyPRQYJh53fk5TZGVUdEhiTmtXEiAbFFxzMg0UKhI8PQBbbU9UdEhiTmtXVWVPFEE/OxsbJUYzclNTAiQGOUYwCzgYGTMKHEhodBEcaQB1JgYWKk9UdEhiTmtXVWVPFEFzdFhaJQk2MwJTKWVJdA54KCIZEQMGRhInFxATJQJ9cCMSLSkWOxBgR0FXVWVPFEFzdFhaaUZ1ck5TLSNUOUgjAC9XGGs/Rgg+NQoDGQcnJk4HLCAadBonGj4FG2UCGjEhPRUbOx8FMxwHahUbJwE2ByQZVSABUGtzdFhaaUZ1ck5TZGVUdEhiBy1XGGUbXAQ9dBQVKgc5ch5TeWUZbi4rAC8xHDccQCI7PRQeHg48MQY6NwRcdiojHS4nFDcbFk1zIAoPLE9ucgcVZDVUIAAnAGsFEDEaRg9zJFYqJhU8JgccKmUROgxiCyUTf2VPFEFzdFhaaUZ1cgsdIE9UdEhiTmtXVSABUEEueHJaaUZ1ck5TZD5UOgkvC2tKVWcoVRM3MRZaCgk8PE4gLCoEdkRiTiwSAWVSFAcmOhsOIAk7ekdTNiAAIRosTi0eGyE4WxM/MFBYDgcnNgsdByodOkprTi4ZEWUSGGtzdFhaaUZ1chVTKiQZMUh/TmkkECYdURVzGxoYMEYwPBoBPWdYdA8nGmtKVSMaWgInPRcUYU91IAsHMTcadA4rAC8gGjcDUElxBx0ZOwMhHQwRPWdddA0sCmsKWU9PFEFzKXIfJwJfNBsdJzEdOwZiOi4bEDUARhUgeh8VYQg0PwtaTmVUdEgkATlXKmlPUUE6OlgTOQc8IB1bECAYMRgtHD8EWykGRxV7fVFaLQlfck5TZGVUdEgrCGsSWysOWQRzaUVaJwc4N04HLCAaXkhiTmtXVWVPFEFzdBQVKgc5ch5TeWUReg8nGmNef2VPFEFzdFhaaUZ1cgcVZDVUIAAnAGsiASwDR08nMRQfOQknJkYDZG5UAg0hGiQFRmsBURZ7ZFRafUp1Ykdaf2UGMRw3HCVXATcaUUE2OhxwaUZ1ck5TZGUROgxITmtXVSABUGtzdFhaOwMhJxwdZCMVOBsnZC4ZEU9lGUxztu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjptDktv3SjN7nl9D/1vTDtu3qq/PFsPvjTmhZdFlzQGshPBY6dS0AXlVXaYTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxGIuASgWGWU5XRImNRQJaVt1KU4gMCQAMUh/TjBXEzADWAMhPR8SPUZocggSKDYReEgsAQ0YEmVSFAcyOAsfaRt5cjERJSYfIRhiU2sMCGUSPg08NxkWaQAgPA0HLSoadAojDSACBQkGUwknPRYdYU9fck5TZCwSdAYnFj9fIywcQQA/J1YlKwc2ORsDbWUAPA0sTjkSATAdWkE2OhxwaUZ1cjgaNzAVOBtsMSkWFi4aRE8RJhEdIRI7Nx0AZGVUdFViIiIQHTEGWgZ9FgoTLg4hPAsAN09UdEhiOCIEACQDR08MNhkZIhMlfC0fKyYfAAEvC2tXVWVPCUEfPR8SPQ87NUAwKCoXPzwrAy59VWVPFDc6Jw0bJRV7DQwSJy4BJEYFAiQVFCk8XAA3Ow8JaVt1HgcULDEdOg9sKScYFyQDZwkyMBcNOmx1ck5TEiwHIQkuHWUoFyQMXxQjej4VLiM7Nk5TZGVUdEhiU2s7HCIHQAg9M1Y8JgEQPAp5ZGVUdD4rHT4WGTZBawMyNxMPOUgTPQkgMCQGIEhiTmtXVXhPeAg0PAwTJwF7FAEUFzEVJhxICyUTfyMaWgInPRcUaTA8IRsSKDZaJw02KD4bGScdXQY7IFAMYGx1ck5TEiwHIQkuHWUkASQbUU81IRQWKxQ8NQYHZHhUIlNiDCoUHjAfeAg0PAwTJwF9e2RTZGVUPQ5iGGsDHSABFC06MxAOIAgyfCwBLSIcIAYnHThXSGVcD0EfPR8SPQ87NUAwKCoXPzwrAy5XSGVeAFpzGBEdIRI8PAldAykbNgkuPSMWESoYR0FudB4bJRUwWE5TZGUROBsnZGtXVWVPFEFzGBEdIRI8PAldBjcdMwA2AC4EBmVSFDc6Jw0bJRV7DQwSJy4BJEYAHCIQHTEBURIgdBcIaVdfck5TZGVUdEgOBywfASwBU08QOBcZIjI8PwtTZHhUAgExGyobBmswVgAwPw0KZyU5PQ0YECwZMUgtHGtGQU9PFEFzdFhaaSo8NQYHLSsTei8uASkWGRYHVQU8IwtadEYDOx0GJSkHejcgDygcADVBcw08NhkWGg40NgEEN2UKaUgkDycEEE9PFEFzMRYeQwM7NmQVMSsXIAEtAGshHDYaVQ0gegsfPSg6FAEUbDNdXkhiTmshHDYaVQ0geisOKBIwfAAcAioTdFViGHBXFyQMXxQjGBEdIRI8PAlbbU9UdEhiBy1XA2UbXAQ9dDQTLg4hOwAUagMbMy0sCmtKVXQKAlpzGBEdIRI8PAldAioTBxwjHD9XSGVeUVdZdFhaaQM5IQtTCCwTPBwrACxZMyoIcQ83dEVaHw8mJw8fN2srNgkhBT4HWwMAUyQ9MFgVO0ZkYl5Df2U4PQ8qGiIZEmspWwYAIBkIPUZocjgaNzAVOBtsMSkWFi4aRE8VOx8pPQcnJk4cNmVEdA0sCkESGyFlPkx+dJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1KfhxIrX/qni5af6pIPGxJrv2YTAwozm1E9ZeUhzXGVXIAxP1uHHdBQVKAJ1HQwALSEdNQYXB2tfLHckHUEyOhxaKxM8PgpTMC0RdB8rAC8YAk9CGUGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/6R0dWWwfig+9uV4NWNofGxweiY3Pa3x/55NDcdOhxqRmksLHckaUEfOxkeIAgyciERNywQPQksOyJXEyodFEQgdFZUZ0R8aAgcNigVIEABASURHCJBcyAeESc0CCsQe0d5TikbNwkuTgceFzcORhh/dCwSLAswHw8dJSIRJkRiPSoBEAgOWgA0MQpwJQk2MwJTKy4hHUh/TjsUFCkDHAcmOhsOIAk7ekd5ZGVUdCQrDDkWBzxPFEFzdFhHaQo6MwoAMDcdOg9qCSoaEH8nQBUjEx0OYSU6PAgaI2shHTcQKxs4VWtBFEMfPRoIKBQsfAIGJWddfUBrZGtXVWU7XAQ+MTUbJwcyNxxTeWUYOwkmHT8FHCsIHAYyOR1AARIhIikWMG03OwYkByxZIAwwZiQDG1hUZ0Z3MwoXKysHezwqCyYSOCQBVQY2JlYWPAd3e0dbbU9UdEhiPSoBEAgOWgA0MQpaaVt1PgESIDYAJgEsCWMQFCgKDiknIAg9LBJ9EQEdIiwTej0LMRkyJQpPGk9zdhkeLQk7IUEgJTMRGQksDywSB2sDQQBxfVFSYGwwPApaTiwSdAYtGmsYHhAmFA4hdBYVPUYZOwwBJTcNdBwqCyV9VWVPFBYyJhZSaz0MYCVTDDAWCUgEDyIbECFPQA5zOBcbLUYaMB0aICwVOj0rQGs2FyodQAg9M1ZYYGx1ck5TGwJaDVoJMQw2MhonYSMMGDc7DSMRclNTKiwYb0gwCz8CBytlUQ83XnIWJgU0Pk48NDEdOwYxQmsjGiIIWAQgdEVaBQ83IA8BPWs7JBwrASUEWWUjXQMhNQoDZzI6NQkfITZ+GAEgHCoFDGspWxMwMTsSLAU+MAELZHhUMgkuHS59fykAVwA/dB4PJwUhOwEdZAsbIAEkF2MDHDEDUU1zMB0JKkp1NxwBbU9UdEhiIiIVByQdTVsdOwwTLx99KWRTZGVUdEhiTh8eASkKFEFzdFhaaVt1NxwBZCQaMEhqTA4FByodFIPT9lhYaUh7choaMCkRfUgtHGsDHDEDUU1ZdFhaaUZ1ck43ITYXJgEyGiIYG2VSFAU2JxtaJhR1cExfTmVUdEhiTmtXISwCUUFzdFhaaUZ1b05HaE9UdEhiE2J9ECsLPms/OxsbJUYCOwAXKzJUaUgOBykFFDcWDiIhMRkOLDE8PAocM20PXkhiTmsjHDEDUUFzdFhaaUZ1ck5TZHhUdi8wATxXFGUoVRM3MRZaaYTV8E5THXc/dCA3DGtXA2dPGk9zFxcULw8yfD0wFgwkADcUKxlbf2VPFEEVOxcOLBR1ck5TZGVUdEhiTnZXVxxdf0EANwoTORJ1EA8QL3c2NQspTmuV9edPFENzelZaCgk7NAcUagI1GS0dIAo6MGllFEFzdDYVPQ8zKz0aICBUdEhiTmtXSGVNZgg0PAxYZWx1ck5TFy0bIys3HT8YGAYaRhI8JlhHaRInJwtfTmVUdEgBCyUDEDdPFEFzdFhaaUZ1clNTMDcBMURITmtXVQQaQA4APBcNaUZ1ck5TZGVUaUg2HD4SWU9PFEFzBh0JIBw0MAIWZGVUdEhiTmtKVTEdQQR/XlhaaUYWPRwdITcmNQwrGzhXVWVPFFxzZUhWQxt8WGQfKyYVOEgWDykEVXhPT2tzdFhaDgcnNgsdZGVUaUgVByUTGjJVdQU3ABkYYUQSMxwXIStWeEhiTmkEFDMKFkh/XlhaaUYGOgEDZGVUdEh/ThweGyEAQ1sSMBwuKAR9cD0bKzVWeEhiTmtXVzUOVwoyMx1YYEpfck5TZBURIBtiTmtXVXhPYwg9MBcNcycxNjoSJm1WBA02HWlbVWVPFEFxPB0bOxJ3e0J5ZGVUdDguDzISB2VPFFxzAxEULQkiaC8XIBEVNkBgPicWDCAdFk1zdFhYPBUwIExaaE9UdEhiIyIEFmVPFEFzaVgtIAgxPRlJBSEQAAkgRmk6HDYMFk1zdFhaaUQiIAsdJy1WfURITmtXVQYAWgc6MwtaaVt1BQcdICoDbikmCh8WF21Ndw49MhEdOkR5ck5RICQANQojHS5VXGllFEFzdCsfPRI8PAkAZHhUAwEsCiQATwQLUDUyNlBYGgMhJgcdIzZWeEhgHS4DASwBUxJxfVRwaUZ1ci0BISEdIBtiTnZXIiwBUA4kbjkeLTI0MEZRBzcRMAE2HWlbVWVNXQ81O1pTZWwoWGReaWWWwOig+suV4cVPYCARdElaq+bBcikyFgExGkig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOhIAiQUFClPcwU9ABoCBUZocjoSJjZaEwkwCi4ZTwQLUC02MgwuKAQ3PRZbbU8YOwsjAmswESs/WAA9IFhHaSExPDoRPAlOFQwmOioVXWcuQRU8dCgWKAghcEd5KCoXNQRiKS8ZPSQdQgQgIFhHaSExPDoRPAlOFQwmOioVXWcnVRMlMQsOaUl1EQEfKCAXIEprZEEwESs/WAA9IEI7LQIZMwwWKG0PdDwnFj9XSGVNdw49IBEUPAkgIQIKZDUYNQY2HWsDHSBPRwQ/MRsOLAJ1IQsWIGUVNxotHThXDCoaRkE8IxYfLUYzMxweamdYdCwtCzggByQfFFxzIAoPLEYoe2Q0ICskOAksGnE2ESErXRc6MB0IYU9fFQodFCkVOhx4Ly8TPCsfQRV7digWKAghAQsWIAsVOQ1gQmsMVREKTBVzaVhYGgMwNk4dJSgRdEAnFioUAWxNGEEXMR4bPAohclNTZgYVJhotGmlbVRUDVQI2PBcWLQMnclNTZgYVJhotGmdXJjEdVRYxMQoIMEp1fEBdZml+dEhiTh8YGikbXRFzaVhYHR8lN04HLCBUJw0nCmsZFCgKFAAgdBEOaQclIgsSNjZUPQZiFyQCB2UGWhc2OgwVOx91ehkaMC0bIRxiNRgSECEyHU9xeHJaaUZ1EQ8fKCcVNwNiU2sRACsMQAg8OlAMYEYUJxocAyQGMA0sQBgDFDEKGhE/NRYOGgMwNk5OZDNUMQYmTjZefwQaQA4UNQoeLAh7ARoSMCBaJAQjAD8kECALFFxzdjsbOxQ6Jkx5TgIQOjguDyUDTwQLUDU8Mx8WLE53ExsHKxUYNQY2TGdXDmU7URkndEVaaycgJgFTFCkVOhxiRiYWBjEKRkhxeFg+LAA0JwIHZHhUMgkuHS5bf2VPFEEHOxcWPQ8lclNTZhYEJg0jCjhXBiAKUBJzJhkULQk4PhdTJSYGOxsxTjIYADdPUgAhOVgKJQkhfExfTmVUdEgBDycbFyQMX0FudB4PJwUhOwEdbDNddAEkTj1XAS0KWkESIQwVDgcnNgsdajYANRo2Lz4DGhUDVQ8nfFFaLAomN04yMTEbEwkwCi4ZWzYbWxESIQwVGQo0PBpbbWUROgxiCyUTVThGPiY3OigWKAghaC8XIBYYPQwnHGNVJSkOWhUXMRQbMER5chVTECAMIEh/TmknGSQBQEE6OgwfOxA0PkxfZAERMgk3Aj9XSGVfGlR/dDUTJ0Zocl5ddWlUGQk6TnZXQGlPZg4mOhwTJwF1b05BaGUnIQ4kBzNXSGVNFBJxeHJaaUZ1BgEcKDEdJEh/TmkjHCgKFAM2IA8fLAh1Nw8QLGUEOAksGmVVWU9PFEFzFxkWJQQ0MQVTeWUSIQYhGiIYG20ZHUESIQwVDgcnNgsdahYANRwnQDsbFCsbcAQ/NQFadEYjcgsdIGUJfWIFCiUnGSQBQFsSMBwuJgEyPgtbZg8dIBwnHGlbVT5PYAQrIFhHaUQHMwAXKygdLg1iGiIaHCsIR0N/dDwfLwcgPhpTeWUAJh0nQkFXVWVPYA48OAwTOUZockwyICEHdKrzX3lSVTcOWgU8ORYfOhV1IQFTMC0RdBgjGj8SBytPXRI9cwxaOQMnNAsQMCkNdBotDCQDHCZBFk1ZdFhaaSU0PgIRJSYfdFViCD4ZFjEGWw97IlFaCBMhPSkSNiEROkYRGioDEGsFXRUnMQpadEYjcgsdIGUJfWJIKS8ZPSQdQgQgIEI7LQIZMwwWKG0PdDwnFj9XSGVNdRQnO1USKBQjNx0HZDcdJA1iHicWGzEcFAA9MFgNKAo+cgEFITdUMBotHjsSEWUJRhQ6IFgOJkYlOw0YZCwAdB0yQGlbVQEAURIEJhkKaVt1JhwGIWUJfWIFCiU/FDcZURInbjkeLSI8JAcXITdcfWIFCiU/FDcZURInbjkeLTI6NQkfIW1WFR02AQMWBzMKRxVxeFgBaTIwKhpTeWVWFR02AWs/FDcZURIndAgWKAghIUxfZAERMgk3Aj9XSGUJVQ0gMVRwaUZ1cjocKykAPRhiU2tVNiQDWBJzIBAfaQ40IBgWNzFUJg0vAT8SVSoBFAQlMQoDaRY5MwAHZCoadBEtGzlXEyQdWU9xeHJaaUZ1EQ8fKCcVNwNiU2sRACsMQAg8OlAMYEY8NE4FZDEcMQZiLz4DGgIORgU2OlYJPQcnJi8GMCo8NRo0CzgDXWxPUQ0gMVg7PBI6FQ8BICAaehs2ATs2ADEAfAAhIh0JPU58cgsdIGUROgxiE2J9MiEBfAAhIh0JPVwUNgogKCwQMRpqTAMWBzMKRxUaOgwfOxA0PkxfZD5UAA06GmtKVWcnVRMlMQsOaQ87JgsBMiQYdkRiKi4RFDADQEFudEtWaSs8PE5OZHRYdCUjFmtKVXNfGEEBOw0ULQ87NU5OZHRYdDs3CC0eDWVSFENzJ1pWQ0Z1ck4wJSkYNgkhBWtKVSMaWgInPRcUYRB8ci8GMCozNRomCyVZJjEOQAR9PBkIPwMmJicdMCAGIgkuTnZXA2UKWgVzKVFwDgI7Gg8BMiAHIFIDCi8zHDMGUAQhfFFwDgI7Gg8BMiAHIFIDCi8jGiIIWAR7djkPPQkWPQIfISYAdkRiFWsjED0bFFxzdjkPPQl1BQ8fL2g3OwQuCygDVTcGRARxeFg+LAA0JwIHZHhUMgkuHS5bf2VPFEEHOxcWPQ8lclNTZhIVOAMxTiQBEDdPUQAwPFgIIBYwcggBMSwAdBstTiIDVSQaQA5+JBEZIhV1Jx5dZml+dEhiTggWGSkNVQI4dEVaLxM7MRoaKytcIkFiBy1XA2UbXAQ9dDkPPQkSMxwXIStaJxwjHD82ADEAdw4/OB0ZPU58cgsfNyBUFR02AQwWByEKWk8gIBcKCBMhPS0cKCkRNxxqR2sSGyFPUQ83dAVTQyExPCYSNjMRJxx4Ly8TJikGUAQhfFo5Jgo5Nw0HDSsAMRo0DydVWWUUFDU2LAxadEZ3EQEfKCAXIEgrAD8SBzMOWEN/dDwfLwcgPhpTeWVAeEgPByVXSGVeGEEeNQBadEZjYkJTFioBOgwrACxXSGVeGEEAIR4cIB51b05RZDZWeGJiTmtXNiQDWAMyNxNadEYzJwAQMCwbOkA0R2s2ADEAcwAhMB0UZzUhMxoWaiYbOAQnDT8+GzEKRhcyOFhHaRB1NwAXZDhdXmIuASgWGWUoUA8HNgAoaVt1Bg8RN2szNRomCyVNNCELZgg0PAwuKAQ3PRZbbU8YOwsjAmswESs8UQ0/dEVaDgI7BgwLFn81MAwWDylfVxYKWA1ze1gtKBIwIExaTikbNwkuTgwTGxYbVRUgdEVaDgI7BgwLFn81MAwWDylfVwkGQgRzNxcPJxIwIB1RbU9+EwwsPS4bGX8uUAUfNRofJU4ucjoWPDFUaUhgLz4DGmgcUQ0/J1gSLAoxcggcKyFUNQYmTjwWASAdR0EyOBRaMAkgIE4DKCQaIBtiASVXASwCURMgelpWaSI6Nx0kNiQEdFViGjkCEGUSHWsUMBYpLAo5aC8XIAEdIgEmCzlfXE8oUA8AMRQWcycxNjocIyIYMUBgLz4DGhYKWA1xeFgBaTIwKhpTeWVWFR02AWskECkDFAc8OxxYZUYRNwgSMSkAdFViCCobBiBDPkFzdFguJgk5JgcDZHhUdi4rHC4EVTEHUUEgMRQWaRQwPwEHIWtUBxwjAC9XGyAORkEnPB1aGgM5Pk49FAZadkRITmtXVQYOWA0xNRsRaVt1NBsdJzEdOwZqGGJXHCNPQkEnPB0UaScgJgE0JTcQMQZsHT8WBzEuQRU8Bx0WJU58cgsfNyBUFR02AQwWByEKWk8gIBcKCBMhPT0WKClcfUgnAC9XECsLFBx6Xj8eJzUwPgJJBSEQBwQrCi4FXWc8UQ0/HRYOLBQjMwJRaGUPdDwnFj9XSGVNZwQ/OFgTJxIwIBgSKGdYdCwnCCoCGTFPCUFgZFRaBA87clNTcWlUGQk6TnZXQ3VfGEEBOw0ULQ87NU5OZHVYdDs3CC0eDWVSFENzJ1pWQ0Z1ck4wJSkYNgkhBWtKVSMaWgInPRcUYRB8ci8GMCozNRomCyVZJjEOQAR9Jx0WJS87JgsBMiQYdFViGGsSGyFPSUhZExwUGgM5PlQyICEwPR4rCi4FXWxlcwU9Bx0WJVwUNgonKyITOA1qTAoCASo4VRU2JlpWaR11BgsLMGVJdEoDGz8YVRIOQAQhdB8bOwIwPB1RaGUwMQ4jGycDVXhPUgA/Jx1WQ0Z1ck4nKyoYIAEyTnZXVwYOWA0gdAwSLEYCMxoWNhwbIRoFDzkTECscFBM2ORcOLEh1EAEcNzEHdA8wATwDHWtNGGtzdFhaCgc5PgwSJy5UaUgkGyUUASwAWkklfVgTL0YjchobIStUFR02AQwWByEKWk8gIBkIPScgJgEkJTERJkBrTi4bBiBPdRQnOz8bOwIwPEAAMCoEFR02ARwWASAdHEhzMRYeaQM7Nk4ObU8zMAYRCycbTwQLUDI/PRwfO053BQ8HITc9OhwnHD0WGWdDFBpzAB0CPUZockwkJTERJkgrAD8SBzMOWEN/dDwfLwcgPhpTeWVCZERiIyIZVXhPBVF/dDUbMUZoclhDdGlUBgc3AC8eGyJPCUFjeFgpPAAzOxZTeWVWdBtgQkFXVWVPdwA/OBobKg11b04VMSsXIAEtAGMBXGUuQRU8ExkILQM7fD0HJTEReh8jGi4FPCsbURMlNRRadEYjcgsdIGUJfWIFCiUkECkDDiA3MDwTPw8xNxxbbU8zMAYRCycbTwQLUCMmIAwVJ04ucjoWPDFUaUhgPS4bGWUJWw43dDY1HkR5cigGKiZUaUgkGyUUASwAWkl6dCofJAkhNx1dIiwGMUBgPS4bGQMAWwVxfUNaBwkhOwgKbGcnMQQuTGdXVwMGRgQ3elpTaQM7Nk4ObU8zMAYRCycbTwQLUCMmIAwVJ04ucjoWPDFUaUhgOSoDEDdPei4EdlRaaUZ1cigGKiZUaUgkGyUUASwAWkl6dCofJAkhNx1dLSsCOwMnRmkgFDEKRiYyJhwfJxV3e1VTCioAPQ47RmkgFDEKRkN/dFo8IBQwNkBRbWUROgxiE2J9fykAVwA/dBQYJTY5MwAHISFUdEh/TgwTGxYbVRUgbjkeLSo0MAsfbGckOAksGi4TVWVPDkFjdlFwJQk2MwJTKCcYHAkwGC4EASALFFxzExwUGhI0Jh1JBSEQGAkgCydfVw0ORhc2JwwfLUZvcl5RbU8YOwsjAmsbFyktWxQ0PAxaaUZ1b040ICsnIAk2HXE2ESEjVQM2OFBYGg46Ik4RMTwHdFJiXmlefykAVwA/dBQYJTU6PgpTZGVUdEh/TgwTGxYbVRUgbjkeLSo0MAsfbGcnMQQuTigWGSkcDkFjdlFwJQk2MwJTKCcYARg2ByYSVWVPFFxzExwUGhI0Jh1JBSEQGAkgCydfVxAfQAg+MVhaaUZvcl5DfnVEblhyTGJ9MiEBZxUyIAtACAIxFgcFLSERJkBrZAwTGxYbVRUgbjkeLSQgJhocKm0PdDwnFj9XSGVNZgQgMQxaOhI0Jh1RaGUyIQYhTnZXEzABVxU6OxZSYEYGJg8HN2sGMRsnGmNeTmUhWxU6MgFSazUhMxoAZmlUdjonHS4DW2dGFAQ9MFgHYGxff0NTptH0tvzCjN/3VREudkFhdJr63UYGGiEjZKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7kEbGiYOWEEAPAguKx4ZclNTECQWJ0YRBiQHTwQLUC02MgwuKAQ3PRZbbU8YOwsjAmskHTU8UQQ3J1hHaTU9IjoRPAlOFQwmOioVXWc8UQQ3J1hcaSEwMxxRbU8YOwsjAmskHTUqUwYgdFhHaTU9IjoRPAlOFQwmOioVXWcqUwYgdF5aDBAwPBoAZmx+XjsqHhgSECEcDiA3MDQbKwM5ehVTECAMIEh/Tmk2ADEAGQMmLQtaOgMwNk4SKiFUMw0jHGsEHSofFBInOxsRaQk7cg9TMCwZMRpsTgoTEWUMWww+NVUJLBY0IA8HISFUOgkvCzhZV2lPcA42Jy8IKBZ1b04HNjARdBVrZBgfBRYKUQUgbjkeLSI8JAcXITdcfWIRBjskECALR1sSMBwzJxYgJkZRFyARMCYjAy4EV2lPT0EHMQAOaVt1cD0WISEHdBwtTikCDGdDFCU2MhkPJRJ1b05RByQGJgc2QhgDByQYVgQhJgFWCwogNwwWNjcNeDwtAyoDGmdDPkFzdFgqJQc2NwYcKCERJkh/TmkUGigCVUwgMQgbOwchNwpTKiQZMRtgQkFXVWVPYA48OAwTOUZockwwKygZNUUxCzsWByQbUQVzOBEJPUY6NE4AISAQdAYjAy4EVTEAFBEmJhsSKBUwchkbIStUPQZiHT8YFi5BFk1ZdFhaaSU0PgIRJSYfdFViCD4ZFjEGWw97IlFwaUZ1ck5TZGU1IRwtPSMYBWs8QAAnMVYJLAMxHA8eITZUaUg5E0FXVWVPFEFzdB4VO0Y7cgcdZDEbJxwwByUQXTNGDgY+NQwZIU53CTBfGW5WfUgmAUFXVWVPFEFzdFhaaUY5PQ0SKGUHdFViAHEaFDEMXElxCl0JY057f0dWN29QdkFITmtXVWVPFEFzdFhaIAB1IU4NeWVWdkg2Bi4ZVTEOVg02ehEUOgMnJkYyMTEbBwAtHmUkASQbUU8gMR0eBwc4Nx1fZDZddA0sCkFXVWVPFEFzdB0ULWx1ck5TISsQdBVrZBgfBRYKUQUgbjkeLTI6NQkfIW1WFR02AQkCDBYKUQUgdlRaMkYBNxYHZHhUdik3GiRXNzAWFBI2MRwJa0p1FgsVJTAYIEh/Ti0WGTYKGGtzdFhaCgc5PgwSJy5UaUgkGyUUASwAWkklfVg7PBI6AQYcNGsnIAk2C2UWADEAZwQ2MAtadEYjaU4aImUCdBwqCyVXNDAbWzI7OwhUOhI0IBpbbWUROgxiCyUTVThGPjI7JCsfLAImaC8XIAEdIgEmCzlfXE88XBEAMR0eOlwUNgo6KjUBIEBgKS4WBwsOWQQgdlRaMkYBNxYHZHhUdi8nDzlXASpPVhQqdlRaDQMzMxsfMGVJdEoVDz8SBywBU0EQNRZWHRQ6JQsfZml+dEhiThsbFCYKXA4/MB0IaVt1cA0cKSgVeRsnHioFFDEKUEE9NRUfOkR5WE5TZGU3NQQuDCoUHmVSFAcmOhsOIAk7ehhaTmVUdEhiTmtXNDAbWzI7OwhUGhI0JgtdIyAVJiYjAy4EVXhPTxxZdFhaaUZ1ck4VKzdUOkgrAGsDGjYbRgg9M1AMYFwyPw8HJy1cdjMcQhZcV2xPUA5ZdFhaaUZ1ck5TZGVUOAchDydXBmVSFA9pORkOKg59cDBWN29cekVrSzhdUWdGPkFzdFhaaUZ1ck5TZCwSdBtiEHZXV2dPQAk2OlgOKAQ5N0AaKjYRJhxqLz4DGhYHWxF9BwwbPQN7NQsSNgsVOQ0xQmsEXGUKWgVZdFhaaUZ1ck4WKiF+dEhiTi4ZEWUSHWsAPAgpLAMxIVQyICEgOw8lAi5fVwQaQA4RIQE9LAcncEJTP2UgMRA2TnZXVwQaQA5zFg0DaQEwMxxRaGUwMQ4jGycDVXhPUgA/Jx1WQ0Z1ck4wJSkYNgkhBWtKVSMaWgInPRcUYRB8ci8GMConPAcyQBgDFDEKGgAmIBc9LAcnclNTMn5UPQ5iGGsDHSABFCAmIBcpIQklfB0HJTcAfEFiCyUTVSABUEEufXIpIRYGNwsXN381MAwGBz0eESAdHEhZBxAKGgMwNh1JBSEQBwQrCi4FXWc8XA4jHRYOLBQjMwJRaGUPdDwnFj9XSGVNZwk8JFgZIQM2OU4aKjERJh4jAmlbVQEKUgAmOAxadEZgfk4+LStUaUhzQms6FD1PCUFlZFRaGwkgPAoaKiJUaUhzQmskACMJXRlzaVhYaRV3fmRTZGVUFwkuAikWFi5PCUE1IRYZPQ86PEYFbWU1IRwtPSMYBWs8QAAnMVYTJxIwIBgSKGVJdB5iCyUTVThGPmsAPAg/LgEmaC8XIAkVNg0uRjBXISAXQEFudFo7PBI6fwwGPTZUJA02Ti4QEjZPVQ83dAwIIAEyNxwAZCACMQY2QSUeEi0bGxUhNQ4fJQ87NUMeITcXPAksGmsEHSofR09xeFg+JgMmBRwSNGVJdBwwGy5XCGxlZwkjER8dOlwUNgo3LTMdMA0wRmJ9Ji0fcQY0J0I7LQIcPB4GMG1WEQ8lICoaEDZNGEEodCwfMRJ1b05RASITJ0g2AWsVADxNGEEXMR4bPAohclNTZgYbOQUtAGsyEiJNGGtzdFhaGQo0MQsbKykQMRpiU2tVFioCWQB+Jx0KKBQ0JgsXZCATM0gsDyYSBmdDPkFzdFg5KAo5MA8QL2VJdA43ACgDHCoBHBd6XlhaaUZ1ck5TBTAAOzsqATtZJjEOQAR9MR8dBwc4Nx1TeWUPKWJiTmtXVWVPFAc8JlgUaQ87chocNzEGPQYlRj1eTyICVRUwPFBYEjh5D0VRbWUQO2JiTmtXVWVPFEFzdFgWJgU0Pk4AZHhUOlIvDz8UHW1NakQgflBUZE9wIURXZmx+dEhiTmtXVWVPFEFzPR5aOkYrb05RZmUAPA0sTj8WFykKGgg9Jx0IPU4UJxocFy0bJEYRGioDEGsKUwYdNRUfOkp1IUdTISsQXkhiTmtXVWVPUQ83XlhaaUYwPApTOWx+BwAyKywQBn8uUAUHOx8dJQN9cC8GMCo2IREHCSwEV2lPT0EHMQAOaVt1cC8GMCpUFh07Ti4QEjZNGEEXMR4bPAohclNTIiQYJw1uZGtXVWUsVQ0/NhkZIkZocggGKiYAPQcsRj1eVQQaQA4APBcKZzUhMxoWaiQBIAcHCSwEVXhPQlpzPR5aP0YhOgsdZAQBIAcRBiQHWzYbVRMnfFFaLAgxcgsdIGUJfWIRBjsyEiIcDiA3MDwTPw8xNxxbbU8nPBgHCSwETwQLUDU8Mx8WLE53FxgWKjEnPAcyTGdXDmU7URkndEVaaycgJgFTBjANdC00CyUDVTYHWxFxeFg+LAA0JwIHZHhUMgkuHS5bf2VPFEEHOxcWPQ8lclNTZgcBLRtiCz0SGzFCRwk8JFgJPQk2OU5VZAAVJxwnHGsEASoMX0EkPB0UaQc2JgcFIWtWeGJiTmtXNiQDWAMyNxNadEYzJwAQMCwbOkA0R2s2ADEAZwk8JFYpPQchN0AWMiAaIDsqATtXSGUZD0E6MlgMaRI9NwBTBTAAOzsqATtZBjEORhV7fVgfJwJ1NwAXZDhdXjsqHg4QEjZVdQU3ABcdLgowekw9LSIcIDsqATtVWWUUFDU2LAxadEZ3ExsHK2U2IRFiICIQHTFPRwk8JFpWaSIwNA8GKDFUaUgkDycEEGllFEFzdDsbJQo3Mw0YZHhUMh0sDT8eGitHQkhzFQ0OJjU9PR5dFzEVIA1sACIQHTFPCUElb1gTL0YjchobIStUFR02ARgfGjVBRxUyJgxSYEYwPApTISsQdBVrZBgfBQAIUxJpFRweHQkyNQIWbGcgJgk0CyceGyIiURMwPFpWaR11BgsLMGVJdEoDGz8YVQcaTUEHJhkMLAo8PAlTCSAGNwAjAD9VWWUrUQcyIRQOaVt1NA8fNyBYXkhiTms0FCkDVgAwP1hHaQAgPA0HLSoafB5rTgoCASo8XA4jeisOKBIwfBoBJTMROAEsCWtKVTNUFAg1dA5aPQ4wPE4yMTEbBwAtHmUEASQdQEl6dB0ULUYwPApTOWx+XgQtDSobVRYHRDNzaVguKAQmfD0bKzVOFQwmPCIQHTEoRg4mJBoVMU53AxsaJy5UNQs2ByQZBmdDFEM4MQFYYGwGOh4hfgQQMCQjDC4bXT5PYAQrIFhHaUQYMwAGJSlUOwYnQzgfGjFPRwk8JFgbKhI8PQAAamdYdCwtCzggByQfFFxzIAoPLEYoe2QgLDUmbikmCg8eAywLURN7fXIpIRYHaC8XIAcBIBwtAGMMVREKTBVzaVhYCxMsci8/CGUHMQ0mHWtfEzcAWUE/PQsOYER5cigGKiZUaUgkGyUUASwAWkl6XlhaaUYzPRxTG2lUOkgrAGseBSQGRhJ7FQ0OJjU9PR5dFzEVIA1sHS4SEQsOWQQgfVgeJkYHNwMcMCAHeg4rHC5fVwcaTTI2MRxYZUY7e1VTMCQHP0Y1DyIDXXVBBUhzMRYeQ0Z1ck49KzEdMhFqTBgfGjVNGEFxAAoTLAJ1MBsKLSsTdBsnCy8EW2dGPgQ9MFgHYGwGOh4hfgQQMCo3Gj8YG20UFDU2LAxadEZ3EBsKZAQ4GEglCyoFVW0JRg4+dBQTOhJ8cEJTAjAaN0h/Ti0CGyYbXQ49fFFwaUZ1cggcNmUreEgsTiIZVSwfVQghJ1A7PBI6AQYcNGsnIAk2C2UQECQdegA+MQtTaQI6cjwWKSoAMRtsCCIFEG1NdhQqEx0bO0R5cgBaf2UANRspQDwWHDFHBE9ifVgfJwJfck5TZAsbIAEkF2NVJi0AREN/dFouOw8wNk4RMTwdOg9iCS4WB2tNHWs2OhxaNE9fAQYDFn81MAwAGz8DGitHT0EHMQAOaVt1cCwGPWU1GCRiCywQBmVHUhM8OVgWIBUhe0xfZAMBOgtiU2sRACsMQAg8OlBTQ0Z1ck4VKzdUC0RiAGseG2UGRAA6JgtSCBMhPT0bKzVaBxwjGi5ZECIIegA+MQtTaQI6cjwWKSoAMRtsCCIFEG1NdhQqBB0ODAEycEJTKmxPdBwjHSBZAiQGQEljeklTaQM7NmRTZGVUGgc2By0OXWc8XA4jdlRaazInOwsXZCcBLQEsCWsSEiIcGkN6Xh0ULUYoe2QgLDUmbikmCg8eAywLURN7fXIpIRYHaC8XIAcBIBwtAGMMVREKTBVzaVhYGwMxNwseZAQ4GEggGyIbAWgGWkEwOxwfOkR5WE5TZGUgOwcuGiIHVXhPFjUhPR0JaQMjNxwKZC4aOx8sTioUASwZUUEwOxwfaQAnPQNTMC0RdAo3BycDWCwBFA06JwxUa0pfck5TZAMBOgtiU2sRACsMQAg8OlBTaScgJgEjITEHehonCi4SGAYAUAQgfDYVPQ8zK0dTISsQdBVrZBgfBRdVdQU3HRYKPBJ9cC0GNzEbOSstCi5VWWUUFDU2LAxadEZ3ERsAMCoZdAstCi5VWWUrUQcyIRQOaVt1cExfZBUYNQsnBiQbESAdFFxzdiwDOQN1M04QKyERekZsTGdXNiQDWAMyNxNadEYzJwAQMCwbOkBrTi4ZEWUSHWsAPAgocycxNiwGMDEbOkA5Th8SDTFPCUFxBh0eLAM4cg0GNzEbOUghAS8SV2lPchQ9N1hHaQAgPA0HLSoafEFITmtXVSkAVwA/dBsVLQN1b048NDEdOwYxQAgCBjEAWSI8MB1aKAgxciEDMCwbOhtsLT4EASoCdw43MVYsKAogN04cNmVWdmJiTmtXHCNPVw43MVhHdEZ3cE4HLCAadCYtGiIRDG1Ndw43MVpWaUQQPx4HPWdYdBwwGy5eTmUdURUmJhZaLAgxWE5TZGUmMQUtGi4EWyMGRgR7djsWKA84MwwfIQYbMA1gQmsUGiEKHVpzGhcOIAAsekwwKyERdkRiTB8FHCALDkFxdFZUaQU6NgtaTiAaMEg/R0F9WGhP1vXTtuz6q/LVcjoyBmVHdIrC+msnMBE8FIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyWw5PQ0SKGUkMRwOTnZXISQNR08DMQwJcycxNiIWIjEzJgc3HikYDW1NZwQ/OFhcaSs0PA8UIWdYdEoqCyoFAWdGPjE2IDRACAIxHg8RISlcL0gWCzMDVXhPFjI2OBRaOQMhIU4aKmUWIQQpTiQFVSoBUUwgPBcOZ0YXN04QJTcRMh0uTjweAS1PZwQ/OFg7BSp0cEJTACoRJz8wDztXSGUbRhQ2dAVTQzYwJiJJBSEQEAE0By8SB21GPjE2IDRACAIxBgEUIykRfEoDGz8YJiADWDE2IAtYZUYucjoWPDFUaUhgLz4DGmU8UQ0/dDk2BUYFNxoAZG0YOwcyR2lbVQEKUgAmOAxadEYzMwIAIWlUBgExBTJXSGUbRhQ2eHJaaUZ1BgEcKDEdJEh/TmknEDcGWwU6NxkWJR91NAcBITZUBw0uAgobGRUKQBJ9dC0JLEYiOxobZCYVJg1sTGd9VWVPFCIyOBQYKAU+clNTIjAaNxwrASVfA2xPdRQnOygfPRV7ARoSMCBaNR02ARgSGSk/URUgdEVaP111OwhTMmUAPA0sTgoCASo/URUgegsOKBQhekdTISsQdA0sCmsKXE8/URUfbjkeLTU5OwoWNm1WBw0uAhsSAQwBQAQhIhkWa0p1KU4nIT0AdFViTBgSGSlCRAQndBEUPQMnJA8fZmlUEA0kDz4bAWVSFFJjeFg3IAh1b05GaGU5NRBiU2tBRXVDFDM8IRYeIAgyclNTdGlUBx0kCCIPVXhPFkEgdlRwaUZ1ci0SKCkWNQspTnZXEzABVxU6OxZSP091ExsHKxURIBtsPT8WASBBRwQ/OCgfPS87JgsBMiQYdFViGGsSGyFPSUhZBB0OBVwUNgo3LTMdMA0wRmJ9JSAbeFsSMBw4PBIhPQBbP2UgMRA2TnZXVxYKWA1zFTQ2aRYwJh1TCgojdkRiKiQCFykKdw06NxNadEYhIBsWaE9UdEhiOiQYGTEGREFudFo1JwN4IQYcMGUnMQQuTgo7OWtPcA4mNhQfZAU5Ow0YZDEbdAstAC0eByhBFk1ZdFhaaSAgPA1TeWUSIQYhGiIYG21GFCAmIBcqLBImfB0WKCk1OARqR3BXOyobXQcqfFoqLBImcEJTZhYROAQDAidXEywdUQV9dlFaLAgxchNaTk8YOwsjAmsnEDE9FFxzABkYOkgFNxoAfgQQMDorCSMDMjcAQRExOwBSayMkJwcDZGNUFgctHT9VWWVNXwQqdlFwGQMhAFQyICE4NQonAmMMVREKTBVzaVhYBAc7Jw8fZDURIEgnHz4eBTZPVQ83dBoVJhUhchoBLSITMRoxTmM1ECBPdw4/OxYDZUYYJxoSMCwbOkgPDygfHCsKGEE2IBtTZ0R5ciocITYjJgkyTnZXATcaUUEufXIqLBIHaC8XIAEdIgEmCzlfXE8/URUBbjkeLSQgJhocKm0PdDwnFj9XSGVNYBM6Mx8fO0YYJxoSMCwbOkgPDygfHCsKFk1zEg0UKkZocggGKiYAPQcsRmJXJyACWxU2J1YcIBQwekwjITE5IRwjGiIYGwgOVwk6Oh0pLBQjOw0WGxcxdkFiCyUTVThGPjE2ICpACAIxEBsHMCoafBNiOi4PAWVSFEMGJx1aGQMhcj4cMSYcdkRiTmtXVWVPFEFzdFg8PAg2clNTIjAaNxwrASVfXGU9UQw8IB0JZwA8IAtbZhURIDgtGygfIDYKFkhzMRYeaRt8WD4WMBdOFQwmLD4DASoBHBpzAB0CPUZockwmNyBUEgkrHDJXOyAbFk1zdFhaaUZ1ck5TZGUyIQYhTnZXEzABVxU6OxZSYEYHNwMcMCAHeg4rHC5fVwMOXRMqGh0OCAUhOxgSMCAQdkFiCyUTVThGPjE2ICpACAIxEBsHMCoafBNiOi4PAWVSFEMGJx1aDwc8IBdTFzAZOQcsCzlVWWVPFEFzdFg8PAg2clNTIjAaNxwrASVfXGU9UQw8IB0JZwA8IAtbZgMVPRo7PT4aGCoBURMSNwwTPwchNwpRbWUROgxiE2J9JSAbZlsSMBw4PBIhPQBbP2UgMRA2TnZXVxAcUUEDMQxaBwc4N04hITcbOAQnHGlbVWVPFCcmOhtadEYzJwAQMCwbOkBrThkSGCobURJ9MhEILE53AgsHCiQZMTonHCQbGSAddQInPQ4bPQMxcEdTISsQdBVrZEFaWGWNoOGxwPiY3eZ1Bi8xZHFUtujWThs7NBwqZkGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOGxwPiY3ea3xu6R0MWWwOig+suV4cWNoOFZOBcZKAp1AgIBECcMGEh/Th8WFzZBZA0yLR0IcycxNiIWIjEgNQogATNfXE8DWwIyOFg3JhAwBg8RZHhUBAQwOikPOX8uUAUHNRpSays6JAseISsAdkFIAiQUFClPYgggABkYaUZocj4fNhEWLCR4Ly8TISQNHEMFPQsPKAomcEd5TggbIg0WDylNNCELeAAxMRRSMkYBNxYHZHhUdjsyCy4TWWUFQQwjdBkULUY4PRgWKSAaIEgqCycHEDccGkEBMVUbORY5OwsAZCoadBonHTsWAitBFk1zEBcfOjEnMx5TeWUAJh0nTjZefwgAQgQHNRpACAIxFgcFLSERJkBrZAYYAyA7VQNpFRweGgo8NgsBbGcjNQQpPTsSECFNGEEodCwfMRJ1b05REyQYP0gRHi4SEWdDFCU2MhkPJRJ1b05BdGlUGQEsTnZXRHNDFCwyLFhHaVRlYkJTFioBOgwrACxXSGVfGEEAIR4cIB51b05RZDYAIQwxQThVWU9PFEFzABcVJRI8Ik5OZGczNQUnTi8SEyQaWBVzPQtae1Z7cEJTByQYOAojDSBXSGUiWxc2OR0UPUgmNxokJSkfBxgnCy9XCGxleQ4lMSwbK1wUNgogKCwQMRpqTAECGDU/WxY2JlpWaR11BgsLMGVJdEoIGyYHVRUAQwQhdlRaDQMzMxsfMGVJdF1yQms6HCtPCUFmZFRaBActclNTd3VEeEgQAT4ZESwBU0FudEhWaSU0PgIRJSYfdFViIyQBECgKWhV9Jx0OAxM4Ij4cMyAGdBVrZAYYAyA7VQNpFRweHQkyNQIWbGc9Og4IGyYHV2lPFEEodCwfMRJ1b05RDSsSPQYrGi5XPzACREN/dDwfLwcgPhpTeWUSNQQxC2dXNiQDWAMyNxNadEYYPRgWKSAaIEYxCz8+GyMlQQwjdAVTQys6JAsnJSdOFQwmOiQQEikKHEMdOxsWIBZ3fk5TZGUPdDwnFj9XSGVNeg4wOBEKa0p1ck5TZGVUdCwnCCoCGTFPCUE1NRQJLEp1EQ8fKCcVNwNiU2s6GjMKWQQ9IFYJLBIbPQ0fLTVUKUFIIyQBEBEOVlsSMBw+IBA8NgsBbGx+GQc0Cx8WF38uUAUHOx8dJQN9cCgfPWdYdEhiTmtXVT5PYAQrIFhHaUQTPhdRaGUwMQ4jGycDVXhPUgA/Jx1WaTI6PQIHLTVUaUhgOQokMWVEFDIjNRsfZioGOgcVMGdYdCsjAicVFCYEFFxzGRcMLAswPBpdNyAAEgQ7TjZefwgAQgQHNRpACAIxAQIaICAGfEoEAjIkBSAKUEN/dFgBaTIwKhpTeWVWEgQ7ThgHECALFk1zEB0cKBM5Jk5OZH1EeEgPByVXSGVeBE1zGRkCaVt1Zl5DaGUmOx0sCiIZEmVSFFF/dDsbJQo3Mw0YZHhUGQc0CyYSGzFBRwQnEhQDGhYwNwpTOWx+GQc0Cx8WF38uUAUXPQ4TLQMnekd5CSoCMTwjDHE2ESE7WwY0OB1Sayc7JgcyAg5WeEhiTjBXISAXQEFudFo7JxI8fy81D2dYdCwnCCoCGTFPCUEnJg0fZUYBPQEfMCwEdFViTAkbGiYER0EnPB1ae1Z4PwcdZCwQOA1iBSIUHmtNGEEQNRQWKwc2OU5OZAgbIg0vCyUDWzYKQCA9IBE7Dy11L0d5CSoCMQUnAD9ZBiAbdQ8nPTk8Ak4hIBsWbU85Ox4nOioVTwQLUCU6IhEeLBR9e2Q+KzMRAAkgVAoTERYDXQU2JlBYAQ8hMAELZmlUdEhiFWsjED0bFFxzdjATPQQ6Kk4ALT8RdkRiKi4RFDADQEFudEpWaSs8PE5OZHdYdCUjFmtKVXdfGEEBOw0ULQ87NU5OZHVYdDs3CC0eDWVSFENzJwwPLRV3fmRTZGVUAActAj8eBWVSFEMRPR8dLBR1IAEcMGUENRo2TnZXAiwLURNzNxcWJQM2JgccKmUGNQwrGzhZV2lPdwA/OBobKg11b04+KzMROQ0sGmUEEDEnXRUxOwBaNE9fHwEFIREVNlIDCi8zHDMGUAQhfFFwBAkjNzoSJn81MAwAGz8DGitHT0EHMQAOaVt1cD0SMiBUNx0wHC4ZAWUfWxI6IBEVJ0R5cigGKiZUaUgkGyUUASwAWkl6dBEcaSs6JAseISsAehsjGC4nGjZHHUEnPB0UaSg6JgcVPW1WBAcxTGdVJiQZUQV9dlFaLAomN049KzEdMhFqTBsYBmdDFi88dBsSKBR3fhoBMSBddA0sCmsSGyFPSUhZGRcMLDI0MFQyICE2IRw2ASVfDmU7URkndEVaazQwMQ8fKGUHNR4nCmsHGjYGQAg8OlpWaSAgPA1TeWUSIQYhGiIYG21GFAg1dDUVPwM4NwAHajcRNwkuAhsYBm1GFBU7MRZaBwkhOwgKbGckOxtgQmklECYOWA02MFZYYEYwPh0WZAsbIAEkF2NVJSocFk1xGhcOIQ87NU4AJTMRMEpuGjkCEGxPUQ83dB0ULUYoe2R5EiwHAAkgVAoTEQkOVgQ/fANaHQMtJk5OZGcjOxouCmsbHCIHQAg9M1ZYZUYRPQsAEzcVJEh/Tj8FACBPSUhZAhEJHQc3aC8XIAEdIgEmCzlfXE85XRIHNRpACAIxBgEUIykRfEoEGycbFzcGUwkndlRaMkYBNxYHZHhUdi43AicVBywIXBVxeFg+LAA0JwIHZHhUMgkuHS5bVQYOWA0xNRsRaVt1BAcAMSQYJ0YxCz8xACkDVhM6MxAOaRt8WDgaNxEVNlIDCi8jGiIIWAR7djYVDwkycEJTZGVUdEg5Th8SDTFPCUFxBh0XJhAwcggcI2dYdCwnCCoCGTFPCUE1NRQJLEp1EQ8fKCcVNwNiU2shHDYaVQ0gegsfPSg6FAEUZDhdXmIuASgWGWU/WBMHNgAoaVt1Bg8RN2skOAk7CzlNNCELZgg0PAwuKAQ3PRZbbU8YOwsjAmsjBRUgfRJzdFhadEYFPhwnJj0mbikmCh8WF21NeQAjdCg1ABV3e2QfKyYVOEgWHhsbFDwKRhJzaVgqJRQBMBYhfgQQMDwjDGNVJSkOTQQhdCwqa09fWDoDFAo9J1IDCi87FCcKWEkodCwfMRJ1b05RCysReQsuBygcVTEKWAQjOwoOOkh1HD4wZCsVOQ0xTioFEGUJQRspLVUXKBI2OgsXZCwadB8tHCAEBSQMUU9xeFg+JgMmBRwSNGVJdBwwGy5XCGxlYBEDGzEJcycxNioaMiwQMRpqR0ERGjdPa01zMVgTJ0Y8Ig8aNjZcAA0uCzsYBzEcGg06JwxSYE91NgF5ZGVUdAQtDSobVSsOWQRzaVgfZwg0Pwt5ZGVUdDwyPgQ+Bn8uUAURIQwOJgh9KU4nIT0AdFViTKnx52VNFE99dBYbJAN5cigGKiZUaUgkGyUUASwAWkl6XlhaaUZ1ck5TLSNUOgc2Th8SGSAfWxMnJ1YdJk47MwMWbWUAPA0sTgUYASwJTUlxAChYZUY7MwMWZGtadEpiACQDVSMAQQ83dlRaPRQgN0d5ZGVUdEhiTmsSGTYKFC88IBEcME53Bj5RaGVWtu7QTmlXW2tPWgA+MVFaLAgxWE5TZGUROgxiE2J9ECsLPms/OxsbJUYzJwAQMCwbOkglCz8nGSQWURMdNRUfOk58WE5TZGUYOwsjAmsYADFPCUEoKXJaaUZ1NAEBZBpYdBhiByVXHDUOXRMgfCgWKB8wIB1JAyAABAQjFy4FBm1GHUE3O3JaaUZ1ck5TZCwSdBhiEHZXOSoMVQ0DOBkDLBR1JgYWKmUANQouC2UeGzYKRhV7Ow0OZUYlfCASKSBddA0sCkFXVWVPUQ83XlhaaUY8NE5QKzAAdFV/TntXAS0KWkEnNRoWLEg8PB0WNjFcOx02QmtVXSsAWgR6dlFaLAgxWE5TZGUGMRw3HCVXGjAbPgQ9MHIuOTY5MxcWNjZOFQwmIioVEClHT0EHMQAOaVt1cDoWKCAEOxo2Tj8YVSobXAQhdAgWKB8wIB1TLStUIAAnTjgSBzMKRk9xeFg+JgMmBRwSNGVJdBwwGy5XCGxlYBEDOBkDLBQmaC8XIAEdIgEmCzlfXE87RDE/NQEfOxVvEwoXADcbJAwtGSVfVxEfZA0yLR0Ia0p1KU4nIT0AdFViTBsbFDwKRkN/dC4bJRMwIU5OZCIRIDguDzISBwsOWQQgfFFWaSIwNA8GKDFUaUhgRiUYGyBGFk1zFxkWJQQ0MQVTeWUSIQYhGiIYG21GFAQ9MFgHYGwBIj4fJTwRJht4Ly8TNzAbQA49fANaHQMtJk5OZGcmMQ4wCzgfVSkGRxVxeFg8PAg2clNTIjAaNxwrASVfXE9PFEFzPR5aBhYhOwEdN2sgJDguDzISB2UOWgVzGwgOIAk7IUAnNBUYNREnHGUkEDE5VQ0mMQtaPQ4wPE48NDEdOwYxQB8HJSkOTQQhbisfPTA0PhsWN20TMRwSAioOEDchVQw2J1BTYEYwPAp5ISsQdBVrZB8HJSkOTQQhJ0I7LQIXJxoHKytcL0gWCzMDVXhPFjU2OB0KJhQhchocZDYROA0hGi4TV2lPchQ9N1hHaQAgPA0HLSoafEFITmtXVSkAVwA/dBZadEYaIhoaKysHejwyPicWDCAdFAA9MFg1ORI8PQAAahEEBAQjFy4FWxMOWBQ2XlhaaUY5PQ0SKGUEdFViAGsWGyFPZA0yLR0IOlwTOwAXAiwGJxwBBiIbEW0BHWtzdFhaIAB1Ik4SKiFUJEYBBioFFCYbURNzIBAfJ2x1ck5TZGVUdAQtDSobVS0dREFudAhUCg40IA8QMCAGbi4rAC8xHDccQCI7PRQeYUQdJwMSKiodMDotAT8nFDcbFkhZdFhaaUZ1ck4aImUcJhhiGiMSG2U6QAg/J1YOLAowIgEBMG0cJhhsPiQEHDEGWw9zf1gsLAUhPRxAaisRI0BwQmtHWWVfHUhzMRYeQ0Z1ck4WKiF+MQYmTjZef09CGUGxwPiY3ea3xu5TEAQ2dF1ijMvjVQgmZyJztuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVWAIcJyQYdCUrHSg7VXhPYAAxJ1Y3IBU2aC8XIAkRMhwFHCQCBScATElxExkXLEZzci0GNjcROgs7TGdXVywBUg5xfXI3IBU2HlQyICE4NQonAmMMVREKTBVzaVhYDgc4N04aKiMbdAksCmsOGjAdFA06Ih1aGg4wMQUfITZUNgkuDyUUEGtNGEEXOx0JHhQ0Ik5OZDEGIQ1iE2J9OCwcVy1pFRweDQ8jOwoWNm1dXiUrHSg7TwQLUC0yNh0WYU53AgISJyBOdE0xTGJNEyodWQAnfDsVJwA8NUA0BQgxCyYDIw5eXE8iXRIwGEI7LQIZMwwWKG1cdjguDygSVQwrDkF2MFpTcwA6IAMSMG03OwYkByxZJQkudyQMHTxTYGwYOx0QCH81MAwODykSGW1HFiIhMRkOJhRvcksAZmxOMgcwAyoDXQYAWgc6M1Y5GyMUBiEhbWx+GQExDQdNNCELcAglPRwfO058WAIcJyQYdAQgAhgfED1PCUEePQsZBVwUNgo/JScROEBgPSMSFi4DURJpdFVYYGxfPgEQJSlUGQExDRlXSGU7VQMgejUTOgVvEwoXFiwTPBwFHCQCBScATElxBx0IPwMncEJTZjIGMQYhBmlefwgGRwIBbjkeLSo0MAsfbD5UAA06GmtKVWc9UQs8PRZaPQ48IU4AITcCMRpiATlXHSofFBU8dBlaLxQwIQZTNDAWOAEhTjgSBzMKRk9xeFg+JgMmBRwSNGVJdBwwGy5XCGxleQggNypACAIxFgcFLSERJkBrZAYeBiY9DiA3MDoPPRI6PEYIZBERLBxiU2tVJyAFWwg9dAwSIBV1IQsBMiAGdkRITmtXVQMaWgJzaVgcPAg2JgccKm1ddA8jAy5NMiAbZwQhIhEZLE53BgsfITUbJhwRCzkBHCYKFkhpAB0WLBY6IBpbByoaMgElQBs7NAYqaygXeFg2JgU0Pj4fJTwRJkFiCyUTVThGPiw6JxsocycxNiwGMDEbOkA5Th8SDTFPCUFxBx0IPwMncgYcNGVcJgksCiQaXGdDPkFzdFg8PAg2clNTIjAaNxwrASVfXE9PFEFzdFhaaSg6JgcVPW1WHAcyTGdXVxYKVRMwPBEULkh7fExaTmVUdEhiTmtXASQcX08gJBkNJ04zJwAQMCwbOkBrZGtXVWVPFEFzdFhaaQo6MQ8fZBEndFViCSoaEH8oURUAMQoMIAUwekwnISkRJAcwGhgSBzMGVwRxfXJaaUZ1ck5TZGVUdEguASgWGWUnQBUjBx0IPw82N05OZCIVOQ14KS4DJiAdQggwMVBYARIhIj0WNjMdNw1gR0FXVWVPFEFzdFhaaUY5PQ0SKGUbP0RiHC4EVXhPRAIyOBRSLxM7MRoaKytcfWJiTmtXVWVPFEFzdFhaaUZ1IAsHMTcadA8jAy5NPTEbRCY2IFBSaw4hJh4AfmpbMwkvCzhZByoNWA4rehsVJEkjY0EUJSgRJ0dnCmQEEDcZURMgeygPKwo8MVEAKzcAGxomCzlKNDYMEg06OREOdFdlYkxafiMbJgUjGmM0GisJXQZ9BDQ7CiMKGypabU9UdEhiTmtXVWVPFEE2OhxTQ0Z1ck5TZGVUdEhiTiIRVSsAQEE8P1gOIQM7ciAcMCwSLUBgJiQHV2lNfBUnJD8fPUYzMwcfISFadkQ2HD4SXH5PRgQnIQoUaQM7NmRTZGVUdEhiTmtXVWUDWwIyOFgVIlR5cgoSMCRUaUgyDSobGW0JQQ8wIBEVJ058chwWMDAGOkgKGj8HJiAdQggwMUIwGikbFgsQKyERfBonHWJXECsLHWtzdFhaaUZ1ck5TZGUdMkgsAT9XGi5dFA4hdBYVPUYxMxoSZCoGdAYtGmsTFDEOGgUyIBlaPQ4wPE49KzEdMhFqTAMYBWdDFiMyMFgILBUlPQAAIWtWeBwwGy5eTmUdURUmJhZaLAgxWE5TZGVUdEhiTmtXVSMARkEMeFgJOxB1OwBTLTUVPRoxRi8WASRBUAAnNVFaLQlfck5TZGVUdEhiTmtXVWVPFAg1dAsIP0glPg8KLSsTdAksCmsEBzNBWQArBBQbMAMnIU4SKiFUJxo0QDsbFDwGWgZzaFgJOxB7Pw8LFCkVLQ0wHWtaVXRPVQ83dAsIP0g8Nk4NeWUTNQUnQAEYFwwLFBU7MRZwaUZ1ck5TZGVUdEhiTmtXVWVPFEEHB0IuLAowIgEBMBEbBAQjDS4+GzYbVQ8wMVA5JggzOwldFAk1Fy0dJw9bVTYdQk86MFRaBQk2MwIjKCQNMRprVWsFEDEaRg9ZdFhaaUZ1ck5TZGVUdEhiTi4ZEU9PFEFzdFhaaUZ1ck4WKiF+dEhiTmtXVWVPFEFzGhcOIAAsekw7KzVWeEoMAWsEEDcZURNzMhcPJwJ7cEIHNjARfWJiTmtXVWVPFAQ9MFFwaUZ1cgsdIGUJfWJIQ2ZXOSwZUUEmJBwbPQMmWBoSNy5aJxgjGSVfEzABVxU6OxZSYGx1ck5TMy0dOA1iGioEHmsYVQgnfElTaQI6WE5TZGVUdEhiHigWGSlHUhQ9NwwTJgh9e2RTZGVUdEhiTmtXVWUGUkE/NhQqJQc7JgsXZGVUNQYmTicVGRUDVQ8nMRxUGgMhBgsLMGVUdBwqCyVXGScDZA0yOgwfLVwGNxonIT0AfEoSAioZASALFEFzblhYaUh7cj0HJTEHehguDyUDECFGFAQ9MHJaaUZ1ck5TZGVUdEgrCGsbFyknVRMlMQsOLAJ1MwAXZCkWOCAjHD0SBjEKUE8AMQwuLB4hchobIStUOAouJioFAyAcQAQ3bisfPTIwKhpbZg0VJh4nHT8SEWVVFENzelZaGhI0Jh1dLCQGIg0xGi4TXGUKWgVZdFhaaUZ1ck5TZGVUPQ5iAikbNyoaUwkndFhaaQc7Nk4fJik2Ox0lBj9ZJiAbYAQrIFhaaUYhOgsdZCkWOCotGywfAX88URUHMQAOYUQGOgEDZCcBLRtiVGtVVWtBFDInNQwJZwQ6JwkbMGxUMQYmZGtXVWVPFEFzdFhaaQ8zcgIRKBYbOAxiTmtXVWUOWgVzOBoWGgk5NkAgITEgMRA2TmtXVWVPQAk2OlgWKwoGPQIXfhYRIDwnFj9fVxYKWA1zNxkWJRVvckxTamtUBxwjGjhZBioDUEhzMRYeQ0Z1ck5TZGVUdEhiTiIRVSkNWDQjIBEXLEZ1ck4SKiFUOAouOzsDHCgKGjI2ICwfMRJ1ck5TMC0ROkguDCciBTEGWQRpBx0OHQMtJkZRETUAPQUnTmtXVX9PFkF9elgpPQchIUAGNDEdOQ1qR2JXECsLPkFzdFhaaUZ1ck5TZCwSdAQgAhgfED1PFEFzdFgbJwJ1PgwfFy0RLEYRCz8jED0bFEFzdFhaPQ4wPE4fJiknPA06VBgSAREKTBV7disSLAU+PgsAfmVWdEZsTh4DHCkcGgY2ICsSLAU+PgsAbGxddA0sCkFXVWVPFEFzdB0ULU9fck5TZCAaMGInAC9ef09CGUGxwPiY3ea3xu5TEAQ2dFBijMvjVQY9cSUaACtaq/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTtuz6q/LVsPrzptH0tvzCjN/3l9Hv1vXTXhQVKgc5ci0BCGVJdDwjDDhZNjcKUAgnJ0I7LQIZNwgHAzcbIRggATNfVwQNWxQndAwSIBV1GhsRZmlUdgEsCCRVXE8sRi1pFRweBQc3NwJbP2UgMRA2TnZXVwIdWxZzNVg9KBQxNwBTpsXgdDFwJWs/ACdNGEEXOx0JHhQ0Ik5OZDEGIQ1iE2J9NjcjDiA3MDQbKwM5ehVTECAMIEh/Tmk2VSYDUQA9eFgcPAo5K04QMTYAOwUrFCoVGSBPUwAhMB0UZAcgJgEeJTEdOwZiBj4VW2dDFCU8MQstOwclclNTMDcBMUg/R0E0BwlVdQU3EBEMIAIwIEZaTgYGGFIDCi87FCcKWEl7disZOw8lJk4FITcHPQcsTnFXUDZNHVs1OwoXKBJ9EQEdIiwTejsBPAInIRo5cTN6fXI5OypvEwoXCCQWMQRqTB4+VSkGVhMyJgFaaUZ1clRTCycHPQwrDyUiHGdGPiIhGEI7LQIZMwwWKG1WASFiDz4DHSodFEFzdFhac0YMYAVTFyYGPRg2TgkWFi5ddgAwP1pTQyUnHlQyICE4NQonAmNfVxYOQgRzMhcWLQMnck5TZH9UcRtgR3ERGjcCVRV7FxcULw8yfD0yEgArBicNOmJef08DWwIyOFg5OzR1b04nJScHeiswCy8eATZVdQU3BhEdIRISIAEGNCcbLEBgOioVVQIaXQU2dlRaaws6PAcHKzdWfWIBHBlNNCELeAAxMRRSMkYBNxYHZHhUdjk3BygcVTcKUgQhMRYZLEa30vpTMy0VIEgnDygfVTEOVkE3Ox0Jc0R5ciocITYjJgkyTnZXATcaUUEufXI5OzRvEwoXACwCPQwnHGNefwYdZlsSMBw2KAQwPkYIZBERLBxiU2tVl8XNFCYyJhwfJ0a30vpTBTAAO0gyAioZAWVAFAkyJg4fOhJ1fU4QKykYMQs2TmRXBiADWEF8dA8bPQMnfExfZAEbMRsVHCoHVXhPQBMmMVgHYGwWIDxJBSEQGAkgCydfDmU7URkndEVaa4TV8E4gLCoEdIrC+ms2ADEAGQMmLVgJLAMxIUJTIyAVJkRiCywQBmlPURc2OgwJZUY2PQoWN2tWeEgGAS4EIjcOREFudAwIPAN1L0d5BzcmbikmCgcWFyADHBpzAB0CPUZockyRxOdUBA02HWuV9dFPZwQ/OFgKLBImfk4eMTEVIAEtAGsaFCYHXQ82eFgYJgkmJh1dZmlUEAcnHRwFFDVPCUEnJg0faRt8WC0BFn81MAwODykSGW0UFDU2LAxadEZ3sO7RZBUYNREnHGuV9dFPeQ4lMRUfJxJ5cggfPWlUOgchAiIHWWUbUQ02JBcIPRV5chgaNzAVOBtsTGdXMSoKRzYhNQhadEYhIBsWZDhdXiswPHE2ESEjVQM2OFABaTIwKhpTeWVWtujgTgYeBiZP1uHHdCsSLAU+PgsAaGUHMRo0CzlXByAFWwg9exAVOUh3fk43KyAHAxojHmtKVTEdQQRzKVFwChQHaC8XIAkVNg0uRjBXISAXQEFudFqYycR1EQEdIiwTJ0ig7t9XJiQZUU4/OxkeaRYnNx0WMGUEJgckBycSBmtNGEEXOx0JHhQ0Ik5OZDEGIQ1iE2J9Njc9DiA3MDQbKwM5ehVTECAMIEh/TmmV9edPZwQnIBEULhV1sO7nZBA9dBgwCy0EWWUOVxU6OxZaIQkhOQsKN2lUIAAnAy5ZV2lPcA42Jy8IKBZ1b04HNjARdBVrZEFaWGWNoOGxwPiY3eZ1Bi8xZHJUtujWThgyIREmeiYAdJruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9U8DWwIyOFgpLBIZclNTECQWJ0YRCz8DHCsIR1sSMBw2LAAhFRwcMTUWOxBqTAIZASAdUgAwMVpWaUQ4PQAaMCoGdkFIPS4DOX8uUAUfNRofJU4ucjoWPDFUaUhgOCIEACQDFBEhMR4fOwM7MQsAZCMbJkg2Bi5XGCABQUE6IAsfJQB7cEJTACoRJz8wDztXSGUbRhQ2dAVTQzUwJiJJBSEQEAE0By8SB21GPjI2IDRACAIxBgEUIykRfEoRBiQANjAcQA4+Fw0IOgkncEJTP2UgMRA2TnZXVwYaRxU8OVg5PBQmPRxRaGUwMQ4jGycDVXhPQBMmMVRwaUZ1ci0SKCkWNQspTnZXEzABVxU6OxZSP091HgcRNiQGLUYRBiQANjAcQA4+Fw0IOgknclNTMmUROgxiE2J9JiAbeFsSMBw2KAQwPkZRBzAGJwcwTggYGSodFkhpFRweCgk5PRwjLSYfMRpqTAgCBzYARiI8OBcIa0p1KWRTZGVUEA0kDz4bAWVSFCI8Oh4TLkgUES02ChFYdDwrGicSVXhPFiImJgsVO0YWPQIcNmdYXkhiTms0FCkDVgAwP1hHaQAgPA0HLSoafAtrTgceFzcORhhpBx0OChMnIQEBByoYOxpqDWJXECsLFBx6XisfPSpvEwoXADcbJAwtGSVfVwsAQAg1LSsTLQN3fk4IZBMVOB0nHWtKVT5PFi02MgxYZUZ3AAcULDFWdBVuTg8SEyQaWBVzaVhYGw8yOhpRaGUgMRA2TnZXVwsAQAg1PRsbPQ86PE4ALSERdkRITmtXVQYOWA0xNRsRaVt1NBsdJzEdOwZqGGJXOSwNRgAhLUIpLBIbPRoaIjwnPQwnRj1eVSABUEEufXIpLBIZaC8XIAEGOxgmATwZXWc6fTIwNRQfa0p1KU4lJSkBMRtiU2sMVWdYAURxeFpLeVZwcEJRdXdBcUpuTHpCRWBNFBx/dDwfLwcgPhpTeWVWZVhyS2lbVREKTBVzaVhYHC91AQ0SKCBWeGJiTmtXNiQDWAMyNxNadEYzJwAQMCwbOkA0R2s7HCcdVRMqbisfPSIFGz0QJSkRfBwtAD4aFyAdHBdpMwsPK053d0tRaGdWfUFrTi4ZEWUSHWsAMQw2cycxNioaMiwQMRpqR0EkEDEjDiA3MDQbKwM5ekw+ISsBdCMnFykeGyFNHVsSMBwxLB8FOw0YITdcdiUnAD48EDwNXQ83dlRaMkYRNwgSMSkAdFViLSQZEywIGjUcEz82DDkeFzdfZAsbASFiU2sDBzAKGEEHMQAOaVt1cDocIyIYMUgPCyUCV2USHWsAMQw2cycxNioaMiwQMRpqR0EkEDEjDiA3MDoPPRI6PEYIZBERLBxiU2tVICsDWwA3dDAPK0R5ciocMScYMSsuBygcVXhPQBMmMVRwaUZ1cjocKykAPRhiU2tVJyACWxc2J1gOIQN1BydTJSsQdAwrHSgYGysKVxUgdB0MLBQsJgYaKiJadkRITmtXVQMaWgJzaVgcPAg2JgccKm1ddDcFQBJFPhoodSYMHC04FioaEyo2AGVJdAYrAnBXOSwNRgAhLUIvJwo6MwpbbWUROgxiE2J9fykAVwA/dCsfPTR1b04nJScHejsnGj8eGyIcDiA3MCoTLg4hFRwcMTUWOxBqTAoUASwAWkEbOwwRLB8mcEJTZi4RLUprZBgSARdVdQU3GBkYLAp9KU4nIT0AdFViTBoCHCYEFAo2LQtaLwkncgEdIWgHPAc2TioUASwAWhJ9dlRaDQkwITkBJTVUaUg2HD4SVThGPjI2ICpACAIxFgcFLSERJkBrZBgSARdVdQU3GBkYLAp9cD0WKClUMgctCmleTwQLUCo2LSgTKg0wIEZRDCoAPw07PS4bGWdDFBpZdFhaaSIwNA8GKDFUaUhgKWlbVQgAUARzaVhYHQkyNQIWZmlUAA06GmtKVWc8UQ0/dlRwaUZ1ci0SKCkWNQspTnZXEzABVxU6OxZSKAUhOxgWbWUdMkgjDT8eAyBPQAk2OlgoLAs6JgsAaiMdJg1qTBgSGSkpWw43dlFBaSg6JgcVPW1WHAc2BS4OV2lNZwQ/OFZYYEYwPApTISsQdBVrZBgSARdVdQU3GBkYLAp9cDkSMCAGdA8jHC8SGzZNHVsSMBwxLB8FOw0YITdcdiAtGiASDBIOQAQhdlRaMmx1ck5TACASNR0uGmtKVWcnFk1zGRceLEZockwnKyITOA1gQmsjED0bFFxzdi8bPQMncEJ5ZGVUdCsjAicVFCYEFFxzMg0UKhI8PQBbJSYAPR4nR2seE2UOVxU6Ih1aPQ4wPE4hISgbIA0xQCIZAyoEUUlxAxkOLBQSMxwXISsHdkF5TgUYASwJTUlxHBcOIgMscEJREyQAMRpsTGJXECsLFAQ9MFgHYGwGNxohfgQQMCQjDC4bXWc7WwY0OB1aCBMhPU4jKCQaIEprVAoTEQ4KTTE6NxMfO053GgEHLyANBAQjAD9VWWUUPkFzdFg+LAA0JwIHZHhUdjhgQms6GiEKFFxzdiwVLgE5N0xfZBERLBxiU2tVJSkOWhVxeHJaaUZ1EQ8fKCcVNwNiU2sRACsMQAg8OlAbKhI8JAtaTmVUdEhiTmtXHCNPVQInPQ4faRI9NwB5ZGVUdEhiTmtXVWVPXQdzFQ0OJiE0IAoWKmsnIAk2C2UWADEAZA0yOgxaPQ4wPE4yMTEbEwkwCi4ZWzYbWxESIQwVGQo0PBpbbX5UGgc2By0OXWcnWxU4MQFYZUQFPg8dMGU7Ei5gR0FXVWVPFEFzdFhaaUYwPh0WZAQBIAcFDzkTECtBRxUyJgw7PBI6AgISKjFcfVNiICQDHCMWHEMbOwwRLB93fkwjKCQaIEgNIGleVSABUGtzdFhaaUZ1cgsdIE9UdEhiCyUTVThGPjI2ICpACAIxHg8RISlcdjonDSobGWUcVRc2MFgKJhV3e1QyICE/MRESBygcEDdHFik8IBMfMDQwMQ8fKGdYdBNITmtXVQEKUgAmOAxadEZ3AExfZAgbMA1iU2tVISoIUw02dlRaHQMtJk5OZGcmMQsjAidVWU9PFEFzFxkWJQQ0MQVTeWUSIQYhGiIYG20OVxU6Ih1TaQ8zcg8QMCwCMUg2Bi4ZVQgAQgQ+MRYOZxQwMQ8fKBUbJ0BrVWs5GjEGUhh7djAVPQ0wK0xfZhcRNwkuAi4TW2dGFAQ9MFgfJwJ1L0d5TgkdNhojHDJZISoIUw02Hx0DKw87Nk5OZAoEIAEtADhZOCABQSo2LRoTJwJfWENeZKfg1IrW7qnj9WU7XAQ+MVhRaTU0JAtTJSEQOwYxTqnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1JruyYTB0oznxKfg1IrW7qnj9af7tIPH1HITL0YBOgseIQgVOgklCzlXFCsLFDIyIh03KAg0NQsBZDEcMQZITmtXVREHUQw2GRkUKAEwIFQgITE4PQowDzkOXQkGVhMyJgFTQ0Z1ck4gJTMRGQksDywSB388URUfPRoIKBQseiIaJjcVJhFrZGtXVWU8VRc2GRkUKAEwIFQ6IysbJg0WBi4aEBYKQBU6Oh8JYU9fck5TZBYVIg0PDyUWEiAdDjI2IDEdJwknNycdICAMMRtqFWtVOCABQSo2LRoTJwJ3chNaTmVUdEgWBi4aEAgOWgA0MQpAGgMhFAEfICAGfCstAC0eEms8dTcWCyo1BjJ8WE5TZGUnNR4nIyoZFCIKRlsAMQw8JgoxNxxbByoaMgElQBg2IwAwdycUB1FwaUZ1cj0SMiA5NQYjCS4FTwcaXQ03FxcULw8yAQsQMCwbOkAWDykEWwYAWgc6MwtTQ0Z1ck4nLCAZMSUjACoQEDdVdREjOAEuJjI0MEYnJScHejsnGj8eGyIcHWtzdFhaOQU0PgJbIjAaNxwrASVfXGU8VRc2GRkUKAEwIFQ/KyQQFR02AScYFCEsWw81PR9SYEYwPApaTiAaMGJIICQDHCMWHEMKZjNaARM3cEJTZgkbNQwnCmsRGjdPFkF9elg5JggzOwldAwQ5ETcMLwYyVWtBFEN9dCgILBUmcjwaIy0AFxwwAmsDGmUbWwY0OB1Ua09fIhwaKjFcfEoZN3k8KGUjWwA3MRxaLwkncksAZG0kOAkhCwITVWALHU9xfUIcJhQ4MxpbByoaMgElQAw2OAAweiAeEVRaCgk7NAcUahU4FSsHMQIzXGxl'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Grow A garden/Grow-a-garden', checksum = 2958163137, interval = 2, antiSpy = { kick = true, halt = true } })
