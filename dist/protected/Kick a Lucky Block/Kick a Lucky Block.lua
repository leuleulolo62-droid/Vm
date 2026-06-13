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

local __k = 'PyxeGbrbwe7QRbFTam0Nne7G'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
