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

local __k = 'xRvtrD0bFzmWP699RMurRtGR'
local __p = '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KBYEGWJjQ0V+VHd8QGNWWV9kdRolHwE7NVhNM3JtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyHT4FERsiEA8pHgh3bQsZGxYoFhc8AGd6TmJbTEJhGUBmDgUyPjwZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHICFQAjVRYLEwN7cEJYSzUoAT8zDGdvWGJYQUJoEFJoTFh3fRsZfiAoFAZYVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFIhXBEjWkB6cGRYVzYiGHhyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEIyGx8wNUJ0UDxhVQYzBiA3DB8XDFJ5EFJoSF17cAYXAGpHVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHITGhZOEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWgg7I1MzGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGc7HnIbGxYhEF97Wk8HNURfXDE5VVpjRHd3WH9WBhs3WxtvWE0jOFNXM3JtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVAYlQgUjDiA+PhoZTTM/EhcmOSYqWG9WRFx9B05mS0NncBsUGQIoBxQ3FzNYWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEIjFh4yOVAZVD0pEFJvSWdwPz0ZEFJsCFJrQ1hyeRQZTTooG3hyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEIyGx8wNUJ0UDxhVQYzBiA3DB8XDFJ5EFJoQlx7cAYXAGRtWF9yMT8xHT4aERwwOkJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZXD4+EBs0VCo9HDdWSU9kEiYjGQg5JBYRD2JgTUJ3XWVyDDoTGnhkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXI5FAA1ETMfETxaVAYlQgUjDiA2KBYEGWJjQ0N+VHd8T2tWWV9kdxAjGxldcBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVI3GDQ3WH9bVCAlXgYpF2d3cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGcm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JBYEGXouAAAgESkmKj0ZAFwUXxEvDgQ4PhYUGSYsBxU3ABc9C3tYORMjXgsyDwkyWhYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWDsQVBYtQxZmRk1vcEJRXDxHVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWg8lNVdSM3JtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVBcqVGhmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJ/WWcAHX8fBwExVUILFRsyBFkZUDRtAR09VCEzCnJeBhc3VRY1Whk+PVNWTCZkf1JyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEAsgWgk+I0IZB3J+RVImHCI8cnJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXIlAB9oOSgkHQYZXAYlQgUjDj04Ix8zGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWERwgOkJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZXDwpf1JyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWABM3W0wxGwQjeAYXCntHVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVCI8HFhWVFJkEEJmWk13cBYZGXJtVVJyVGdyWHJWVFJkOkJmWk13cBYZGXJtVVJyVGdyWHJWVFJkEEJmWk16fRZrXCE5GgA3VCk9Cj8XGFITUQ4tKR0yNVIzGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVRonGWkFGT4dJwIhVQZmR01mZjwZGXJtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtf1JyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVJyVGd/VXIiER4hQA00Dk0yKFdaTT40VR08AChyEzsVH1I0UQZmDgJ3N0NYSzMjARc3VCUnDCYZGlIyWREvGAQ7OUJAM3JtVVJyVGdyWHJWVFJkEEJmWk13cBYZGXJtVVIgGygmVhEwBhMpVUJ7Wi4RIldUXHwjEAV6Hy4xEwIXEFwUXxEvDgQ4PhYSGQQoFgY9BnR8FjcBXEJoEFFqWl1+eTwZGXJtVVJyVGdy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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
