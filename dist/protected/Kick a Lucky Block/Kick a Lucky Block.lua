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

local __k = 'WCzEFZXAkzAT9oyBtbfVB0J5'
local __p = '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QU9EYkRMUGFuEHobb3JaaGt6HTkIHy04XAENSFRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVMi8JIC88eCwEHiR0BFJZYDAHBTMsRGodYXNXfXZ/cWNLDikxV2VZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2MOJDQ9PTUmEy94GRsYMBMHEhsjSGoId3NUcHZ2eHFFTHR0FEJZBQYHByJIEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWY/NDIOWmx5GT0YLBANC1xiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGEfGzMzXBs0KxpORiIjQi1QIw4bPWZneHFFSHF4GV9Xe0xoRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2MfKyJQeGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWiQ4SgpzYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGpcMWMXKiI/eHxWWmMEXB0fJxcWRn5zAHoQd25aNy8pMzhCWGEgUQoXSFRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZTI7KiYODgw9V0NZNhUQATM2fStNd35adWhjb21LS29kGUJUYiQHFDAnUz4/d2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGEOFjIxUAlZLxsGA3Z/DWoXECwVIWZyYHFGQ3RxEE1ZNhwHCFxiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGEfGzMzXBs0KxpORiIjQi1QIw4bPWZneHFFQnB4GV9Xe0JCS3tidTJWMi8WICguUmFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZJxgRAz8kECdaMyZaeHt6egUOGSQ6TU9RdERPXmZnGWgVIysfK0x6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlQWByQlVT54Pi1WZTI7KiYODgw1QU9EYkRMUGduEHobYHpaaGt6HzMOGzVeGU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnYnXDlQd25XZRQ7NiUEF0t0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGpB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TU9EYlwBEyQwVSRBBSwVMWgKNzICDig7V09UYgADFDEnRBpaJGpUCCc9NigfDyUxM09ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVdyocZSIzKzVLRmFsGRsRJxpoRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWiMmXA4SSFRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZSM0PEtLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZvHWpnMm4TNjUvPWEmFTcxbQBZKxJCEjktECxUJWNSNyMpPTUYWjU9VAoWNwBLbHZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eCgNWiU9ShtZfFRRVnY2WC9bXWNaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlQKEzt4fSVDMhcVbTI7KiYODhE7SkZzYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaICg+UmFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZJxoGbHZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaMScpM28cGyggEV9XcV1oRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEC9bM0laZWZ6eGFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6UmFLWmF0GU9ZYlRCRnZiEGoVd2NaZWZ6eGFLWmF5FE8rJwcWCSQnECRaJS4bKWYNOS0AKTExXAtzYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRj43XWRiNi8RFjY/PSVLR2FlD2VZYlRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCbHZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnZiEGoYemMuICo/KC4ZDmExQQ4aNhgbRjksRCUVPCoZLmYqOSVLDi50XhoYMBUMEjMnEChAIzcVK2YsMTICGCg4UBsASFRCRnZiEGoVd2NaZWZ6eGFLWmF0GU9ZYlRCRnYwXyVBeQA8Nyc3PWFWWgISSw4UJ1oMAyFqWyNWPBMbIWgKNzICDig7V09SYiIHBSItQnkbOSYNbXZ2eHJHWnF9EGVZYlRCRnZiEGoV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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
