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
-- substring patterns (tools sometimes suffix/version their GUI names)
local SPY_GUI = { "dex", "remotespy", "remote spy", "simplespy", "hydroxide", "spygui", "infiniteyield" }
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
				local nm = string.lower(c.Name)
				for _, pat in ipairs(SPY_GUI) do
					if string.find(nm, pat, 1, true) then return true, "GUI: " .. c.Name end
				end
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
		local n = 0
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
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
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
				if o.kick ~= false then
					pcall(function()
						local lp = game:GetService("Players").LocalPlayer
						lp:Kick(o.kickMessage or ("Tamper detected (" .. tostring(name) .. ")"))
					end)
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

local __k = 'fAZr3SdnjQ4yhbC0yraPFDVR'
local __p = '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EEJ+EElcV2dqZGZ8XnB6Xx5zIRYJNFgVDQw3OllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyAy0pF1o1RAMFNVFZVV9jEj0XAjUoMHZ6UHF3SgN2TUxKJVwcBmhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmEuE0E0ARonOFpVSBYiQh4XFR0nPHZvRnF0RwN/RF5EZwFZRU9jdwsXACRMZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhM2CB0PcRlUSDAiXh0dDFpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE4eMEYeDRYOWRdeQSQnNjE3Egw7ChNuRF5EYwRVSFJtCUF4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmE/HFdZRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcVEVGwdJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY7AGE3HVc2RFNXcRYpDRAlVRoGQXh3dGZ3Rmx6AFogDxdDcxQNAActOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UkcyFgkPJXkQBk5jRBgABjUyCTcqRnx6Qh1qU0JKYBpJSE9uECkXEzYjJyJYRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE4PPUccAQRjXRYWBHB7eXZwIS41FhN7XF5HaAFcQUBjRBEXD1pmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE4eMEYeDRYOWRdeQSQnNjE3Egw7ChNuRF5EaQVVSFJtCU9STH1mAS4xAy02F10nbk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjVRUBBDkgZDs9AiR6Tw5zRioPMlEXHEJrBklfWWBjbXRyEik/HDlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkGACIhISIfDy92UkcyFgkPJXkYEEJ+EElcV2FqZGZ8UXh6Xx5zIxwPMEBzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXAjKCU3Rmx3UmEyCgoFPD5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHYmBzM9F0ceDQBGcUAYGgUmRDQTGXB7ZGZ8VHF2UgN9XVdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkXDzRMZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRiQ0FjlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KWxRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJuHVklADkyZCM8Eig2Ung6BwUpPloNGg0vXBwATwMlJTo3Ric7Hl8gRBkDJVwQBkI3UQsVBCQLLThyBy8+UkcyFgkPJXkYEGhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSDT8lJTpyBSAqBkYhAQo5MlUVDUJ+EBcbDVpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyCi45E19zFw0LPVE6BwwtOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXAqKzUzCmEpEVI/ATwPMFcRDQZjDVkUADw1IVxyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6AVAyCAspPloXSF9jYgwcMjU0Mj8xA28KAFYBAQAONEZDKw0tXhwRFXggMTgxEig1HBt6bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjWR9SDz8yZB07BSoZHV0nFgEGPVELRistfRAcCDcnKTNyEik/HDlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkBAjEqIRU9CC9gNlogBwEEP1EaHEpqOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UkE2EBsYPz5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQTUoIFxyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRAIFMlUVSBEgURUXQW1mDz8xDQI1HEchCwIGNEZXOwEiXBx4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmEzFBMgBw8GNBRHVUI3UQsVBCQLLThyBy8+UkAwBQIPcQhESBYiQh4XFR0nPHYmDiQ0eBNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEAoRADwjFjMzBSk/FhNuRBoYJFFzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyBSAqBkYhAQo5MlUVDUJ+EAoRADwjTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcUcaCQ4mcxYcD2oCLSUxCS80F1AnTEdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkXDzRMZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRiQ0FhpZRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcT5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjHVRSNjEvMHYnFmEuHRNiSltKIlEaBwwnQ1kUDiJmMD43RjI5E182RBoFcVwQHEI3WBxSFTE0IzMmRmkyF1IhEAwPMEBZDg0xEBQTGXA1NDM3AmhQUhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRAIFMlUVSAErVRoZMiQnNiJyW2EuG1A4TEdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSBUrWRUXQT4pMHYhBSA2F2E2BQ0CNFBZCQwnEDIbAjsFKzgmFC42HlYhSicEHF0XAQUiXRxSAD4iZCI7BSpyWxN+RA0CNFcSOxYiQg1SXXB3amNyBy8+UnA1A0ArJEAWIwsgW1kWDlpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UmEmCj0PI0IQCwdteBwTEyQkITcmXBY7G0d7TWRKcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZDQwnOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXAvInYhBSA2F3A8CgBEElsXBgcgRBwWQSQuIThyFSI7HlYQCwAEa3AQGwEsXhcXAiRubXY3CCVQUhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRGRKcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZRU9jA1dSJD4iZCI6A2E3G106Aw8HNBQOARYrEA0aBHAFBQYGMxMfNhMgBw8GNBQPCQ42VXNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmMCQ7ASY/AHY9ACUDMl9RCwMzRAwABDQVJzc+A2hQUhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6F103bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRGRKcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5HfBQ/BAMkEA0aBHA0ISInFC96PHwERB0FcVkYAQxjXBYdEXAlJTh1EmEuF182FAEYJRQdHRAqXh5SFjEvMH0mESQ/HDlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhM6FzwPJUELBgstVy0dKjklLwYzAmFnUkchEQtgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KWxRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRlUSFZtEC4TCCRmIjkgRhIuE0cmF04ePhQbDQEsXRxSQwQ1MTgzCyh4UhsyAhoPIxQVCQwnWRcVQXtmJiQzDy8oHUdzEBwLP0cfBxAuGXNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlfTHASLD8hRiw/E10gRBoCNBQeCQ8mEBETEnA2NjkxAzIpF1dzEAYPcV8QCwljURcWQSMyJSQmAyV6Bls2RBwPJUELBkIwVQgHBD4lIVxyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY+CSI7HhMnFxs5JVULHEJ+EA0bAjtubVxyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHYlDig2FxMUBQMPGVUXDA4mQlchFTEyMSVyGHx6UGcgEQALPF1bSAMtVFkGCDMtbH9yS2EuAUYAEA8YJRRFSFN2EBgcBXAFIjF8JzQuHXg6BwVKNVtzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEA0TEjtoMzc7EmlqXAF6bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRAsENT5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZRU9jfRYEBHAyK3Y5DyIxUkMyAE4fIl0XD0ILRRQTDz8vIHYiDjgpG1AgREYfP1UXCwosQhwWTXAxJSA3RjEvAVs2F04EMEAMGgMvXABba3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQTwpJzc+Riw1BFYQDA8YcQlZJA0gURUiDTE/ISR8JSk7AFIwEAsYWxRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcVgWCwMvEAsdDiRmeXY/CTc/MVsyFk4LP1BZBQ01VToaACJoFCQ7CyAoC2MyFhpgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KPVsaCQ5jWAwfQW1mKTkkAwIyE0FzBQAOcVkWHgcAWBgAWxYvKjIUDzMpBnA7DQIOHlI6BAMwQ1FQKSUrJTg9DyV4WzlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhM6Ak4YPlsNSAMtVFkaFD1mJTg2RgY7H1YbBQAOPVELRjE3UQ0HEnB7eXZwMjIvHFI+DUxKJVwcBmhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSDT8lJTpyEiAoFVYnNAEZcQlZAwsgWykTBX4WKyU7Eig1HBN4RDgPMkAWGlFtXhwFSWBqZGV+RnFzeBNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5gcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSE9uED0XFTU0KT88A2EtE0U2RB0aNFEdSAQxXxRSADMyLSA3RjY7BFZzDQBKJlsLAxEzURoXa3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY+CSI7HhMkBRgPAkQcDQZjDVlDVGVMZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRjE5E18/TAgfP1cNAQ0tGFB4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmE2HVAyCE49FRRESBAmQQwbEzVuFjMiCig5E0c2AD0ePkYYDwdtYxETEzUiahIzEiB0JVIlASoLJVVQYkJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmIjkgRh52UkQyEgtKOFpZARIiWQsBSScpNj0hFiA5Fx0EBRgPIg4+DRYAWBAeBSIjKn57T2E+HTlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkeDjMnKHY2BzU7Ug5zMypEBlUPDREYRxgEBH4IJTs3O0t6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEIqVlkWACQnZDc8AmE+E0cySj0aNFEdSBYrVRd4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcUMYHgcQQBwXBXB7ZDIzEiB0IUM2AQpgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRiMoF1I4bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQTUoIFxyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRAsENT5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjVRcWSFpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZybGF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhN+SU45NEBZGxczVQtSCTkhLHYFBy0xIUM2AQpKJVtZBxc3QgwcQSQuIXYlBzc/eBNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE4CJFlXPwMvWyoCBDUiZGtyESAsF2AjAQsOcR5ZWkx2OllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXAuMTtoJSk7HFQ2NxoLJVFRLQw2XVc6FD0nKjk7AhIuE0c2MBcaNBorHQwtWRcVSFpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZybGF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhN+SU4nPkIcPA1jRBYFACIiZD07BSp6AlI3bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRQRHQ95fRYEBAQpbCIzFCY/BmM8F0dgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSGhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSTH1mEzc7EmEvHEc6CE4JPVsKDUI3X1kZCDMtZCYzAkt6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzCAEJMFhZBQ01VSoGACIyZGtyEig5GRt6bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRQOAAsvVVkGCDMtbH9yS2E3HUU2NxoLI0BZVEJyBVkTDzRmBzA1SAAvBlwYDQ0BcVAWYkJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmKDkxBy16EUYhFgsEJXcRCRBjDVk+DjMnKAY+Bzg/AB0QDA8YMFcNDRBJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY+CSI7HhMwERwYNFoNOg0sRFlPQTMzNiQ3CDUZGlIhRA8ENRQaHRAxVRcGIjgnNngCFCg3E0EqNA8YJT5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQTkgZDUnFDM/HEcBCwEecUARDQxJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6HlwwBQJKNV0KHEJ+EFERFCI0ITgmNC41Bh0DCx0DJV0WBkJuEA0TEzcjMAY9FWh0P1I0CgceJFAcYkJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRig8Ulc6FxpKbRRBSBYrVRd4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcVYLDQMoOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UlY9AGRKcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBraXYAA2wzAUAmAU4nPkIcPA1jWR9SFT8pZDAzFGFyAFYgARoZcUAQBQcsRQ1ba3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRAcMcVAQGxZjDllBUXAyLDM8bGF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkaFD18CTkkAxU1WkcyFgkPJWQWG0tJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6F103bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjVRcWa3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6BlIgD0AdMF0NQFJtA1B4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZDM8Akt6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzbk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRURUIRVQoGDiIjZDg9FCw7HhMEBQIBAkQcDQZJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQTgzKXgFBy0xIUM2AQpKbBRIXmhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSa3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZ/S2EOF182FAEYJRQcEAMgRBULQT8oMDlyDSg5GRMjBQpKJVtZDxciQhgcFTUjZDQnEjU1HBMlDR0DM10VARY6OllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXA0KzkmSAIcAFI+AU5XcXc/GgMuVVccBCduLz8xDRE7Fh0DCx0DJV0WBkJoEC8XAiQpNmV8CCQtWgN/RF1GcQRQQWhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSa3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZ/S2EcHUEwAU4QPlocSBczVBgGBHA1K3YZDyIxMEYnEAEEcVUJGAciQgpSCD0rITI7BzU/HkpZRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcUQaCQ4vGB8HDzMyLTk8TmhQUhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRQVBwEiXFkoDj4jBzk8EjM1Hl82Fk5XcUYcGRcqQhxaMzU2KD8xBzU/FmAnCxwLNlFXJQ0nRRUXEn4FKzgmFC42HlYhKAELNVELRjgsXhwxDj4yNjk+CiQoWzlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSDgsXhwxDj4yNjk+CiQoSGYjAA8eNG4WBgdrGXNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmITg2T0t6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmE/HFdZRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzbk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRENHcXULGgs1VR1SACRmLz8xDWEqE1d9RCcHPFEdAQM3VRULQSIjNyIzFDV6EUowCAtEWxRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcUccGxEqXxclCD41ZGtyFSQpAVo8CjkDP0dZQ0JyOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEHNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlfTHAFKDMzFGE8HlI0RB0FcVgWBxJjUxgcQSIjNyIzFDV6G14+AQoDMEAcBBtJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjWQogBCQzNjg7CCYOHXg6BwU6MFBZVUIlURUBBFpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXAqJSUmLSg5GXY9AE5XcUAQCwlrGXNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFl4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSTH1mDDc8Ai0/UlQ2CgsYMFhZGwcwQxAdD3AqLTs7Ekt6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmE2HVAyCE4eMEYeDRYQRAtSXHAJNCI7CS8pXGA2Fx0DPlotCRAkVQ1cNzEqMTNyCTN6UHo9AgcEOEAcSmhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEIqVlkGACIhISIBEjN6DA5zRicEN10XARYmElkGCTUoTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmE2HVAyCE4GOFkQHEJ+EA0dDyUrJjMgTjU7AFQ2ED0eIx1zSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEBAUQTwvKT8mRiA0FhMgAR0ZOFsXPwstQ1lMXHAqLTs7EmEuGlY9bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjcx8VTxEzMDkZDyIxUg5zAg8GIlFzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXA2Jzc+Cmk8B10wEAcFPxxQSDYsVx4eBCNoBSMmCQozEVhpNwseB1UVHQdrVhgeEjVvZDM8AmhQUhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRQ1AQAxUQsLWx4pMD80H2l4IVYgFwcFPxQVAQ8qRFkABDElLDM2Rml4Uh19RAIDPF0NSExtEFtSFjkoN398RgAvBlxzLwcJOhQKHA0zQBwWT3JvTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmE/HkA2bk5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjfBAQEzE0PWwcCTUzFEp7Rj0PIkcQBwxjYAsdBiIjNyVoRmN6XB1zFwsZIl0WBjUqXgpST35mZnlwRm90Ul86CQceeD5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjVRcWa3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQTUoIFxyRmF6UhNzRE5KcRRZSEJjEFlSQTUqNzNYRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyEiApGR0kBQceeQRXXUtJEFlSQXBmZHZyRmF6UhNzRE5KcRQcBgZJEFlSQXBmZHZyRmF6UhNzRAsENT5ZSEJjEFlSQXBmZHY3CCVQUhNzRE5KcRQcBgZJEFlSQXBmZHYmBzIxXEQyDRpCeD5ZSEJjVRcWazUoIH9YbGx3UnImEAFKAlEVBEIPXxYCayQnNz18FTE7BV17AhsEMkAQBwxrGXNSQXBmMz47CiR6BkEmAU4OPj5ZSEJjEFlSQTkgZBU0AW8bB0c8NwsGPRQNAActOllSQXBmZHZyRmF6Ul88Bw8GcVkAOA4sRFlPQTcjMBsrNi01Bht6bk5KcRRZSEJjEFlSQTkgZDsrNi01BhMnDAsEWxRZSEJjEFlSQXBmZHZyRmE2HVAyCE4HNEARBwZjDVk9ESQvKzghSBI/Hl8eARoCPlBXPgMvRRxSDiJmZgU3Ci16M18/RmRKcRRZSEJjEFlSQXBmZHZyCi45E19zFgsHPkAcJgMuVVlPQXIEGwU3Ci0bHl9xbk5KcRRZSEJjEFlSQXBmZHZYRmF6UhNzRE5KcRRZSEJjEBAUQT0jMD49AmFnTxNxNwsGPRQ4BA5jcgBSMzE0LSIrRGEuGlY9bk5KcRRZSEJjEFlSQXBmZHZyRmF6AFY+CxoPH1UUDUJ+EFswPgMjKDoTCi0YC2EyFgceKBZzSEJjEFlSQXBmZHZyRmF6UlY/FwsDNxQUDRYrXx1SXG1mZgU3Ci16IVo9AwIPcxQNAActOllSQXBmZHZyRmF6UhNzRE5KcRRZGgcuXw0XLzErIXZvRmMYLWA2CAJIWxRZSEJjEFlSQXBmZHZyRmE/HFdZRE5KcRRZSEJjEFlSQXBmZFxyRmF6UhNzRE5KcRRZSEJjQBoTDTxuIiM8BTUzHV17TWRKcRRZSEJjEFlSQXBmZHZyRmF6Un02EBkFI19XIQw1XxIXMjU0MjMgTjM/H1wnASALPFFQYkJjEFlSQXBmZHZyRmF6UhM2CgpDWxRZSEJjEFlSQXBmZDM8Akt6UhNzRE5KcVEXDGhjEFlSQXBmZCIzFSp0BVI6EEZZeD5ZSEJjVRcWazUoIH9YbGx3UnImEAFKAVgYCwdjcgsTCD40KyIhbDU7AVh9Fx4LJlpRDhctUw0bDj5ubVxyRmF6BVs6CAtKJUYMDUInX3NSQXBmZHZyRig8UnA1A0ArJEAWOA4iUxxSFTgjKlxyRmF6UhNzRE5KcRQVBwEiXFkfGAAqKyJyW2E9F0ceHT4GPkBRQWhjEFlSQXBmZHZyRmEzFBM+HT4GPkBZHAomXnNSQXBmZHZyRmF6UhNzRE5KPVsaCQ5jQxUdFSNmeXY/HxE2HUdpIgcENXIQGhE3cxEbDTRuZgU+CTUpUBpZRE5KcRRZSEJjEFlSQXBmZD80RjI2HUcgRBoCNFpzSEJjEFlSQXBmZHZyRmF6UhNzRE4MPkZZAUJ+EEheQWN2ZDI9bGF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRig8Ul08EE4pN1NXKRc3XykeADMjZCI6Ay96EEE2BQVKNFodYkJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSA4sUxgeQSMqKyIcByw/Ug5zRj0GPkBbSExtEBB4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSDT8lJTpyFWFnUkA/CxoZa3IQBgYFWQsBFRMuLTo2TjI2HUcdBQMPeD5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRQQDkIwEBgcBXAoKyJyFXscG103IgcYIkA6AAsvVFFQMTwnJzM2NiAoBhF6RBoCNFpzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEAkRADwqbDAnCCIuG1w9TEdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFk8BCQxKyQ5SAczAFYAARwcNEZRSjEceRcGBCInJyJwSmEzWzlzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KNFodQWhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSFTE1L3glByguWgN9UUdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KNFodYkJjEFlSQXBmZHZyRmF6UhNzRE5KNFodYkJjEFlSQXBmZHZyRmF6UhM2CgpgcRRZSEJjEFlSQXBmITg2bGF6UhNzRE5KNFodYkJjEFlSQXBmMDchDW8tE1onTF1DWxRZSEImXh14BD4ibVxYS2x6M0YnC04/IVMLCQYmECkeADMjIHYQFCAzHEE8EB1KeWEKDRFjYxUdFXAvKjI3HmEzHEc2AwsYIhVQYhYiQxJcEiAnMzh6ADQ0EUc6CwBCeD5ZSEJjRxEbDTVmMCQnA2E+HTlzRE5KcRRZSAslEDoUBn4HMSI9MzE9AFI3ASwGPlcSG0I3WBwca3BmZHZyRmF6UhNzRBoaBVs7CREmGFB4QXBmZHZyRmF6UhNzCAEJMFhZBRsTXBYGQW1mIzMmKzgKHlwnTEdgcRRZSEJjEFlSQXBmLTByCzgKHlwnRBoCNFpzSEJjEFlSQXBmZHZyRmF6Ul88Bw8GcUcVBxYwEERSDCkWKDkmXAczHFcVDRwZJXcRAQ4nGFshDT8yN3R7bGF6UhNzRE5KcRRZSEJjEFkbB3A1KDkmFWEuGlY9bk5KcRRZSEJjEFlSQXBmZHZyRmF6HlwwBQJKJVULDwc3EERSLiAyLTk8FW8PAlQhBQoPBVULDwc3Hi8TDSUjZDkgRmMbHl9xbk5KcRRZSEJjEFlSQXBmZHZyRmF6G1VzEA8YNlENSF9+EFszDTxkZCI6Ay9QUhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6FFwhRAdKbBRIREJwAFkWDlpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyDyd6HFwnRC0MNho4HRYsZQkVEzEiIRQ+CSIxARMnDAsEcVYLDQMoEBwcBVpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyCi45E19zF05XcUcVBxYwCj8bDzQALSQhEgIyG183TEw5PVsNSkJtHlkbSFpmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyDyd6ARMyCgpKIg4/AQwndhAAEiQFLD8+Aml4Il8yBwsOAVULHEBqEA0aBD5MZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhMjBw8GPRwfHQwgRBAdD3hvTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcXocHBUsQhJcJzk0IQU3FDc/ABtxJjE/IVMLCQYmElVSCHlMZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhM2CgpDWxRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSFTE1L3glByguWgN9VkdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSActVHNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkXDzRMZHZyRmF6UhNzRE5KcRRZSEJjEFkXDSMjTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZDo9BSA2UkA/CxokJFlZVUI3UQsVBCR8KTcmBSlyUGA/CxpKeREdQ0thGXNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkbB3A1KDkmKDQ3Ukc7AQBgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSA4sUxgeQT4zKXZvRjU1HEY+BgsYeUcVBxYNRRRba3BmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY+CSI7HhMgRFNKIlgWHBF5dhAcBRYvNiUmJSkzHld7Rj0GPkBbSExtEBcHDHlMZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRig8UkBzBQAOcUdDLgstVD8bEyMyBz47CiVyUGM/BQ0PNWQYGhZhGVkGCTUoTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzCAEJMFhZCwoiQllPQRwpJzc+Ni07C1YhSi0CMEYYCxYmQnNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRi01EVI/RBwFPkBZVUIgWBgAQTEoIHYxDiAoSHU6CgosOEYKHCErWRUWSXIOMTszCC4zFmE8Cxo6MEYNSktJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY7AGEoHVwnRBoCNFpzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyFC41Bh0QIhwLPFFZVUIwHjo0EzErIXZ5Rhc/EUc8Fl1EP1EOQFJvEEpeQWBvTnZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcUAYGwltRxgbFXh2amV7bGF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KNFodYkJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmNDUzCi1yFEY9BxoDPlpRQWhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmEUF0ckCxwBf3IQGgcQVQsEBCJuZhQNMzE9AFI3AUxGcVoMBUtJEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHY3CCVzeBNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE4PP1BzSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZDQwnOllSQXBmZHZyRmF6UhNzRE5KcRRZDQwnOllSQXBmZHZyRmF6UhNzRE4PP1BzSEJjEFlSQXBmZHZyAy8+eBNzRE5KcRRZDQwnOllSQXBmZHZyEiApGR0kBQceeQdQYkJjEFkXDzRMITg2T0tQXx5zJg8JOlMLBxctVFkeDj82ZCI9RiUjHFI+DQ0LPVgASBczVBgGBHACNjkiAi4tHEBzTDsaNkYYDAdjQxUdFSNmJTg2Rg4tHFY3RBkPOFMRHBFqOg0TEjtoNyYzES9yFEY9BxoDPlpRQWhjEFlSFjgvKDNyEjMvFxM3C2RKcRRZSEJjEFRfQWFoZAQ3ADM/AVtzCxkENFBZHwcqVxEGEnAiNjkiAi4tHDlzRE5KcRRZSBIgURUeSTYzKjUmDy40WhpZRE5KcRRZSEJjEFlSDT8lJTpyCTY0F1dzWU49NF0eABYQVQsECDMjBzo7Ay8uXHwkCgsOcVsLSBk+OllSQXBmZHZyRmF6Ulo1RE0FJlocDEJ+DVlCQSQuIThYRmF6UhNzRE5KcRRZSEJjEBYFDzUiZGtyHWF4JVw8AAsEcWcNAQEoElkPa3BmZHZyRmF6UhNzRAsENT5ZSEJjEFlSQXBmZHYdFjUzHV0gSiEdP1EdPwcqVxEGEmoVISIEBy0vF0B7CxkENFBQYkJjEFlSQXBmITg2T0tQUhNzRE5KcRRURUJxHlkgBDY0ISU6RjI2HUcnAQpKM0YYAQwxXw0BQTQ0KyY2CTY0Ul86FxpgcRRZSEJjEFkCAjEqKH40Ey85Blo8CkZDWxRZSEJjEFlSQXBmZDo9BSA2Ul4qNAIFJRRESAUmRDQLMTwpMH57bGF6UhNzRE5KcRRZSA4sUxgeQSYnKCM3FWFnUkhzRi8GPRZZFWhjEFlSQXBmZHZyRmFQUhNzRE5KcRRZSEJjWR9SDCkWKDkmRiA0FhM+HT4GPkBDLgstVD8bEyMyBz47CiVyUGA/CxoZcx1ZHAomXnNSQXBmZHZyRmF6UhNzRE5KPVsaCQ5jQxUdFSNmeXY/HxE2HUd9NwIFJUdzSEJjEFlSQXBmZHZyRmF6UlU8Fk4DcQlZWU5jA0lSBT9MZHZyRmF6UhNzRE5KcRRZSEJjEFkeDjMnKHYhCi4uPFI+AU5XcRYqBA03EllcT3AvTnZyRmF6UhNzRE5KcRRZSEJjEFlSDT8lJTpyFWFnUkA/CxoZa3IQBgYFWQsBFRMuLTo2TjI2HUcdBQMPeD5ZSEJjEFlSQXBmZHZyRmF6UhNzRAIFMlUVSAAxURAcEz8yCjc/A2FnUhEdCwAPcz5ZSEJjEFlSQXBmZHZyRmF6UhNzRGRKcRRZSEJjEFlSQXBmZHZyRmF6Ul88Bw8GcVYVBwEoEERSEnAnKjJyFXscG103IgcYIkA6AAsvVFFQMTwnJzM2NiAoBhF6bk5KcRRZSEJjEFlSQXBmZHZyRmF6G1VzBgIFMl9ZHAomXnNSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFkQEzEvKiQ9Eg87H1ZzWU4IPVsaA1gEVQ0zFSQ0LTQnEiRyUHoXRkdKPkZZQAAvXxoZWxYvKjIUDzMpBnA7DQIOHlI6BAMwQ1FQLD8iITpwT2E7HFdzBgIFMl9DLgstVD8bEyMyBz47CiUVFHA/BR0ZeRY0BwYmXFtbTx4nKTN7Ri4oUhEDCA8JNFBbYkJjEFlSQXBmZHZyRmF6UhNzRE5KNFodYkJjEFlSQXBmZHZyRmF6UhNzRE5KJVUbBAdtWRcBBCIybCAzCjQ/AR9zFxoYOFoeRgQsQhQTFXhkFzo9EmF/FhN7QR1DcxhZAU5jUgsTCD40KyIcByw/WxpZRE5KcRRZSEJjEFlSQXBmZDM8Akt6UhNzRE5KcRRZSEImXAoXa3BmZHZyRmF6UhNzRE5KcRQfBxBjWVlPQWFqZGViRiU1eBNzRE5KcRRZSEJjEFlSQXBmZHZyEiA4HlZ9DQAZNEYNQBQiXAwXEnxmZgU+CTV6UBN9Sk4DcRpXSEBjGDcdDzVvZn9YRmF6UhNzRE5KcRRZSEJjEBwcBVpmZHZyRmF6UhNzRE4PP1BzSEJjEFlSQXBmZHZybGF6UhNzRE5KcRRZSC0zRBAdDyNoESY1FCA+F2cyFgkPJQ4qDRYVURUHBCNuMjc+EyQpWzlzRE5KcRRZSActVFB4a3BmZHZyRmF6BlIgD0AdMF0NQFdqOllSQXAjKjJYAy8+WzlZSUNKEEENB0IBRQBSNjUvIz4mFWFyIkE8AxwPIkcQBwxjUhgBBDRmKzhyFi07C1YhRA0LIlxQYhYiQxJcEiAnMzh6ADQ0EUc6CwBCeD5ZSEJjRxEbDTVmMCQnA2E+HTlzRE5KcRRZSAslEDoUBn4HMSI9JDQjJVY6AwYeIhQNAActOllSQXBmZHZyRmF6Ul88Bw8GcXcVAQctRDsTDTEoJzMBAzMsG1A2RFNKI1EIHQsxVVEgBCAqLTUzEiQ+IUc8Fg8NNBo0BwY2XBwBTwMjNiA7BSQpPlwyAAsYf3cVAQctRDsTDTEoJzMBAzMsG1A2TWRKcRRZSEJjEFlSQXAqKzUzCmE4E18yCg0PcQlZKw4qVRcGIzEqJTgxAxI/AEU6BwtEE1UVCQwgVXNSQXBmZHZyRmF6UhM6Ak4IMFgYBgEmEA0aBD5MZHZyRmF6UhNzRE5KcRRZSE9uECoXACIlLHY0FC43Ul48FxpKNEwJDQwwWQ8XQTQpMzhyEi56EVs2BR4PIkBzSEJjEFlSQXBmZHZyRmF6UlU8Fk4DcQlZSxEsQg0XBQcjLTE6EjJ2UgJ/RENbcVAWYkJjEFlSQXBmZHZyRmF6UhNzRE5KPVsaCQ5jR1lPQSMpNiI3AhY/G1Q7EB0xOGlzSEJjEFlSQXBmZHZyRmF6UhNzRE4DNxQXBxZjRBgQDTVoIj88AmkNF1o0DBo5NEYPAQEmcxUbBD4yahklCCQ+XhMkSgALPFFQSBYrVRd4QXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSDT8lJTpyBS4pBnwxDk5XcX0XDgstWQ0XLDEyLHg8AzZyBR0wCx0eeD5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRQQDkIhURUTDzMjZGhvRiI1AUccBgRKJVwcBmhjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSETMnKDp6ADQ0EUc6CwBCeD5ZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEFlSQR4jMCE9FCp0NFohAT0PI0IcGkphYxEdEQ8EMS9wSmF4JVY6AwYeAlwWGEBvEA5cDzErIX9YRmF6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UlY9AEdgcRRZSEJjEFlSQXBmZHZyRmF6UhNzRE5KcRRZSBYiQxJcFjEvMH5jT0t6UhNzRE5KcRRZSEJjEFlSQXBmZHZyRmF6UhNzBhwPMF9ZRU9jcgwLQT8oKC9yEik/UlE2FxpKMFIfBxAnURseBHAxIT81DjV6G11zEAYDIhQNAQEoOllSQXBmZHZyRmF6UhNzRE5KcRRZSEJjEBwcBVpmZHZyRmF6UhNzRE5KcRRZSEJjEBwcBVpmZHZyRmF6UhNzRE5KcRRZDQwnOllSQXBmZHZyRmF6UlY9AGRKcRRZSEJjEBwcBVpmZHZyRmF6UkcyFwVEJlUQHEpwGXNSQXBmITg2bCQ0FhpZbkNHcXUMHA1jcgwLQQM2ITM2RhQqFUEyAAsZW0AYGwltQwkTFj5uIiM8BTUzHV17TWRKcRRZHwoqXBxSFSIzIXY2CUt6UhNzRE5KcV0fSCElV1czFCQpBiMrNTE/F1dzEAYPPz5ZSEJjEFlSQXBmZHYiBSA2Hhs1EQAJJV0WBkpqOllSQXBmZHZyRmF6UhNzRE45IVEcDDEmQg8bAjUFKD83CDVgIFYiEQsZJWEJDxAiVBxaUHlMZHZyRmF6UhNzRE5KNFodQWhjEFlSQXBmZDM8Akt6UhNzRE5KcUAYGwltRxgbFXh1bVxyRmF6F103bgsENR1zYk9uEC0iQQcnKD1yJS40HFYwEAcFPz4rHQwQVQsECDMjah43BzMuEFYyEFQpPloXDQE3GB8HDzMyLTk8TmhQUhNzRAcMcXcfD0wXYC4TDTsDKjcwCiQ+Ukc7AQBgcRRZSEJjEFkeDjMnKHYxDiAoUg5zKAEJMFgpBAM6VQtcIjgnNjcxEiQoeBNzRE5KcRRZBA0gURVSEz8pMHZvRiIyE0FzBQAOcVcRCRB5dhAcBRYvNiUmJSkzHld7RiYfPFUXBwsnYhYdFQAnNiJwT0t6UhNzRE5KcVgWCwMvEBEHDHB7ZDU6BzN6E103RA0CMEZDLgstVD8bEyMyBz47CiUVFHA/BR0ZeRYxHQ8iXhYbBXJvTnZyRmF6UhNzbk5KcRRZSEJjWR9SEz8pMHYzCCV6GkY+RA8ENRQRHQ9tfRYEBBQvNjMxEig1HB0eBQkEOEAMDAdjDllCQSQuIThYRmF6UhNzRE5KcRRZBA0gURVSEiAjITJyW2EZFFR9MD49MFgSOxImVR1SDiJmcWZYRmF6UhNzRE5KcRRZGg0sRFcxJyInKTNyW2EoHVwnSi0sI1UUDUJoEBEHDH4LKyA3IigoF1AnDQEEcR5ZQBEzVRwWQXpmdHhiVnZzeBNzRE5KcRRZDQwnOllSQXAjKjJYAy8+WzlZSUNKGFofAQwqRBxSKyUrNHYxCS80F1AnDQEEW2EKDRAKXgkHFQMjNiA7BSR0OEY+FDwPIEEcGxZ5cxYcDzUlMH40Ey85Blo8CkZDWxRZSEIqVlkxBzdoDTg0LDQ3AhMnDAsEWxRZSEJjEFlSDT8lJTpyBSk7ABNuRCIFMlUVOA4iSRwATxMuJSQzBTU/ADlzRE5KcRRZSA4sUxgeQTgzKXZvRiIyE0FzBQAOcVcRCRB5dhAcBRYvNiUmJSkzHlccAi0GMEcKQEALRRQTDz8vIHR7bGF6UhNzRE5KOFJZABcuEA0aBD5MZHZyRmF6UhNzRE5KOUEUUiErURcVBAMyJSI3TgQ0B159LBsHMFoWAQYQRBgGBAQ/NDN8LDQ3Alo9A0dgcRRZSEJjEFkXDzRMZHZyRiQ0Fjk2CgpDWz5URUINXxoeCCBmKDk9FksIB10AARwcOFccRjE3VQkCBDR8Bzk8CCQ5Bhs1EQAJJV0WBkpqOllSQXAvInYRACZ0PFwwCAcacUARDQxJEFlSQXBmZHY+CSI7HhMwDA8YcQlZJA0gURUiDTE/ISR8JSk7AFIwEAsYWxRZSEJjEFlSCDZmJz4zFGEuGlY9bk5KcRRZSEJjEFlSQTYpNnYNSmE5Glo/AE4DPxQQGAMqQgpaAjgnNmwVAzUeF0AwAQAOMFoNG0pqGVkWDlpmZHZyRmF6UhNzRE5KcRRZAQRjUxEbDTR8DSUTTmMYE0A2NA8YJRZQSAMtVFkRCTkqIHgRBy8ZHV8/DQoPcUARDQxJEFlSQXBmZHZyRmF6UhNzRE5KcRQaAAsvVFcxAD4FKzo+DyU/Ug5zAg8GIlFzSEJjEFlSQXBmZHZyRmF6UlY9AGRKcRRZSEJjEFlSQXAjKjJYRmF6UhNzRE4PP1BzSEJjEBwcBVojKjJ7bEt3XxMSChoDcXU/I2gPXxoTDQAqJS83FG8TFl82AFQpPloXDQE3GB8HDzMyLTk8TjFrWzlzRE5KOFJZKwQkHjgcFTkHAh1yBy8+UkNiRFBKYARJWEI3WBwca3BmZHZyRmF6HlwwBQJKJ10LHBciXDAcESUyZGtyASA3FwkUARo5NEYPAQEmGFskCCIyMTc+Ly8qB0ceBQALNlELSktJEFlSQXBmZHYkDzMuB1I/LQAaJEBDOwctVDIXGBUwITgmTjUoB1Z/RCsEJFlXIwc6cxYWBH4RaHY0By0pFx9zAw8HNB1zSEJjEFlSQXAyJSU5SDY7G0d7VEBbeD5ZSEJjEFlSQSYvNiInBy0THEMmEFQ5NFodIwc6dQ8XDyRuIjc+FSR2UnY9EQNEGlEAKw0nVVclTXAgJTohA216FVI+AUdgcRRZSActVHMXDzRvTlweDyMoE0EqXiAFJV0fEUphexARCnAnZBonBSojUnE/Cw0BcWcaGgszRFkeDjEiITJzRj16KwE4RD0JI10JHEBqOg=='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
