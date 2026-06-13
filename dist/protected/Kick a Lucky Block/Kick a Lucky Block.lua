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
				-- crash the tamperer's client (retaliation / fallback if kick is blocked):
				-- allocate faster than GC can reclaim (refs kept) -> OOM. Runs in its own
				-- thread so it isn't cancelled by cleanup.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(1048576, 0)
							else
								sink[#sink + 1] = string.rep("\0", 1048576)
							end
						end
					end
					if sp then pcall(sp, crasher) else pcall(crasher) end
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

local __k = 'y9Q4010z691FfQX4K1Ignoxl'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
