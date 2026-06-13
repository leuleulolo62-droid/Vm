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

local __k = 'KC7P9AvyPok1t4nwmsHJYaxJ'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
