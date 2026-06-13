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
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
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

local __k = 'exv2KXCIx7W6buvlM3YqKX5e'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, antiSpy = { kick = true, halt = true } })
