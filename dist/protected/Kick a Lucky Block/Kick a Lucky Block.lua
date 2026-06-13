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

local __k = 'mLgrgj0DStM5lrGsXd7isMqv'
local __p = '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FFJ6U2hKAV5fbUFYVX1HX0pKdTwwESFZCRwzeXhEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWCCAUFw4MECk8ECgVUU9nURwBVAwdOVFeW3xKSldPGWZzACVQAnhnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWwTExUNVTAeHSMZTAYmAT8BQyQSNVFLTXxJR1dGEHR9QngVQV9nNCoBVh15bVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkcPXDc2VGAYTCAmHTwLWmNTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGQnFT9SCQYKGjZIFx0SPxYTGQEGCkdXEHR9Rn0ZTEJpSmBuF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWwCHANgEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVChZHxdNU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVEfC2wKHQMPEHluVG9lCQAhFjsQF0FCfUFTTWFHAA4ZWz16Vm1BBBcpeXhEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUhMLQiM2AABcAl5nBzkWUAwHABAOTXFHQklTB2hzRWMFTF9qUwgBRQ8WLgV8TWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGQ2GD5QBRRnHjcAUklOcFFUKiMIFkdCCHR+TXgQRVBnBzABWWNTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGQnFT9SCQYKGjZIFx0SPxYTGQEGCkdXEHR9THwZTEJpSm5EGkRTCAkVCCALFwkeOmRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnFjQXUgAVbRwZCSlHT1pKEgA2FyhbGFJvRWhJD1lWZFNWGSQCHG1KEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3gQVhsUKAU7BCJLUhMLQiM2AABUFFJ6U2hKAVhfbUFYWnVHX0pKdzY2FTk/TFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0kWIQITTWFKUjULXiA8GUcVTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVEC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GFJ6U3AHQhsBKB8CPyMIBkk6Xzc6ACRaAlJqUywFRQ4WOSEZHmVJPwYNXi0nASlQZlJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTSUBUgMDQzBzSG0NTAYvFjZuF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVC9HCRMseXhEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUgIEVE5zVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0leYFEkCGEOARQfVWQeGztQOB1nGj5EQwYcbRcXH2xPAAIZVTAgVDlcARcoBixNPUlTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEC01VClcHwZnTXhXB0kHJRQYZ2xHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3gMQgRJAB4ACBgIWhMLQiM2AB1aH1tNU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHFwkOOmRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnFjYAPUlTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHBgYZW2okFSRBREJpQHFuF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbRQYCUZHUkdKEGRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKOmRzVG0VTFJnU3hEF0lTbVFWTWxHUkdKEGRzVG0YQVIVFisQWBsWbR8ZHyEGHkc9USg4Jz1QCRZNU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEFwEGIF8hDCAMIRcPVSBzSW0EWnhnU3hEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEPUlTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0lTbVFbQGwzFwsPQCshAG1QFBMkBzQdFwYdOR5WBiUEGUcaUSBzACIVCwcmATkKQwwWbRMDGTgIHEccWTc6FiRZBQY+eXhEF0lTbVFWTWxHUkdKEGRzVG0VTFJnU3hEF0kBIh4CQw8hAAYHVWRuVA5zHhMqFnYKUh5bJhgVBhwGFkk6Xzc6ACRaAlJsUw4BVB0cP0JYAykQWldGEHd/VH0cRXhnU3hEF0lTbVFW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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-4qCpdIawhSAV
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, watermark = 'Y2k-4qCpdIawhSAV', neuterAC = true, antiSpy = { kick = true, halt = true } })
