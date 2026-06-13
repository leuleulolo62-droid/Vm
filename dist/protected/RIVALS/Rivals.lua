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

local __k = 'T9vu87xbnHjgfex60mzieyT1'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
