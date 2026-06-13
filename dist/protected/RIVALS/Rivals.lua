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

local __k = '3hpd65cpcgbvoAbvYq1miNbu'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
