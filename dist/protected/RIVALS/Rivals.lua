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

local __k = '0Pzc0szXzA159wC9fXPWwK2r'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
