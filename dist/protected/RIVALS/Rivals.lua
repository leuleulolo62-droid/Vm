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

local __k = 'G11fbA8K0d3xpwwmEDbDd2CM'
local __p = 'ahxqPWhIagJmJX8rUJX3+WUdUC9EGgwvNFhVDwMvEWtlLTlxIAUYCTAnFi0LXGMvMlhdAkxhfT1VFkpYFhIWGTA2B2QTQCI9NBFFDgdhXypdARQLUDggI2UnDi0BXDdtC0RQRg4gQS5CbjpQGRkEGSQqASFJXiY7Il0RCwc1UCRUREAQERMYGiwqBW1EXTFtIVhDAxFhWWtCAVIUUAUSACowB2hEUy8hZ0FSBw4tFSxFBUEcFRNZZ09NIwdEQiw+M0RDA0JpSi5TC0UdAhITTSM2DSlERisoZ31EFAMxUGtmKRMbHxkEGSQqFmQUXSwhbgsREgokGCpeEFpVEx8SDDFOayABRiYuM0IRDg0uUzgQEloZUB4EDiYoDTcRQCZiLkJdBQ4uSz5CARNQExsYHjA2B2kQSzMoZ1ddDxIyEWtRCldYHRIDDDElACgBOEohKFJaFU5hWSVUREEdABgFGTZkDTIBQGMFM0VBNQczTiJTAR1YJB8SHyAiDTYBEjclLkIRFQEzUTtERH09JjIlTS0rDS8CRy0uM1heCEUyMkJRRF0ZBB4BCGoWDSYIXTttBmF4RgQ0VihEDVwWUBYZCWUKJxIhYGMlKF5aFUIgGCxcC1EZHFcaCDElDyEQWiwpaRF4EkIuVidJbjoLGBYTAjI3QikBRisiI0IRCQxhTCNVRFQZHRJQHmUrFSpEfjYsZ1JdBxEyGCJeF0cZHhQSHmVsDjEFEiAhKEJEFAcyEWcQFlYZFAR9ZDUlETcNRCYhPh0RBwwlGDlVClcdAgRXDiktByoQHzAkI1QfRjEkSj1VFh4eERQeAyJkAycQWywjNBFCEgM4GDtcBUYLGRUbCGtOaE0oRyJtch8ASxEgXi4QKEYZBU1XAypkSXlIEi0iZ1JeCBYoVj5VSBMWH1cWUid+AWQQVzEjJkNISGgcZUE6SR5XX1ckCDcyCycBQUkhKFJQCkIRVCpJAUELUFdXTWVkQmREEn5tIFBcA1gGXT9jAUEOGRQSRWcUDiUdVzE+ZRg7Cg0iWScQNkYWIxIFGywnB2REEmNtZxEMRgUgVS4KI1YMIxIFGywnB2xGYDYjFFRDEAsiXWkZbl8XExYbTRA3BzYtXDM4M2JUFBQoWy4QWRMfERoSVwIhFhcBQDUkJFQZRDcyXTl5CkMNBCQSHzMtASFGG0khKFJQCkIWVzlbF0MZExJXTWVkQmREEn5tIFBcA1gGXT9jAUEOGRQSRWcTDTYPQTMsJFQTT2gtVyhRCBM0GRAfGSwqBWREEmNtZxERRl9hXypdAQk/FQMkCDcyCycBGmEBLlZZEgsvX2kZbl8XExYbTQYrDigBUTckKF8RRkJhGGsQWRMfERoSVwIhFhcBQDUkJFQZRCEuVCdVB0cRHxkkCDcyCycBEGpHK15SBw5hai5ACFobEQMSCRYwDTYFVSZwZ1ZQCwd7fy5EN1YKBh4UCG1mMCEUXiouJkVUAjE1VzlRA1ZaWX19ASonAyhEfiwuJl1hCgM4XTkQWRMoHBYOCDc3TAgLUSIhF11QHwczMidfB1IUUDQWACA2A2REEmNtZwwRMQ0zUzhABVAdXjQCHzchDDAnUy4oNVA7bE9sF2QQMXpYHB4VHyQ2G2RMa3EmZx4RKQAyUS9ZBV1YAwMWDi5taCgLUSIhZ0NUFg1hBWsSDEcMAARNQmo2AzNKVSo5L0RTExEkSihfCkcdHgNZDiopTR1WWRAuNVhBEiAgWyACJlIbG1g4DzYtBi0FXBYkaFxQDwxuGkFcC1AZHFc7BCc2AzYdEmNtZxERW0ItVypUF0cKGRkQRSIlDyFeejc5N3ZUEkozXTtfRB1WUFU7BCc2AzYdHC84JhMYT0poMidfB1IUUCMfCCghLyUKUyQoNREMRg4uWS9DEEERHhBfCiQpB34sRjc9AFRFThAkSCQQSh1YUhYTCSoqEWswWiYgInxQCAMmXTkeCEYZUl5eRWxODisHUy9tFFBHAy8gVipXAUFYUEpXASolBjcQQCojIBlWBw8kAgNEEEM/FQNfHyA0DWRKHGNvJlVVCQwyFxhRElY1ERkWCiA2TCgRU2FkbhkYbGgtVyhRCBM3AAMeAis3QnlEfiovNVBDH0wOSD9ZC10LehsYDiQoQhALVSQhIkIRW0INUSlCBUEBXiMYCiIoBzduOG5gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2luH25tFGVwMidLFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS2gtVyhRCBM+HBYQHmV5Qj9uO25gZ1JeCwAgTEE5N1oUFRkDLCwpQmREEmNtZwwRAAMtSy4cbjorGRsSAzEWAyMBEmNtZxERW0InWSdDAR9YUFdaQGUiAygXV2NwZ11UAQs1GGN2K2VYFxYDCCFtTmQQQDYoZwwRFAMmXWsYCFwbG1cZCCQ2BzcQG0lEBlhcIA03aipUDUYLUFdXTXhkU3VUHklEBlhcLgs1WiRIRBNYUFdXTXhkQAwBUydvaxERS09hcC5RABNXUDUYCTxkTWQqVyI/IkJFbGsAUSZmDUAREhsSLi0hAS9ED2M5NURUSmhIeSJdMFYZHTQfCCYvQmREEn5tM0NEA05LMQpZCWMKFRMeDjEtDSpEEmNwZwEfVk5LMQVfN0MKFRYTTWVkQmREEmNwZ1dQChEkFEE5KlwqFRQYBClkQmREEmNtZwwRAAMtSy4cbjosAh4QCiA2ACsQEmNtZxERW0InWSdDAR9yeSMFBCIjBzYgVy8sPhERRkJ8GHseVABUen4/BDEmDTwhSjMsKVVUFEJhBWtWBV8LFVt9ZA0tFiYLShAkPVQRRkJhGGsNRAtUen4kBSozJCsSEmNtZxERRkJhBWtWBV8LFVt9ZGhpQiEXQklEAkJBIwwgWidVABNYUEpXCyQoESFIOEoINEFzCRphGGsQRBNYTVcDHzAhTk5tdzA9CVBcA0JhGGsQRA5YBAUCCGlOawEXQgsoJl1FDkJhGGsNREcKBRJbZ0wBETQgWzA5Jl9SA0JhBWtEFkYdXH1+KDY0NjYFUSY/ZxERRl9hXipcF1ZUen4yHjUQByUJcSsoJFoRW0I1Sj5VSDlxNQQHICQ8Ji0XRmNtZwwRV1JxCGc6bXYLADQYASo2QmREEmNwZ3JeCg0zC2VWFlwVIjA1RXVoQnZVAm9tdQMIT05LMWYdRF4XBhIaCCswaE0zUy8mFEFUAwYOVmsNRFUZHAQSQWUTAygPYTMoIlURW0JwDmc6bXkNHQc4A2VkQmREEn5tIVBdFQdtGAFFCUMoHwASH2V5QnFUHklEDl9XLBcsSGsQRBNYTVcRDCk3B2huOwUhPn5fRkJhGGsQRA5YFhYbHiBoQgIISxA9IlRVRl9hDnscbjo2HxQbBDULDGREEmNwZ1dQChEkFEE5SR5YABsWFCA2aE0lXDckBldaRkJhBWtWBV8LFVt9ZAYxETALXwUiMREMRgQgVDhVSBM+HwEhDCkxB2RZEnR9azs4IBctVClCDVQQBEpXCyQoESFIOEpgahFWBw8kMkJxEUcXIQISGCBkX2QCUy8+Ih07G2hLVCRTBV9YMxgZAyAnFi0LXDBtehFKG0JhGGYdRGE6KCQUHyw0FgcLXC0oJEVYCQwyGD9fRFAUFRYZZykrASUIEhclNVRQAhFhGGsQRA5YCwpXTWVpT2QFUTckMVQRCg0uSGtdBUETFQUEZykrASUIEhEoNEVeFAcyGGsQRA5YCwpXTWVpT2QCRy0uM1heCBFhTCQQEV0cH1cfAiovEWsWVzAkPVRCRg0vGD5eCFwZFH0bAiYlDmQgQCI6Ll9WFUJhGGsNREgFUFdXQGhkJxc0Eic/JkZYCAVhVylaAVAMA1cHCDdkEigFSyY/TTtdCQEgVGtWEV0bBB4YA2UwECUHWWsuKF9fT2hIeyReClYbBB4YAzYfQQcLXC0oJEVYCQwyGGAQVW5YTVcUAisqaE0WVzc4NV8RBQ0vVkFVCldyelpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5yXVpXPgQCJ2Q2dxACC2d0NDFhEChRB1sdFFtXHyBpECEXXS87IlURAgcnXSVDDUUdHA5eZ2hpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVp9ASonAyhEYhBtehF9CQEgVBtcBUodAk0gDCwwJCsWcSskK1UZRDItWTJVFmAbAh4HGTZmS05uXiwuJl0RABcvWz9ZC11YBAUOPyA1Fy0WV2skKUJFT2hIUS0QClwMUB4ZHjFkFiwBXGM/IkVEFAxhViJcRFYWFH1+ASonAyhEXShhZ1xeAkJ8GDtTBV8UWAUSHDAtECFIEiojNEUYbGsoXmtfDxMMGBIZTTchFjEWXGMgKFURAwwlMkJCAUcNAhlXAywoaCEKVklHK15SBw5hfiJXDEcdAjQYAzE2DSgIVzFHK15SBw5hXj5eB0cRHxlXCiAwJAdMG0lELlcRIAsmUD9VFnAXHgMFAikoBzZERisoKRFDAxY0SiUQIlofGAMSHwYrDDAWXS8hIkMRAwwlMkJcC1AZHFcZAiEhQnlEYhB3AVhfAiQoSjhEJ1sRHBNfTwYrDDAWXS8hIkNCREtLMSVfAFZYTVcZAiEhQiUKVmMjKFVUXCQoVi92DUELBDQfBCkgSmYiWyQlM1RDJQ0vTDlfCF8dAlVeZ0wCCyMMRiY/BF5fEhAuVCdVFhNFUAMFFBchEzENQCZlKV5VA0tLMTlVEEYKHlcxBCIsFiEWcSwjM0NeCg4kSkFVCldyehsYDiQoQiIRXCA5Ll5fRgUkTA1ZA1sMFQVfRE9NDisHUy9tAXIRW0ImXT92JxtRen4eC2UqDTBEdABtM1lUCEIzXT9FFl1YHh4bTSAqBk5tXiwuJl0RAEJ8GDlRE1QdBF8xLmlkQAgLUSIhAVhWDhYkSmkZbjoRFlcRTXh5QioNXmM5L1RfbGtIVCRTBV9YHxxbTTdkX2QUUSIhKxlXEwwiTCJfChtRUAUSGTA2DGQicW0BKFJQCiQoXyNEAUFYFRkTRE9Nay0CEiwmZ0VZAwxhXmsNREFYFRkTZ0whDCBuOzEoM0RDCEInMi5eADlyXVpXHyA3DSgSV2MsZ0NUCw01XWtFClcdAlclCDUoCycFRiYpFEVeFAMmXWViAV4XBBIETSc9QjQFRittNFRWCwcvTDg6CFwbERtXPyApDTABQQUiK1VUFEJ8GBlVFF8RExYDCCEXFisWUyQofXdYCAYHUTlDEHAQGRsTRWcWBykLRiY+ZRg7Cg0iWScQAkYWEwMeAitkBSEQYCYgKEVUTkxvFmI6bVoeUBkYGWUWBykLRiY+AV5dAgczGD9YAV1YAhIDGDcqQioNXmMoKVU7bw4uWypcRF0XFBJXUGUWBykLRiY+AV5dAgczMkJcC1AZHFcECCI3QnlESWNjaR8RG2hIVCRTBV9YGVdKTXROazMMWy8oZ19eAgdhWSVURFpYTEpXTjYhBTdEVixHTjhfCQYkGHYQClwcFU0xBCsgJC0WQTcOL1hdAkoyXSxDP1olWX1+ZCxkX2QNEmhtdjs4AwwlMkJCAUcNAhlXAyogB04BXCdHTRwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25HahwRMiMTfw5kLX0/UF8HDDY3CzIBEjEoJlVCRg0vVDIZbh5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWY6CFwbERtXJQwQIAs8bQ0MCnRiRl9hQ0E5LFYZFFdKTT5kQAwNRiEiP3lUBwZjFGsSLFoMEhgPJSAlBhcJUy8hZR0RRCokWS8SRE5Uen41AiE9QnlESWNvD1hFBA05eiRUHRFUUFU/BDEmDTwmXSc0FFxQCg5jFGsSLEYVERkYBCEWDSsQYiI/MxMdRkAUSDtVFmcXAgQYT2U5Tk4ZOEkhKFJQCkInTSVTEFoXHlcRBDc3FgcMWy8pb1xeAgctFGteBV4dA159ZCkrASUIEiptehEAbGs2UCJcARMRUEtKTWYqAykBQWMpKDs4bw4uWypcRENYTVcaAiEhDn4iWy0pAVhDFRYCUCJcABsWERoSHh4tP21uO0okIRFBRhYpXSUQFlYMBQUZTTVkByoAOEpELhEMRgthE2sBbjodHhN9ZDchFjEWXGMjLl07AwwlMkFcC1AZHFcRGCsnFi0LXGMkNHBdDxQkEChYBUFRen4bAiYlDmQMRy5tehFSDgMzGCpeABMbGBYFVwMtDCAiWzE+M3JZDw4ldy1zCFILA19VJTApAyoLWydvbjs4DwRhUD5dRFIWFFcfGChqKiEFXjclZw0MRlJhTCNVChMKFQMCHytkBCUIQSZtIl9VbGszXT9FFl1YEx8WH2U6X2QKWy9HIl9VbGgtVyhRCBMeBRkUGSwrDGQNQQYjIlxIThItSmcQEFYZHTQfCCYvS05tWyVtN11DRl98GAdfB1IUIBsWFCA2QjAMVy1tNVRFExAvGC1RCEAdUBIZCU9NCyJEXCw5Z0VUBw8CUC5TDxMMGBIZTTchFjEWXGM5NURURgcvXEE5CFwbERtXACwqB2RED2MBKFJQCjItWTJVFgk/FQM2GTE2CyYRRiZlZWVUBw8IfGkZbjoUHxQWAWUwCiENQGNwZ0FdFFgGXT9xEEcKGRUCGSBsQBABUy4EAxMYbGsoXmtdDV0dUEpKTSstDmQLQGM5L1RYFEJ8BWteDV9YBB8SA2U2BzARQC1tM0NEA0IkVi86bUEdBAIFA2UpCyoBEj1wZ0VZAwszMi5eADlyHBgUDClkBDEKUTckKF8REQ0zVC9kC2AbAhISA200DTdNOEohKFJQCkI3FGtfChNFUDQWACA2A34zXTEhI2VeMAskTztfFkcoHx4ZGW00DTdNOEo/IkVEFAxhbi5TEFwKQlkZCDJsFGo8HmM7aWgYSkIuVmcQEh0iehIZCU9OT2lEQCI0JFBCEkI3UThZBloUGQMOTSM2DSlEUSIgIkNQRhYuGD9RFlQdBFtXBCIqDTYNXCRtK15SBw5hE2tEBUEfFQNXDi0lEE4IXSAsKxFXEwwiTCJfChMRAyEeHiwmDiFMRiI/IFRFNgMzTGcQEFIKFxIDLi0lEG1uOy8iJFBdRhIgSipdFxNFUCUWFCYlETA0UzEsKkIfCAc2EGI6bUMZAhYaHmsCCygQVzEZPkFURl9hfSVFCR0qEQ4UDDYwJC0IRiY/E0hBA0wEQChcEVcden4bAiYlDmQCWy85IkMRW0I6GAhRCVYKEVcKZ0wtBGQoXSAsK2FdBxskSmVzDFIKERQDCDdkFiwBXGMrLl1FAxAaGy1ZCEcdAldcTXQZQnlEfiwuJl1hCgM4XTkeJ1sZAhYUGSA2QiEKVklELlcREgMzXy5EJ1sZAlcDBSAqQiINXjcoNWoSAAstTC5CRBhYQSpXUGUwAzYDVzcOL1BDRgcvXEE5FFIKERoEQwMtDjABQAcoNFJUCAYgVj9DLV0LBBYZDiA3QnlEVCohM1RDbGstVyhRCBMXAh4QBCtkX2QnUy4oNVAfJSQzWSZVSmMXAx4DBCoqaE0IXSAsKxFVDxBhBWtEBUEfFQMnDDcwTBQLQSo5Ll5fRk9hVzlZA1oWen4bAiYlDmQWVzBtehFmCRAqSztRB1ZCIhYODiQ3FmwLQCoqLl8dRgYoSmcQFFIKERoERE9NECEQRzEjZ0NUFUJ8BWteDV9yFRkTZ09pT2QHWiwiNFQREgokGClVF0dYAx4bCCswTyUNX2M5JkNWAxZ6GDlVEEYKHgRXFmU0AzYQD29tJlhcNg0yBWcQB1sZAkpXEGUrEGQKWy9HK15SBw5hXj5eB0cRHxlXCiAwMS0IVy05E1BDAQc1EGI6bV8XExYbTSYhDDABQGNwZ3JQCwczWWVmDVYPABgFGRYtGCFEGGN9aQQ7bw4uWypcRFEdAwNbTSchETA3USw/Ijs4Cg0iWScQFF8ZCRIFHmV5QhQIUzooNUILIQc1aCdRHVYKA19eZ0woDScFXmMkZwwRV2hITyNZCFZYGVdLUGVnEigFSyY/NBFVCWhIMSdfB1IUUAcbH2V5QjQIUzooNUJqDz9LMUJcC1AZHFcUBSQ2QnlEQi8/aXJZBxAgWz9VFjlxeR4RTSYsAzZEUy0pZ1hCJw4oTi4YB1sZAl5XDCsgQi0Xdy0oKkgZFg4zFGt2CFIfA1k2BCgQByUJcSsoJFoYRhYpXSU6bTpxHBgUDClkFSUKRg0sKlRCbGtIMSJWRHUUERAEQwQtDwwNRiEiPxEMW0JjeiRUHRFYBB8SA09Na01tRSIjM39QCwcyGHYQLHosMjgvMgsFLwE3HAEiI0g7b2tIXSdDATlxeX5+GiQqFgoFXyY+ZwwRLisVegRoO305PTIkQw0hAyBuO0pEIl9VbGtIMSdfB1IUUAcWHzFkX2QCWzE+M3JZDw4lEChYBUFUUAAWAzEKAykBQWptKEMRAAszSz9zDFoUFF8UBSQ2TmQsexcPCGluKCMMfRgeJlwcCV59ZExNCyJEQiI/MxFFDgcvMkI5bToUHxQWAWU3ATYBVy1hZ15fNQEzXS5eSBMcFQcDBWV5QjMLQC8pE15iBRAkXSUYFFIKBFknAjYtFi0LXGpHTjg4bwsnGCReN1AKFRIZTSQqBmQAVzM5LxEPRlJhTCNVCjlxeX5+ZCkrASUIEickNEURW0JpSyhCAVYWUFpXDiAqFiEWG20AJlZfDxY0XC46bTpxeX4bAiYlDmQUUzA+TTg4b2tIUS0QIl8ZFwRZPiwoByoQYCIqIhFFDgcvMkI5bTpxeQcWHjZkX2QQQDYoTTg4b2tIXSdDATlxeX5+ZEw0AzcXEn5tI1hCEkJ9BWt2CFIfA1k2BCgCDTI2UyckMkI7b2tIMUJVCldyeX5+ZEwtBGQUUzA+Z1BfAkJpViRERHUUERAEQwQtDxINQSovK1RyDgciU2tfFhMRAyEeHiwmDiFMQiI/Mx0RBQogSmIZREcQFRl9ZExNa01tWyVtKV5FRgAkSz9jB1wKFVcYH2UgCzcQEn9tJVRCEjEiVzlVREcQFRl9ZExNa01tOyEoNEViBQ0zXWsNRFcRAwN9ZExNa01tO25gZ0FDAwYoWz9ZC11YWBsSDCFkAD1ERCYhKFJYEhtoMkI5bTpxeX4bAiYlDmQFWy5tehFBBxA1FhtfF1oMGRgZZ0xNa01tO0okIRF3CgMmS2VxDV4oAhITBCYwCysKEn1tdxFFDgcvMkI5bTpxeX5+ASonAyhERCYhZwwRFgMzTGVxF0AdHRUbFAktDCEFQBUoK15SDxY4MkI5bTpxeX5+DCwpQnlEUyogZxoREActGGEQIl8ZFwRZLCwpMjYBViouM1heCGhIMUI5bTpxFRkTZ0xNa01tO0ovIkJFRl9hQ2tABUEMUEpXHSQ2FmhEUyogF15CRl9hWSJdSBMbGBYFTXhkASwFQGMwTTg4b2tIMS5eADlxeX5+ZCAqBk5tO0pEIl9VbGtIMS5eADlxeRIZCU9Nay1ED2MkZxoRV2hIXSVUbjoKFQMCHytkACEXRkkoKVU7bE9sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahw7S09hewR9JnIsUD84Ig4XQmwNXDA5Jl9SA00yUSVXCFYMHxlXACAwCisAEjAlJlVeEQsvX2vS5KdYHhhXAyQwCzIBEisiKFpCT2hsFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcbA4uWypcRHhIXFc8XGlkKXZIEgh+ZwwRFRYzUSVXSlAQEQVfXWxoQjcQQCojIB9SDgMzEHoZSBMLBAUeAyJqASwFQGt/bh0RFRYzUSVXSlAQEQVfXmxOaGlJEhAkK1RfEkIAUSYKREAQERMYGmUDBzAnUy4oNVB1BxYgGCReREcQFVc7AiYlDgINVSs5IkMRDwwyTCpeB1ZYAxhXGS0hQiMFXyZqNDscS0IuTyUQElIUGRMWGSAgQiINQCZtN1BFDkIyXSVUFxMXBQVXHyAgCzYBUTcoIxFQDw9vGBlVSVIIABseCCFkDSpEQCY+N1BGCExLVCRTBV9YFgIZDjEtDSpEVy0+MkNUNQstXSVEJVoVOBgYBm1taE0IXSAsKxFXDwUpTC5CRA5YFxIDKywjCjABQGtkTThYAEIvVz8QAlofGAMSH2UwCiEKEjEoM0RDCEIkVi86bVoeUAUWGiIhFmwCWyQlM1RDSkJjZxRJVlgnFxQTT2xkFiwBXGM/IkVEFAxhXSVUbjoUHxQWAWUrEC0DEn5tIVhWDhYkSmV3AUc7ERoSHyQAAzAFEmNtZxEcS0IzXThfCEUdA1cDBSBkASgFQTBtKlRFDg0lMkJZAhMMCQcSRSo2CyNNEj1wZxNXEwwiTCJfChFYBB8SA2U2BzARQC1tIl9VbGszWTxDAUdQFh4QBTEhEGhEEBwSPgNaOQUiXGkcRFwKGRBeZ0wiCyMMRiY/aXZUEiEgVS5CBXcZBBZXUGUiFyoHRioiKRlCAw4nFGseSh1Ren5+ASonAyhEUSdtehFeFAsmEDhVCFVUUFlZQ2xOa00NVGMLK1BWFUwSUSdVCkc5GRpXDCsgQjcBXiVtegwRAQc1fiJXDEcdAl9eTSQqBmQQSzMob1JVT0J8BWsSEFIaHBJVTTEsBypuO0pEN1JQCg5pXj5eB0cRHxlfRE9Na01tXiwuJl0RCRAoXyJeRA5YExMsJnUZaE1tO0okIRFfCRZhVzlZA1oWUAMfCCtkECEQRzEjZ1RfAmhIMUI5CFwbERtXGSQ2BSEQEn5tIFRFNQstXSVEMFIKFxIDRWxOa01tOyorZ0VQFAUkTGtEDFYWen5+ZExNDisHUy9tKEERW0IuSiJXDV1WIBgEBDEtDSpuO0pETjhSAjkKCRYQWRM7NgUWACBqDCETGiw9axFFBxAmXT8eBVoVIBgERE9Na01tOyorZ3ddBwUyFhhZCFYWBCUWCiBkFiwBXElETjg4b2siXBB7Vm5YTVcDDDcjBzBKQiI/Mzs4b2tIMUJTAGgzQypXUGUHJDYFXyZjKVRGTktLMUI5bTodHhN9ZExNayEKVklETjhUCAZoMkI5AV0cen5+HyAwFzYKEiApTThUCAZLMRlVF0cXAhIENmYWBzcQXTEoNBEaRlMcGHYQAkYWEwMeAitsS05tOy8iJFBdRgRhBWtXAUc+GRAfGSA2Sm1uO0okIRFXRgMvXGtCBUQfFQNfC2lkQBs7S3EmGFZSAkBoGD9YAV1yeX5+C2sDBzAnUy4oNVB1BxYgGHYQFlIPFxIDRSNoQmY7bTp/LG5WBQZjEUE5bToKEQAECDFsBGhEEBwSPgNaOQUiXGkcRF0RHF59ZEwhDCBuOyYjIztUCAZLMmYdRH0XUCQHHyAlBn5EQSssI15GRiUkTBhAFlYZFFcYA2UwCiFEdSIgIkFdBxsUTCJcDUcBUAQeAyIoBzALXGNgeRFYAgcvTCJEHR1yHBgUDClkBDEKUTckKF8RAwwyTTlVKlwrAAUSDCEMDSsPGmpHTl1eBQMtGAxlRA5YBAUOPyA1Fy0WV2sfIkFdDwEgTC5UN0cXAhYQCGsJDSARXiY+fXdYCAYHUTlDEHAQGRsTRWcDAykBQi8sPmRFDw4oTDISTRpyeR4RTSsrFmQjZ2M5L1RfRhAkTD5CChMdHhN9ZCwiQjYFRSQoMxl2M05hGhRvHQETLwQHHyAlBmZNEjclIl8RFAc1TTleRFYWFH1+ASonAyhEXzdtehFWAxYsXT9REFIaHBJfKhBtaE0IXSAsKxFeEQwkSmsNRBsVBFcWAyFkECUTVSY5b1xFSkJjZxRZClcdCFVeRGUrEGQjZ0lELlcREhsxXWNfE10dAl5XE3hkQDAFUC8oZRFFDgcvGCRHClYKUEpXKhBkByoAOEo9JFBdCkoyXT9CAVIcHxkbFGlkDTMKVzFhZ1dQChEkEUE5CFwbERtXAjctBWRZEiw6KVRDSCUkTBhAFlYZFH1+BCNkFj0UV2siNVhWT0I/BWsSAkYWEwMeAitmQjAMVy1tNVRFExAvGC5eADlxAhYAHiAwSgMxHmNvGG5IVAkeSztCAVIcUltXGTcxB21uOyw6KVRDSCUkTBhAFlYZFFdKTSMxDCcQWywjb0JUCgRtGGUeShpyeX4eC2UCDiUDQW0DKGJBFAcgXGtEDFYWUAUSGTA2DGQndDEsKlQfCAc2EGIQAV0cen5+HyAwFzYKEiw/LlYZFQctXmcQSh1WWX1+CCsgaE02VzA5KENUFTliai5DEFwKFQRXRmV1P2RZEiU4KVJFDw0vEGI6bToIExYbAW0iFyoHRioiKRkYRg02Vi5CSnQdBCQHHyAlBmRZEiw/LlYRAwwlEUE5AV0cehIZCU9OT2lEfCxtFVRSCQstAmtCAUMUERQSTRoWBycLWy9tKF8REgokGAxFChMRBBIaTSYoAzcXEm5zZ19eSw0xGDxYDV8dUBEbDCIjByBKOC8iJFBdRgQ0VihEDVwWUBIZHjA2BwoLYCYuKFhdLg0uU2MZbjoUHxQWAWUqDSABEn5tF2ILIAsvXA1ZFkAMMx8eASFsQAkLVjYhIkITT2hIViRUARNFUBkYCSBkAyoAEi0iI1QLIAsvXA1ZFkAMMx8eASFsQA0QVy4ZPkFUFUBoMkJeC1cdUEpXAyogB2QFXCdtKV5VA1gHUSVUIloKAwM0BSwoBmxGdTYjZRg7bw4uWypcRHQNHjQbDDY3QnlERjE0FVRAEwszXWNeC1cdWX1+BCNkDCsQEgQ4KXJdBxEyGD9YAV1YAhIDGDcqQiEKVklELlcRFAM2Xy5ETHQNHjQbDDY3TmRGbRw0dVpuFAciVyJcRhpYBB8SA2U2BzARQC1tIl9VbGsxWypcCBsLFQMFCCQgDSoIS29tAERfJQ4gSzgcRFUZHAQSRE9NDisHUy9tKENYAUJ8GDlRE1QdBF8wGCsHDiUXQW9tZW5jAwEuUScSTTlxGRFXGTw0B2wLQCoqbhFPW0JjXj5eB0cRHxlVTTEsBypEQCY5MkNfRgcvXEE5FlIPAxIDRQIxDAcIUzA+axETOT04CiBvFlYbHx4bT2lkFjYRV2pHTnZECCEtWThDSmwqFRQYBClkX2QCRy0uM1heCEoyXSdWSBNWXlleZ0xNCyJEdC8sIEIfKA0TXShfDV9YBB8SA2U2BzARQC1tIl9VbGtISi5EEUEWUBgFBCJsESEIVG9taR8fT2hIXSVUbjoqFQQDAjchER9HYCY+M15DAxFhE2sBORNFUBECAyYwCysKGmpHTjhBBQMtVGNWEV0bBB4YA21tQgMRXAAhJkJCSD0TXShfDV9YTVcYHywjQiEKVmpHTlRfAmgkVi86bh5VUBoWBCswByoFXCAoZ11eCRJ7GCBVAUNYGBgYBjZkAzQUXiooIxFQBRAuSzgQFlYLABYAAzZkFSwNXiZtJl9IRgEuVSlREBMeHBYQTSw3QisKOC8iJFBdRgQ0VihEDVwWUAQDDDcwISsJUCI5ClBYCBYgUSVVFhtRen4eC2UQCjYBUyc+aVJeCwAgTGtEDFYWUAUSGTA2DGQBXCdHTmVZFAcgXDgeB1wVEhYDTXhkFjYRV0lEM1BCDUwySCpHChseBRkUGSwrDGxNOEpEMFlYCgdhbCNCAVIcA1kUAigmAzBEVixHTjg4FgEgVCcYAV0LBQUSPiwoByoQcyogD15eDUtLMUI5FFAZHBtfCCs3FzYBfCweN0NUBwYJVyRbTTlxeX4HDiQoDmwBXDA4NVR/CTAkWyRZCHsXHxxeZ0xNazAFQShjMFBYEkpxFn4ZbjpxFRkTZ0whDCBNOCYjIzs7S09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gajscS0IVagJ3I3YqMjgjTW0iCzYBQWM5L1QRAQMsXWxDRFwPHlcEBSorFmQNXDM4MxFGDgcvGCpZCVYcUBYDTSQqQiEKVy40bjscS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gTV1eBQMtGC1FClAMGRgZTSY2DTcXWiIkNXRfAw84EGI6bR5VUB4ETTEsB2QHQCw+NFlQDxBhWz5CFlYWBBsOTSoyBzZEUy1tIl9UCxthUCJEBlwAT31+ASonAyhERiI/IFRFRl9hXy5EN1oUFRkDOSQ2BSEQGmpHTlhXRgwuTGtEBUEfFQNXGS0hDGQWVzc4NV8RAAMtSy4QAV0cen4bAiYlDmQHVy05IkMRW0ICWSZVFlJWJh4SGjUrEDA3WzkoZxsRVkx0MkJcC1AZHFcEDjchBypED2M6KENdAjYuayhCAVYWWAMWHyIhFmoUUzE5aWFeFQs1USReTTlxAhIDGDcqQmwXUTEoIl8RS0IiXSVEAUFRXjoWCistFjEAV2NxehEAXmgkVi86bl8XExYbTSMxDCcQWywjZ0JFBxA1bDlZA1QdAhUYGW1taE0NVGMZL0NUBwYyFj9CDVQfFQVXGS0hDGQWVzc4NV8RAwwlMkJkDEEdERMEQzE2CyMDVzFtehFFFBckMkJEBUATXgQHDDIqSiIRXCA5Ll5fTktLMUJHDFoUFVcjBTchAyAXHDc/LlZWAxBhWSVURHUUERAEQxE2CyMDVzEvKEURAg1LMUI5CFwbERtXCyw2ByBED2MrJl1CA2hIMUJAB1IUHF8RGCsnFi0LXGtkTTg4b2soXmtTFlwLAx8WBDcBDCEJS2tkZ0VZAwxLMUI5bToUHxQWAWUiCyMMRiY/ZwwRAQc1fiJXDEcdAl9eZ0xNa01tWyVtIVhWDhYkSmtEDFYWen5+ZExNayINVSs5IkMLLwwxTT8YRmAMEQUDPi0rDTANXCRvbjs4b2tIMUJWDUEdFFdKTTE2FyFuO0pETjhUCAZLMUI5bVYWFH1+ZEwhDCBNOEpETlhXRgQoSi5UREcQFRl9ZExNazAFQShjMFBYEkoHVCpXFx0sAh4QCiA2JiEIUzpkTTg4bwctSy46bTpxeQMWHi5qFSUNRmt9aQEET2hIMUJVCldyeX4SAyFOa00wWjEoJlVCSBYzUSxXAUFYTVcZBClOayEKVmpHIl9VbGhsFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcbE9sGAN5MHE3KFcyNRUFLAAhYGNlJF1YAww1GDlRHVAZAwNXDCwgWWQWVzA5KENUFUIuVmtUDUAZEhsSRE9pT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaZykrASUIEiY1N1BfAgclaCpCEEBYTVcMEE8oDScFXmMrMl9SEgsuVmtDEFIKBD8eGScrGgEcQiIjI1RDTktLMSJWRGcQAhIWCTZqCi0QUCw1Z0VZAwxhSi5EEUEWUBIZCU9NNiwWVyIpNB9ZDxYjVzMQWRMMAgISZ0wwAzcPHDA9JkZfTgQ0VihEDVwWWF59ZEwzCi0IV2MZL0NUBwYyFiNZEFEXCFcWAyFkJCgFVTBjD1hFBA05fTNABV0cFQVXCSpOa01tQiAsK10ZABcvWz9ZC11QWX1+ZExNDisHUy9tN11QHwczS2sNRGMUEQ4SHzZ+JSEQYi8sPlRDFUpoMkI5bToUHxQWAWUtQnlEA0lETjg4EQooVC4QDRNETVdUHSklGyEWQWMpKDs4b2tIMSdfB1IUUAcbH2V5QjQIUzooNUJqDz9LMUI5bToUHxQWAWUnCiUWEn5tN11DSCEpWTlRB0cdAn1+ZExNay0CEiAlJkMRBwwlGCJDIV0dHQ5fHSk2TmQQQDYobhFQCAZhUThxCFoOFV8UBSQ2S2QQWiYjTTg4b2tIMSdfB1IUUB8VTXhkASwFQHkLLl9VIAszSz9zDFoUFF9VJSwwACsccCwpPhMYbGtIMUI5bVoeUB8VTSQqBmQMUHkENHAZRCAgSy5gBUEMUl5XGS0hDE5tO0pETjg4DwRhViRERFYAABYZCSAgMiUWRjAWL1NsRhYpXSU6bTpxeX5+ZEwhGjQFXCcoI2FQFBYyYyNSORNFUB8VQxYtGCFuO0pETjg4bwcvXEE5bTpxeX5+BSdqMS0eV2NwZ2dUBRYuSngeClYPWDEbDCI3TAwNRiEiP2JYHAdtGA1cBVQLXj8eGScrGhcNSCZhZ3ddBwUyFgNZEFEXCCQeFyBtaE1tO0pETjhZBEwVSipeF0MZAhIZDjxkX2RVOEpETjg4b2spWmVzBV07HxsbBCEhQnlEVCIhNFQ7b2tIMUI5AV0cen5+ZExNByoAOEpETjg4D0J8GCIQTxNJen5+ZEwhDCBuO0pEIl9VT2hIMUJEBUATXgAWBDFsUmpQG0lETlRfAmhIMWYdREEdAwMYHyBOa00CXTFtN1BDEk5hSyJKARMRHlcHDCw2EWwBSjMsKVVUAjIgSj9DTRMcH31+ZEw0ASUIXmsrMl9SEgsuVmMZRFoeUAcWHzFkAyoAEjMsNUUfNgMzXSVEREcQFRlXHSQ2Fmo3WzkoZwwRFQs7XWtVCldYFRkTRE9NayEKVklETlRJFgMvXC5UNFIKBARXUGU/H05tOxclNVRQAhFvUCJEBlwAUEpXAywoaE0BXCdkTVRfAmhLFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS2hsFWt1N2NYWDMFDDItDCNEcxMEbjscS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gTV1eBQMtGC1FClAMGRgZTSshFQAWUzQkKVYZBQ4gSzgcREMKHwcERE9NDisHUy9tKFodRgZhBWtAB1IUHF8RGCsnFi0LXGtkZ0NUEhczVmt0FlIPGRkQQyshFWwHXiI+NBgRAwwlEUE5DVVYHhgDTSovQjAMVy1tNVRFExAvGCVZCBMdHhN9ZCMrEGQPHmM7Z1hfRhIgUTlDTEMKHwcERGUgDU5tOzMuJl1dTgQ0VihEDVwWWF5XCR4vP2RZEjVtIl9VT2hIXSVUbjoKFQMCHytkBk4BXCdHTV1eBQMtGC1FClAMGRgZTSglCSEhQTNlN11DT2hIUS0QIEEZBx4ZCjYfEigWb2M5L1RfRhAkTD5CChM8AhYABCsjER8UXjEQZ1RfAmhIVCRTBV9YAxIDTXhkGU5tOyEiPxERRkJhBWteAUQ8AhYABCsjSmY3QzYsNVQTSkJhGDAQMFsRExwZCDY3QnlEA29tAVhdCgclGHYQAlIUAxJbTRMtES0GXiZtehFXBw4yXWtNTR9yeX4VAj0LFzBEEn5tKVRGIhAgTyJeAxtaIwYCDDchQGhEEmM2Z2VZDwEqVi5DFxNFUERbTQMtDigBVmNwZ1dQChEkFGtmDUAREhsSTXhkBCUIQSZhZ3JeCg0zGHYQJ1wUHwVEQyshFWxUHnNhdxgRG0ttMkI5ClIVFVdXTWV5QioBRQc/JkZYCAVpGh9VHEdaXFdXTWVkGWQ3WzkoZwwRV1FtGAhVCkcdAldKTTE2FyFIEgw4M11YCAdhBWtEFkYdXFchBDYtACgBEn5tIVBdFQdhRWIcbjpxFB4EGWVkQmRZEi0oMHVDBxUoViwYRmcdCANVQWVkQmRESWMeLktURl9hCXkcRHAdHgMSH2V5QjAWRyZhZ35EEg4oVi4QWRMMAgISQWUSCzcNUC8oZwwRAAMtSy4QGRpUen5+BSAlDjAMEmNwZ19UESYzWTxZClRQUjseAyBmTmREEmNtPBFlDgsiUyVVF0BYTVdFQWUSCzcNUC8oZwwRAAMtSy4QGRpUen5+BSAlDjAMcCRwZ19UESYzWTxZClRQUjseAyBmTmREEmNtPBFlDgsiUyVVF0BYTVdFQWUSCzcNUC8oZwwRAAMtSy4cRHAXHBgFTXhkISsIXTF+aV9UEUpxFHscVBpYDV5bZ0xNFjYFUSY/ZxEMRgwkTw9CBUQRHhBfTwktDCFGHmNtZxERHUIVUCJTD10dAwRXUGV1TmQyWzAkJV1URl9hXipcF1ZYDV5bZ0w5aE0gQCI6Ll9WFTkxVDltRA5YAxIDZ0w2BzARQC1tNFRFbAcvXEE6CFwbERtXCzAqATANXS1tL1hVAycySGNDAUdRen4RAjdkPWhEVmMkKRFBBwszS2NDAUdRUBMYZ0xNCyJEVmM5L1RfRhIiWSdcTFUNHhQDBCoqSm1EVm0bLkJYBA4kGHYQAlIUAxJXCCsgS2QBXCdHTlRfAmgkVi86bl8XExYbTSMxDCcQWywjZ1JdAwMzfThATBpyeREYH2U0DjZIEjAoMxFYCEIxWSJCFxs8AhYABCsjEW1EVixHTjhXCRBhZ2cQABMRHlcHDCw2EWwXVzdkZ1VebGtIMSJWRFdYBB8SA2U0ASUIXmsrMl9SEgsuVmMZRFdCIhIaAjMhSm1EVy0pbhFUCAZLMUJVCldyeX4zHyQzCyoDQRg9K0NsRl9hViJcbjodHhN9CCsgaE4IXSAsKxFXEwwiTCJfChMNABMWGSABETRMG0lELlcRCA01GA1cBVQLXjIEHQAqAyYIVydtM1lUCGhIMS1fFhMnXFcECDFkCypEQiIkNUIZIhAgTyJeA0BRUBMYTS0tBiEhQTNlNFRFT0IkVi86bToKFQMCHytOayEKVklEK15SBw5hWyRcC0FYTVcxASQjEWohQTMOKF1eFGhIVCRTBV9YABsWFCA2EWRZEhMhJkhUFBF7fy5ENF8ZCRIFHm1taE0IXSAsKxFYRl9hCUE5E1sRHBJXBGV4X2RHQi8sPlRDFUIlV0E5bV8XExYbTTUoEGRZEjMhJkhUFBEaURY6bToUHxQWAWU3BzBED2MgJlpUIxExEDtcFhpyeX4bAiYlDmQHWiI/ZwwRFg4zFghYBUEZEwMSH09NaygLUSIhZ1lDFkJ8GChYBUFYERkTTSYsAzZedCojI3dYFBE1eyNZCFdQUj8CACQqDS0AYCwiM2FQFBZjEUE5bV8XExYbTS0hAyBED2MuL1BDRgMvXGtTDFIKSjEeAyECCzYXRgAlLl1VTkAJXSpURhpyeX4bAiYlDmQSUy8kIxEMRgQgVDhVbjpxGRFXDi0lEGQFXCdtL0NBRgMvXGtYAVIcUBYZCWU0DjZETH5tC15SBw4RVCpJAUFYERkTTSw3IygNRCZlJFlQFEthTCNVCjlxeX4bAiYlDmQBXCYgPhEMRgsyfSVVCUpQABsFQWUCDiUDQW0INEFlAwMseyNVB1hRen5+ZCwiQiEKVy40Z15DRgwuTGt2CFIfA1kyHjUQByUJcSsoJFoREgokVkE5bTpxHBgUDClkBi0XRmNwZxlyBw8kSioeJ3UKERoSQxUrES0QWywjZxwRDhAxFhtfF1oMGRgZRGsJAyMKWzc4I1Q7b2tIMSJWRFcRAwNXUXhkJCgFVTBjAkJBKwM5fCJDEBMMGBIZZ0xNa01tXiwuJl0REg0xaCRDSBMXHiMYHWV5QjMLQC8pE15iBRAkXSUYDFYZFFknAjYtFi0LXGNmZ2dUBRYuSngeClYPWEdbTXVqVWhEAmpkTTg4b2tIVCRTBV9YEhgDPSo3TmQLXAEiMxEMRhUuSidUMFwrEwUSCCtsCjYUHBMiNFhFDw0vGGYQMlYbBBgFXmsqBzNMAm9tdB8DSkJxEWI6bTpxeX4eC2UrDBALQmMiNRFeCCAuTGtEDFYWen5+ZExNazIFXiopZwwREhA0XUE5bTpxeX4bAiYlDmQMEn5tKlBFDkwgWjgYBlwMIBgEQxxkT2QQXTMdKEIfP0tLMUI5bTpxHBgUDClkFWRZEittbREBSFd0MkI5bTpxeRsYDiQoQjxED2M5KEFhCRFvYGsdRERYX1dFZ0xNa01tOy8iJFBdRhthBWtEC0MoHwRZNE9Na01tO0pgahFTCRpLMUI5bTpxGRFXKyklBTdKdzA9BV5JRhYpXSU6bTpxeX5+ZDYhFmoGXTsCMkUfNQs7XWsNRGUdEwMYH3dqDCETGjRhZ1kYXUIyXT8eBlwAPwIDQxUrES0QWywjZwwRMAciTCRCVh0WFQBfFWlkG21fEjAoMx9TCRoOTT8eMloLGRUbCGV5QjAWRyZHTjg4b2tIMThVEB0aHw9ZPiw+B2RZEhUoJEVeFFBvVi5HTERUUB9eVmU3BzBKUCw1aWFeFQs1USReRA5YJhIUGSo2UGoKVzRlPx0RH0t6GDhVEB0aHw9ZLiooDTZED2MuKF1eFFlhSy5ESlEXCFkhBDYtACgBEn5tM0NEA2hIMUI5bTodHAQSZ0xNa01tO0o+IkUfBA05Fh1ZF1oaHBJXUGUiAygXV3htNFRFSAAuQARFEB0uGQQeDykhQnlEVCIhNFQ7b2tIMUI5AV0cen5+ZExNa2lJEi0sKlQ7b2tIMUI5DVVYNhsWCjZqJzcUfCIgIhFFDgcvMkI5bTpxeX4ECDFqDCUJV20ZIklFRl9hSCdCSncRAwcbDDwKAykBEiw/Z0FdFEwPWSZVbjpxeX5+ZEw3BzBKXCIgIh9hCREoTCJfChNFUCESDjErEHZKXCY6b0VeFjIuS2VoSBMBUFpXXHBtaE1tO0pETjhCAxZvVipdAR07HxsYH2V5QicLXiw/fBFCAxZvVipdAR0uGQQeDykhQnlERjE4Ijs4b2tIMUJVCEAden5+ZExNa00XVzdjKVBcA0wXUThZBl8dUEpXCyQoESFuO0pETjg4AwwlMkI5bTpxeVpaTSEtETAFXCAoTTg4b2tIMSJWRHUUERAEQwA3EgANQTcsKVJURhYpXSU6bTpxeX5+ZDYhFmoAWzA5aWVUHhZhBWtDEEERHhBZCyo2DyUQGmFoI1wTSkIsWT9YSlUUHxgFRSEtETBNG0lETjg4b2tISy5ESlcRAwNZPSo3CzANXS1tehFnAwE1VzkCSl0dB18DAjUUDTdKam9tPhEaRgphE2sCTTlxeX5+ZExNESEQHCckNEUfJQ0tVzkQWRMbHxsYH35kESEQHCckNEUfMAsyUSlcARNFUAMFGCBOa01tO0pEIl1CA2hIMUI5bTpxAxIDQyEtETBKZCo+LlNdA0J8GC1RCEAden5+ZExNayEKVklETjg4b2tsFWtYAVIUBB9XDyQ2aE1tO0pETl1eBQMtGCNFCRNFUBQfDDd+JC0KVgUkNUJFJQooVC9/AnAUEQQERWcMFykFXCwkIxMYbGtIMUI5bVoeUDEbDCI3TAEXQgsoJl1FDkIgVi8QDEYVUAMfCCtOa01tO0pETl1eBQMtGDtTEBNFUBoWGS1qASgFXzNlL0RcSCokWSdEDBNXUBoWGS1qDyUcGnJhZ1lEC0wMWTN4AVIUBB9eQWV0TmRVG0lETjg4b2tIVCRTBV9YGA9XUGU8QmlEBklETjg4b2tISy5ESlsdERsDBQcjTAIWXS5tehFnAwE1VzkCSl0dB18fFWlkG21fEjAoMx9ZAwMtTCNyAx0sH1dKTRMhATALQHFjKVRGTgo5FGtJRBhYGF5MTTYhFmoMVyIhM1lzAUwXUThZBl8dUEpXGTcxB05tO0pETjg4FQc1FiNVBV8MGFkxHyopQnlEZCYuM15DVEwvXTwYDEtUUA5XRmUsQm5EGnJtahFBBRZoEXAQF1YMXh8SDCkwCmowXWNwZ2dUBRYuSnkeClYPWB8PQWU9Qm9EWmpHTjg4b2tIMThVEB0QFRYbGS1qISsIXTFtehFyCQ4uSngeAkEXHSUwL212V3FEH2MgJkVZSAQtVyRCTAFNRVddTTUnFm1IEi4sM1kfAA4uVzkYVgZNUF1XHSYwS2hEBHNkTTg4b2tIMUJDAUdWGBIWATEsTBINQSovK1QRW0I1Sj5VbjpxeX5+ZCAoESFuO0pETjg4bxEkTGVYAVIUBB9ZOyw3CyYIV2NwZ1dQChEkA2tDAUdWGBIWATEsICNKZCo+LlNdA0J8GC1RCEAden5+ZExNayEKVklETjg4b2tsFWtEFlIbFQV9ZExNa01tWyVtAV1QARFvfThAMEEZExIFTTEsBypuO0pETjg4bxEkTGVEFlIbFQVZKzcrD2RZEhUoJEVeFFBvVi5HTHAZHRIFDGsSCyETQiw/M2JYHAdvYGsfRAFUUDQWACA2A2oyWyY6N15DEjEoQi4ePRpyeX5+ZExNazcBRm05NVBSAxBvbCQQWRMuFRQDAjd2TCoBRWs5KEFhCRFvYGcQHRNTUB9eZ0xNa01tO0o+IkUfEhAgWy5CSnAXHBgFTXhkASsIXTF2Z0JUEkw1SipTAUFWJh4EBCcoB2RZEjc/MlQ7b2tIMUI5AV8LFX1+ZExNa01tQSY5aUVDBwEkSmVmDUAREhsSTXhkBCUIQSZHTjg4b2tIXSVUbjpxeX5+CCsgaE1tO0ooKVU7b2tIXSVUbjpxFRkTZ0xNCyJEXCw5Z0dQCgslGD9YAV1YGB4TCAA3EmwXVzdkZ1RfAmhIMSIQWRMRUFxXXE9NByoAOCYjIzs7S09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gajscS0IMdx11KXY2JH1aQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VehsYDiQoQiIRXCA5Ll5fRgUkTANFCRtRen4bAiYlDmQHEn5tC15SBw4RVCpJAUFWMx8WHyQnFiEWOEo/IkVEFAxhW2tRCldYE00xBCsgJC0WQTcOL1hdAi0neydRF0BQUj8CACQqDS0AEGphZ1I7AwwlMkFcC1AZHFcRGCsnFi0LXGM+M1BDEi8uTi5dAV0MPRYeAzElCyoBQGtkTThYAEIVUDlVBVcLXhoYGyBkFiwBXGM/IkVEFAxhXSVUbjosGAUSDCE3TCkLRCZtehFFFBckMkJEFlIbG18lGCsXBzYSWyAoaXlUBxA1Wi5REAk7HxkZCCYwSiIRXCA5Ll5fTktLMUJZAhMWHwNXOS02ByUAQW0gKEdURhYpXSUQFlYMBQUZTSAqBk5tOy8iJFBdRgo0VWsNRFQdBD8CAG1taE1tWyVtL0RcRhYpXSU6bTpxGRFXKyklBTdKZSIhLGJBAwcldyUQEFsdHlcfGChqNSUIWRA9IlRVRl9hfidRA0BWJxYbBhY0ByEAEiYjIzs4b2soXmt2CFIfA1k9GCg0LSpERisoKRFZEw9vcj5dFGMXBxIFTXhkJCgFVTBjDURcFjIuTy5CXxMQBRpZODYhKDEJQhMiMFRDRl9hTDlFARMdHhN9ZEwhDCBuOyYjIxgYbAcvXEE6SR5YGRkRBCstFiFEWDYgNztFFAMiU2NlF1YKORkHGDEXBzYSWyAoaXtECxITXTpFAUAMSjQYAyshATBMVDYjJEVYCQxpEUE5DVVYNhsWCjZqKyoCeDYgNxFFDgcvMkI5CFwbERtXBTApQnlEVSY5D0RcTktLMUJZAhMQBRpXGS0hDGQUUSIhKxlXEwwiTCJfChtRUB8CAH8HCiUKVSYeM1BFA0oEVj5dSnsNHRYZAiwgMTAFRiYZPkFUSCg0VTtZClRRUBIZCWxkByoAOEooKVU7AwwlEWI6bh5VUBEbFE8oDScFXmMrK0hnAw5LVCRTBV9YFgIZDjEtDSpEQTcsNUV3ChtpEUE5DVVYJB8FCCQgEWoCXjptM1lUCEIzXT9FFl1YFRkTZ0wQCjYBUyc+aVddH0J8GD9CEVZyeQMWHi5qETQFRS1lIURfBRYoVyUYTTlxeRsYDiQoQiwRX29tJFlQFEJ8GCxVEHsNHV9eZ0xNDisHUy9tL0NBRl9hWyNRFhMZHhNXDi0lEH4iWy0pAVhDFRYCUCJcABtaOAIaDCsrCyA2XSw5F1BDEkBoMkI5E1sRHBJXOS02ByUAQW0rK0gRBwwlGA1cBVQLXjEbFAoqQiALOEpETllEC05hWyNRFhNFUBASGQ0xD2xNOEpETllDFkJ8GChYBUFYERkTTSYsAzZedCojI3dYFBE1eyNZCFdQUj8CACQqDS0AYCwiM2FQFBZjEUE5bToRFlcfHzVkFiwBXElETjg4DwRhViRERFUUCSESAWUwCiEKOEpETjg4AA44bi5cRA5YORkEGSQqASFKXCY6bxNzCQY4bi5cC1ARBA5VRE9Na01tOyUhPmdUCkwMWTN2C0EbFVdKTRMhATALQHBjKVRGTlNtGHocRAJRUF1XVCB9aE1tO0pEIV1IMActFhsQWRNBFUN9ZExNa00CXjobIl0fMActVyhZEEpYTVchCCYwDTZXHC0oMBkBSkJxFGsATTlxeX5+ZCMoGxIBXm0dJkNUCBZhBWtYFkNyeX5+ZCAqBk5tO0pEK15SBw5hVSRGARNFUCESDjErEHdKXCY6bwEdRlJtGHsZbjpxeX4bAiYlDmQHVGNwZ3JQCwczWWVzIkEZHRJ9ZExNay0CEhY+IkN4CBI0TBhVFkURExJNJDYPBz0gXTQjb3RfEw9vcy5JJ1wcFVkgRGUwCiEKEi4iMVQRW0IsVz1VRBhYExFZISorCRIBUTciNRFUCAZLMUI5bVoeUCIECDcNDDQRRhAoNUdYBQd7cTh7AUo8HwAZRQAqFylKeSY0BF5VA0wSEWtEDFYWUBoYGyBkX2QJXTUoZxwRBQRvdCRfD2UdEwMYH2UhDCBuO0pETlhXRjcyXTl5CkMNBCQSHzMtASFeezAGIkh1CRUvEA5eEV5WOxIOLiogB2olG2M5L1RfRg8uTi4QWRMVHwESTWhkASJKYCoqL0VnAwE1VzkQAV0cen5+ZEwtBGQxQSY/Dl9BExYSXTlGDVAdSj4EJiA9JisTXGsIKURcSCkkQQhfAFZWNF5XGS0hDGQJXTUoZwwRCw03XWsbRFAeXiUeCi0wNCEHRiw/Z1RfAmhIMUI5DVVYJQQSHwwqEjEQYSY/MVhSA1gISwBVHXcXBxlfKCsxD2ovVzoOKFVUSDExWShVTRMMGBIZTSgrFCFED2MgKEdURklhbi5TEFwKQ1kZCDJsUmhEA29tdxgRAwwlMkI5bToRFlciHiA2KyoURzceIkNHDwEkAgJDL1YBNBgAA20BDDEJHAgoPnJeAgdvdC5WEGAQGREDRGUwCiEKEi4iMVQRW0IsVz1VRB5YJhIUGSo2UWoKVzRldx0RV05hCGIQAV0cen5+ZEwiDj0yVy9jEVRdCQEoTDIQWRMVHwESTW9kJCgFVTBjAV1INRIkXS86bTpxFRkTZ0xNaxYRXBAoNUdYBQdvai5eAFYKIwMSHTUhBn4zUyo5bxg7b2skVi86bToRFlcRATwSByhERisoKRFXChsXXScKIFYLBAUYFG1tWWQCXjobIl0RW0IvUScQAV0cen5+OS02ByUAQW0rK0gRW0IvUSc6bVYWFF59CCsgaE5JH2MjKFJdDxJLVCRTBV9YFgIZDjEtDSpEQTcsNUV/CQEtUTsYTTlxGRFXOS02ByUAQW0jKFJdDxJhTCNVChMKFQMCHytkByoAOEoZL0NUBwYyFiVfB18RAFdKTTE2FyFuOzc/JlJaTjA0VhhVFkURExJZPjEhEjQBVnkOKF9fAwE1EC1FClAMGRgZRWxOa00NVGMjKEURIA4gXzgeKlwbHB4HIitkFiwBXGM/IkVEFAxhXSVUbjpxHBgUDClkASwFQGNwZ31eBQMtaCdRHVYKXjQfDDclATABQElETlhXRgEpWTkQEFsdHn1+ZEwiDTZEbW9tNxFYCEIoSCpZFkBQEx8WH38DBzAgVzAuIl9VBww1S2MZTRMcH31+ZExNCyJEQnkENHAZRCAgSy5gBUEMUl5XDCsgQjRKcSIjBF5dCgslXWtEDFYWen5+ZExNEmonUy0OKF1dDwYkGHYQAlIUAxJ9ZExNayEKVklETjhUCAZLMUJVCldyeRIZCWxtaCEKVklHahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH0lgahFhKiMYfRk6SR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFUEdSRMZHgMeQCQiCU4QQCIuLBl9CQEgVBtcBUodAlk+CSkhBn4nXS0jIlJFTgQ0VihEDVwWWF59ZCwiQgIIUyQ+aXBfEgsAXiAQEFsdHn1+ZDUnAygIGiU4KVJFDw0vEGI6bTpxHBgUDClkFDFED2MqJlxUXCUkTBhVFkURExJfTxMtEDARUy8YNFRDREtLMUI5EkZCMxYHGTA2BwcLXDc/KF1dAxBpEUE5bToOBU00ASwnCQYRRjciKQMZMAciTCRCVh0WFQBfRGxOa00BXCdkTThUCAZLXSVUTRpyelpaTSYxETALX2MrKEcRSUInTSdcBkERFx8DTSglCyoQUyojIkM7Cg0iWScQF1IOFRMxAiJODisHUy9tIURfBRYoVyUQF0cZAgMnASQ9BzYpUyojM1BYCAczEGI6bVoeUCMfHyAlBjdKQi8sPlRDRhYpXSUQFlYMBQUZTSAqBk5tZis/IlBVFUwxVCpJAUFYTVcDHzAhaE0QQCIuLBljEwwSXTlGDVAdXiUSAyEhEBcQVzM9IlULJQ0vVi5TEBseBRkUGSwrDGxNOEpELlcRCA01GB9YFlYZFARZHSklGyEWEjclIl8RFAc1TTleRFYWFH1+ZCwiQgIIUyQ+aXJEFRYuVQ1fEhMMGBIZTTUnAygIGiU4KVJFDw0vEGIQJ1IVFQUWQwMtBygAfSUbLlRGRl9hfidRA0BWNhgBOyQoFyFEVy0pbhFUCAZLMUJZAhM+HBYQHmsCFygIUDEkIFlFRhYpXSU6bTpxPB4QBTEtDCNKcDEkIFlFCAcyS2sNRAByeX5+ISwjCjANXCRjBF1eBQkVUSZVRA5YQUV9ZExNLi0DWjckKVYfIA0mfSVURA5YQRJOZ0xNawgNVSs5Ll9WSCUtVylRCGAQERMYGjZkX2QCUy8+Ijs4bwcvXEE5AV0cWV59CCsgaE5JH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpaGlJEgQMCnQRSUIMcRhzbh5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWY6CFwbERtXCzAqATANXS1tLV5YCDM0XT5VTBpyeRsYDiQoQjYCEn5tIFRFNAcsVz9VTBE1EQMUBSglCS0KVWFhZxN7CQsvaT5VEVZaWX1+BCNkECJEUy0pZ0NXXCsyeWMSNlYVHwMSKzAqATANXS1vbhFFDgcvMkI5FFAZHBtfCzAqATANXS1lbhFDAFgIVj1fD1YrFQUBCDdsS2QBXCdkTThUCAZLXSVUbjkUHxQWAWUiFyoHRioiKRFDAwYkXSZzC1cdWBQYCSBtaE0IXSAsKxFDAEJ8GCxVEGEdHRgDCG1mJiUQU2FhZxNjAwYkXSZzC1cdUl59ZCwiQjYCEiIjIxFDAFgISwoYRmEdHRgDCAMxDCcQWywjZRgRBwwlGChfAFZYERkTTWYnDSABEn1tdxFFDgcvMkI5CFwbERtXAi5oQjYBQWNwZ0FSBw4tEC1FClAMGRgZRWxkECEQRzEjZ0NXXCsvTiRbAWAdAgESH20nDSABG2MoKVUYbGtIUS0QC1hYBB8SA09Na00oWyE/JkNIXCwuTCJWHRsDUCMeGSkhQnlEEAAiI1QTSkIFXThTFloIBB4YA2V5QmY3RyEgLkVFAwZ7GGkQSh1YExgTCGlkNi0JV2NwZwURG0tLMUJVCldyeRIZCU8hDCBuOC8iJFBdRgQ0VihEDVwWUAUSHjUlFSoqXTRlbjs4Cg0iWScQFlZYTVcQCDEWBykLRiZlZXVEAw4yGmcQRmEdAwcWGisKDTNGG0lELlcRFAdhWSVUREEdSj4ELG1mMCEJXTcoAkdUCBZjEWtEDFYWen5+HSYlDihMVDYjJEVYCQxpEWtCAQk+GQUSPiA2FCEWGmptIl9VT2hIXSVUblYWFH19ASonAyhEVDYjJEVYCQxhSz9RFkc5BQMYPDAhFyFMG0lELlcRMgozXSpUFx0JBRICCGUwCiEKEjEoM0RDCEIkVi86bWcQAhIWCTZqEzEBRyZtehFFFBckMkJEBUATXgQHDDIqSiIRXCA5Ll5fTktLMUJHDFoUFVcjBTchAyAXHDI4IkRURgMvXGt2CFIfA1k2GDErMzEBRyZtI147b2tISChRCF9QGhgeAxQxBzEBG0lETjhFBxEqFjxRDUdQRl59ZEwhDCBuO0oZL0NUBwYyFjpFAUYdUEpXAywoaE0BXCdkTVRfAmhLFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS2hsFWt1N2NYIjI5KQAWQggrfRNHahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH0k5NVBSDUoTTSVjAUEOGRQSQxchDCABQBA5IkFBAwZ7eyReClYbBF8RGCsnFi0LXGtkTThBBQMtVGNFFFcZBBIyHjVtaE1JH2MLCGcRBQszWydVbjoRFlcxASQjEWo3Wiw6AV5HRhYpXSU6bToRFlcZAjFkJjYFRSojIEIfOT0nVz0QEFsdHn1+ZEwAECUTWy0qNB9uOQQuTmsNRF0dBzMFDDItDCNMEAAkNVJdA0BtGDAQMFsRExwZCDY3QnlEA29tAVhdCgclGHYQAlIUAxJbTQsxDxcNViY+ZwwRUFZtGAhfCFwKUEpXLiooDTZXHCU/KFxjISBpCGcCVQNUQkVORGU5S05tOyYjIzs4bw4uWypcRFBYTVczHyQzCyoDQW0SGFdeEGhIMSJWRFBYBB8SA09Na00HHBEsI1hEFUJ8GA1cBVQLXjYeAAMrFBYFVio4NDs4b2siFhtfF1oMGRgZTXhkISUJVzEsaWdYAxUxVzlEN1oCFVddTXVqV05tO0ouaWdYFQsjVC4QWRMMAgISZ0xNByoAOEooK0JUDwRhfDlRE1oWFwRZMhoiDTJERisoKTs4byYzWTxZClQLXigoCyoyTBINQSovK1QRW0InWSdDATlxFRkTZyAqBm1NOEk5NVBSDUoRVCpJAUELXicbDDwhEBYBXyw7Ll9WXCEuViVVB0dQFgIZDjEtDSpMQi8/bjs4Cg0iWScQF1YMUEpXKTclFS0KVTAWN11DO2hIUS0QF1YMUAMfCCtOa00CXTFtGB0RAkIoVmtABVoKA18ECDFtQiALEiorZ1UREgokVmtAB1IUHF8RGCsnFi0LXGtkZ1ULNAcsVz1VTBpYFRkTRGUhDCBEVy0pTTg4IhAgTyJeA0AjABsFMGV5QioNXklEIl9VbAcvXGIZbjlVXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdbh5VUCA+IwELNWRPEhcMBWI7S09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gajt9DwAzWTlJSnUXAhQSLi0hAS8GXTttehFXBw4yXUE6CFwbERtXOiwqBisTEn5tC1hTFAMzQXFzFlYZBBIgBCsgDTNMSUlEE1hFCgdhBWsSNnouMTskT2lOawILXTcoNREMRkAYCiAQN1AKGQcDTQclAS9WcCIuLBMdbGsPVz9ZAkorGRMSTXhkQBYNVSs5ZR07bzEpVzxzEUAMHxo0GDc3DTZED2M5NURUSmhIey5eEFYKUEpXGTcxB2huOwI4M15iDg02GHYQEEENFVt9ZBchES0eUyEhIhEMRhYzTS4cbjo7HwUZCDcWAyANRzBtehEAVk5LRWI6bl8XExYbTRElADdED2M2TThyCQ8jWT8QRBNFUCAeAyErFX4lVicZJlMZRCEuVSlREBFUUFdXTzYzDTYAQWFkazs4MAsyTSpcFxNYTVcgBCsgDTNecycpE1BTTkAXUThFBV8LUltXTWchGyFGG29HTnxeEAcsXSVERA5YJx4ZCSozWAUAVhcsJRkTKw03XSZVCkdaXFdVDCYwCzINRjpvbh07bzItWTJVFhNYUEpXOiwqBisTCAIpI2VQBEpjaCdRHVYKUltXTWVmFzcBQGFkazs4IQMsXWsQRBNYTVcgBCsgDTNecycpE1BTTkAGWSZVRh9YUFdXTWc0AycPUyQoZRgdbGsCVyVWDVQLUFdKTRItDCALRXkMI1VlBwBpGghfClURFwRVQWVkQCAFRiIvJkJUREttMkJjAUcMGRkQHmV5QhMNXCciMAtwAgYVWSkYRmAdBAMeAyI3QGhEEDAoM0VYCAUyGmIcbjo7AhITBDE3QmRZEhQkKVVeEVgAXC9kBVFQUjQFCCEtFjdGHmNtZVhfAA1jEWc6GTlyXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSTlVXVc0IggGIxBEZgIPTRwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25HK15SBw5heyRdBlIMPFdKTRElADdKcSwgJVBFXCMlXAdVAkc/AhgCHScrGmxGcyogZR0RRAEzVzhDDFIRAlVeZykrASUIEgAiKlNQEjBhBWtkBVELXjQYACclFn4lVicfLlZZEiUzVz5ABlwAWFU0AigmAzBGHmNvNFlYAw4lGmI6bnAXHRUWGQl+IyAAZiwqIF1UTkASUSdVCkc5GRpVQWU/aE0wVzs5ZwwRRDEoVC5eEBM5GRpVQWUAByIFRy85ZwwRAAMtSy4cRGERAxwOTXhkFjYRV29HTmVeCQ41UTsQWRNaIhITBDchATAXEjclIhFWBw8kHzgQC0QWUAQfAjFkFitERisoZ0VQFAUkTGUQKFYfGQNXUGUCLRJJVSI5IlUfRE5LMQhRCF8aERQcTXhkBDEKUTckKF8ZEEthfidRA0BWIx4bCCswIy0JEn5tMQoRDwRhTmtEDFYWUAQDDDcwISsJUCI5ClBYCBYgUSVVFhtRUBIZCWUhDCBIOD5kTXJeCwAgTAcKJVccNAUYHSErFSpMEAIkKnxeAgdjFGtLbjosFQ8DTXhkQAkLViZvaxFnBw40XTgQWRMDUFU7CCItFmZIEmEfJlZUREI8FGt0AVUZBRsDTXhkQAgBVSo5ZR07byEgVCdSBVATUEpXCzAqATANXS1lMRgRIA4gXzgeN1oUFRkDPyQjB2RZEms7ZwwMRkATWSxVRhpYFRkTQU85S04nXS4vJkV9XCMlXA9CC0McHwAZRWcFCyksWzcvKEkTSkI6MkJkAUsMUEpXTw0tFiYLSmFhZ2dQChckS2sNREhYUj8SDCFmTmRGcCwpPhMRG05hfC5WBUYUBFdKTWcMByUAEG9HTnJQCg4jWShbRA5YFgIZDjEtDSpMRGptAV1QARFveSJdLFoMEhgPTXhkFGQBXCdhTUwYbCEuVSlREH9CMRMTPiktBiEWGmEMLlx3CRRjFGtLbjosFQ8DTXhkQAIrZGMfJlVYExFjFGt0AVUZBRsDTXhkU3VUHmMALl8RW0JzCGcQKVIAUEpXWHV0TmQ2XTYjI1hfAUJ8GHscRGANFhEeFWV5QmZEQjtvazs4JQMtVClRB1hYTVcRGCsnFi0LXGs7bhF3CgMmS2VxDV4+HwElDCEtFzdED2M7Z1RfAk5LRWI6J1wVEhYDIX8FBiA3XiopIkMZRCMoVRtCAVdaXFcMZ0wQBzwQEn5tZWFDAwYoWz9ZC11aXFczCCMlFygQEn5tdx0RKwsvGHYQVB9YPRYPTXhkU2hEYCw4KVVYCAVhBWsCSDlxJBgYATEtEmRZEmEBIlBVRg8uTiJeAxMMEQUQCDE3QmwWUyo+IhFXCRBheiRHS2AWGQcSH2U0ECsOVyA5Ll1UFUtvGmc6bXAZHBsVDCYvQnlEVDYjJEVYCQxpTmIQIl8ZFwRZLCwpMjYBViouM1heCEJ8GD0QAV0cXH0KRE8HDSkGUzcBfXBVAjYuXyxcARtaMR4aOyw3CyYIV2FhZ0o7bzYkQD8QWRNaJh4EBCcoB2QnWiYuLBMdRiYkXipFCEdYTVcDHzAhTk5tcSIhK1NQBQlhBWtWEV0bBB4YA20yS2QiXiIqNB9wDw8XUThZBl8dMx8SDi5kX2QSEiYjIx07G0tLeyRdBlIMPE02CSEQDSMDXiZlZXBYCzYkWSYSSBMDen4jCD0wQnlEEBcoJlwRJQokWyASSBM8FREWGCkwQnlERjE4Ih07byEgVCdSBVATUEpXCzAqATANXS1lMRgRIA4gXzgeJVoVJBIWAAYsBycPEn5tMRFUCAZtMjYZbnAXHRUWGQl+IyAAZiwqIF1UTkASUCRHIlwOUltXFk9NNiEcRmNwZxN1FAM2GA1/MhM7GQUUASBmTmQgVyUsMl1FRl9hXipcF1ZUen40DCkoACUHWWNwZ1dECAE1USReTEVRUDEbDCI3TBcMXTQLKEcRW0I3GC5eAB9yDV59ZwYrDyYFRhF3BlVVMg0mXydVTBE2HyQHHyAlBmZIEjhHTmVUHhZhBWsSKlxYIwcFCCQgQGhEdiYrJkRdEkJ8GC1RCEAdXFclBDYvG2RZEjc/MlQdbGsCWSdcBlIbG1dKTSMxDCcQWywjb0cYRiQtWSxDSn0XIwcFCCQgQnlERHhtLlcREEI1UC5eREAMEQUDLiopACUQfyIkKUVQDwwkSmMZRFYWFFcSAyFoaDlNOAAiKlNQEjB7eS9UMFwfFxsSRWcKDRYBUSwkKxMdRhlLMR9VHEdYTVdVIypkMCEHXSohZR0RIgcnWT5cEBNFUBEWATYhTk5tcSIhK1NQBQlhBWtWEV0bBB4YA20yS2QiXiIqNB9/CTAkWyRZCBNFUAFMTSwiQjJERisoKRFCEgMzTAhfCVEZBDoWBCswAy0KVzFlbhFUCAZhXSVUSDkFWX00AigmAzA2CAIpI2VeAQUtXWMSMEERFxASHycrFmZIEjhHTmVUHhZhBWsSMEERFxASHycrFmZIEgcoIVBEChZhBWtWBV8LFVtXPyw3CT1ED2M5NURUSmhIbCRfCEcRAFdKTWcCCzYBQWM5L1QRAQMsXWxDREAQHxgDTSwqEjEQEjQlIl8RHw00SmtTFlwLAx8WBDdkCzdEXS1tJl8RAwwkVTIeRh9yeTQWASkmAycPEn5tIURfBRYoVyUYEhpYNhsWCjZqNjYNVSQoNVNeEkJ8GD0LRFoeUAFXGS0hDGQXRiI/M2VDDwUmXTlSC0dQWVcSAyFkByoAHkkwbjtyCQ8jWT9iXnIcFCQbBCEhEGxGZjEkIHVUCgM4GmcQHzlxJBIPGWV5QmYwQCoqIFRDRiYkVCpJRh9YNBIRDDAoFmRZEnNjdwIdRi8oVmsNRANUUDoWFWV5QnRKB29tFV5ECAYoViwQWRNKXFckGCMiCzxED2NvZ0ITSmhIeypcCFEZExxXUGUiFyoHRioiKRlHT0IHVCpXFx0sAh4QCiA2JiEIUzptehFHRgcvXGc6GRpyMxgaDyQwMH4lVicZKFZWCgdpGgNZEFEXCDIPHWdoQj9uOxcoP0URW0JjcCJEBlwAUDIPHSQqBiEWEG9tA1RXBxctTGsNRFUZHAQSQWUWCzcPS2NwZ0VDEwdtMkJzBV8UEhYUBmV5QiIRXCA5Ll5fThRoGA1cBVQLXj8eGScrGgEcQiIjI1RDRl9hTnAQDVVYBlcDBSAqQjcQUzE5D1hFBA05fTNABV0cFQVfRGUhDCBEVy0paztMT2gCVyZSBUcqSjYTCRYoCyABQGtvD1hFBA05ayJKARFUUAx9ZBEhGjBED2NvD1hFBA05GBhZHlZaXFczCCMlFygQEn5tfx0RKwsvGHYQUB9YPRYPTXhkUHFIEhEiMl9VDwwmGHYQVB9yeTQWASkmAycPEn5tIURfBRYoVyUYEhpYNhsWCjZqKi0QUCw1FFhLA0J8GD0QAV0cXH0KRE9OT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQE9pT2QyexAYBn1iRjYAekEdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sMidfB1IUUCEeHglkX2QwUyE+aWdYFRcgVDgKJVccPBIRGQI2DTEUUCw1bxN0NTJjFGsSAUodUl59ASonAyhEZCo+FREMRjYgWjgeMloLBRYbHn8FBiA2WyQlM3ZDCRcxWiRITBEvHwUbCWdoQmYJUzNvbjs7MAsydHFxAFcsHxAQASBsQAEXQgYjJlNdAwZjFGtLRGcdCANXUGVmJyoFUC8oZ3RiNkBtGA9VAlINHANXUGUiAygXV29HTnJQCg4jWShbRA5YFgIZDjEtDSpMRGptAV1QARFvfThAIV0ZEhsSCWV5QjJEVy0pZ0wYbDQoSwcKJVccJBgQCikhSmYhQTMPKEkTSkJhGGsQHxMsFQ8DTXhkQAYLSiY+ZR0RRkJhGA9VAlINHANXUGUwEDEBHmNtBFBdCgAgWyAQWRMeBRkUGSwrDGwSG2MLK1BWFUwESztyC0tYTVcBTSAqBmQZG0kbLkJ9XCMlXB9fA1QUFV9VKDY0LCUJV2FhZxERRhlhbC5IEBNFUFU5DCghEWZIEmNtZxF1AwQgTSdERA5YBAUCCGlkQgcFXi8vJlJaRl9hXj5eB0cRHxlfG2xkJCgFVTBjAkJBKAMsXWsNREVYFRkTTThtaBINQQ93BlVVMg0mXydVTBE9Awc/CCQoFixGHmNtPBFlAxo1GHYQRnsdERsDBWdoQmREEgcoIVBEChZhBWtEFkYdXFdXLiQoDiYFUShtehFXEwwiTCJfChsOWVcxASQjEWohQTMFIlBdEgphBWtGRFYWFFcKRE8SCzcoCAIpI2VeAQUtXWMSIUAINB4EGSQqASFGHjhtE1RJEkJ8GGl0DUAMERkUCGdoQmQgVyUsMl1FRl9hTDlFAR9YUDQWASkmAycPEn5tIURfBRYoVyUYEhpYNhsWCjZqJzcUdio+M1BfBQdhBWtGRFYWFFcKRE8SCzcoCAIpI2VeAQUtXWMSIUAIJAUWDiA2QGhEEjhtE1RJEkJ8GGlkFlIbFQUET2lkQmQgVyUsMl1FRl9hXipcF1ZUUDQWASkmAycPEn5tIURfBRYoVyUYEhpYNhsWCjZqJzcUZjEsJFRDRl9hTmtVCldYDV59Oyw3Ln4lVicZKFZWCgdpGg5DFGcdERpVQWVkQmQfEhcoP0URW0JjbC5RCRM7GBIUBmdoQgABVCI4K0URW0I1Sj5VSBNYMxYbASclAS9ED2MrMl9SEgsuVmNGTRM+HBYQHmsBETQwVyIgBFlUBQlhBWtGRFYWFFcKRE8SCzcoCAIpI2JdDwYkSmMSIUAIPRYPKSw3FmZIEjhtE1RJEkJ8GGl9BUtYNB4EGSQqASFGHmMJIldQEw41GHYQVQNIQFtXICwqQnlEA3N9axF8BxphBWsDVANIXFclAjAqBi0KVWNwZwEdRjE0Xi1ZHBNFUFVXAGdoaE0nUy8hJVBSDUJ8GC1FClAMGRgZRTNtQgIIUyQ+aXRCFi8gQA9ZF0dYTVcBTSAqBmQZG0kbLkJ9XCMlXAdRBlYUWFUyPhVkISsIXTFvbgtwAgYCVydfFmMRExwSH21mJzcUcSwhKEMTSkI6MkJ0AVUZBRsDTXhkISsIXTF+aVdDCQ8TfwkYVB9YQkZHQWV2UH1NHmMZLkVdA0J8GGl1N2NYMxgbAjdmTk5tcSIhK1NQBQlhBWtWEV0bBB4YA20yS2QiXiIqNB90FRICVydfFhNFUAFXCCsgTk4ZG0lHEVhCNFgAXC9kC1QfHBJfTwMxDigGQCoqL0UTSkI6GB9VHEdYTVdVKzAoDiYWWyQlMxMdRiYkXipFCEdYTVcRDCk3B2huOwAsK11TBwEqGHYQAkYWEwMeAitsFG1EdC8sIEIfIBctVClCDVQQBFdKTTN/Qi0CEjVtM1lUCEIyTCpCEGMUEQ4SHwglCyoQUyojIkMZT0IkVDhVRH8RFx8DBCsjTAMIXSEsK2JZBwYuTzgQWRMMAgISTSAqBmQBXCdtOhg7MAsyanFxAFcsHxAQASBsQAcRQTciKndeEEBtGDAQMFYABFdKTWcHFzcQXS5tAX5nRE5hfC5WBUYUBFdKTSMlDjcBHklEBFBdCgAgWyAQWRMeBRkUGSwrDGwSG2MLK1BWFUwCTThEC14+HwFXUGUyWWQNVGM7Z0VZAwxhSz9RFkcoHBYOCDcJAy0KRiIkKVRDTkthXSVURFYWFFcKRE8SCzc2CAIpI2JdDwYkSmMSIlwOJhYbGCBmTmQfEhcoP0URW0JjfgRmRh9YNBIRDDAoFmRZEnR9axF8DwxhBWsEVB9YPRYPTXhkU3ZUHmMfKERfAgsvX2sNRANUen40DCkoACUHWWNwZ1dECAE1USReTEVRUDEbDCI3TAILRBUsK0RURl9hTmtVCldYDV59Z2hpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVp9QGhkLwsydw4ICWURMiMDMmYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09LVCRTBV9YPRgBCAlkX2QwUyE+aXxeEAcsXSVEXnIcFDsSCzEDECsRQiEiPxkTNRIkXS8SSBNaERQDBDMtFj1GG0khKFJQCkIMVz1VNhNFUCMWDzZqLysSVy4oKUULJwYlaiJXDEc/AhgCHScrGmxGcyY/LlBdRE5hGiZfElZVFB4WCioqAyhJAGFkTTt8CRQkdHFxAFcsHxAQASBsQBMFXigeN1RUAi0vGmcQHxMsFQ8DTXhkQBMFXigeN1RUAkBtGA9VAlINHANXUGUiAygXV29HTnJQCg4jWShbRA5YFgIZDjEtDSpMRGptAV1QARFvbypcD2AIFRITIitkX2QSCWMkIRFHRhYpXSUQF0cZAgM6AjMhDyEKRg4sLl9FBwsvXTkYTRMdHAQSTSkrASUIEitwIFRFLhcsEGIQDVVYGFcDBSAqQixKZSIhLGJBAwclBXoGRFYWFFcSAyFkByoAEj5kTXxeEAcNAgpUAGAUGRMSH21mNSUIWRA9IlRVRE5hQ2tkAUsMUEpXTxY0ByEAEG9tA1RXBxctTGsNRAJOXFc6BCtkX2RVBG9tClBJRl9hCXkASBMqHwIZCSwqBWRZEnNhTThyBw4tWipTDxNFUBECAyYwCysKGjVkZ3ddBwUyFhxRCFgrABISCWV5QjJEVy0pZ0wYbC8uTi58XnIcFCMYCiIoB2xGeDYgN35fRE5hQ2tkAUsMUEpXTw8xDzREYiw6IkMTSkIFXS1REV8MUEpXCyQoESFIOEoOJl1dBAMiU2sNRFUNHhQDBCoqSjJNEgUhJlZCSCg0VTt/ChNFUAFMTSwiQjJERisoKRFCEgMzTAZfElYVFRkDICQtDDAFWy0oNRkYRgcvXGtVCldYDV59ICoyBwhecycpFF1YAgczEGl6EV4IIBgACDdmTmQfEhcoP0URW0JjaCRHAUFaXFczCCMlFygQEn5tcgEdRi8oVmsNRAZIXFc6DD1kX2RWB3NhZ2NeEwwlUSVXRA5YQFt9ZAYlDigGUyAmZwwRABcvWz9ZC11QBl5XKyklBTdKeDYgN2FeEQczGHYQEhMdHhNXEGxOaAkLRCYffXBVAjYuXyxcARtaORkRJzApEmZIEjhtE1RJEkJ8GGl5ClURHh4DCGUOFykUEG9tA1RXBxctTGsNRFUZHAQSQU9NISUIXiEsJFoRW0InTSVTEFoXHl8BRGUCDiUDQW0EKVd7Ew8xGHYQEhMdHhNXEGxOLysSVxF3BlVVMg0mXydVTBE+HA44A2doQj9EZiY1MxEMRkAHVDIQTGQ5IzNYPjUlASFLYSskIUUYRE5hfC5WBUYUBFdKTSMlDjcBHmMfLkJaH0J8GD9CEVZUen40DCkoACUHWWNwZ1dECAE1USReTEVRUDEbDCI3TAIISwwjZwwREFlhUS0QEhMMGBIZTTYwAzYQdC80bxgRAwwlGC5eABMFWX06AjMhMH4lViceK1hVAxBpGg1cHWAIFRITT2lkGWQwVzs5ZwwRRCQtQWtjFFYdFFVbTQEhBCURXjdtehEHVk5hdSJeRA5YQkdbTQglGmRZEnF4dx0RNA00Vi9ZClRYTVdHQU9NISUIXiEsJFoRW0InTSVTEFoXHl8BRGUCDiUDQW0LK0hiFgckXGsNREVYFRkTTThtaAkLRCYffXBVAjYuXyxcARtaPhgUASw0LSpGHmM2Z2VUHhZhBWsSKlwbHB4HT2lkJiECUzYhMxEMRgQgVDhVSBMqGQQcFGV5QjAWRyZhTThyBw4tWipTDxNFUBECAyYwCysKGjVkZ3ddBwUyFgVfB18RADgZTXhkFH9EWyVtMRFFDgcvGDhEBUEMPhgUASw0Sm1EVy0pZ1RfAkI8EUE6SR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFUEdSRMoPDYuKBdkNgUmOG5gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2luXiwuJl0RNg4gQQcQWRMsERUEQxUoAz0BQHkMI1V9AwQ1fzlfEUMaHw9fTxAwCygNRjpvaxETERAkVihYRhpyeicbDDwIWAUAVhciIFZdA0pjeSVEDXIeG1VbTT5kNiEcRmNwZxNwCBYoGAp2LxFUUDMSCyQxDjBED2MrJl1CA05LMQhRCF8aERQcTXhkBDEKUTckKF8ZEEthfidRA0BWMRkDBAQiCWRZEjVtIl9VRh9oMhtcBUo0SjYTCQcxFjALXGs2Z2VUHhZhBWsSNlYLABYAA2UKDTNGHmMZKF5dEgsxGHYQRncNFRsEV2UtDDcQUy05Z0NUFRIgTyUSSBM+BRkUTXhkECEXQiI6KX9eEUI8EUFgCFIBPE02CSEGFzAQXS1lPBFlAxo1GHYQRmEdAxIDTQYsAzYFUTcoNRMdRiQ0VigQWRMeBRkUGSwrDGxNOEohKFJQCkIpGHYQA1YMOAIaRWx/Qi0CEittM1lUCEIxWypcCBseBRkUGSwrDGxNEitjD1RQChYpGHYQVBMdHhNeTSAqBk4BXCdtOhg7bE9sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahw7S09hfwp9IRMsMTV9QGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXX0bAiYlDmQjUy4oCxEMRjYgWjgeI1IVFU02CSEIByIQdTEiMkFTCRppGgZREFAQHRYcBCsjQGhEEDA6KENVFUBoMidfB1IUUDAWACAWQnlEZiIvNB92Bw8kAgpUAGERFx8DKjcrFzQGXTtlZWNUEQMzXDgSSBNaABYUBiQjB2ZNOEkKJlxUKlgAXC9yEUcMHxlfFmUQBzwQEn5tZXteDwxhaT5VEVZaXFcxGCsnQnlEWCwkKWBEAxckGDYZbnQZHRI7VwQgBhALVSQhIhkTJxc1VxpFAUYdUltXFmUQBzwQEn5tZXBEEg1haT5VEVZaXFczCCMlFygQEn5tIVBdFQdtMkJzBV8UEhYUBmV5QiIRXCA5Ll5fThRoGA1cBVQLXjYCGSoVFyERV2NwZ0cKRgsnGD0QEFsdHlcEGSQ2FgURRiwcMlREA0poGC5eABMdHhNXEGxOaAMFXyYffXBVAisvSD5ETBE7HxMSLyo8QGhESWMZIklFRl9hGhlVAFYdHVc0AiEhQGhEdiYrJkRdEkJ8GGkSSBMoHBYUCC0rDiABQGNwZxNSCQYkFmUeRh9YNh4ZBDYsByBED2M5NURUSmhIeypcCFEZExxXUGUiFyoHRioiKRlHT0IzXS9VAV47HxMSRTNtQiEKVmMwbjs7S09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gajscS0ISfR9kLX0/I1cjLAdOT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQE8oDScFXmMAIl9ERl9hbCpSFx0rFQMDBCsjEX4lVicBIldFIRAuTTtSC0tQUj4ZGSA2BCUHV2FhZxNcCQwoTCRCRhpyejoSAzB+IyAAZiwqIF1UTkASUCRHJ0YLBBgaLjA2ESsWEG9tPBFlAxo1GHYQRnANAwMYAGUHFzYXXTFvaxF1AwQgTSdERA5YBAUCCGlOawcFXi8vJlJaRl9hXj5eB0cRHxlfG2xkLi0GQCI/Ph9iDg02ez5DEFwVMwIFHio2QnlERGMoKVURG0tLdS5eEQk5FBMzHyo0BisTXGtvCV5FDwQSUS9VRh9YC1cjCD0wQnlEEA0iM1hXH0ISUS9VRh9YJhYbGCA3QnlESWNvC1RXEkBtGGliDVQQBFVXEGlkJiECUzYhMxEMRkATUSxYEBFUen40DCkoACUHWWNwZ1dECAE1USReTEVRUDseDzclED1eYSY5CV5FDwQ4ayJUARsOWVcSAyFkH21ufyYjMgtwAgYFSiRAAFwPHl9VKRUNQGhESWMZIklFRl9hGh55RGAbERsST2lkNCUIRyY+ZwwRHUJjD34VRh9YUkZHXWBmTmRGA3F4YhMdRkBwDXsVRhMFXFczCCMlFygQEn5tZQABVkdjFEE5J1IUHBUWDi5kX2QCRy0uM1heCEo3EWt8DVEKEQUOVxYhFgA0exAuJl1UThYuVj5dBlYKWF8BVyI3FyZMEGZoZR0RREBoEWIZRFYWFFcKRE8JByoRCAIpI3VYEAslXTkYTTk1FRkCVwQgBggFUCYhbxN8Aww0GABVHVERHhNVRH8FBiAvVzodLlJaAxBpGgZVCkYzFQ4VBCsgQGhESWMJIldQEw41GHYQRmERFx8DPi0tBDBGHmMDKGR4Rl9hTDlFAR9YJBIPGWV5QmYwXSQqK1QRKwcvTWkQGRpyPRIZGH8FBiAmRzc5KF8ZHUIVXTNERA5YUiIZASolBmZIEhEkNFpIRl9hTDlFAR9YNgIZDmV5QiIRXCA5Ll5fTkthdCJSFlIKCU0iAykrAyBMG2MoKVURG0tLMgdZBkEZAg5ZOSojBSgBeSY0JVhfAkJ8GARAEFoXHgRZICAqFw8BSyEkKVU7bE9sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahw7S09hexl1IHosI1cjLAdOT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQE8oDScFXmMONVRVRl9hbCpSFx07AhITBDE3WAUAVg8oIUV2FA00SClfHBtaORkRAjcpAzANXS1vaxETDwwnV2kZbnAKFRNNLCEgLiUGVy9lZWN4MCMNa2vS5KdYKUUcTRYnEC0URmMPJlJaVCAgWyASTTk7AhITVwQgBggFUCYhb0oRMgc5TGsNRBE9BhIFFGUiByUQRzEoZ0ZDBxIyGD9YARMfERoSSjZkDTMKEiAhLlRfEkItWTJVFhMXAlcRBDchEWQFEjEoJl0RFAcsVz9VSBMIExYbAWgjFyUWViYpaRMdRiYuXThnFlIIUEpXGTcxB2QZG0kONVRVXCMlXAdRBlYUWFUhCDc3CysKCGN8aQEfVkBoMkEdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sMmYdRHI8NDg5PmVsFiwBXyZtbBFSCQwnUSwQF1IOFVgbAiQgTSURRiwhKFBVT2hsFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcbDYpXSZVKVIWERASH38XBzAoWyE/JkNITi4oWjlRFkpReiQWGyAJAyoFVSY/fWJUEi4oWjlRFkpQPB4VHyQ2G21uYSI7InxQCAMmXTkKLVQWHwUSOS0hDyE3Vzc5Ll9WFUpoMhhRElY1ERkWCiA2WBcBRgoqKV5DAysvXC5IAUBQC1dVICAqFw8BSyEkKVUTRh9oMh9YAV4dPRYZDCIhEH43VzcLKF1VAxBpGhlZElIUAy5FBmdtaBcFRCYAJl9QAQczAhhVEHUXHBMSH21mMC0SUy8+HgNaSQEuVi1ZA0BaWX0kDDMhLyUKUyQoNQtzEwstXAhfClURFyQSDjEtDSpMZiIvNB9yCQwnUSxDTTksGBIaCAglDCUDVzF3BkFBChsVVx9RBhssERUEQxYhFjANXCQ+bjtiBxQkdSpeBVQdAk07AiQgIzEQXS8iJlVyCQwnUSwYTTlyXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSTlVXVc0IQAFLGQxfA8CBnU7S09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gahwcS09sFWYdSR5VXVpaQGhpT2lJH25gajt9DwAzWTlJXnwWJRkbAiQgSiIRXCA5Ll5fTktLMWYdREAMHwdXDCkoQjAMQCYsI0I7bwQuSmtbRFoWUAcWBDc3ShAMQCYsI0IYRgYuGB9YFlYZFAQsBhhkX2QKWy9tIl9VbGsHVCpXFx0rGRsSAzEFCylED2MrJl1CA1lhfidRA0BWPhgkHTchAyBED2MrJl1CA1lhfidRA0BWPhglCCYrCyhED2MrJl1CA2hIfidRA0BWJAUeCiIhECYLRmNwZ1dQChEkA2t2CFIfA1k/BDEmDTwhSjMsKVVUFEJ8GC1RCEAden4xASQjEWohQTMIKVBTCgclGHYQAlIUAxJMTQMoAyMXHAUhPn5fRl9hXipcF1ZDUDEbDCI3TAoLUS8kN35fRl9hXipcF1ZyeVpaTTchETALQCZtL15eDRFhF2tCAUARChITTTUlEDAXOEorKEMROU5hXiUQDV1YGQcWBDc3ShYBQTciNVRCT0IlV2tAB1IUHF8RA2xkByoAOEorKEMRFgMzTGcQF1oCFVceA2U0Ay0WQWsoP0FQCAYkXBtRFkcLWVcTAmU0ASUIXmsrMl9SEgsuVmMZRFoeUAcWHzFkAyoAEjMsNUUfNgMzXSVEREcQFRlXHSQ2Fmo3WzkoZwwRFQs7XWtVCldYFRkTRGUhDCBuO25gZ1VDBxUoVixDbjobHBIWHwA3EmxNOEokIRF1FAM2USVXFx0nLxEYG2UwCiEKEjMuJl1dTgQ0VihEDVwWWF5XKTclFS0KVTBjGG5XCRR7ai5dC0UdWF5XCCsgS39EdjEsMFhfARFvZxRWC0VYTVcZBClkByoAOEpgahFSCQwvXShEDVwWA31+Cyo2QhtIEiBtLl8RDxIgUTlDTHAXHhkSDjEtDSoXG2MpKBFBBQMtVGNWEV0bBB4YA21tQidedio+JF5fCAciTGMZRFYWFF5XCCsgaE1JH2M/IkJFCRAkGChRCVYKEVgbBCIsFi0KVUlEN1JQCg5pXj5eB0cRHxlfRGUICyMMRiojIB92Cg0jWSdjDFIcHwAETXhkFjYRV2MoKVUYbAcvXGI6bn8REgUWHzx+LCsQWyU0b0oRMgs1VC4QWRNaIj4hLAkXQGhEdiY+JENYFhYoVyUQWRNaPBgWCSAgTGQ2WyQlM2JZDwQ1GD9fREcXFxAbCGtmTmQwWy4oZwwRU0I8EUE='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
