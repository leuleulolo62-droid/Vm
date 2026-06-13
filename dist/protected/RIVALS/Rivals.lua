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

local __k = '4BeaMIme0NQk0tsad9ZSr4uu'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-pv1OS96kbmmI
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, watermark = 'Y2k-pv1OS96kbmmI', neuterAC = true, antiSpy = { kick = true, halt = true } })
