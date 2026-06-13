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

local __k = 'k2acC9NdRV2c44u9P57NjUYv'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
