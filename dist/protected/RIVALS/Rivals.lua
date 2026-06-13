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

local __k = 'mO1gGwHxVtRxfWnsNThwENtN'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
