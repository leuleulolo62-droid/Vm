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
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
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

local __k = 'du9sHVeuecbKLvJVe9AxszYa'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, antiSpy = { kick = true, halt = true } })
