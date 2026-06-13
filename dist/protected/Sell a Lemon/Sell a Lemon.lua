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

local __k = 'V080UPErFk1PRJ9qEQVQspql'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true } })
