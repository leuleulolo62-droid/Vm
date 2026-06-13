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

local __k = 'RxX8dDsUa4G4mU1Ri36Q6VKo'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true } })
