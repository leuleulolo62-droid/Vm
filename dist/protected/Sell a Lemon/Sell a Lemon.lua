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

local __k = 'TWMsR6iAXtGkv5RnFjucDMuU'
local __p = 'eXptkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIfmpGVhUBCyoGVQJkARA4OzltOydUST14AnZFRj9/Q2ZKICpkd1UaNiQkFztXBxQRVG8yRF5yPSUYHBMwbTc0Nzx/MTNVAmhSWWpLVnIzAyNKT0MXKBk5dDZtPzdbBi94W2c9E1s2HCNKEQY3bRY8ICUiHSEWFWEIGCYIE3w2TnFTR1V8fkxmZGB/R2YCY2x1VKX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/kxgHAVkIxohdDAsHjcMIDIUGyYPE1F6R2YeHQYqbRI0OTJjPz1XDSQ8ThAKH0F6R2YPGwdOR1h4dLXZ/7Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfBxF1gXnLU/cN4VAgpJXwWJwckVTYNbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVW3wNVHXn8Wi9XMltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkcauYy03FyYHVkc3HilKSENmJQEhJCR3XH1ECDZ2Ey4fHkAwGzUPBwArIwEwOiNjED1bRhhqHxQIBFwiGgQLFgh2DxQ2P3gCESFfDSg5GhICWVgzByhFV2lOIRo2NTttFSdYCjUxGylLGlozChMjXRY2IVxfdHdtUz5ZCiA0VDUKARVvTiELGAZ+BQEhJBAoB3pDGy1xfmdLVhU7CGYeDBMhZQc0I35tTm8WSyctGiQfH1o8TGYeHQYqR1V1dHdtU3IWBS47FStLGV5+TjQPBhYoOVVodCcuEj5aQSctGiQfH1o8Rm9KBwYwOAc7dCUsBHpRCCw9WGceBFl7TiMEEUpObVV1dHdtU3JfD2E3H2cKGFFyGj8aEEs2KAYgOCNkUywLSWM+ASkIAlw9AGRKAQshI1UnMSM4ATwWGyQrASsfVlA8CkxKVUNkbVV1dD4rUz1dSSA2EGcfD0U3RjQPBhYoOVx1aWptUTRDByIsHSgFVBUmBiMEf0NkbVV1dHdtU3IWSWx1VBMDExUgCzUfGRdkJAEmMTsrUz9fDiksVCUOVlRyGTQLBRMhP1l1ITk6ATNGSSgsfmdLVhVyTmZKVUNkbRk6NzYhUzFDGzM9GjNLSxUgCzUfGRdObVV1dHdtU3IWSWF4EigZVmpyU2ZbWUNxbRE6XndtU3IWSWF4VGdLVhVyTmYDE0MwNAUwfDQ4ASBTBzVxVDlWVhc0GygJAQorI1d1ID8oHXJEDDUtBilLFUAgHCMEAUMhIxFfdHdtU3IWSWF4VGdLVhVyTioFFgIobRo+ZnttHTdOHRM9BzIHAhVvTjYJFA8oZRMgOjQ5Gj1YQWh4BiIfA0c8TiUfBxEhIwF9MzYgFn4WHDM0XWcOGFF7ZGZKVUNkbVV1dHdtU3IWSWExEmcFGUFyAS1YVRcsKBt1NiUoEjkWDC88fmdLVhVyTmZKVUNkbVV1dHcuBiBEDC8sVHpLGFAqGhQPBhYoOX91dHdtU3IWSWF4VGcOGFFYTmZKVUNkbVV1dHdtGjQWHTgoEW8IA0cgCygeXEM6cFV3MiIjECZfBi96VDMDE1tyHCMeABEqbRYgJiUoHSYWDC88fmdLVhVyTmZKEA0gR1V1dHdtU3IWRGx4MiYHGlczDS1QVRc2NFU0J3c+ByBfByZSVGdLVhVyTmYGGgAlIVUzOnttLHILSS03FSMYAkc7ACFCAQw3OQc8OjBlATNBQGhSVGdLVhVyTmYDE0MiI1UhPDIjUyBTHTQqGmcNGB01DysPXEMhIxFfdHdtUzdaGiRSVGdLVhVyTmYYEBcxPxt1ODgsFyFCGyg2E28ZF0J7Rm9gVUNkbRA7MF1tU3IWGyQsATUFVls7AkwPGwdORxk6NzYhUx5fCzM5Bj5LVhVyTmZXVQ8rLBEAHX8/FiJZSW92VGUnH1cgDzQTWw8xLFd8XjsiEDNaSRUwESoOO1Q8DyEPB0N5bRk6NTMYOnpEDDE3VGlFVhczCiIFGxBrGR0wOTIAEjxXDiQqWiseFxd7ZCoFFgIobSY0IjIAEjxXDiQqVGdWVlk9DyI/PEs2KAU6dHljU3BXDSU3GjREJVQkCwsLGwIjKAd7OCIsUXs8Yy03FyYHVnoiGi8FGxBkbVV1dHdwUx5fCzM5Bj5FOUUmBykEBmkoIhY0OHcZHDVRBSQrVGdLVhVyU2YmHAE2LAcsegMiFDVaDDJSfmpGVtfG4qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/5j9/Q2aI4eFkbSYQBgEEMBdlSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGeJ4rdYQ2tKl/fQr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLyfw8rLhQ5dAchEitTGzJ4VGdLVhVyTmZKVV5kKhQ4MW0KFiZlDDMuHSQOXhcCAicTEBE3b1xfODguEj4WOzQ2JyIZAFwxC2ZKVUNkbVV1aXcqEj9TUwY9ABQOBEM7DSNCVzExIyYwJiEkEDcUQEs0GyQKGhUACzYGHAAlORAxByMiATNRDGFlVCAKG1BoKSMeJgY2Oxw2MX9vITdGBSg7FTMOEmYmATQLEgZmZH85OzQsH3JhBjMzBzcKFVByTmZKVUNkbVVodDAsHjcMLiQsJyIZAFwxC25IIgw2JgYlNTQoUXs8BS47FStLI0Y3HA8EBRYwHhAnIj4uFnIWVGE/FSoOTHI3GhUPBxUtLhB9dgI+FiB/BzEtABQOBEM7DSNIXGlOIRo2NTttPz1VCC0IGCYSE0dyU2Y6GQI9KAcmehsiEDNaOS05DSIZfFk9DScGVSAlIBAnNXdtU3IWSXx4IygZHUYiDyUPWyAxPwcwOiMOEj9TGyBSfmpGVtfG4qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/5j9/Q2aI4eFkbTYaGhEENHIWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGeJ4rdYQ2tKl/fQr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLyfw8rLhQ5dBQrFHILSTpSVGdLVnQnGikpGQonJjkwOTgjU28WDyA0ByJHfBVyTmYrABcrGAUyJjYpFnIWSWFlVCEKGkY3QkxKVUNkDAAhOwI9FCBXDSQMFTUME0FyU2ZINA8ob1lfdHdtUxNDHS4IHCgFE3o0CCMYVV5kKxQ5JzJheXIWSWEZATMENVQhBgIYGhNkbVVodDEsHyFTRUt4VGdLN0AmARQPFwo2OR11dHdtTnJQCC0rEWthVhVyTgcfAQwBOxo5IjJtU3IWSXx4EiYHBVB+ZGZKVUMFOAE6FSQuFjxSSWF4VGdWVlMzAjUPWWlkbVV1FSI5HAJZHiQqOCIdE1lyU2YMFA83KFlfdHdtUxNDHS4NBCAZF1E3PikdEBFkcFUzNTs+Fn48SWF4VAYeAloGBysPNgI3JVV1dGptFTNaGiR0fmdLVhUTGzIFMAI2IxAnFjgiACYWVGE+FSsYExlYTmZKVSIxORoROyIvHzd5Dyc0HSkOVghyCCcGBgZoR1V1dHcMBiZZJCg2HSAKG1AADyUPVV5kKxQ5JzJheXIWSWEZATMEO1w8ByELGAYQPxQxMXdwUzRXBTI9WE1LVhVyLzMeGiAsLBsyMRssETdaSXx4EiYHBVB+ZGZKVUMFOAE6Fz8sHTVTKi40GzUYVghyCCcGBgZoR1V1dHcIIAJmBSAhETUYVhVyTmZXVQUlIQYweF1tU3IWLBIINyYYHnEgATZKVUNkcFUzNTs+Fn48SWF4VAI4JmErDSkFG0NkbVV1dGptFTNaGiR0fmdLVhUFDyoBJhMhKBF1dHdtU3ILSXBuWE1LVhVyJDMHBTMrOhAndHdtU3IWVGFtRGthVhVyTgEYFBUtOQx1dHdtU3IWSXx4RX5dWAd+ZGZKVUMCIQwQOjYvHzdSSWF4VGdWVlMzAjUPWWlkbVV1Ejs0ICJTDCV4VGdLVhVyU2ZfRU9ObVV1dBkiED5fGWF4VGdLVhVyTntKEwIoPhB5XndtU3J/BycSASobVhVyTmZKVUN5bRM0OCQoX1gWSWF4ITcMBFQ2CwIPGQI9bVV1aXd9XWcaY2F4VGc7BFAhGi8NECchIRQsdHdwU2MGRUt4VGdLNFo9HTIuEA8lNFV1dHdtTnIFWW1SVGdLVnQ8Gi8rMyhkbVV1dHdtU28WDyA0ByJHfEhYZGtHVYHQwZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+9YHQzZfB1LXZ87Ci6aPM9KX/9tfG7qT+5WlpYFW3wNVtUwZPCi43GmcjE1kiCzQZVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmaI4eFOYFh1tsPZkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HNXjsiEDNaSSctGiQfH1o8TiEPATc9Lho6On9keXIWSWE+GzVLKRlyASQAVQoqbRwlNT4/AHphBjMzBzcKFVBoKSMeNgstIREnMTllWnsWDS5SVGdLVhVyTmYDE0NsIhc/bh4+MnoULy40ECIZVBxyATRKGgEudzwmFX9vPj1SDC16XWcEBBU9DCxQPBAFZVcWOzkrGjVDGyAsHSgFVBx7TicEEUMrLx97GjYgFmhQAC88XGU/D1Y9AShIXEMwJRA7XndtU3IWSWF4VGdLVlk9DScGVQwzIxAndGptHDBcUwcxGiMtH0chGgUCHA8gZVcaIzkoAXAfY2F4VGdLVhVyTmZKVQoibRoiOjI/UzNYDWE3AykOBA8bHQdCVywmJxA2IAEsHydTS2h4FSkPVlolACMYWzUlIQAwdGpwUx5ZCiA0JCsKD1AgTjICEA1ObVV1dHdtU3IWSWF4VGdLVkc3GjMYG0MrLx9fdHdtU3IWSWF4VGdLE1s2ZGZKVUNkbVV1MTkpeXIWSWE9GiNhVhVyTjQPARY2I1U7PTtHFjxSY0s0GyQKGhU0GygJAQorI1UyMSMMHz5jGSYqFSMOJFA/ATIPBkswNBY6OzlkeXIWSWE0GyQKGhUgCzUfGRdkcFUuKV1tU3IWACd4GigfVkErDSkFG0MwJRA7dCUoBydEB2EqETQeGkFyCygOf0NkbVU5OzQsH3JGHDM7HGdWVkErDSkFG1kCJBsxEj4/ACZ1ASg0EG9JJkAgDS4LBgY3b1xfdHdtUztQSS83AGcbA0cxBmYeHQYqbQcwICI/HXJEDDItGDNLE1s2ZGZKVUMiIgd1C3ttHDBcSSg2VC4bF1wgHW4aABEnJU8SMSMJFiFVDC88FSkfBR17R2YOGmlkbVV1dHdtUztQSS46Hn0iBXR6TBQPGAwwKDMgOjQ5Gj1YS2h4FSkPVlowBGgkFA4hbUhodHUYAzVECCU9VmcfHlA8ZGZKVUNkbVV1dHdtUyZXCy09Wi4FBVAgGm4YEBAxIQF5dDgvGXs8SWF4VGdLVhU3ACJgVUNkbRA7MF1tU3IWGyQsATUFVkc3HTMGAWkhIxFfXjsiEDNaSSctGiQfH1o8TiEPATY0Kgc0MDICAyZfBi8rXDMSFVo9AG9gVUNkbRk6NzYhUz1GHTJ4SWcQVHQ+AmQXf0NkbVU5OzQsH3JEDCw3ACIYVghyCSMeNA8oGAUyJjYpFgBTBC4sETRDAkwxASkEXGlkbVV1Mjg/Uw0aSTM9GWcCGBU7HicDBxBsPxA4OyMoAHsWDS5SVGdLVhVyTmYGGgAlIVUlNSUoHSZ4CCw9VHpLBFA/QBYLBwYqOVU0OjNtATdbRxE5BiIFAhscDysPVQw2bVcAOjwjHCVYS0t4VGdLVhVyTi8MVQ0rOVUhNTUhFnxQAC88XCgbAkZ+TjYLBwYqOTs0OTJkUyZeDC9SVGdLVhVyTmZKVUNkORQ3ODJjGjxFDDMsXCgbAkZ+TjYLBwYqOTs0OTJkeXIWSWF4VGdLE1s2ZGZKVUMhIxFfdHdtUyBTHTQqGmcEBkEhZCMEEWlOIRo2NTttFSdYCjUxGylLA0U1HCcOEDclPxIwIH85CjFZBi90VDMKBFI3Gm9gVUNkbRwzdDkiB3JCECI3GylLAl03AGYYEBcxPxt1MTkpeXIWSWE0GyQKGhUiGzQJHUN5bQEsNzgiHWhwAC88Mi4ZBUERBi8GEUtmHQAnNz8sADdFS2hSVGdLVlw0TigFAUM0OAc2PHc5GzdYSTM9ADIZGBU3ACJgVUNkbRwzdCMsATVTHWFlSWdJN1k+TGYeHQYqR1V1dHdtU3IWDy4qVBhHVlowBGYDG0MtPRQ8JiRlAydECiliMyIfMlAhDSMEEQIqOQZ9fX5tFz08SWF4VGdLVhVyTmZKHAVkIhc/bh4+MnoUOyQ1GzMOMEA8DTIDGg1mZFU0OjNtHDBcRw85GSJLSwhyTBMaEhElKRB3dCMlFjw8SWF4VGdLVhVyTmZKVUNkbQU2NTshWzRDByIsHSgFXhxyASQATyoqOxo+MQQoASRTG2lpXWcOGFF7ZGZKVUNkbVV1dHdtUzdYDUt4VGdLVhVyTiMEEWlkbVV1MTs+FlgWSWF4VGdLVlk9DScGVQFkcFUlISUuG2hwAC88Mi4ZBUERBi8GEUswLAcyMSNkeXIWSWF4VGdLH1NyDGYeHQYqR1V1dHdtU3IWSWF4VCEEBBUNQmYFFwlkJBt1PScsGiBFQSNiMyIfMlAhDSMEEQIqOQZ9fX5tFz08SWF4VGdLVhVyTmZKVUNkbRwzdDgvGWh/GgBwVhUOG1omCwAfGwAwJBo7dn5tEjxSSS46HmklF1g3TntXVUERPRInNTMoUXJCASQ2fmdLVhVyTmZKVUNkbVV1dHdtU3IWGSI5GCtDEEA8DTIDGg1sZFU6Nj13OjxABio9JyIZAFAgRndDVQYqKVxfdHdtU3IWSWF4VGdLVhVyTiMEEWlkbVV1dHdtU3IWSWE9GiNhVhVyTmZKVUMhIxFfdHdtUzdYDUs9GiNhfFk9DScGVQUxIxYhPTgjUzVTHRUhFygEGGc3AykeEBBsOQw2OzgjWlgWSWF4HSFLGFomTjITFgwrI1UhPDIjUyBTHTQqGmcFH1lyCygOf0NkbVU5OzQsH3JEDCw3ACIYVghyGj8JGgwqdzM8OjMLGiBFHQIwHSsPXhcACysFAQY3b1xfdHdtUztQSS83AGcZE1g9GiMZVRcsKBt1JjI5BiBYSS8xGGcOGFFYTmZKVQ8rLhQ5dCUoACdaHWFlVDwWfBVyTmYMGhFkEll1JnckHXJfGSAxBjRDBFA/ATIPBlkDKAEWPD4hFyBTB2lxXWcPGT9yTmZKVUNkbQcwJyIhBwlERw85GSI2VghyHExKVUNkKBsxXndtU3JEDDUtBilLBFAhGyoefwYqKX9fODguEj4WDzQ2FzMCGVtyCSMeNgI3JV18XndtU3JaBiI5GGcDA1FyU2YmGgAlISU5NS4oAXxmBSAhETUsA1xoKC8EESUtPwYhFz8kHzYeSwkNMGVCfBVyTmYDE0MsOBF1ID8oHVgWSWF4VGdLVlk9DScGVQElIVVodD84F2hwAC88Mi4ZBUERBi8GEUtmDxQ5NTkuFnAaSTUqASJCfBVyTmZKVUNkJBN1NjYhUyZeDC9SVGdLVhVyTmZKVUNkIRo2NTttHjNfB2FlVCUKGg8UBygOMwo2PgEWPD4hF3oUJCAxGmVCfBVyTmZKVUNkbVV1dD4rUz9XAC94AC8OGD9yTmZKVUNkbVV1dHdtU3IWBS47FStLFVQhBmZXVQ4lJBtvEj4jFxRfGzIsNy8CGlF6TAULBgtmZH91dHdtU3IWSWF4VGdLVhVyByBKFgI3JVU0OjNtEDNFAXsRBwZDVGE3FjImFAEhIVd8dCMlFjw8SWF4VGdLVhVyTmZKVUNkbVV1dHchHDFXBWEsET8fVghyDScZHU0QKA0hbjA+BjAeSxp8WBpJWhVwTG9gVUNkbVV1dHdtU3IWSWF4VGdLVhUgCzIfBw1kORo7ITovFiAeHSQgAG5LGUdyXkxKVUNkbVV1dHdtU3IWSWF4ESkPfBVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVlA8CkxKVUNkKBsxXndtU3JEDDUtBilLRj83ACJgfw8rLhQ5dDE4HTFCAC42VCAOAnw8DSkHEEttR1V1dHchHDFXBWEwASNLSxUeASULGTMoLAwwJnkdHzNPDDMfAS5RMFw8CgADBxAwDh08ODNlURpjLWNxfmdLVhU7CGYCAAdkOR0wOl1tU3IWSWF4VCsEFVQ+TjUeFA0gbUh1PCIpSRRfByUeHTUYAnY6ByoOXUEIKBg6OgQ5EjxSS214ADUeExxYTmZKVUNkbVU8Mnc+BzNYDWEsHCIFfBVyTmZKVUNkbVV1dDsiEDNaSSQ5BikYVghyHTILGwd+Cxw7MBEkASFCKikxGCNDVHAzHCgZV09kOQcgMX5HU3IWSWF4VGdLVhVyByBKEAI2IwZ1NTkpUzdXGy8rTg4YNx1wOiMSAS8lLxA5dn5tBzpTB0t4VGdLVhVyTmZKVUNkbVV1JjI5BiBYSSQ5BikYWGE3FjJgVUNkbVV1dHdtU3IWDC88fmdLVhVyTmZKEA0gR1V1dHcoHTY8SWF4VDUOAkAgAGZIIA0vIxoiOnVHFjxSY0t1WWclGRU3FjIPBw0lIVUnMToiBzdFSS89ESMOEhV/TiMcEBE9OR08OjBtBiFTGmEsDSQEGVtyHCMHGhchPn9feXptkca6i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPNkca2i9XYltPrlKHSjNLql/fEr+HVtsPdeX8bSaPM9mdLI3xyPQM+IDNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dLXZ8VgbRGG64NOJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/cG64MeJ4rWw+saI4eOm2fW3wNev59LU/dlSGCgIF1lyOS8EEQwzbUh1GD4vATNEEHsbBiIKAlAFBygOGhRsNiE8IDsoTnBlDC00VCZLOlA/AShKCUMdfx53eBQoHSZTG3wsBjIOWnQnGik5HQwzcAEnITIwWlhaBiI5GGc/F1chTntKDmlkbVV1GTYkHXIWSWF4SWc8H1s2ATFQNAcgGRQ3fHUAEjtYS214VGdLVhczDTIDAwowNFd8eF1tU3IWPygrASYHVhVyU2Y9HA0gIgJvFTMpJzNUQWMOHTQeF1lwQmZKVUEhNBB3fXtHU3IWSQwxByRLVhVyTntKIgoqKRoibhYpFwZXC2l6OSgdE1g3ADJIWUNmIBojMXVkX1gWSWF4MzUKBl07DTVKSEMTJBsxOyB3MjZSPSA6XGUsBFQiBi8JBkFobVc8OTYqFnAfRUt4VGdLJUEzGjVKVUNkcFUCPTkpHCUMKCU8ICYJXhcBGiceBkFobVV1dHUpEiZXCyArEWVCWj9yTmZKJgYwOVV1dHdtTnJhAC88GzBRN1E2OicIXUEXKAEhPTkqAHAaSWMrETMfH1s1HWRDWWk5R385OzQsH3J7DC8tMzUEA0VyU2Y+FAE3YyYwICN3MjZSJSQ+AAAZGUAiDCkSXUEJKBsgdntvADdCHSg2EzRJXz8fCygfMhErOAVvFTMpMSdCHS42XDw/E00mU2Q/Gw8rLBF3eBE4HTELDzQ2FzMCGVt6R2YmHAE2LAcsbgIjHz1XDWlxVCIFEkh7ZAsPGxYDPxogJG0MFzZ6CCM9GG9JO1A8G2YIHA0gb1xvFTMpODdPOSg7HyIZXhcfCygfPgY9Lxw7MHVhCBZTDyAtGDNWVGc7CS4eJgstKwF3eBkiJhsLHTMtEWs/E00mU2QnEA0xbR4wLTUkHTYUFGhSOC4JBFQgF2g+GgQjIRAeMS4vGjxSSXx4OzcfH1o8HWgnEA0xBhAsNj4jF1g8PSk9GSImF1szCSMYTzAhOTk8NiUsASseJSg6BiYZDxxYPSccEC4lIxQyMSV3IDdCJSg6BiYZDx0eByQYFBE9ZH8GNSEoPjNYCCY9Bn0iEVs9HCM+HQYpKCYwICMkHTVFQWhSJyYdE3gzACcNEBF+HhAhHTAjHCBTIC88ET8OBR0pTAsPGxYPKAw3PTkpUS8fYxI5AiImF1szCSMYTzAhOTM6ODMoAXoUOiQ0GAsOG1o8QR9YHkFtRyY0IjIAEjxXDiQqTgUeH1k2LSkEEwojHhA2ID4iHXpiCCMrWhQOAkF7ZBICEA4hABQ7NTAoAWh3GTE0DRMEIlQwRhILFxBqHhAhIH5HeX8bSaPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5j9/Q2ZKOCINA1UBFRVHXn8Wi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7fFk9DScGVSIxORoXOy9tTnJiCCMrWgoKH1toLyIOOQYiOTInOyI9ET1OQWMZATMEVnMzHCtIWUEmIgF3fV1HMidCBgM3DH0qElEGASENGQZsbzQgIDgOHztVAg09GSgFVBkpZGZKVUMQKA0haXUMBiZZSQI0HSQAVnk3AykEV09ObVV1dBMoFTNDBTVlEiYHBVB+ZGZKVUMHLBk5NjYuGG9QHC87AC4EGB0kR2YpEwRqDAAhOxQhGjFdJSQ1GylWABU3ACJGfx5tR38UISMiMT1OUwA8EBMEEVI+C25INBYwIjY0Jz8JAT1GS20jfmdLVhUGCz4eSEEFOAE6dBQiHz5TCjV4NyYYHhUWHCkaV09ObVV1dBMoFTNDBTVlEiYHBVB+ZGZKVUMHLBk5NjYuGG9QHC87AC4EGB0kR2YpEwRqDAAhOxQsADpyGy4oSTFLE1s2QkwXXGlODAAhOxUiC2h3DSUMGyAMGlB6TAcfAQwRPRInNTMoUX5NY2F4VGc/E00mU2QrABcrbSAlMyUsFzcURUt4VGdLMlA0DzMGAV4iLBkmMXtHU3IWSQI5GCsJF1Y5UyAfGwAwJBo7fCFkUxFQDm8ZATMEI0U1HCcOEF4ybRA7MHtHDns8YwAtACgpGU1oLyIOIQwjKhkwfHUMBiZZOS4vETUnE0M3AmRGDmlkbVV1ADI1B28UKDQsG2c4E1k3DTJKJQwzKAd3eF1tU3IWLSQ+FTIHAgg0DyoZEE9ObVV1dBQsHz5UCCIzSSEeGFYmBykEXRVtbTYzM3kMBiZZOS4vETUnE0M3AnscVQYqKVlfKX5HeRNDHS4aGz9RN1E2OikNEg8hZVcUISMiJiJRGyA8ERcEAVAgTGoRf0NkbVUBMS85TnB3HDU3VBIbEUczCiNKJQwzKAd3eF1tU3IWLSQ+FTIHAgg0DyoZEE9ObVV1dBQsHz5UCCIzSSEeGFYmBykEXRVtbTYzM3kMBiZZPDE/BiYPE2U9GSMYSBVkKBsxeF0wWlg8KDQsGwUEDg8TCiIuBww0KRoiOn9vJiJRGyA8ERMKBFI3GmRGDmlkbVV1ADI1B28UPDE/BiYPExUGDzQNEBdmYX91dHdtNzdQCDQ0AHpJN1k+TGpgVUNkbSM0OCIoAG9RDDUNBCAZF1E3ITYeHAwqPl0yMSMZCjFZBi9wXW5HfBVyTmYpFA8oLxQ2P2orBjxVHSg3Gm8dXxURCCFENBYwIiAlMyUsFzdiCDM/ETNWABU3ACJGfx5tR38UISMiMT1OUwA8EBQHH1E3HG5IIBMjPxQxMRMoHzNPS20jICITAghwOzYNBwIgKFURMTssCnAaLSQ+FTIHAghnQgsDG151YTg0LGp/Q35yDCIxGSYHBQhiQhQFAA0gJBsyaWdhICdQDyggSWVbWAQhTGopFA8oLxQ2P2orBjxVHSg3Gm8dXxURCCFEIBMjPxQxMRMoHzNPVDdyRGlaVlA8CjtDf2koIhY0OHcCFTRTGwM3DGdWVmEzDDVEOAItI08UMDMfGjVeHQYqGzIbFFoqRmQrABcrbTozMjI/UX4UGSk3GiJJXz9YISAMEBEGIg1vFTMpJz1RDi09XGUqA0E9Pi4FGwYLKxMwJnVhCFgWSWF4ICITAghwLzMeGkMUJRo7MXcCFTRTG2N0fmdLVhUWCyALAA8wcBM0OCQoX1gWSWF4NyYHGlczDS1XExYqLgE8OzllBXsWKic/WgYeAloCBikEECwiKxAnaSFtFjxSRUslXU1hWxhyjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUR1h4dHcdIRdlPQgfMU1GWxWw+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4PNOIRo2NTttIyBTGjUxEyIpGU1yU2Y+FAE3Yzg0PTl3MjZSOyg/HDMsBFonHiQFDUtmHQcwJyMkFDcURWMiFTdJXz9YPjQPBhctKhAXOy93MjZSPS4/EysOXhcTGzIFJwYmJAchPHVhCFgWSWF4ICITAghwLzMeGkMWKBc8JiMlUX48SWF4VAMOEFQnAjJXEwIoPhB5XndtU3J1CC00FiYIHQg0GygJAQorI10jfXcOFTUYKDQsGxUOFFwgGi5XA0MhIxF5XipkeVhmGyQrAC4ME3c9FnwrEQcQIhIyODJlURNDHS4dAigHAFBwQj1gVUNkbSEwLCNwURNDHS54MTEEGkM3TGpgVUNkbTEwMjY4HyYLDyA0ByJHfBVyTmYpFA8oLxQ2P2orBjxVHSg3Gm8dXxURCCFENBYwIjAjOzs7Fm9ASSQ2EGthCxxYZBYYEBAwJBIwFjg1SRNSDRU3EyAHEx1wLzMeGiI3LhA7MHVhCFgWSWF4ICITAghwLzMeGkMFPhYwOjNvX1gWSWF4MCINF0A+GnsMFA83KFlfdHdtUxFXBS06FSQAS1MnACUeHAwqZQN8dBQrFHx3HDU3NTQIE1s2UzBKEA0gYX8ofV1HIyBTGjUxEyIpGU1oLyIOJg8tKRAnfHUdATdFHSg/EQMOGlQrTGoRIQY8OUh3BCUoACZfDiR4MCIHF0xwQgIPEwIxIQFoZWdhPjtYVHR0OSYTSwNiQgIPFgopLBkmaWdhIT1DByUxGiBWRhkBGyAMHBt5bwZ3eBQsHz5UCCIzSSEeGFYmBykEXRVtbTYzM3kdATdFHSg/EQMOGlQrUzBKEA0gMFxfXnpgU7Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5E1GWxVyLAklJjcXR1h4dLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+Us0GyQKGhUQASkZASErNVVodAMsESEYJCAxGn0qElEeCyAeMhErOAU3Oy9lURBZBjIsB2VHVE8zHmRDf2kGIhomIBUiC2h3DSUMGyAMGlB6TAcfAQwQJBgwFzY+G3AaEkt4VGdLIlAqGntINBYwIlUBPTooUxFXGil6WE1LVhVyKiMMFBYoOUgzNTs+Fn48SWF4VAQKGlkwDyUBSAUxIxYhPTgjWyQfSQI+E2kqA0E9Oi8HECAlPh1oIncoHTYaYzxxfk0pGVohGgQFDVkFKREBOzAqHzceSwAtACguF0c8CzQoGgw3OVd5L11tU3IWPSQgAHpJN0AmAWYvFBEqKAd1FjgiACYURUt4VGdLMlA0DzMGAV4iLBkmMXtHU3IWSQI5GCsJF1Y5UyAfGwAwJBo7fCFkUxFQDm8ZATMEM1QgACMYNwwrPgFoIncoHTYaYzxxfk0pGVohGgQFDVkFKREBOzAqHzceSwAtACgvGUAwAiMlEwUoJBswdns2eXIWSWEMET8fSxcTGzIFVScrOBc5MXcCFTRaAC89VmthVhVyTgIPEwIxIQFoMjYhADcaY2F4VGcoF1k+DCcJHl4iOBs2ID4iHXpAQGEbEiBFN0AmAQIFAAEoKDozMjskHTcLH2E9GiNHfEh7ZEwoGgw3OTc6LG0MFzZiBiY/GCJDVHQnGikpHQIqKhAZNTUoH3AaEkt4VGdLIlAqGntINBYwIlUWPDYjFDcWJSA6EStJWj9yTmZKMQYiLAA5IGorEj5FDG1SVGdLVnYzAioIFAAvcBMgOjQ5Gj1YQTdxVAQNERsTGzIFNgslIxIwGDYvFj4LH2E9GiNHfEh7ZEwoGgw3OTc6LG0MFzZiBiY/GCJDVHQnGikpHQIqKhAWOzsiASEURTpSVGdLVmE3FjJXVyIxORp1Fz8sHTVTSQI3GCgZBRd+ZGZKVUMAKBM0ITs5TjRXBTI9WE1LVhVyLScGGQElLh5oMiIjECZfBi9wAm5LNVM1QAcfAQwHJRQ7MzIOHD5ZGzJlAmcOGFF+ZDtDf2kGIhomIBUiC2h3DSULGC4PE0d6TAQFGhAwCRA5NS5vXyliDDksSWUpGVohGmYuEA8lNFd5EDIrEidaHXxrRGsmH1tvX3ZGOAI8cERnZHsJFjFfBCA0B3pbWmc9GygOHA0jcEV5ByIrFTtOVGMrVmsoF1k+DCcJHl4iOBs2ID4iHXpAQGEbEiBFNFo9HTIuEA8lNEgjdDIjFy8fY0t1WWeJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9ZgWE5kbTgcGh4KMh9zOkt1WWeJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9ZgGQwnLBl1EzYgFhBZEWFlVBMKFEZ8IycDG1kFKREHPTAlBxVEBjQoFigTXhcfBygDEgIpKAZ3eHUqEj9TGSA8Vm5hfHIzAyMoGht+DBExADgqFD5TQWMZATMEO1w8ByELGAYWLBYwdns2eXIWSWEMET8fSxcTGzIFVTElLhB3eF1tU3IWLSQ+FTIHAgg0DyoZEE9ObVV1dBQsHz5UCCIzSSEeGFYmBykEXRVtbTYzM3kMBiZZJCg2HSAKG1AADyUPSBVkKBsxeF0wWlg8LiA1EQUEDg8TCiI+GgQjIRB9dhY4Bz17AC8xEyYGE2EgDyIPV08/R1V1dHcZFipCVGMZATMEVmEgDyIPV09ObVV1dBMoFTNDBTVlEiYHBVB+ZGZKVUMHLBk5NjYuGG9QHC87AC4EGB0kR2YpEwRqDAAhOxokHTtRCCw9IDUKElBvGGYPGwdoRwh8Xl1gXnLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64ddhWxhyThU+NDcXbSEUFl1gXnLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64ddhGloxDypKJhclOQYZdGptJzNUGm8LACYfBQ8TCiImEAUwCgc6IScvHCoeSxE0FT4OBBd+TDMZEBFmZH9fODguEj4WBSM0NyYYHhVyTntKJhclOQYZbhYpFx5XCyQ0XGUoF0Y6TnxKW01qb1xfODguEj4WBSM0PSkIGVg3TntKJhclOQYZbhYpFx5XCyQ0XGUiGFY9AyNKT0NqY1t3fV0hHDFXBWE0Fis/D1Y9AShKSEMXORQhJxt3MjZSJSA6EStDVGErDSkFG0N+bVt7enVkeT5ZCiA0VCsJGmU9HWZKVUN5bSYhNSM+P2h3DSUUFSUOGh1wPikZHBctIht1bndjXXwUQEs0GyQKGhU+DCosBxYtOQZ1aXceBzNCGg1iNSMPOlQwCypCVyU2OBwhJ3ciHXJbCDF4TmdFWBtwR0xgGQwnLBl1ByMsByFkSXx4ICYJBRsBGiceBlkFKREHPTAlBxVEBjQoFigTXhcRBicYFAAwKAd3eHUsECZfHygsDWVCfFk9DScGVQ8mIT0wNTs5G3IWVGELACYfBWdoLyIOOQImKBl9dh8oEj5CAWFiVGlFWBd7ZCoFFgIobRk3OAAeU3IWSWF4SWc4AlQmHRRQNAcgARQ3MTtlUQVXBSoLBCIOEhVoTmhEW0FtRxk6NzYhUz5UBQsIVGdLVhVyU2Y5AQIwPidvFTMpPzNUDC1wVg0eG0UCATEPB0N+bVt7enVkeT5ZCiA0VCsJGnIgDzADARpkcFUGIDY5AAAMKCU8OCYJE1l6TAEYFBUtOQx1bndjXXwUQEtSJzMKAkYeVAcOESExOQE6On82eXIWSWEMET8fSxcGPmYeGkMQNBY6OzlvX1gWSWF4MjIFFQg0GygJAQorI118XndtU3IWSWF4GCgIF1lyGj8JGgwqbUh1MzI5JytVBi42XG5hVhVyTmZKVUMtK1UhLTQiHDwWHSk9Gk1LVhVyTmZKVUNkbVU5OzQsH3JFGSAvGhcKBEFyU2YeDAArIhtvEj4jFxRfGzIsNy8CGlF6TBUaFBQqb1l1ICU4Fns8SWF4VGdLVhVyTmZKGQwnLBl1Nz8sAXILSQ03FyYHJlkzFyMYWyAsLAc0NyMoAVgWSWF4VGdLVhVyTmYGGgAlIVUnOzg5U28WCik5BmcKGFFyDS4LB1kCJBsxEj4/ACZ1ASg0EG9JPkA/DygFHAcWIhohBDY/B3AfY2F4VGdLVhVyTmZKVQoibQc6OyNtBzpTB0t4VGdLVhVyTmZKVUNkbVV1PTFtACJXHi8IFTUfVlQ8CmYZBQIzIyU0JiN3OiF3QWMaFTQOJlQgGmRDVRcsKBtfdHdtU3IWSWF4VGdLVhVyTmZKVUM2IhohehQLATNbDGFlVDQbF0I8PicYAU0HCwc0OTJtWHJgDCIsGzVYWFs3GW5aWUNxYVVlfV1tU3IWSWF4VGdLVhVyTmZKEA83KH91dHdtU3IWSWF4VGdLVhVyTmZKVU5pbTM8OjNtEjxPSTE5BjNLH1tyGj8JGgwqR1V1dHdtU3IWSWF4VGdLVhVyTmZKEww2bSp5dDgvGXJfB2ExBCYCBEZ6Gj8JGgwqdzIwIBMoADFTByU5GjMYXhx7TiIFf0NkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVQoibRo3Pm0EABMeSwM5ByI7F0cmTG9KAQshI391dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtAT1ZHW8bMjUKG1ByU2YFFwlqDjMnNTooU3kWPyQ7ACgZRRs8CzFCRU9keFl1ZH5HU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSSMqESYAfBVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVlA8CkxKVUNkbVV1dHdtU3IWSWF4VGdLVlA8CkxKVUNkbVV1dHdtU3IWSWF4ESkPfBVyTmZKVUNkbVV1dHdtU3J6ACMqFTUSTHs9Gi8MDEtmGRA5MSciASZTDWEsG2cfD1Y9AShLV0pObVV1dHdtU3IWSWF4ESkPfBVyTmZKVUNkKBkmMV1tU3IWSWF4VGdLVhUeByQYFBE9dzs6ID4rCnoUPTg7GygFVls9GmYMGhYqKVR3fV1tU3IWSWF4VCIFEj9yTmZKEA0gYX8ofV1HXn8Wi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7fBh/TmYnOjUBADAbAHcZMhAWQQwxByRCfBh/TqT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3X85OzQsH3J7Bjc9OGdWVmEzDDVEOAo3Lk8UMDMBFjRCLjM3ATcJGU16TAUCFBElLgEwJnVhUSdFDDN6XU1hO1okCwpQNAcgHhk8MDI/W3BhCC0zJzcOE1FwQj0+EBswcFcCNTsmICJTDCV6WAMOEFQnAjJXRFVoABw7aWZ7Xx9XEXxtRHdHMlAxBysLGRB5fVkHOyIjFztYDnxoWBQeEFM7FntIV08HLBk5NjYuGG9QHC87AC4EGB0kR0xKVUNkDhMyegAsHzllGSQ9EHodfBVyTmYGGgAlIVU9ITptTnJ6BiI5GBcHF0w3HGgpHQI2LBYhMSVtEjxSSQ03FyYHJlkzFyMYWyAsLAc0NyMoAWhwAC88Mi4ZBUERBi8GESwiDhk0JyRlURpDBCA2Gy4PVBxYTmZKVQoibR0gOXc5GzdYSSktGWk8F1k5PTYPEAd5O1UwOjNHFjxSFGhSfgoEAFAeVAcOETAoJBEwJn9vOSdbGRE3AyIZVBkpOiMSAV5mBwA4JAciBDdES20cESEKA1kmU3NaWS4tI0hgZHsAEioLXHFoWAMOFVw/DyoZSFNoHxogOjMkHTULWW0LASENH01vTGRGNgIoIRc0NzxwFSdYCjUxGylDABxYTmZKVSAiKlsfITo9Iz1BDDNlAk1LVhVyAikJFA9kJQA4dGptPz1VCC0IGCYSE0d8LS4LBwInORAndDYjF3J6BiI5GBcHF0w3HGgpHQI2LBYhMSV3NTtYDQcxBjQfNV07AiIlEyAoLAYmfHUFBj9XBy4xEGVCfBVyTmYDE0MsOBh1ID8oHXJeHCx2PjIGBmU9GSMYSBV/bR0gOXkYADd8HCwoJCgcE0dvGjQfEEMhIxFfMTkpDns8Yww3AiInTHQ2ChUGHAchP113EyUsBTtCEGN0DxMODkFvTAEYFBUtOQx3eBMoFTNDBTVlRX5dWng7AHtaWS4lNUhgZGdhNzdVACw5GDRWRhkAATMEEQoqKkhleAQ4FTRfEXx6VmsoF1k+DCcJHl4iOBs2ID4iHXpAQEt4VGdLNVM1QAEYFBUtOQxoIl1tU3IWPi4qHzQbF1Y3QAEYFBUtOQxoIl0oHTZLQEtSOSgdE3loLyIOIQwjKhkwfHUEHTR8HCwoVmsQfBVyTmY+EBswcFccOjEkHTtCDGESASobVBlYTmZKVSchKxQgOCNwFTNaGiR0fmdLVhURDyoGFwInJkgzITkuBztZB2kuXWcoEFJ8JygMPxYpPUgjdDIjF348FGhSfgoEAFAeVAcOETcrKhI5MX9vPT1VBSgoVmsQfBVyTmY+EBswcFcbOzQhGiIURUt4VGdLMlA0DzMGAV4iLBkmMXtHU3IWSQI5GCsJF1Y5UyAfGwAwJBo7fCFkUxFQDm8WGyQHH0VvGGYPGwdoRwh8Xl0AHCRTJXsZECM/GVI1AiNCVyIqORwUEhxvXyk8SWF4VBMODkFvTAcEAQpkDDMedntHU3IWSQU9EiYeGkFvCCcGBgZoR1V1dHcOEj5aCyA7H3oNA1sxGi8FG0syZFUWMjBjMjxCAAAeP3odVlA8CmpgCEpORxk6NzYhUx9ZHyQKVHpLIlQwHWgnHBAndzQxMAUkFDpCLjM3ATcJGU16TAAGHAQsOVd5dichEjxTS2hSfgoEAFAAVAcOETcrKhI5MX9vNT5PS20jfmdLVhUGCz4eSEECIQx3eF1tU3IWLSQ+FTIHAgg0DyoZEE9ObVV1dBQsHz5UCCIzSSEeGFYmBykEXRVtbTYzM3kLHytzByA6GCIPS0NyCygOWWk5ZH9fGTg7FgAMKCU8JysCElAgRmQsGRoXPRAwMHVhCAZTETVlVgEHDxUBHiMPEUFoCRAzNSIhB28DWW0VHSlWRxkfDz5XQFN0YTEwNz4gEj5FVHF0JigeGFE7ACFXRU8XOBMzPS9wUXAaKiA0GCUKFV5vCDMEFhctIht9In5tMDRRRwc0DRQbE1A2UzBKEA0gMFxfXhoiBTdkUwA8EAUeAkE9AG4Rf0NkbVUBMS85TnBiOWEsG2c/D1Y9AShIWWlkbVV1EiIjEG9QHC87AC4EGB17ZGZKVUNkbVV1ODguEj4WHTg7GygFVghyCSMeIRonIho7fH5HU3IWSWF4VGcCEBUmFyUFGg1kOR0wOl1tU3IWSWF4VGdLVhU+ASULGUM3PRQiOgcsASYWVGEsDSQEGVtoKC8EESUtPwYhFz8kHzYeSxIoFTAFVBlyGjQfEEpObVV1dHdtU3IWSWF4GCgIF1lyDS4LB0N5bTk6NzYhIz5XECQqWgQDF0czDTIPB2lkbVV1dHdtU3IWSWE0GyQKGhUgASkeVV5kLh00JncsHTYWCik5Bn0tH1s2KC8YBhcHJRw5MH9vOydbCC83HSM5GVomPicYAUFtR1V1dHdtU3IWSWF4VC4NVkc9ATJKAQshI391dHdtU3IWSWF4VGdLVhVyByBKBhMlOhsFNSU5UzNYDWErBCYcGGUzHDJQPBAFZVcXNSQoIzNEHWNxVDMDE1tYTmZKVUNkbVV1dHdtU3IWSWF4VGcZGVomQAUsBwIpKFVodCQ9EiVYOSAqAGkoMEczAyNKXkMSKBYhOyV+XTxTHmloWGdeWhViR0xKVUNkbVV1dHdtU3IWSWF4ESsYEz9yTmZKVUNkbVV1dHdtU3IWSWF4VCEEBBUNQmYFFwlkJBt1PScsGiBFQTUhFygEGA8VCzIuEBAnKBsxNTk5AHofQGE8G01LVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGcCEBU9DCxQPBAFZVcXNSQoIzNEHWNxVDMDE1tYTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVRErIgF7FxE/Ej9TSXx4GyUBWHYUHCcHEENvbSMwNyMiAWEYByQvXHdHVgB+TnZDf0NkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVU3JjIsGFgWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3JTByVSVGdLVhVyTmZKVUNkbVV1dHdtU3JTByVSVGdLVhVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVhVyTmZKVUNkARw3JjY/Cmh4BjUxEj5DVGE3AiMaGhEwKBF1IDhtBytVBi42VWVCfBVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVlA+HSNgVUNkbVV1dHdtU3IWJSg6BiYZDw8cATIDExpsbyEsNzgiHXJYBjV4EigeGFFzTG9gVUNkbVV1dHcoHTY8SWF4VCIFEhlYE29gfy4rOxAHbhYpFxBDHTU3Gm8QfBVyTmY+EBswcFcBBHc5HHJlGSA7EWVHfBVyTmYsAA0ncBMgOjQ5Gj1YQWhSVGdLVhVyTmYGGgAlIVU2PDY/U28WJS47FSs7GlQrCzRENgslPxQ2IDI/eXIWSWF4VGdLGloxDypKBwwrOVVodDQlEiAWCC88VCQDF0doKC8EESUtPwYhFz8kHzYeSwktGSYFGVw2PCkFATMlPwF3fV1tU3IWSWF4VC4NVkc9ATJKAQshI391dHdtU3IWSWF4VGcHGVYzAmYZBQInKFVodAAiATlFGSA7EX0tH1s2KC8YBhcHJRw5MH9vICJXCiR6XU1LVhVyTmZKVUNkbVU8Mnc+AzNVDGEsHCIFfBVyTmZKVUNkbVV1dHdtU3JaBiI5GGcbF0cmTntKBhMlLhBvEj4jFxRfGzIsNy8CGlEdCAUGFBA3ZVcFNSU5UXsWBjN4BzcKFVBoKC8EESUtPwYhFz8kHzZ5DwI0FTQYXhcfASIPGUFtR1V1dHdtU3IWSWF4VGdLVhU7CGYaFBEwbQE9MTlHU3IWSWF4VGdLVhVyTmZKVUNkbVUnOzg5XRFwGyA1EWdWVkUzHDJQMgYwHRwjOyNlWnIdSRc9FzMEBAZ8ACMdXVNobUB5dGdkeXIWSWF4VGdLVhVyTmZKVUNkbVV1GD4vATNEEHsWGzMCEEx6TBIPGQY0IgchMTNtBz0WOjE5FyJKVBxYTmZKVUNkbVV1dHdtU3IWSSQ2EE1LVhVyTmZKVUNkbVUwOCQoeXIWSWF4VGdLVhVyTmZKVUMIJBcnNSU0SRxZHSg+DW9JJUUzDSNKGwwwbRM6ITkpUnAfY2F4VGdLVhVyTmZKVQYqKX91dHdtU3IWSSQ2EE1LVhVyCygOWWk5ZH9fGTg7FgAMKCU8NjIfAlo8Rj1gVUNkbSEwLCNwUQZmSTU3VBEEH1FyPikYAQIob1lfdHdtUxRDByJlEjIFFUE7AShCXGlkbVV1dHdtUz5ZCiA0VCQDF0dyU2YmGgAlISU5NS4oAXx1ASAqFSQfE0dYTmZKVUNkbVU5OzQsH3JEBi4sVHpLFV0zHGYLGwdkLh00Jm0LGjxSLygqBzMoHlw+Cm5IPRYpLBs6PTMfHD1COSAqAGVCfBVyTmZKVUNkJBN1JjgiB3JCASQ2fmdLVhVyTmZKVUNkbRM6JncSX3JZCyt4HSlLH0UzBzQZXTQrPx4mJDYuFmhxDDUcETQIE1s2DygeBkttZFUxO11tU3IWSWF4VGdLVhVyTmZKHAVkIhc/ehksHjcWVHx4VhEEH1EACzIfBw0UIgchNTtvUzNYDWE3Fi1RP0YTRmQnGgchIVd8dCMlFjw8SWF4VGdLVhVyTmZKVUNkbVV1dHc/HD1CRwIeBiYGExVvTikIH1kDKAEFPSEiB3ofSWp4IiIIAlogXWgEEBRsfVl1YXttQ3s8SWF4VGdLVhVyTmZKVUNkbVV1dHcBGjBECDMhTgkEAlw0F25IIQYoKAU6JiMoF3JCBmEOGy4PVmU9HDILGUJmZH91dHdtU3IWSWF4VGdLVhVyTmZKVREhOQAnOl1tU3IWSWF4VGdLVhVyTmZKEA0gR1V1dHdtU3IWSWF4VCIFEj9yTmZKVUNkbVV1dHcBGjBECDMhTgkEAlw0F25IIwwtKVUFOyU5Ej4WBy4sVCEEA1s2T2RDf0NkbVV1dHdtFjxSY2F4VGcOGFF+ZDtDf2kJIgMwBm0MFzZ0HDUsGylDDT9yTmZKIQY8OUh3AAdtBz0WJCg2HSAKG1AhTGpgVUNkbTMgOjRwFSdYCjUxGylDXz9yTmZKVUNkbRk6NzYhUzFeCDN4SWcnGVYzAhYGFBohP1sWPDY/EjFCDDNSVGdLVhVyTmYGGgAlIVUnOzg5U28WCik5BmcKGFFyDS4LB1kCJBsxEj4/ACZ1ASg0EG9JPkA/DygFHAcWIhohBDY/B3AfY2F4VGdLVhVyByBKBwwrOVUhPDIjeXIWSWF4VGdLVhVyTiAFB0MbYVU6Nj1tGjwWADE5HTUYXmI9HC0ZBQInKE8SMSMJFiFVDC88FSkfBR17R2YOGmlkbVV1dHdtU3IWSWF4VGdLH1NyASQAWy0lIBB1aWptUR9fByg/FSoOVmczDSNIVQIqKVU6Nj13OiF3QWMVGyMOGhd7TjICEA1ObVV1dHdtU3IWSWF4VGdLVhVyTmYYGgwwYzYTJjYgFnILSS46Hn0sE0ECBzAFAUttbV51AjIuBz1EWm82ETBDRhlyW2pKRUpObVV1dHdtU3IWSWF4VGdLVhVyTmYmHAE2LAcsbhkiBztQEGl6ICIHE0U9HDIPEUMwIlUYPTkkFDNbDDJ5Vm5hVhVyTmZKVUNkbVV1dHdtU3IWSWEqETMeBFtYTmZKVUNkbVV1dHdtU3IWSSQ2EE1LVhVyTmZKVUNkbVUwOjNHU3IWSWF4VGdLVhVyIi8IBwI2NE8bOyMkFSseSwwxGi4MF1g3HWYEGhdkKxogOjNsUXs8SWF4VGdLVhU3ACJgVUNkbRA7MHtHDns8Y2x1VKX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/kxHWENkCicUBB8EMAEWPQAafmpGVtfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5WkoIhY0OHcKFSp6SXx4ICYJBRsVHCcaHQonPk8UMDMBFjRCLjM3ATcJGU16TBQPGwchPxw7M3VhUT9ZBygsGzVJXz9YKSASOVkFKREXISM5HDweEkt4VGdLIlAqGntIOAI8bTInNSclGjFFS21SVGdLVnMnACVXExYqLgE8OzllWnJFDDUsHSkMBR17QBQPGwchPxw7M3kcBjNaADUhOCIdE1lvKygfGE0VOBQ5PSM0PzdADC12OCIdE1lgX31KOQomPxQnLW0DHCZfDzhwVgAZF0U6ByUZT0MJDC13fXcoHTYaYzxxfk0sEE0eVAcOESExOQE6On82eXIWSWEMET8fSxcfByhKMhElPR08NyRvX1gWSWF4MjIFFQg0GygJAQorI118dCQoByZfByYrXG5FJFA8CiMYHA0jYyQgNTskByt6DDc9GHouGEA/QBcfFA8tOQwZMSEoH3x6DDc9GHdaTRUeByQYFBE9dzs6ID4rCnoULjM5BC8CFUZoTgsjO0FtbRA7MHtHDns8YwY+DAtRN1E2LDMeAQwqZQ5fdHdtUwZTETVlVgkEVmY6DyIFAhBmYX91dHdtNSdYCnw+ASkIAlw9AG5Df0NkbVV1dHdtPztRATUxGiBFMVk9DCcGJgslKRoiJ3dwUzRXBTI9fmdLVhVyTmZKOQojJQE8OjBjPCdCDS43BgYGFFw3ADJKSEMHIhk6JmRjHTdBQXB0RWtaXz9yTmZKVUNkbTk8NiUsASsMJy4sHSESXhcBBicOGhQ3bRE8JzYvHzdSS2hSVGdLVlA8CmpgCEpORzIzLBt3MjZSKzQsACgFXk5YTmZKVTchNQFodhE4Hz4WKzMxEy8fVBlYTmZKVSUxIxZoMiIjECZfBi9wXU1LVhVyTmZKVS8tKh0hPTkqXRBEACYwACkOBUZyU2ZbRWlkbVV1dHdtUx5fDiksHSkMWHY+ASUBIQopKFVodGZ/eXIWSWF4VGdLOlw1BjIDGwRqChk6NjYhIDpXDS4vB2dWVlMzAjUPf0NkbVV1dHdtPztUGyAqDX0lGUE7CD9CVyUxIRl1NiUkFDpCSSQ2FSUHE1FwR0xKVUNkKBsxeF0wWlg8LicgOH0qElEQGzIeGg1sNn91dHdtJzdOHXx6JiIGGUM3TgAFEkFoR1V1dHcLBjxVVCctGiQfH1o8Rm9gVUNkbVV1dHcBGjVeHSg2E2ktGVIBGicYAUN5bUVfdHdtU3IWSWEUHSADAlw8CWgsGgQBIxF1aXd8Q2IGWXFSVGdLVhVyTmYmHAQsORw7M3kLHDV1Bi03BmdWVnY9AikYRk0qKAJ9ZXt8X2MfY2F4VGdLVhVyIi8IBwI2NE8bOyMkFSseSwc3E2cZE1g9GCMOV0pObVV1dDIjF348FGhSfisEFVQ+TgEMDTFkcFUBNTU+XRVECDEwHSQYTHQ2ChQDEgswCgc6IScvHCoeSw4oAC4GH08zGi8FGxBmYVcvNSdvWlg8LicgJn0qElEQGzIeGg1sNn91dHdtJzdOHXx6OCgcVmU9Aj9KOAwgKFd5XndtU3JwHC87SSEeGFYmBykEXUpObVV1dHdtU3JQBjN4K2tLGVc4Ti8EVQo0LBwnJ38aHCBdGjE5FyJRMVAmKiMZFgYqKRQ7ICRlWnsWDS5SVGdLVhVyTmZKVUNkJBN1OzUnSRtFKGl6NiYYE2UzHDJIXEMlIxF1Ojg5Uz1UA3sRBwZDVHg3HS46FBEwb1x1ID8oHVgWSWF4VGdLVhVyTmZKVUNkIhc/ehosBzdEACA0VHpLM1snA2gnFBchPxw0OHkeHj1ZHSkIGCYYAlwxZGZKVUNkbVV1dHdtUzdYDUt4VGdLVhVyTmZKVUMtK1U6Nj13OiF3QWMcESQKGhd7TikYVQwmJ08cJxZlUQZTETUtBiJJXxUmBiMEf0NkbVV1dHdtU3IWSWF4VGcEFF9oKiMZARErNF18XndtU3IWSWF4VGdLVlA8CkxKVUNkbVV1dDIjF1gWSWF4VGdLVnk7DDQLBxp+AxohPTE0W3B6BjZ4BCgHDxU/ASIPVQI0PRk8MTNvWlgWSWF4ESkPWj8vR0xgMgU8H08UMDMPBiZCBi9wD01LVhVyOiMSAV5mCRwmNTUhFnJzDyc9FzMYVBlYTmZKVSUxIxZoMiIjECZfBi9wXU1LVhVyTmZKVQUrP1UKeHciETgWAC94HTcKH0chRhEFBwg3PRQ2MW0KFiZyDDI7ESkPF1smHW5DXEMgIn91dHdtU3IWSWF4VGcCEBU9DCxQPBAFZVcFNSU5GjFaDAQ1HTMfE0dwR2YFB0MrLx9vHSQMW3BiGyAxGGVCVlogTikIH1kNPjR9dgQgHDlTS2h4GzVLGVc4VA8ZNEtmCxwnMXVkUyZeDC9SVGdLVhVyTmZKVUNkbVV1dDgvGXxzByA6GCIPVghyCCcGBgZObVV1dHdtU3IWSWF4ESkPfBVyTmZKVUNkKBsxXndtU3IWSWF4OC4JBFQgF3wkGhctKwx9dhIrFTdVHTJ4EC4YF1c+CyJIXGlkbVV1MTkpX1hLQEtSMyETJA8TCiIoABcwIht9L11tU3IWPSQgAHpJJFA/ATAPVTQlORAndntHU3IWSQctGiRWEEA8DTIDGg1sZH91dHdtU3IWSRY3BiwYBlQxC2g+EBE2LBw7egAsBzdEPTM5GjQbF0c3ACUTVV5kfH91dHdtU3IWSRY3BiwYBlQxC2g+EBE2LBw7egAsBzdEOyQ+GCIIAlQ8DSNKSEN0R1V1dHdtU3IWPi4qHzQbF1Y3QBIPBxElJBt7AzY5FiBhCDc9Jy4RExVvTnZgVUNkbVV1dHcBGjBECDMhTgkEAlw0F25IIgIwKAd1MD4+EjBaDCV6XU1LVhVyCygOWWk5ZH9fEzE1IWh3DSUMGyAMGlB6TAcfAQwDPxQlPD4uAHAaEkt4VGdLIlAqGntINBYwIlUZOyBtNCBXGSkxFzRJWj9yTmZKMQYiLAA5IGorEj5FDG1SVGdLVnYzAioIFAAvcBMgOjQ5Gj1YQTdxfmdLVhVyTmZKHAVkO1UhPDIjeXIWSWF4VGdLVhVyTjUPARctIxImfH5jITdYDSQqHSkMWGQnDyoDARoIKAMwOHdwUxdYHCx2JTIKGlwmFwoPAwYoYzkwIjIhQ2M8SWF4VGdLVhVyTmZKOQojJQE8OjBjND5ZCyA0Jy8KElolHWZXVQUlIQYwXndtU3IWSWF4VGdLVnk7DDQLBxp+AxohPTE0W3B3HDU3VCsEARU1HCcaHQonPlUaGnVkeXIWSWF4VGdLE1s2ZGZKVUMhIxF5XipkeVgbRGG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46Ww+9aI4POm2OW3wcev5sLU/NG64deJ46VYQ2tKVTUNHiAUGHcZMhA8RGx4ltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCZCoFFgIobSM8JxttTnJiCCMrWhECBUAzAnwrEQcIKBMhEyUiBiJUBjlwVgI4Jhd+TCMTEEFtR38DPSQBSRNSDRU3EyAHEx1wKxU6JQ8lNBAnJ3VhCFgWSWF4ICITAghwKxU6VTMoLAwwJiRvX1gWSWF4MCINF0A+GnsMFA83KFlfdHdtUxFXBS06FSQAS1MnACUeHAwqZQN8dBQrFHxzOhEIGCYSE0chUzBKEA0gYX8ofV1HJTtFJXsZECM/GVI1AiNCVyYXHTY0Jz8JAT1GS20jfmdLVhUGCz4eSEEBHiV1FzY+G3JyGy4oVmthVhVyTgIPEwIxIQFoMjYhADcaY2F4VGcoF1k+DCcJHl4iOBs2ID4iHXpAQGEbEiBFM2YCLScZHSc2IgVoIncoHTYaYzxxfk09H0YeVAcOETcrKhI5MX9vNgFmPTg7GygFVBkpZGZKVUMQKA0haXUIIAIWJDh4ID4IGVo8TGpgVUNkbTEwMjY4HyYLDyA0ByJHfBVyTmYpFA8oLxQ2P2orBjxVHSg3Gm8dXxURCCFEMDAUGQw2OzgjTiQWDC88WE0WXz9YQ2tKl/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFtsLdkcemi9TIltL7lKDCjNP6l/bUr+DFXnpgU3J7KAgWVAskOWUBZGtHVYHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxLXY47Cj+aPN5KX+5tfH/qT/5YHR3ZfAxF1HXn8WKDQsG2coGlwxBWYmEA4rI1V9NzskEDlFSScqAS4fVnY+ByUBMQYwKBYhOyU+U3kWPiAzEQ4FFVo/CxUeBwYlIFxfIDY+GHxFGSAvGm8NA1sxGi8FG0ttR1V1dHc6GztaDGEsBjIOVlE9ZGZKVUNkbVV1PTFtMDRRRwAtACgoGlwxBQoPGAwqbQE9MTlHU3IWSWF4VGdLVhVyAikJFA9kOQw2OzgjU28WDiQsID4IGVo8Rm9gVUNkbVV1dHdtU3IWRGx4NysCFV5yDyoGVQU2OBwhdBQhGjFdLSQsESQfGUchTi8EVRcsKFUhLTQiHDw8SWF4VGdLVhVyTmZKHAVkOQw2OzgjUyZeDC9SVGdLVhVyTmZKVUNkbVV1dDsiEDNaSSI0HSQABRVvTnZgVUNkbVV1dHdtU3IWSWF4VCEEBBUNQmYFFwlkJBt1PScsGiBFQTUhFygEGA8VCzIuEBAnKBsxNTk5AHofQGE8G01LVhVyTmZKVUNkbVV1dHdtU3IWSSg+VCkEAhURCCFENBYwIjY5PTQmPzdbBi94AC8OGBUwHCMLHkMhIxFfdHdtU3IWSWF4VGdLVhVyTmZKVUNpYFUWOD4uGBZTHSQ7ACgZVlo8TiAYAAowbQU0JiM+eXIWSWF4VGdLVhVyTmZKVUNkbVV1PTFtHDBcUwgrNW9JNVk7DS0uEBchLgE6JnVkUzNYDWFwGyUBWGUzHCMEAU0KLBgwbjEkHTYeSwI0HSQAVBxyATRKGgEuYyU0JjIjB3x4CCw9TiECGFF6TAAYAAowb1x8dCMlFjw8SWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWGSI5GCtDEEA8DTIDGg1sZFUzPSUoED5fCio8ETMOFUE9HG4FFwltbRA7MH5HU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtED5fCiorVHpLFVk7DS0ZVUhkfH91dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVU8MncuHztVAjJ4SnpLQwVyGi4PG0MmPxA0P3coHTY8SWF4VGdLVhVyTmZKVUNkbVV1dHcoHTY8SWF4VGdLVhVyTmZKVUNkbRA7MF1tU3IWSWF4VGdLVhU3ACJgVUNkbVV1dHdtU3IWRGx4NSsYGRUxDyoGVTQlJhAcOjQiHjdlHTM9FSpLEFogTiQfHA8gJBsyJ11tU3IWSWF4VGdLVhU+ASULGUM2KBg6IDI+U28WDiQsID4IGVo8PCMHGhchPl0hLTQiHDwfY2F4VGdLVhVyTmZKVQoibQcwOTg5FiEWCC88VDUOG1omCzVEIgIvKDw7NzggFgFCGyQ5GWcfHlA8ZGZKVUNkbVV1dHdtU3IWSWE0GyQKGhUiGzQJHUN5bQEsNzgiHXJXByV4AD4IGVo8VAADGwcCJAcmIBQlGj5SQWMIATUIHlQhCzVIXGlkbVV1dHdtU3IWSWF4VGdLH1NyHjMYFgtkOR0wOl1tU3IWSWF4VGdLVhVyTmZKVUNkbRM6JncSX3JXGyQ5VC4FVlwiDy8YBks0OAc2PG0KFiZ1ASg0EDUOGB17R2YOGmlkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUMtK1U7OyNtMDRRRwAtACgoGlwxBQoPGAwqbQE9MTltESBTCCp4ESkPfBVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVlk9DScGVQslPiAlMyUsFzcWVGE+FSsYEz9yTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhU0ATRKKk9kKVU8OnckAzNfGzJwFTUOFw8VCzIuEBAnKBsxNTk5AHofQGE8G01LVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyByBKEVkNPjR9dgUoHj1CDActGiQfH1o8TG9KFA0gbRF7GjYgFnILVGF6ITcMBFQ2C2RKAQshI391dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSSk5BxIbEUczCiNKSEMwPwAwXndtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4FjUOF15YTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVQYqKX91dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVUwOjNHU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtGjQWASArITcMBFQ2C2YeHQYqR1V1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHc9EDNaBWk+ASkIAlw9AG5DVREhIBohMSRjJDNdDAg2FygGE2YmHCMLGFkNIwM6PzIeFiBADDNwFTUOFxscDysPXEMhIxF8XndtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVhVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVhVyTmZKVUNkKBsxXndtU3IWSWF4VGdLVlA8CkxKVUNkbVV1dDIjF1gWSWF4VGdLVkEzHS1EAgItOV1lemJkeXIWSWE9GiNhE1s2R0xgWE5kDAAhO3cYAzVECCU9VG8PBFoiCikdG0MwLAcyMSNkeSZXGip2BzcKAVt6CDMEFhctIht9fV1tU3IWHikxGCJLAkcnC2YOGmlkbVV1dHdtUztQSQI+E2kqA0E9OzYNBwIgKFUhPDIjeXIWSWF4VGdLVhVyTioFFgIobQEsNzgiHXILSSY9ABMSFVo9AG5Df0NkbVV1dHdtU3IWSTQoEzUKElAGDzQNEBdsOQw2OzgjX3J1DyZ2NTIfGWAiCTQLEQYQLAcyMSNkeXIWSWF4VGdLE1s2ZGZKVUNkbVV1IDY+GHxBCCgsXAQNERsHHiEYFAchCRA5NS5keXIWSWE9GiNhE1s2R0xgWE5kDAAhO3cdGz1YDGEXEiEOBD8mDzUBWxA0LAI7fDE4HTFCAC42XG5hVhVyTjECHA8hbQEnITJtFz08SWF4VGdLVhU7CGYpEwRqDAAhOwclHDxTJic+ETVLAl03AExKVUNkbVV1dHdtU3JaBiI5GGcfD1Y9AShKSEMjKAEBLTQiHDweQEt4VGdLVhVyTmZKVUMoIhY0OHc/Fj9ZHSQrVHpLEVAmOj8JGgwqHxA4OyMoAHpCECI3GylCfBVyTmZKVUNkbVV1dD4rUyBTBC4sETRLF1s2TjQPGAwwKAZ7BD8iHTd5Dyc9BmcfHlA8ZGZKVUNkbVV1dHdtU3IWSWEoFyYHGh00GygJAQorI118dCUoHj1CDDJ2JC8EGFAdCCAPB1kCJAcwBzI/BTdEQWh4ESkPXz9yTmZKVUNkbVV1dHcoHTY8SWF4VGdLVhU3ACJgVUNkbVV1dHc5EiFdRzY5HTNDRQV7ZGZKVUMhIxFfMTkpWlg8RGx4NTIfGRURASoGEAAwbTY0Jz9tNyBZGWFwByQKGEZyGSkYHhA0LBYwdDEiAXJSGy4oB25hAlQhBWgZBQIzI10zITkuBztZB2lxfmdLVhUlBi8GEEMwPwAwdDMieXIWSWF4VGdLH1NyLSANWyIxORoWNSQlNyBZGWEsHCIFfBVyTmZKVUNkbVV1dDsiEDNaSSI3BiJLSxUACzYGHAAlORAxByMiATNRDHseHSkPMFwgHTIpHQooKV13Fzg/FnAfY2F4VGdLVhVyTmZKVQoibRY6JjJtBzpTB0t4VGdLVhVyTmZKVUNkbVV1ODguEj4WGyQ1JiIaVghyDSkYEFkCJBsxEj4/ACZ1ASg0EG9JJFA/ATIPJwY1OBAmIHVkeXIWSWF4VGdLVhVyTmZKVUMtK1UnMTofFiMWHSk9Gk1LVhVyTmZKVUNkbVV1dHdtU3IWSS03FyYHVlYzHS4uBww0HxA4OyMoU28WGyQ1JiIaTHM7ACIsHBE3OTY9PTspW3B1CDIwMDUEBmY3HDADFgZqHxAxMTIgUXs8SWF4VGdLVhVyTmZKVUNkbVV1dHckFXJVCDIwMDUEBmc3AykeEEMlIxF1NzY+GxZEBjEKESoEAlBoJzUrXUEWKBg6IDILBjxVHSg3GmVCVkE6CyhgVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKWE5kHhY0Onc6HCBdGjE5FyJLEFogTiULBgtkKQc6JCRHU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtFT1ESR50VCgJHBU7AGYDBQItPwZ9Azg/GCFGCCI9TgAOAnE3HSUPGwclIwEmfH5kUzZZY2F4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGcCEBU8ATJKNgUjYzQgIDgOEiFeLTM3BGcfHlA8TiQYEAIvbRA7MF1tU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWBS47FStLGBVvTikIH00KLBgwbjsiBDdEQWhSVGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhh/TgULBgtkKQc6JCRtBiFDCC00DWcDF0M3TmQpFBAsb1U6JndvNyBZGWN4HSlLGFQ/C2YLGwdkLAcwdBUsADdmCDMsB01LVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyByBKXQ1+Kxw7MH9vEDNFASUqGzdJXxU9HGYETwUtIxF9djQsADppDTM3BGVCVlogTihQEwoqKV13MCUiA3AfSS4qVCgJHA8VCzIrARc2JBcgIDJlURFXGikcBigbP1FwR29KFA0gbRo3Pm0EABMeSwM5ByI7F0cmTG9KAQshI391dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSS03FyYHVlEgATYjEUN5bRo3Pm0KFiZ3HTUqHSUeAlB6TAULBgsAPxolHTNvWnJZG2E3Fi1FOFQ/C0xKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dCcuEj5aQSctGiQfH1o8Rm9KFgI3JTEnOycfFj9ZHSRiPSkdGV43PSMYAwY2ZREnOycEF3sWDC88XU1LVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVRclPh57IzYkB3oGR3BxfmdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhU3ACJgVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKEA0gR1V1dHdtU3IWSWF4VGdLVhVyTmZKEA0gR1V1dHdtU3IWSWF4VGdLVhU3ACJgVUNkbVV1dHdtU3IWDC88fmdLVhVyTmZKEA0gR1V1dHdtU3IWHSArH2kcF1wmRnRDf0NkbVUwOjNHFjxSQEtSWWpLN0AmAWY6BwY3ORwyMXdlITdUADMsHGtLM0M9AjAPWUMFPhYwOjNkeSZXGip2BzcKAVt6CDMEFhctIht9fV1tU3IWHikxGCJLAkcnC2YOGmlkbVV1dHdtUztQSQI+E2kqA0E9PCMIHBEwJVU6JncOFTUYKDQsGwIdGVkkC2YFB0MHKxJ7FSI5HBNFCiQ2EGcfHlA8ZGZKVUNkbVV1dHdtUz5ZCiA0VDMSFVo9AGZXVQQhOSEsNzgiHXofY2F4VGdLVhVyTmZKVQ8rLhQ5dCUoHj1CDDJ4SWcME0EGFyUFGg0WKBg6IDI+WyZPCi43Gm5hVhVyTmZKVUNkbVV1PTFtATdbBjU9B2cfHlA8ZGZKVUNkbVV1dHdtU3IWSWExEmcoEFJ8LzMeGjEhLxwnID9tEjxSSTM9GSgfE0Z8PCMIHBEwJVUhPDIjeXIWSWF4VGdLVhVyTmZKVUNkbVV1JDQsHz4eDzQ2FzMCGVt6R2YYEA4rORAmegUoETtEHSliPSkdGV43PSMYAwY2ZVx1MTkpWlgWSWF4VGdLVhVyTmZKVUNkKBsxXndtU3IWSWF4VGdLVhVyTmYDE0MHKxJ7FSI5HBdABi0uEWcKGFFyHCMHGhchPlsQIjghBTcWHSk9Gk1LVhVyTmZKVUNkbVV1dHdtU3IWSTE7FSsHXlMnACUeHAwqZVx1JjIgHCZTGm8dAigHAFBoJygcGgghHhAnIjI/W3sWDC88XU1LVhVyTmZKVUNkbVV1dHdtFjxSY2F4VGdLVhVyTmZKVUNkbVU8MncOFTUYKDQsGwYYFVA8CmYLGwdkPxA4OyMoAHx3GiI9GiNLAl03AExKVUNkbVV1dHdtU3IWSWF4VGdLVkUxDyoGXQUxIxYhPTgjW3sWGyQ1GzMOBRsTHSUPGwd+BBsjOzwoIDdEHyQqXG5LE1s2R0xKVUNkbVV1dHdtU3IWSWF4ESkPfBVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVlA8CkxKVUNkbVV1dCMsADkYHiAxAG8oEFJ8PjQPBhctKhARMTssCns8SWF4VCIFEj83ACJDf2lpYFUUISMiUwJZHiQqVAsOAFA+Tm4JDAAoKAZ1ID8/HCdRAWEzGigcGBUiATEPB0MqLBgwJ35HBzNFAm8rBCYcGB00GygJAQorI118XndtU3JaBiI5GGc7OWIXPBkkNC4BHlVodCxvJDNaAhIoESIPVBlyTBMaEhElKRAGIDYuGHAaSWMaAT4lE00mTGpKVzchIRAlOyU5US88SWF4VCsEFVQ+TjYFAgY2BBsxMS9tTnIHY2F4VGccHlw+C2YeBxYhbRE6XndtU3IWSWF4HSFLNVM1QAcfAQwUIgIwJhsoBTdaSS4qVAQNERsTGzIFIBMjPxQxMQciBDdESTUwESlhVhVyTmZKVUNkbVV1ODguEj4WHTg7GygFVghyCSMeIRonIho7fH5HU3IWSWF4VGdLVhVyAikJFA9kPxA4OyMoAHILSSY9ABMSFVo9ABQPGAwwKAZ9IC4uHD1YQEt4VGdLVhVyTmZKVUMtK1UnMToiBzdFSTUwESlhVhVyTmZKVUNkbVV1dHdtUz5ZCiA0VCkKG1ByU2Y6OjQBHyobFRoIIAlGBjY9Bg4FElAqM0xKVUNkbVV1dHdtU3IWSWF4HSFLNVM1QAcfAQwUIgIwJhsoBTdaSSA2EGcZE1g9GiMZWzAhIRA2IAciBDdEJSQuEStLF1s2TigLGAZkOR0wOl1tU3IWSWF4VGdLVhVyTmZKVUNkbQU2NTshWzRDByIsHSgFXhxyHCMHGhchPlsGMTsoECZmBjY9BgsOAFA+VA8EAwwvKCYwJiEoAXpYCCw9XWcOGFF7ZGZKVUNkbVV1dHdtU3IWSWE9GiNhVhVyTmZKVUNkbVV1dHdtUztQSQI+E2kqA0E9OzYNBwIgKCU6IzI/UzNYDWEqESoEAlAhQBMaEhElKRAFOyAoAR5THyQ0VCYFEhU8DysPVRcsKBtfdHdtU3IWSWF4VGdLVhVyTmZKVUM0LhQ5OH8rBjxVHSg3Gm9CVkc3AykeEBBqGAUyJjYpFgJZHiQqOCIdE1loJygcGgghHhAnIjI/WzxXBCRxVCIFEhxYTmZKVUNkbVV1dHdtU3IWSSQ2EE1LVhVyTmZKVUNkbVV1dHdtAz1BDDMRGiMODhVvTjYFAgY2BBsxMS9tWHIHY2F4VGdLVhVyTmZKVUNkbVU8Mnc9HCVTGwg2ECITVgtyTRYlIiYWEjsUGRIeUyZeDC94BCgcE0cbACIPDUN5bUR1MTkpeXIWSWF4VGdLVhVyTiMEEWlkbVV1dHdtUzdYDUt4VGdLVhVyTjILBghqOhQ8IH94WlgWSWF4ESkPfFA8Cm9gf05pbTQgIDhtMT1ZGjUrVG8/H1g3LScZHU9kCBQnOjI/MT1ZGjV0VAMEA1c+CwkMEw8tIxB8XiMsADkYGjE5AylDEEA8DTIDGg1sZH91dHdtBDpfBSR4ADUeExU2AUxKVUNkbVV1dD4rUxFQDm8ZATMEIlw/CwULBgtkIgd1FzEqXRNDHS4dFTUFE0cQASkZAUMrP1UWMjBjMidCBgU3ASUHE3o0CCoDGwZkOR0wOl1tU3IWSWF4VGdLVhU+ASULGUMwNBY6OzltTnJRDDUMDSQEGVt6R0xKVUNkbVV1dHdtU3JaBiI5GGcZE1g9GiMZVV5kKhAhAC4uHD1YOyQ1GzMOBR0mFyUFGg1tR1V1dHdtU3IWSWF4VC4NVkc3AykeEBBkOR0wOl1tU3IWSWF4VGdLVhVyTmZKHAVkDhMyehY4Bz1iACw9NyYYHhUzACJKBwYpIgEwJ3kYADdiACw9NyYYHhUmBiMEf0NkbVV1dHdtU3IWSWF4VGdLVhVyHiULGQ9sKwA7NyMkHDweQGEqESoEAlAhQBMZEDctIBAWNSQlSRtYHy4zERQOBEM3HG5DVQYqKVxfdHdtU3IWSWF4VGdLVhVyTiMEEWlkbVV1dHdtU3IWSWF4VGdLH1NyLSANWyIxORoQNSUjFiB0Bi4rAGcKGFFyHCMHGhchPlsAJzIIEiBYDDMaGygYAhUmBiMEf0NkbVV1dHdtU3IWSWF4VGdLVhVyHiULGQ9sKwA7NyMkHDweQGEqESoEAlAhQBMZECYlPxswJhUiHCFCUwg2AigAE2Y3HDAPB0ttbRA7MH5HU3IWSWF4VGdLVhVyTmZKVQYqKX91dHdtU3IWSWF4VGdLVhVyByBKNgUjYzQgIDgJHCdUBSQXEiEHH1s3TicEEUM2KBg6IDI+XRZZHCM0EQgNEFk7ACMpFBAsbQE9MTlHU3IWSWF4VGdLVhVyTmZKVUNkbVUlNzYhH3pQHC87AC4EGB17TjQPGAwwKAZ7EDg4ET5TJic+GC4FE3YzHS5QPA0yIh4wBzI/BTdEQWh4ESkPXz9yTmZKVUNkbVV1dHdtU3IWDC88fmdLVhVyTmZKVUNkbRA7MF1tU3IWSWF4VCIFEj9yTmZKVUNkbQE0JzxjBDNfHWkbEiBFNFo9HTIuEA8lNFxfdHdtUzdYDUs9GiNCfD9/Q2YrABcrbTY9NTkqFnJ6CCM9GE0fF0Y5QDUaFBQqZRMgOjQ5Gj1YQWhSVGdLVkI6ByoPVRc2OBB1MDhHU3IWSWF4VGcCEBURCCFENBYwIjY9NTkqFh5XCyQ0VDMDE1tYTmZKVUNkbVV1dHdtHz1VCC14AD4IGVo8TntKEgYwGQw2OzgjW3s8SWF4VGdLVhVyTmZKGQwnLBl1JjIgHCZTGmFlVCAOAmErDSkFGzEhIBohMSRlBytVBi42XU1LVhVyTmZKVUNkbVU8Mnc/Fj9ZHSQrVCYFEhUgCysFAQY3YzY9NTkqFh5XCyQ0VDMDE1tYTmZKVUNkbVV1dHdtU3IWSTE7FSsHXlMnACUeHAwqZVx1JjIgHCZTGm8bHCYFEVAeDyQPGVkNIwM6PzIeFiBADDNwVh5ZHRUBDTQDBRdmZFUwOjNkeXIWSWF4VGdLVhVyTiMEEWlkbVV1dHdtUzdYDUt4VGdLVhVyTjILBghqOhQ8IH9+Q3s8SWF4VCIFEj83ACJDf2lpYFUUISMiUxFeCC8/EWcoGVk9HDVgAQI3JlsmJDY6HXpQHC87AC4EGB17ZGZKVUMzJRw5MXc5ASdTSSU3fmdLVhVyTmZKHAVkDhMyehY4Bz11ASA2EyIoGVk9HDVKAQshI391dHdtU3IWSWF4VGcHGVYzAmYeDAArIht1aXcqFiZiECI3GylDXz9yTmZKVUNkbVV1dHchHDFXBWEqESoEAlAhTntKEgYwGQw2OzgjITdbBjU9B28fD1Y9AShDf0NkbVV1dHdtU3IWSSg+VDUOG1omCzVKFA0gbQcwOTg5FiEYKik5GiAONVo+ATQZVRcsKBtfdHdtU3IWSWF4VGdLVhVyTjYJFA8oZRMgOjQ5Gj1YQWh4BiIGGUE3HWgpHQIqKhAWOzsiASEMIC8uGywOJVAgGCMYXUpkKBsxfV1tU3IWSWF4VGdLVhU3ACJgVUNkbVV1dHcoHTY8SWF4VGdLVhUmDzUBWxQlJAF9Z2dkeXIWSWE9GiNhE1s2R0xgWE5kDAAhO3cAGjxfDiA1ETRhAlQhBWgZBQIzI10zITkuBztZB2lxfmdLVhUlBi8GEEMwPwAwdDMieXIWSWF4VGdLH1NyLSANWyIxORoYPTkkFDNbDBM5FyJLGUdyLSANWyIxORoYPTkkFDNbDBUqFSMOVkE6CyhgVUNkbVV1dHdtU3IWBS47FStLFVogC2ZXVTEhPRk8NzY5FjZlHS4qFSAOTHM7ACIsHBE3OTY9PTspW3B1BjM9Vm5hVhVyTmZKVUNkbVV1PTFtED1EDGEsHCIFfBVyTmZKVUNkbVV1dHdtU3JaBiI5GGcZE1gACzdKSEMnIgcwbhEkHTZwADMrAAQDH1k2RmQ4EA4rORAHMSY4FiFCS2hSVGdLVhVyTmZKVUNkbVV1dD4rUyBTBBM9BWcfHlA8ZGZKVUNkbVV1dHdtU3IWSWF4VGdLH1NyLSANWyIxORoYPTkkFDNbDBM5FyJLAl03AExKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmYGGgAlIVUnNTQoICZXGzV4SWcZE1gACzdQMwoqKTM8JiQ5MDpfBSVwVgoCGFw1DysPJwInKCYwJiEkEDcYOjU5BjNJXz9yTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhU+ASULGUM2LBYwETkpU28WGyQ1JiIaTHM7ACIsHBE3OTY9PTspW3B7AC8xEyYGE2czDSM5EBEyJBYwehIjF3AfY2F4VGdLVhVyTmZKVUNkbVV1dHdtU3IWSSg+VDUKFVABGicYAUMlIxF1JjYuFgFCCDMsTg4YNx1wPCMHGhchCwA7NyMkHDwUQGEsHCIFfBVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmYaFgIoIV0zITkuBztZB2lxVDUKFVABGicYAVkNIwM6PzIeFiBADDNwXWcOGFF7ZGZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTiMEEWlkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUMwLAY+eiAsGiYeWmhSVGdLVhVyTmZKVUNkbVV1dHdtU3IWSWF4HSFLBFQxCwMEEUMlIxF1JjYuFhdYDXsRBwZDVGc3AykeECUxIxYhPTgjUXsWHSk9Gk1LVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyHiULGQ9sKwA7NyMkHDweQGEqFSQOM1s2VA8EAwwvKCYwJiEoAXofSSQ2EG5hVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLE1s2ZGZKVUNkbVV1dHdtU3IWSWF4VGdLE1s2ZGZKVUNkbVV1dHdtU3IWSWF4VGdLH1NyLSANWyIxORoYPTkkFDNbDBUqFSMOVkE6CyhgVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKGQwnLBl1ICUsFzdlHSAqAGdWVkc3AxQPBFkCJBsxEj4/ACZ1ASg0EG9JO1w8ByELGAYQPxQxMQQoASRfCiR2JzMKBEFwR0xKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmYGGgAlIVUhJjYpFhdYDWFlVDUOG2c3H3wsHA0gCxwnJyMOGztaDWl6OS4FH1IzAyM+BwIgKCYwJiEkEDcYLC88Vm5hVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLH1NyGjQLEQYXORQnIHcsHTYWHTM5ECI4AlQgGnwjBiJsbycwOTg5FhRDByIsHSgFVBxyGi4PG2lkbVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1JDQsHz4eDzQ2FzMCGVt6R2YeBwIgKCYhNSU5SRtYHy4zERQOBEM3HG5DVQYqKVxfdHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1MTkpeXIWSWF4VGdLVhVyTmZKVUNkbVV1dHdtUyZXGip2AyYCAh1hR0xKVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmYDE0MwPxQxMRIjF3JXByV4ADUKElAXACJQPBAFZVcHMToiBzdwHC87AC4EGBd7TjICEA1ObVV1dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dCcuEj5aQSctGiQfH1o8Rm9KARElKRAQOjN3OjxABio9JyIZAFAgRm9KEA0gZH91dHdtU3IWSWF4VGdLVhVyTmZKVUNkbVUwOjNHU3IWSWF4VGdLVhVyTmZKVUNkbVUwOjNHU3IWSWF4VGdLVhVyTmZKVQYqKX91dHdtU3IWSWF4VGcOGFFYTmZKVUNkbVUwOjNHU3IWSWF4VGcfF0Y5QDELHBdsfEV8XndtU3JTByVSESkPXz9YQ2tKIgIoJiYlMTIpU3QWIzQ1BBcEAVAgTioFGhNOHwA7BzI/BTtVDG8QESYZAlc3DzJQNgwqIxA2IH8rBjxVHSg3Gm9CfBVyTmYGGgAlIVU2PDY/U28WJS47FSs7GlQrCzRENgslPxQ2IDI/eXIWSWExEmcIHlQgTjICEA1ObVV1dHdtU3JaBiI5GGcDA1hyU2YJHQI2dzM8OjMLGiBFHQIwHSsPOVMRAicZBktmBQA4NTkiGjYUQEt4VGdLVhVyTi8MVQsxIFUhPDIjeXIWSWF4VGdLVhVyTi8MVQsxIFsCNTsmICJTDCV4CnpLNVM1QBELGQgXPRAwMHc5GzdYSSktGWk8F1k5PTYPEAdkcFUWMjBjJDNaAhIoESIPVlA8CkxKVUNkbVV1dHdtU3JfD2EwASpFPEA/HhYFAgY2bQtodBQrFHx8HCwoJCgcE0dyGi4PG0MsOBh7HiIgAwJZHiQqVHpLNVM1QAwfGBMUIgIwJmxtGydbRxQrEQ0eG0UCATEPB0N5bQEnITJtFjxSY2F4VGdLVhVyCygOf0NkbVUwOjNHFjxSQEtSWWpLOFoxAi8aVQ8rIgVfBiIjIDdEHyg7EWk4AlAiHiMOTyArIxswNyNlFSdYCjUxGylDXz9yTmZKHAVkDhMyehkiED5fGWEsHCIFfBVyTmZKVUNkIRo2NTttEDpXG2FlVAsEFVQ+PioLDAY2YzY9NSUsECZTG0t4VGdLVhVyTi8MVQAsLAd1ID8oHVgWSWF4VGdLVhVyTmYMGhFkEll1JDY/B3JfB2ExBCYCBEZ6DS4LB1kDKAERMSQuFjxSCC8sB29CXxU2AUxKVUNkbVV1dHdtU3IWSWF4HSFLBlQgGnwjBiJsbzc0JzIdEiBCS2h4AC8OGD9yTmZKVUNkbVV1dHdtU3IWSWF4VDcKBEF8LScENgwoIRwxMXdwUzRXBTI9fmdLVhVyTmZKVUNkbVV1dHcoHTY8SWF4VGdLVhVyTmZKEA0gR1V1dHdtU3IWDC88fmdLVhU3ACJgEA0gZH9feXptOjxQAC8xACJLPEA/Hkw/BgY2BBslISMeFiBAACI9Wg0eG0UACzcfEBAwdzY6OjkoECYeDzQ2FzMCGVt6R0xKVUNkJBN1FzEqXRtYDwstGTdLAl03AExKVUNkbVV1dDsiEDNaSSIwFTVLSxUeASULGTMoLAwwJnkOGzNECCIsETVhVhVyTmZKVUMtK1U2PDY/UyZeDC9SVGdLVhVyTmZKVUNkIRo2NTttGydbSXx4Fy8KBA8UBygOMwo2PgEWPD4hFx1QKi05BzRDVH0nAycEGgogb1xfdHdtU3IWSWF4VGdLH1NyBjMHVRcsKBtfdHdtU3IWSWF4VGdLVhVyTi4fGFkHJRQ7MzIeBzNCDGkdGjIGWH0nAycEGgogHgE0IDIZCiJTRwstGTcCGFJ7ZGZKVUNkbVV1dHdtUzdYDUt4VGdLVhVyTiMEEWlkbVV1MTkpeTdYDWhSfmpGVnQ8Gi9KNCUPRxk6NzYhUzNQAgI3GikOFUE7AShKSEMqJBlfIDY+GHxFGSAvGm8NA1sxGi8FG0ttR1V1dHc6GztaDGEsBjIOVlE9ZGZKVUNkbVV1PTFtMDRRRwA2AC4qMH5yGi4PG2lkbVV1dHdtU3IWSWE0GyQKGhUEBzQeAAIoGAYwJndwUzVXBCRiMyIfJVAgGC8JEEtmGxwnICIsHwdFDDN6XU1LVhVyTmZKVUNkbVU0MjwOHDxYDCIsHSgFVghyCScHEFkDKAEGMSU7GjFTQWMIGCYSE0chTG9EOQwnLBkFODY0FiAYICU0ESNRNVo8ACMJAUsiOBs2ID4iHXofY2F4VGdLVhVyTmZKVUNkbVUDPSU5BjNaPDI9Bn0oF0UmGzQPNgwqOQc6ODsoAXofY2F4VGdLVhVyTmZKVUNkbVUDPSU5BjNaPDI9Bn0oGlwxBQQfARcrI0d9AjIuBz1EW282ETBDXxxYTmZKVUNkbVV1dHdtFjxSQEt4VGdLVhVyTiMGBgZObVV1dHdtU3IWSWF4HSFLF1M5LSkEGwYnORw6Onc5GzdYY2F4VGdLVhVyTmZKVUNkbVU0MjwOHDxYDCIsHSgFTHE7HSUFGw0hLgF9fV1tU3IWSWF4VGdLVhVyTmZKFAUvDho7OjIuBztZB2FlVCkCGj9yTmZKVUNkbVV1dHcoHTY8SWF4VGdLVhU3ACJgVUNkbVV1dHc5EiFdRzY5HTNDQxxYTmZKVQYqKX8wOjNkeVgbRGEeGD5LBUwhGiMHfw8rLhQ5dDEhChBZDTgfDTUEWhU0Aj8oGgc9GxA5OzQkBysWVGE2HStHVls7AkweFBAvYwYlNSAjWzRDByIsHSgFXhxYTmZKVRQsJBkwdCM/BjcWDS5SVGdLVhVyTmYDE0MHKxJ7Ejs0NjxXCy09EGcfHlA8ZGZKVUNkbVV1dHdtUz5ZCiA0VCQDF0dyU2YmGgAlISU5NS4oAXx1ASAqFSQfE0dYTmZKVUNkbVV1dHdtGjQWCik5BmcfHlA8ZGZKVUNkbVV1dHdtU3IWSWE0GyQKGhUgASkeVV5kLh00Jm0LGjxSLygqBzMoHlw+Cm5IPRYpLBs6PTMfHD1COSAqAGVCfBVyTmZKVUNkbVV1dHdtU3JfD2EqGygfVkE6CyhgVUNkbVV1dHdtU3IWSWF4VGdLVhU7CGYEGhdkKxksFjgpChVPGy54AC8OGD9yTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhU0Aj8oGgc9CgwnO3dwUxtYGjU5GiQOWFs3GW5INwwgNDIsJjhvWlgWSWF4VGdLVhVyTmZKVUNkbVV1dHdtU3JQBTgaGyMSMUwgAWg6VV5kdBBhXndtU3IWSWF4VGdLVhVyTmZKVUNkbVV1dDEhChBZDTgfDTUEWHgzFhIFBxIxKFVodAEoECZZG3J2GiIcXgw3V2pKTAZ9YVVsMW5keXIWSWF4VGdLVhVyTmZKVUNkbVV1dHdtUzRaEAM3ED4sD0c9QAUsBwIpKFVodCUiHCYYKgcqFSoOfBVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLVlM+FwQFERoDNAc6egcsATdYHWFlVDUEGUFYTmZKVUNkbVV1dHdtU3IWSWF4VGcOGFFYTmZKVUNkbVV1dHdtU3IWSWF4VGcCEBU8ATJKEw89DxoxLQEoHz1VADUhVDMDE1tYTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhVyCCoTNwwgNCMwODguGiZPSXx4PSkYAlQ8DSNEGwYzZVcXOzM0JTdaBiIxAD5JXz9yTmZKVUNkbVV1dHdtU3IWSWF4VGdLVhU0Aj8oGgc9GxA5OzQkBysYPyQ0GyQCAkxyU2Y8EAAwIgdmei0oAT08SWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWDy0hNigPD2M3AikJHBc9Yzg0LBEiATFTSXx4IiIIAlogXWgEEBRsdBBseHd0FmsaSXg9TW5hVhVyTmZKVUNkbVV1dHdtU3IWSWF4VGdLEFkrLCkODDUhIRo2PSM0XQJXGyQ2AGdWVkc9ATJgVUNkbVV1dHdtU3IWSWF4VGdLVhU3ACJgVUNkbVV1dHdtU3IWSWF4VGdLVhU+ASULGUMnLBh1aXcaHCBdGjE5FyJFNUAgHCMEASAlIBAnNV1tU3IWSWF4VGdLVhVyTmZKVUNkbRk6NzYhUzZfG2FlVBEOFUE9HHVEDwY2In91dHdtU3IWSWF4VGdLVhVyTmZKVQoibSAmMSUEHSJDHRI9BjECFVBoJzUhEBoAIgI7fBIjBj8YIiQhNygPExsFR2YeHQYqbRE8JndwUzZfG2FzVCQKGxsRKDQLGAZqARo6PwEoECZZG2E9GiNhVhVyTmZKVUNkbVV1dHdtU3IWSWExEmc+BVAgJygaABcXKAcjPTQoSRtFIiQhMCgcGB0XADMHWyghNDY6MDJjIHsWHSk9GmcPH0dyU2YOHBFkYFU2NTpjMBRECCw9WgsEGV4ECyUeGhFkKBsxXndtU3IWSWF4VGdLVhVyTmZKVUNkJBN1ASQoARtYGTQsJyIZAFwxC3wjBighNDE6IzllNjxDBG8TET4oGVE3QAdDVRcsKBt1MD4/U28WDSgqVGpLFVQ/QAUsBwIpKFsHPTAlBwRTCjU3BmcOGFFYTmZKVUNkbVV1dHdtU3IWSWF4VGcCEBUHHSMYPA00OAEGMSU7GjFTUwgrPyISMlolAG4vGxYpYz4wLRQiFzcYLWh4AC8OGBU2BzRKSEMgJAd1f3cuEj8YKgcqFSoOWGc7CS4eIwYnORondDIjF1gWSWF4VGdLVhVyTmZKVUNkbVV1dD4rUwdFDDMRGjceAmY3HDADFgZ+BAYeMS4JHCVYQQQ2ASpFPVArLSkOEE0XPRQ2MX5tBzpTB2E8HTVLSxU2BzRKXkMSKBYhOyV+XTxTHmloWGdaWhViR2YPGwdObVV1dHdtU3IWSWF4VGdLVhVyTmYDE0MRPhAnHTk9BiZlDDMuHSQOTHwhJSMTMQwzI10QOiIgXRlTEAI3ECJFOlA0GhUCHAUwZFUhPDIjUzZfG2FlVCMCBBV/ThAPFhcrP0Z7OjI6W2IaSXB0VHdCVlA8CkxKVUNkbVV1dHdtU3IWSWF4VGdLVlw0TiIDB00JLBI7PSM4FzcWV2FoVDMDE1tyCi8YVV5kKRwnegIjGiYWQ2EbEiBFMFkrPTYPEAdkKBsxXndtU3IWSWF4VGdLVhVyTmZKVUNkKxksFjgpCgRTBS47HTMSWGM3AikJHBc9bUh1MD4/eXIWSWF4VGdLVhVyTmZKVUNkbVV1Mjs0MT1SEAYhBihFNXMgDysPVV5kLhQ4ehQLATNbDEt4VGdLVhVyTmZKVUNkbVV1MTkpeXIWSWF4VGdLVhVyTiMEEWlkbVV1dHdtUzdaGiRSVGdLVhVyTmZKVUNkJBN1Mjs0MT1SEAYhBihLAl03AGYMGRoGIhEsEy4/HGhyDDIsBigSXhxpTiAGDCErKQwSLSUiU28WByg0VCIFEj9yTmZKVUNkbVV1dHckFXJQBTgaGyMSIFA+ASUDARpkOR0wOncrHyt0BiUhIiIHGVY7Gj9QMQY3OQc6LX9kSHJQBTgaGyMSIFA+ASUDARpkcFU7PTttFjxSY2F4VGdLVhVyCygOf0NkbVV1dHdtBzNFAm8vFS4fXgV8XnVDf0NkbVUwOjNHFjxSQEtSWWpLJUEzGjVKABMgLAEwdDsiHCI8HSArH2kYBlQlAG4MAA0nORw6On9keXIWSWEvHC4HExUmHDMPVQcrR1V1dHdtU3IWBS47FStLAkwxASkEVV5kKhAhAC4uHD1YQWhSVGdLVhVyTmYGGgAlIVU2PDY/U28WJS47FSs7GlQrCzRENgslPxQ2IDI/eXIWSWF4VGdLGloxDypKBwwrOVVodDQlEiAWCC88VCQDF0doKC8EESUtPwYhFz8kHzYeSwktGSYFGVw2PCkFATMlPwF3fV1tU3IWSWF4VCsEFVQ+Ti4fGEN5bRY9NSVtEjxSSSIwFTVRMFw8CgADBxAwDh08ODMCFRFaCDIrXGUjA1gzACkDEUFtR1V1dHdtU3IWGSI5GCtDEEA8DTIDGg1sZFU5NjsOEiFeUxI9ABMODkF6TAULBgtkd1V3enk5HCFCGyg2E28ME0ERDzUCXUptZFUwOjNkeXIWSWF4VGdLBlYzAipCExYqLgE8OzllWnJaCy0RGiQEG1BoPSMeIQY8OV13HTkuHD9TSXt4VmlFEVAmJygJGg4hZVx8dDIjF3s8SWF4VGdLVhUiDScGGUsiOBs2ID4iHXofSS06GBMSFVo9AHw5EBcQKA0hfHUZCjFZBi94TmdJWBt6Gj8JGgwqbRQ7MHc5CjFZBi92OiYGExU9HGZIOwwwbRM6ITkpUXsfSSQ2EG5hVhVyTmZKVUM0LhQ5OH8rBjxVHSg3Gm9CVlkwAhYFBlkXKAEBMS85W3BmBjIxAC4EGBVoTmREW0s2IhohdDYjF3JCBjIsBi4FER0ECyUeGhF3YxswI38gEiZeRyc0GygZXkc9ATJEJQw3JAE8OzljK3saSSw5AC9FEFk9ATRCBwwrOVsFOyQkBztZB28BXWtLG1QmBmgMGQwrP10nOzg5XQJZGigsHSgFWG97R29KGhFkbzt6FXVkWnJTByVxfmdLVhVyTmZKBQAlIRl9MiIjECZfBi9wXU1LVhVyTmZKVUNkbVU5OzQsH3JCECI3GylLSxU1CzI+DAArIht9fV1tU3IWSWF4VGdLVhU+ASULGUM0OAc2PHdwUyZPCi43GmcKGFFyGj8JGgwqdzM8OjMLGiBFHQIwHSsPXhcCGzQJHQI3KAZ3fV1tU3IWSWF4VGdLVhU+ASULGUMnIgA7IHdwU2I8SWF4VGdLVhVyTmZKHAVkPQAnNz9tBzpTB0t4VGdLVhVyTmZKVUNkbVV1Mjg/Uw0aSSAqESZLH1tyBzYLHBE3ZQUgJjQlSRVTHQIwHSsPBFA8Rm9DVQcrR1V1dHdtU3IWSWF4VGdLVhVyTmZKHAVkLAcwNW0EABMeSwc3GCMOBBd7TikYVQI2KBRvHSQMW3B7BiU9GGVCVkE6CyhgVUNkbVV1dHdtU3IWSWF4VGdLVhVyTmZKFgwxIwF1aXcuHCdYHWFzVHZhVhVyTmZKVUNkbVV1dHdtU3IWSWE9GiNhVhVyTmZKVUNkbVV1dHdtUzdYDUt4VGdLVhVyTmZKVUMhIxFfdHdtU3IWSWF4VGdLGlc+KDQfHBc3dyYwIAMoCyYeSwMtHSsPH1s1HWZQVUFqYwE6JyM/GjxRQSI3ASkfXxxYTmZKVUNkbVUwOjNkeXIWSWF4VGdLBlYzAipCExYqLgE8OzllWnJaCy0QESYHAl1oPSMeIQY8OV13HDIsHyZeSXt4VmlFXl0nA2YLGwdkORomICUkHTUeBCAsHGkNGlo9HG4CAA5qBRA0OCMlWnsYR2N3VmlFAlohGjQDGwRsIBQhPHkrHz1ZG2kwASpFO1QqJiMLGRcsZFx1OyVtURwZKGNxXWcOGFF7ZGZKVUNkbVV1JDQsHz4eDzQ2FzMCGVt6R2YGFw8THk8GMSMZFipCQWMPFSsAJUU3CyJKT0NmY1shOyQ5ATtYDmkbEiBFIVQ+BRUaEAYgZFx1MTkpWlgWSWF4VGdLVkUxDyoGXQUxIxYhPTgjW3sWBSM0PhdRJVAmOiMSAUtmBwA4JAciBDdESXt4VmlFAlohGjQDGwRsDhMyeh04HiJmBjY9Bm5CVlA8Cm9gVUNkbVV1dHc9EDNaBWk+ASkIAlw9AG5DVQ8mITInNSEkBysMOiQsICITAh1wKTQLAwowNFVvdHVjXSZZGjUqHSkMXnY0CWgtBwIyJAEsfX5tFjxSQEt4VGdLVhVyTjILBghqOhQ8IH99XWcfY2F4VGcOGFFYCygOXGlOYFh1EQQdUxpTBTE9BjRhGloxDypKExYqLgE8OzltEjZSISg/HCsCEV0mRikIH09kLho5OyVkeXIWSWExEmcEFF9yDygOVQ0rOVU6Nj13NTtYDQcxBjQfNV07AiJCVzp2JjAGBHVkUyZeDC9SVGdLVhVyTmYGGgAlIVU9OHdwUxtYGjU5GiQOWFs3GW5IPQojJRk8Mz85UXs8SWF4VGdLVhU6AmgkFA4hbUh1dg5/GBdlOWNSVGdLVhVyTmYCGU0CJBk5FzghHCAWVGE7GysEBD9yTmZKVUNkbR05ehg4Bz5fByQbGysEBBVvTiUFGQw2R1V1dHdtU3IWAS12Mi4HGmEgDygZBQI2KBs2LXdwU2IYXkt4VGdLVhVyTi4GWywxORk8OjIZATNYGjE5BiIFFUxyU2Zaf0NkbVV1dHdtGz4YOSAqESkfVghyASQAf0NkbVUwOjNHFjxSY0s0GyQKGhU0GygJAQorI1UnMToiBTd+ACYwGC4MHkF6ASQAXGlkbVV1PTFtHDBcSTUwESlhVhVyTmZKVUMoIhY0OHclH3ILSS46Hn0tH1s2KC8YBhcHJRw5MH9vKmBdLBIIVm5hVhVyTmZKVUMtK1U9OHc5GzdYSSk0TgMOBUEgAT9CXEMhIxFfdHdtUzdYDUs9GiNhfBh/TgM5JUMUIRQsMSU+Uz5ZBjFSACYYHRshHicdG0siOBs2ID4iHXofY2F4VGccHlw+C2YeBxYhbRE6XndtU3IWSWF4HSFLNVM1QAM5JTMoLAwwJiRtBzpTB0t4VGdLVhVyTmZKVUMiIgd1C3ttAz5XECQqVC4FVlwiDy8YBksUIRQsMSU+SRVTHRE0FT4OBEZ6R29KEQxObVV1dHdtU3IWSWF4VGdLVlw0TjYGFBohP1UraXcBHDFXBRE0FT4OBBUmBiMEf0NkbVV1dHdtU3IWSWF4VGdLVhVyAikJFA9kLh00JndwUyJaCDg9BmkoHlQgDyUeEBFObVV1dHdtU3IWSWF4VGdLVhVyTmYDE0MnJRQndCMlFjw8SWF4VGdLVhVyTmZKVUNkbVV1dHdtU3IWCCU8PC4MHlk7CS4eXQAsLAd5dBQiHz1EWm8+BigGJHIQRnZGVVFxeFl1ZH5keXIWSWF4VGdLVhVyTmZKVUNkbVV1MTkpeXIWSWF4VGdLVhVyTmZKVUMhIxFfdHdtU3IWSWF4VGdLE1s2ZGZKVUNkbVV1MTs+FlgWSWF4VGdLVhVyTmYMGhFkEll1JDssCjdESSg2VC4bF1wgHW46GQI9KAcmbhAoBwJaCDg9BjRDXxxyCilgVUNkbVV1dHdtU3IWSWF4VC4NVkU+Dz8PB0M6cFUZOzQsHwJaCDg9BmcfHlA8ZGZKVUNkbVV1dHdtU3IWSWF4VGdLGloxDypKFgslP1VodCchEitTG28bHCYZF1YmCzRgVUNkbVV1dHdtU3IWSWF4VGdLVhU7CGYJHQI2bQE9MTltATdbBjc9PC4MHlk7CS4eXQAsLAd8dDIjF1gWSWF4VGdLVhVyTmZKVUNkKBsxXndtU3IWSWF4VGdLVlA8CkxKVUNkbVV1dDIjF1gWSWF4VGdLVkEzHS1EAgItOV1nfV1tU3IWDC88fiIFEhxYZGtHVSYXHVUWNSQlUxZEBjF4GCgEBj8mDzUBWxA0LAI7fDE4HTFCAC42XG5hVhVyTjECHA8hbQEnITJtFz08SWF4VGdLVhU7CGYpEwRqCCYFFzY+GxZEBjF4AC8OGD9yTmZKVUNkbVV1dHchHDFXBWE7FTQDMkc9HjUsGg8gKAd1aXcaHCBdGjE5FyJRMFw8CgADBxAwDh08ODNlURFXGikcBigbBRd7ZGZKVUNkbVV1dHdtUztQSSI5By8vBFoiHQAFGQchP1UhPDIjeXIWSWF4VGdLVhVyTmZKVUMiIgd1C3ttHDBcSSg2VC4bF1wgHW4JFBAsCQc6JCQLHD5SDDNiMyIfNV07AiIYEA1sZFx1MDhHU3IWSWF4VGdLVhVyTmZKVUNkbVU8MnciETgMIDIZXGUpF0Y3PicYAUFtbQE9MTlHU3IWSWF4VGdLVhVyTmZKVUNkbVV1dHdtEjZSISg/HCsCEV0mRikIH09kDho5OyV+XTREBiwKMwVDRABnQmZYQFZobUV8fV1tU3IWSWF4VGdLVhVyTmZKVUNkbRA7MF1tU3IWSWF4VGdLVhVyTmZKEA0gR1V1dHdtU3IWSWF4VCIFEj9yTmZKVUNkbRA5JzJHU3IWSWF4VGdLVhVyCCkYVTxobRo3PnckHXJfGSAxBjRDIVogBTUaFAAhdzIwIBMoADFTByU5GjMYXhx7TiIFf0NkbVV1dHdtU3IWSWF4VGcCEBU9DCxQMwoqKTM8JiQ5MDpfBSVwVh5ZHXABPmRDVRcsKBtfdHdtU3IWSWF4VGdLVhVyTmZKVUM2KBg6IjIFGjVeBSg/HDNDGVc4R0xKVUNkbVV1dHdtU3IWSWF4ESkPfBVyTmZKVUNkbVV1dDIjF1gWSWF4VGdLVlA8CkxKVUNkbVV1dCMsADkYHiAxAG9ZXz9yTmZKEA0gRxA7MH5HeX8bSQQLJGc/D1Y9AShKGQwrPX8hNSQmXSFGCDY2XCEeGFYmBykEXUpObVV1dCAlGj5TSTUqASJLElpYTmZKVUNkbVU8MncOFTUYLBIIID4IGVo8TjICEA1ObVV1dHdtU3IWSWF4GCgIF1lyGj8JGgwqbUh1MzI5JytVBi42XG5hVhVyTmZKVUNkbVV1PTFtBytVBi42VDMDE1tYTmZKVUNkbVV1dHdtU3IWSSA8EA8CEV0+ByECAUswNBY6OzlhUxFZBS4qR2kNBFo/PAEoXVNobUV5dGV4RnsfY2F4VGdLVhVyTmZKVQYqKX91dHdtU3IWSSQ0ByJhVhVyTmZKVUNkbVV1Mjg/Uw0aSS46HmcCGBU7HicDBxBsGhonPyQ9EjFTUwY9AAQDH1k2HCMEXUptbRE6XndtU3IWSWF4VGdLVhVyTmYDE0MrLx97GjYgFmhQAC88XGU/D1Y9AShIXEMwJRA7XndtU3IWSWF4VGdLVhVyTmZKVUNkPxA4OyEoOztRAS0xEy8fXlowBG9gVUNkbVV1dHdtU3IWSWF4VCIFEj9yTmZKVUNkbVV1dHcoHTY8SWF4VGdLVhU3ACJgVUNkbVV1dHc5EiFdRzY5HTNDRRxYTmZKVQYqKX8wOjNkeVh6ACMqFTUSTHs9Gi8MDEtmHhA5OHcsUx5TBC42VBQIBFwiGmYGGgIgKBF0dCttKmBdSRI7Bi4bAhd7ZA=='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true } })
