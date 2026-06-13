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

local __k = 'G0hF9Mdt9ApKwKUjWMvyZ3Gj'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true } })
