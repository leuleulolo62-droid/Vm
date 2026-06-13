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

local __k = 'f00FpfHHsaJLJemrhVQbX0UB'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-oG7hh6NfqWjB
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, watermark = 'Y2k-oG7hh6NfqWjB', neuterAC = true, antiSpy = { kick = true, halt = true } })
