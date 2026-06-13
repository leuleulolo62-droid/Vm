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

local __k = 'E5VVq25HN3w6Iht1kIan5pfF'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
