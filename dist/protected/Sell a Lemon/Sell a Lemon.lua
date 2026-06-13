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

local __k = 'ky7cOkL9dIcFj6ZenlFlrUO6'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, antiSpy = { kick = true, halt = true } })
