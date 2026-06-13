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

local __k = 'IE0KZCqxTaVyAf7q3YV6hPxT'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-9Q9vPR613XQH
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, watermark = 'Y2k-9Q9vPR613XQH', neuterAC = true, antiSpy = { kick = true, halt = true } })
