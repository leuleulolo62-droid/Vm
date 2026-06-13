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

local __k = 'NeX5hjRP0hAG74UoPDTBpo80'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
