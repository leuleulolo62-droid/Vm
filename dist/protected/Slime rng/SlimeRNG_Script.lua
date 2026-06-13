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

local __k = 'FEN0yJppO3vXrMgfHsjl2BFZ'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
