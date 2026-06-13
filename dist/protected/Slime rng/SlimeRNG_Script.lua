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

local __k = 'NCINxfWKZUqSUUA4098GbXkY'
local __p = 'Y24SFXJGd2t6Bh06ODBhZn5+GA8XOkt0bhp7JVg1NDkzJQVZdXVhFGBVWSQHEQ9jbnp7eklQY3lrYENhbGNxPhAZGGc3EVF5ASE6JxwPNiV6fShhPnUUfRkzZRpoUgI/biQsOh8DOT1yfF8AOTwsUWJ3fwsNOQ88KmM9Jh0Idzk/IQQhO3UkWlQzXyIWPw43OGtgYCsKPiY/Bz8UGTogUFVdGHpCLBksK0lDY1VJeGsJECMFHBYEZzpVVyQDNEsJIiIwKwoVd3Z6MhA+MG8GUURqXTUUMQg8ZmEZIhkfMjkpd1hZOToiVVwZaiISNAI6LzcsKisSODk7MhRzaHUmVV1cAgAHLDg8PDUgLR1OdRk/JR06NjQ1UVRqTCgQOQw8bGpDIhcFNid6BwQ9BjAzQllaXWdfeAw4IyZzCR0SBC4oIxgwMH1jZkVXayIQLgI6K2FgRBQJNCo2dSY8Jz4yRFFaXWdfeAw4IyZzCR0SBC4oIxgwMH1jY19LUzQSOQg8bGpDIhcFNid6GR4wNDkRWFFAXTVCZUsJIiIwKwoVeQc1NhA/BTkgTVVLMk1PdUR2bhYAbjQvFRkbByhZOToiVVwZSiISN0tkbmEhOgwWJHF1egMyInsmXURRTSUXKw4rLSwnOh0II2U5Ohx8DGcqZ1NLUTcWGgo6JXELLxsNeAQ4Jhg3PDQvYVkWVSYLNkR7RC8mLRkKdwczNwMyJyxhCRBVVyYGKx8rJy0uZh8HOi5gHQUnJRIkQBhLXTcNeEV3bmEFJxoUNjkjex0mNHdoHRgQMisNOwo1bhchKxUDGio0NBY2J3V8FFxWWSMRLBkwICRhKRkLMnESIQUjEjA1HEJcSChCdkV5bCItKhcIJGQOPRQ+MBggWlFeXTVMNB44bGpgZlFsOyQ5NB1zBjQ3UX1YViYFPRl5c2MlIRkCJD8oPB80fTIgWVUDcDMWKCw8Oms7KwgJd2V0dVMyMTEuWkMWayYUPSY4ICIuKwpIOz47d1h6fXxLPlxWWyYOeDwwICcmOVhbdwczNwMyJyx7d0JcWTMHDwI3Kiw+ZgNsd2t6dSU6ITkkFA0ZGh5QM0sROyFpMlg1OyI3MFEBGxJjGDoZGGdCGw43OiY7bkVGIzkvMF1ZdXVhFHFMTCgxMAQubn5pOgoTMmdQdVFzdQEgVmBYXCMLNgx5c2NxYnJGd2t6GBQ9IBMgUFVtUSoHeFZ5fm17RAVPXUF3eF58dQEAdmMzVCgBOQd5GiIrPVhbdzBQdVFzdRggXV4ZBWc1MQU9ITRzDxwCAyo4fVMeNDwvFhwZGjcDOwA4KSZrZ1Rsd2t6dSQjMicgUFVKGHpCDwI3Kiw+dDkCMx87N1lxACUmRlFdXTRAdEt7PSsgKxQCdWJ2X1FzdXUSQFFNS2dfeDwwICcmOUInMy8ONBN7dwY1VURKGmtCeg84OiIrLwsDdWJ2X1FzdXUVUVxcSCgQLEtkbhQgIBwJIHEbMRUHNDdpFmRcVCISNxktbG9pbBUJIS53MRgyMjovVVwUCmVLdGF5bmNpAxcQMiY/OwVzaHUWXV5dVzBYGQ89GiIrZlorOD0/OBQ9IXdtFBJYWzMLLgItN2FgYnJGd2t6BhQnITwvU0MZBWc1MQU9ITRzDxwCAyo4fVMAMCE1XV5eS2VOeEkqKzc9JxYBJGlzeXsuX19sGR8WGAAjFS55AwwNGzQjBEE2OhIyOXUnQV5aTC4NNksqLyUsHB0XIiIoMFl9e3toPhAZGGcONwg4ImMoPB8Vd3Z6Ll99eyhLFBAZGCsNOwo1biwiYlgUMjgvOQVzaHUxV1FVVG8ELQU6OiomIFBPXWt6dVFzdXVhWF9aWStCNwkzbn5pHB0WOyI5NAU2MQY1W0JYXyJoeEt5bmNpblgAODl6Cl1zJXUoWhBQSCYLKhhxLzEuPVFGMyRQdVFzdXVhFBAZGGdCNwkzbn5pIRoMbRw7PAUVOicCXFlVXG8SdEtqZ0lpblhGd2t6dVFzdXUoUhBXVzNCNwkzbjchKxZGMjkoOgN7dxsuQBBfVzIMPFF5bG1nPlFGMiU+X1FzdXVhFBAZXSkGUkt5bmNpblhGJS4uIAM9dSckRUVQSiJKNwkzZ0lpblhGMiU+fHtzdXVhRlVNTTUMeAQybiInKlgUMjgvOQVzOidhWllVMiIMPGFTIiwqLxRGEyouNCI2JyMoV1UZGGdCeEt5bmNpblhbdzg7MxQBMCQ0XUJcEGUyOQgyLyQsPVpKd2keNAUyBjAzQllaXWVLUgc2LSIlbioJOycJMAMlPDYkd1xQXSkWeEt5bmNpc1gVNi0/BxQiIDwzURgbaygXKgg8bG9pbD4DNj8vJxQgd3lhFmJWVCtAdEt7HCwlIisDJT0zNhQQOTwkWkQbEU0ONwg4ImMAIA4DOT81JwgAMCc3XVNceysLPQUtbn5pPRkAMhk/JAQ6JzBpFmNWTTUBPUl1bmEPKxkSIjk/JlN/dXcIWkZcVjMNKhJ7YmNrBxYQMiUuOgMqBjAzQllaXQQOMQ43OmFgRBQJNCo2dSQjMicgUFVqXTUUMQg8DS8gKxYSd2t6aFEgNDMkZlVITS4QPUN7HSw8PBsDdWd6dzc2NCE0RlVKGmtCej4pKTEoKh0VdWd6dyQjMicgUFVqXTUUMQg8DS8gKxYSdWJQOR4wNDlhZlVbUTUWMDg8PDUgLR0lOyI/OwVzdXV8FENYXiIwPRosJzEsZlo1OD4oNhRxeXVjclVYTDIQPRh7YmNrHB0EPjkuPVN/dXcTUVJQSjMKCw4rOCoqKzsKPi40IVN6XzkuV1FVGBUHOgIrOisaKwoQPig/AAU6OSZhFBAZBWcROQ08HCY4OxEUMmN4Bh4mJzYkFhwZGgEHOR8sPCY6bFRGdRk/NxghIT1jGBAbaiIAMRktJhAsPA4PNC4PIRg/JndoPlxWWyYOeCc2ITcaKwoQPig/Fh06MDs1FBAZGGdCZUsqLyUsHB0XIiIoMFlxBjo0RlNcGmtCei08Lzc8PB0VdWd6dz08OiFjGBAbdCgNLDg8PDUgLR0lOyI/OwVxfF8tW1NYVGcGKyg1JyYnOlhbdw87IRAAMCc3XVNcGCYMPEsdLzcoHR0UISI5MF8wOTwkWkQZVzVCNgI1RElkY1dJdwMfGSEWBwZLWF9aWStCPh43LTcgIRZGMC4uERAnNH1oPhAZGGcLPks3ITdpKgslOyI/OwVzIT0kWhBLXTMXKgV5NT5pKxYCXWt6dVE/OjYgWBBWU2tCLgo1bn5pPhsHOydyMwQ9NiEoW14REWcQPR8sPC1pKgslOyI/OwVpMjA1HBkZXSkGcWF5bmNpPB0SIjk0dVk8PnUgWlQZTD4SPUMvLy9gbkVbd2kuNBM/MHdoFFFXXGcUOQd5ITFpNQVsMiU+X3s/OjYgWBBfTSkBLAI2IGMvIQoLNj8UIBx7O3xLFBAZGClCZUstIS08IxoDJWM0fFE8J3VxPhAZGGcLPks3bn10bkkDZnl6IRk2O3UzUURMSilCKx8rJy0uYB4JJSY7IVlxcHtzUmQbFGcMd1o8f3FgRFhGd2s/OQI2PDNhWhAHBWdTPVJ5bjchKxZGJS4uIAM9dSY1RllXX2kENxk0LzdhbF1IZS0Yd11zO3pwUQkQMmdCeEs8IjAsJx5GOWtkaFFiMGNhFERRXSlCKg4tOzEnbgsSJSI0Ml81OicsVUQRGmJMag0UbG9pIFdXMn1zX1FzdXUkWENcUSFCNktnc2N4K0tGdz8yMB9zJzA1QUJXGDQWKgI3KW0vIQoLNj9yd1R9ZDMKFhwZVmhTPVhwRGNpblgDOzg/dQM2ISAzWhBNVzQWKgI3KWskLwwOeS02Oh4hfTtoHRBcViNoPQU9REklIRsHO2s8IB8wITwuWhBNWSUOPSc8IGs9Z3JGd2t6PBdzISwxURhNEWccZUt7OiIrIh1Edz8yMB9zJzA1QUJXGHdCPQU9RGNpblgKOCg7OVE9dWhhBDoZGGdCPgQrbhxpJxZGJyozJwJ7IXxhUF8ZVmdfeAV5ZWN4bh0IM0F6dVFzJzA1QUJXGCloPQU9REklIRsHO2s8IB8wITwuWhBYSDcOITgpKyYtZg5PXWt6dVEjNjQtWBhfTSkBLAI2IGtgRFhGd2t6dVFzPDNheF9aWSsyNAogKzFnDRAHJSo5IRQhdSEpUV4zGGdCeEt5bmNpblhGOyQ5NB1zPXV8FHxWWyYOCAc4NyY7YDsONjk7NgU2J28HXV5dfi4QKx8aJiolKjcAFCc7JgJ7dx00WVFXVy4GekJTbmNpblhGd2t6dVFzPDNhXBBNUCIMeAN3GSIlJSsWMi4+dUxzI3UkWlQzGGdCeEt5bmMsIBxsd2t6dRQ9MXxLUV5dMk0ONwg4ImMvOxYFIyI1O1EyJSUtTXpMVTdKLkJTbmNpbggFNic2fRcmOzY1XV9XEG5oeEt5bmNpblgPMWsWOhIyOQUtVUlcSmkhMAorLyA9KwpGIyM/O3tzdXVhFBAZGGdCeEs1ISAoIlgOd3Z6GR4wNDkRWFFAXTVMGwM4PCIqOh0UbQ0zOxUVPCcyQHNRUSsGFw0aIiI6PVBEHz43NB88PDFjHToZGGdCeEt5bmNpblgPMWsydQU7MDthXB5zTSoSCAQuKzFpc1gQdy40MXtzdXVhFBAZGCIMPGF5bmNpKxYCfkE/OxVZXzkuV1FVGCEXNggtJywnbgwDOy4qOgMnATppRF9KEU1CeEt5PiAoIhROMT40NgU6OjtpHToZGGdCeEt5bi8mLRkKdygyNANzaHUNW1NYVBcOORI8PG0KJhkUNiguMANZdXVhFBAZGGcLPks6JiI7bhkIM2s5PRAhbxMoWlR/UTURLCgxJy8tZlouIiY7Ox46MQcuW0RpWTUWekJ5OissIHJGd2t6dVFzdXVhFBBaUCYQdiMsIyInIRECBSQ1ISEyJyFvd3ZLWSoHeFZ5DQU7LxUDeSU/IlkjOiZoPhAZGGdCeEt5Ky0tRFhGd2s/OxV6XzAvUDozFWpNd0sDAQ0MbigpBAIOHD4dBl8tW1NYVGc4FyUcERMGHVhbdzBQdVFzdQ5waRAZBWc0PQgtITF6YBYDIGNobEB/dXVzBBwZFXZQcUd5bhh7E1hGamsMMBInOidyGl5cT29XbF11bmN7flRGenpofF1ZdXVhFGsKZWdCZUsPKyA9IQpVeSU/IllrZWdtFBALCGtCdVprZ29pbiNSCmt6aFEFMDY1W0IKFikHL0NofnF8YlhUZ2d6eEBhfHlLFBAZGBxXBUt5c2MfKxsSODlpex82In1wBwAKFGdQaEd5Y3J7Z1RGdxBsCFFzaHUXUVNNVzVRdgU8OWt4e0tRe2toZV1zeGRzHRwzGGdCeDBuE2Npc1gwMiguOgNgezskQxgID3RUdEtrfm9pY0lUfmd6dSprCHVhCRBvXSQWNxlqYC0sOVBXbn1seVFhZXlhGQELEWtoeEt5bhhwE1hGamsMMBInOidyGl5cT29QaV1pYmN7flRGenpofF1zdQ5wBG0ZBWc0PQgtITF6YBYDIGNoZkZheXVzBBwZFXZQcUdTbmNpbiNXZhZ6aFEFMDY1W0IKFikHL0NreHN4YlhUZ2d6eEBhfHlhFGsIChpCZUsPKyA9IQpVeSU/IllhbWRyGBALCGtCdVprZ29DblhGdxBrZixzaHUXUVNNVzVRdgU8OWt6fktXe2toZV1zeGRzHRwZGBxTbDZ5c2MfKxsSODlpex82In1yBQUNFGdTbUd5Y3J6Z1Rsd2t6dSpiYAhhCRBvXSQWNxlqYC0sOVBVY3tueVFiYHlhGQIPEWtCeDBoeB5pc1gwMiguOgNgezskQxgKDnJSdEtoe29pY0lWfmdQdVFzdQ5wA20ZBWc0PQgtITF6YBYDIGNpbUhieXVwARwZFXZScUd5bhh4diVGamsMMBInOidyGl5cT29Wal9qYmN7flRGenpofF1ZdXVhFGsIARpCZUsPKyA9IQpVeSU/IllnZm15GBAIDWtCdV5wYmNpbiNUZxZ6aFEFMDY1W0IKFikHL0NteHB9YlhXYmd6eEBrfHlLFBAZGBxQaTZ5c2MfKxsSODlpex82In11DQcJFGdQaEd5Y3J7Z1RGdxBoZyxzaHUXUVNNVzVRdgU8OWt8f0lSe2trYF1zeGRxHRwzGGdCeDBrfR5pc1gwMiguOgNgezskQxgMC3FadEtoe29pY0lWfmd6dSphYQhhCRBvXSQWNxlqYC0sOVBTYXpteVFiYHlhGQEJEWtoeEt5bhh7eyVGamsMMBInOidyGl5cT29XYF1uYmN4e1RGenpqfF1zdQ5zAm0ZBWc0PQgtITF6YBYDIGNsZEBheXVwARwZFXBLdGF5bmNpFUpRCmtndSc2NiEuRgMXViIVcF1qe3VlbklTe2t3Ylh/dXVhbwIBZWdfeD08LTcmPEtIOS4tfUdlZWNtFAEMFGdPaVlwYklpblhGDHljCFFudQMkV0RWSnRMNg4uZnVxe0FKd3pveVF+YnxtFBAZY3RSBUtkbhUsLQwJJXh0OxQkfWJwBQUVGHZXdEt0eWplRFhGd2sBZkAOdWhhYlVaTCgQa0U3KzRheUtTbmd6ZER/dXhwBBkVGGc5a1kEbn5pGB0FIyQoZl89MCJpAwUAAGtCaV51bm5xZ1Rsd2t6dSpgZghhCRBvXSQWNxlqYC0sOVBRb39peVFiYHlhGQELEWtCeDBqeh5pc1gwMiguOgNgezskQxgBCH9UdEtoe29pY0lWfmdQdVFzdQ5yAW0ZBWc0PQgtITF6YBYDIGNiZkJgeXVwARwZFXZScUd5bhh6eCVGamsMMBInOidyGl5cT29abVNvYmN4e1RGenpqfF1ZdXVhFGsKDxpCZUsPKyA9IQpVeSU/IllrbWFzGBAIDWtCdVppZ29pbiNVbxZ6aFEFMDY1W0IKFikHL0NgfnpxYlhXYmd6eEBjfHlLFBAZGBxRYTZ5c2MfKxsSODlpex82In14BwUNFGdTbUd5Y3J5Z1RGdxBuZSxzaHUXUVNNVzVRdgU8OWtweElWe2trYF1zeGRxHRwzRU1odUZ2YWMaGjkyEkE2OhIyOXUHWFFeS2dfeBBTbmNpbhkTIyQIOh0/dXVhFBAZGGdCZUs/Ly86K1Rsd2t6dRAmIToTUVJQSjMKeEt5bmNpc1gANicpMF1ZdXVhFFFMTCghNwc1KyA9blhGd2t6aFE1NDkyURwzGGdCeAosOiwMPw0PJwk/JgVzdXVhCRBfWSsRPUdTbmNpbhAPMy8/OyM8OTlhFBAZGGdCZUs/Ly86K1Rsd2t6dQM8OTkFUVxYQWdCeEt5bmNpc1hWeXtveXtzdXVhQ1FVUxQSPQ49bmNpblhGd2tndUNheV9hFBAZUjIPKDs2OSY7blhGd2t6dVFudWBxGDoZGGdCOR4tIQE8NzQTNCB6dVFzdXV8FFZYVDQHdGF5bmNpLw0SOAkvLCI/OiEyFBAZGGdfeA04IjAsYnJGd2t6NAQnOhc0TWJWVCsxKA48KmN0bh4HOzg/eXtzdXVhVUVNVwUXISY4KS0sOlhGd2tndRcyOSYkGDoZGGdCOR4tIQE8NzsJPiV6dVFzdXV8FFZYVDQHdGF5bmNpLw0SOAkvLDY8OiVhFBAZGGdfeA04IjAsYnJGd2t6NAQnOhc0TX5cQDM4NwU8bmN0bh4HOzg/eXtzdXVhR1VVXSQWPQ8MPiQ7LxwDd2tndVM/IDYqFhwzGGdCeBg8IiYqOh0CDSQ0MFFzdXVhCRAIFE1CeEt5ICwKIhEWd2t6dVFzdXVhFBAEGCEDNBg8YklpblhGJCczOBQWBgVhFBAZGGdCeEtkbiUoIgsDe0F6dVFzJTkgTVVLfRQyeEt5bmNpblhbdy07OQI2eV88PjpVVyQDNEsqKzA6JxcIBSQ2OQJzaHVxPlxWWyYOeD43IiwoKh0Cd3Z6MxA/JjBLWF9aWStCGwQ3ICYqOhEJOTh6aFEoKF9LWF9aWStCGScVERYZCSonEw4JdUxzLl9hFBAZGisXOwB7YmE6IhcSJGl2dwM8OTkSRFVcXGVOegg2Jy0AIBsJOi54eVMkNDkqZ0BcXSNAdEk0LyQnKww0Ni8zIAJxeV9hFBAZGiIMPQYgDSw8IAxEe2k5OR4lMCcTW1xVS2VOegk2IDY6HBcKOzh4eVM2LSEzVWJWVCshMAo3LSZrYloBOCQqEQM8JQcgQFUbFE1CeEt5bCcmOxoKMgw1OgFxeXcuQlVLUy4ONEl1bCU7Jx0IMwcvNhpxeXcnRllcViMuLQgyDCwmPQxEe2kpORg+MBI0WnRYVSYFPUl1RGNpblhEJCczOBQUIDsHXUJcaiYWPUl1bDAlJxUDED40BxA9MjBjGBJcViIPITgpLzQnHQgDMi94eVMgOTwsUWRYSiAHLDk4ICQsbFRsd2t6dVM8MzMtXV5cdCgNLCo0ITYnOlpKdSkzMjQ9MDg4d1hYViQHekd7PSsgIAEjOS43LDI7NDsiURIVGi8XPw4cICYkNzsONiU5MFN/X3VhFBAbUSkUPRktKycMIB0LLggyNB8wMHdtFlJQXxQOMQY8PWFlbBATMC4JORg+MCZjGBJKUC4MITg1Jy4sPVpKdSI0IxQhITAlZ1xQVSIRekdTbmNpbloBOCQqd11xNCA1W2JWVCtAdGEkRElkY1dJdxgWHDwWdRASZDpVVyQDNEsqIiokKzAPMCM2PBY7ISZhCRBCRU1oNAQ6Ly9pKA0IND8zOh9zPCYSWFlUXW8NOgFwRGNpblgKOCg7OVE9NDgkFA0ZVyUIdiU4IyZzIhcRMjlyfHtzdXVhWF9aWStCMRgJLzE9bkVGOCkwbzggFH1jdlFKXRcDKh97Z2MmPFgJNSFgHAISfXcMUUNRaCYQLElwRGNpblgKOCg7OVE6JhguUFVVGHpCNwkzdAo6D1BEGiQ+MB1xfF9LFBAZGC4EeAIqHiI7OlgSPy40X1FzdXVhFBAZUSFCNgo0K3kvJxYCf2kpORg+MHdoFERRXSlCKg4tOzEnbgwUIi52dR4xP3UkWlQzGGdCeEt5bmMgKFgINiY/bxc6OzFpFlVXXSobekJ5OissIFgUMj8vJx9zISc0URwZVyUIeA43KklpblhGd2t6dRg1dTsgWVUDXi4MPEN7KSwmPlpPdz8yMB9zJzA1QUJXGDMQLQ51biwrJFgDOS9QdVFzdXVhFBBQXmcMOQY8dCUgIBxOdSk2OhNxfHU1XFVXGDUHLB4rIGM9PA0De2s1NxtzMDslPhAZGGdCeEt5JyVpIRoMeRs7JxQ9IXUgWlQZVyUIdjs4PCYnOlYoNiY/bx08IjAzHBkDXi4MPEN7PS8gIx1EfmsuPRQ9dSckQEVLVmcWKh48YmMmLBJGMiU+X1FzdXUkWlQzMmdCeEswKGMgPTUJMy42dQU7MDtLFBAZGGdCeEswKGMnLxUDbS0zOxV7dyYtXV1cGm5CLAM8IGM7KwwTJSV6IQMmMHlhW1JTGCIMPGF5bmNpblhGdyI8dR8yODB7UllXXG9APQU8IzprZ1gSPy40dQM2ISAzWhBNSjIHdEs2LClpKxYCXWt6dVFzdXVhXVYZViYPPVE/Jy0tZloBOCQqd1hzIT0kWhBLXTMXKgV5OjE8K1RGOCkwdRQ9MV9hFBAZGGdCeAI/bi0oIx1cMSI0MVlxNzkuVhIQGDMKPQV5PCY9OwoIdz8oIBR/dTojXhBcViNoeEt5bmNpblgPMWs1NxtpEzwvUHZQSjQWGwMwIidhbCsKPiY/BRAhIXdoFERRXSlCKg4tOzEnbgwUIi52dR4xP3UkWlQzGGdCeEt5bmMgKFgJNSFgExg9MRMoRkNNey8LNA9xbBAlJxUDdWJ6IRk2O3UzUURMSilCLBksK29pIRoMdy40MXtzdXVhFBAZGC4EeAQ7JHkPJxYCESIoJgUQPTwtUGdRUSQKERgYZmELLwsDByooIVN6dTQvUBBXWSoHYg0wICdhbAsWNjw0d1hzIT0kWhBLXTMXKgV5OjE8K1RGOCkwdRQ9MV9hFBAZXSkGUmF5bmNpPB0SIjk0dRcyOSYkGBBXUStoPQU9REklIRsHO2s8IB8wITwuWhBeXTMxNAI0KwItIQoIMi5yOhM5fF9hFBAZUSFCNwkzdAo6D1BEFSopMCEyJyFjHRBWSmcNOgFjBzAIZlorMjgyBRAhIXdoFERRXSloeEt5bmNpblgUMj8vJx9zOjcrPhAZGGcHNg9TbmNpbhEAdyQ4P0saJhRpFn1WXCIOekJ5OissIHJGd2t6dVFzdSckQEVLVmcNOgFjCConKj4PJTguFhk6OTEWXFlaUA4RGUN7DCI6KygHJT94eVEnJyAkHRBWSmcNOgFTbmNpbh0IM0F6dVFzJzA1QUJXGCgAMmE8ICdDRBQJNCo2dRcmOzY1XV9XGCQQPQotKxAlJxUDEhgKfQI/PDgkHToZGGdCNAQ6Ly9pIRNKdz87JxY2IXV8FFlKaysLNQ5xPS8gIx1PXWt6dVE6M3UvW0QZVyxCLAM8IGM7KwwTJSV6MB83X3VhFBBQXmcRNAI0KwsgKRAKPiwyIQIIJjkoWVVkGDMKPQV5PCY9OwoIdy40MXtZdXVhFFxWWyYOeAo9ITEnKx1Gams9MAUAOTwsUXFdVzUMPQ5xOiI7KR0SfkF6dVFzOToiVVwZSCYQLEtkbiItIQoIMi5gHAISfXcDVUNcaCYQLElwbiInKlgHMyQoOxQ2dTozFENVUSoHYi0wICcPJwoVIwgyPB03Aj0oV1hwSwZKeik4PSYZLwoSdWd6IQMmMHxLFBAZGC4EeAU2OmM5LwoSdz8yMB9zJzA1QUJXGCIMPGFTbmNpbhQJNCo2dRk/dWhhfV5KTCYMOw53ICY+ZlouPiwyORg0PSFjHToZGGdCMAd3ACIkK1hbd2kJORg+MBASZG9xdGVoeEt5bislYD4POycZOh08J3V8FHNWVCgQa0U/PCwkHD8kf3t2dUNmYHlhBQAJEU1CeEt5Ji9nAQ0SOyI0MDI8OTozFA0ZeygONxlqYCU7IRU0EAlyZV1zZGVxGBAMCG5oeEt5bislYD4POycOJxA9JiUgRlVXWz5CZUtpYHdDblhGdyM2ez4mITkoWlVtSiYMKxs4PCYnLQFGamtqX1FzdXUpWB59XTcWMCY2KiZpc1gjOT43ezk6Mj0tXVdRTAMHKB8xAywtK1YnOzw7LAIcOwEuRDoZGGdCMAd3DycmPBYDMmtndRA3OicvUVUzGGdCeAM1YBMoPB0II2tndQI/PDgkPjoZGGdCNAQ6Ly9pLBEKO2tndTg9JiEgWlNcFikHL0N7DColIhoJNjk+EgQ6d3xLFBAZGCULNAd3ACIkK1hbd2kJORg+MBASZG97USsOemF5bmNpLBEKO2UbMR4hOzAkFA0ZSCYQLGF5bmNpLBEKO2UJPAs2dWhhYXRQVXVMNg4uZnNlbk5We2tqeVFhYXxLFBAZGCULNAd3Dy8+LwEVGCUOOgFzaHU1RkVcMmdCeEs7Jy8lYCsSIi8pGhc1JjA1FA0ZbiIBLAQrfW0nKw9OZ2d6Zl1zZXxLPhAZGGcONwg4ImMlLBRGamsTOwInNDsiUR5XXTBKej88NjcFLxoDO2l2dRM6OTloPhAZGGcOOgd3HSozK1hbdx4ePBxhezskQxgIFGdSdEtoYmN5Z3JGd2t6ORM/ewEkTEQZBWcRNAI0K20HLxUDXWt6dVE/NzlvdlFaUyAQNx43Khc7LxYVJyooMB8wLHV8FAEzGGdCeAc7Im0dKwASFCQ2OgNgdWhhd19VVzVRdg0rIS4bCTpOZ2d6Z0RmeXVwBAAQMmdCeEs1LC9nGh0eIxguJx44MAEzVV5KSCYQPQU6N2N0bkhsd2t6dR0xOXsVUUhNayQDNA49bn5pOgoTMkF6dVFzOTctGnZWVjNCZUscIDYkYD4JOT90Eh4nPTQsdl9VXE1oeEt5biEgIhRIByooMB8ndWhhR1xQVSJoeEt5bjAlJxUDHyI9PR06Mj01R2tKVC4PPTZ5c2MyJhRGamsyOV1zNzwtWBAEGCULNAckRElpblhGJCczOBR9FDsiUUNNSj4hMAo3KSYtdDsJOSU/NgV7MyAvV0RQVylKB0d5PiI7KxYSfkF6dVFzdXVhFFlfGCkNLEspLzEsIAxGNiU+dQI/PDgkfFleUCsLPwMtPRg6IhELMhZ6IRk2O19hFBAZGGdCeEt5bmM6IhELMgMzMhk/PDIpQENiSysLNQ4EYCsldDwDJD8oOgh7fF9hFBAZGGdCeEt5bmM6IhELMgMzMhk/PDIpQENiSysLNQ4EYCEgIhRcEy4pIQM8LH1oPhAZGGdCeEt5bmNpbgsKPiY/HRg0PTkoU1hNSxwRNAI0Kx5pc1gIPidQdVFzdXVhFBBcViNoeEt5biYnKlFsMiU+X3s/OjYgWBBfTSkBLAI2IGM7KxUJIS4JORg+MBASZBhKVC4PPUJTbmNpbhEAdzg2PBw2HTwmXFxQXy8WKzAqIiokKyVGIyM/O3tzdXVhFBAZGDQOMQY8BiouJhQPMCMuJiogOTwsUW0XUCtYHA4qOjEmN1BPXWt6dVFzdXVhR1xQVSIqMQwxIiouJgwVDDg2PBw2CHsjXVxVAgMHKx8rITphZ3JGd2t6dVFzdSYtXV1ccC4FMAcwKSs9PSMVOyI3MCxzaHUvXVwzGGdCeA43KkksIBxsXSc1NhA/dTM0WlNNUSgMeB4pKiI9KysKPiY/ECIDfXxLFBAZGC4EeAU2OmMPIhkBJGUpORg+MBASZBBNUCIMUkt5bmNpblhGMSQodQI/PDgkGBBPUTQXOQcqbionbggHPjkpfQI/PDgkfFleUCsLPwMtPWppKhdsd2t6dVFzdXVhFBAZSiIPNx08HS8gIx0jBBtyJh06ODBoPhAZGGdCeEt5Ky0tRFhGd2t6dVFzJzA1QUJXMmdCeEs8ICdDRFhGd2s2OhIyOXUyWFlUXQENNA88PDBpc1gdXWt6dVFzdXVhY19LUzQSOQg8dAUgIBwgPjkpITI7PDklHBJ8ViIPMQ4qbGplRFhGd2t6dVFzAjozX0NJWSQHYi0wICcPJwoVIwgyPB03fXcSWFlUXTRAcUdTbmNpblhGd2sNOgM4JiUgV1UDfi4MPC0wPDA9DRAPOy9ydz8DFiZjHRwzGGdCeEt5bmMeIQoNJDs7NhRpEzwvUHZQSjQWGwMwIidhbCsKPiY/BgEyIjsyFhkVMmdCeEt5bmNpGRcUPDgqNBI2bxMoWlR/UTURLCgxJy8tZlo1OyI3MCIjNCIvR31WXCIOK0lwYklpblhGd2t6dSY8Jz4yRFFaXX0kMQU9CCo7PQwlPyI2MVlxBiUgQ15cXAIMPQYwKzBrZ1Rsd2t6dVFzdXUWW0JSSzcDOw5jCConKj4PJTguFhk6OTFpFnFaTC4UPTg1Jy4sPVpPe0F6dVFzKF9LFBAZGCsNOwo1biAmOxYSd3Z6ZXtzdXVhUl9LGBhOeA02IicsPFgPOWszJRA6JyZpR1xQVSIkNwc9KzE6Z1gCOEF6dVFzdXVhFFlfGCENNA88PGM9Jh0IXWt6dVFzdXVhFBAZGCENKksGYmMmLBJGPiV6PAEyPCcyHFZWVCMHKlEeKzcNKwsFMiU+NB8nJn1oHRBdV01CeEt5bmNpblhGd2t6dVFzOToiVVwZVyxCZUswPRAlJxUDfyQ4P1hZdXVhFBAZGGdCeEt5bmNpbhEAdyQxdQU7MDtLFBAZGGdCeEt5bmNpblhGd2t6dVEwJzAgQFVqVC4PPS4KHmsmLBJPXWt6dVFzdXVhFBAZGGdCeEt5bmNpLRcTOT96aFEwOiAvQBASGHZoeEt5bmNpblhGd2t6dVFzdTAvUDoZGGdCeEt5bmNpblgDOS9QdVFzdXVhFBBcViNoeEt5biYnKnJsd2t6dVx+dRMgWFxbWSQJYksqLSInbg8JJSApJRAwMHUoUhBXV2cRKA46JyUgLVgAOCc+MAMgdTMuQV5dGCgAMg46OjBDblhGdyI8dRI8IDs1FA0EGHdCLAM8IElpblhGd2t6dRc8J3UeGBBWWi1CMQV5JzMoJwoVfxw1JxogJTQiUQp+XTMmPRg6Ky0tLxYSJGNzfFE3Ol9hFBAZGGdCeEt5bmMlIRsHO2s1PlFudTwyZ1xQVSJKNwkzZ0lpblhGd2t6dVFzdXUoUhBWU2cWMA43RGNpblhGd2t6dVFzdXVhFBBaSiIDLA4KIiokKz01B2M1Nxt6X3VhFBAZGGdCeEt5bmNpblgFOD40IVFudTYuQV5NGGxCaWF5bmNpblhGd2t6dVE2OzFLFBAZGGdCeEs8ICdDblhGdy40MXs2OzFLPkRYWisHdgI3PSY7OlAlOCU0MBInPDovRxwZbygQMxgpLyAsYDwDJCg/OxUyOyEAUFRcXH0hNwU3KyA9Zh4TOSguPB49fTEkR1MQMmdCeEswKGMcIBQJNi8/MVEnPTAvFEJcTDIQNks8ICdDblhGdyI8dTc/NDIyGkNVUSoHHTgJbiInKlgPJBg2PBw2fTEkR1MQGDMKPQVTbmNpblhGd2suNAI4eyIgXUQRCGlTcWF5bmNpblhGdygoMBAnMAYtXV1cfRQycA88PSBgRFhGd2s/OxVZMDslHRkzMmpPd0R5Hg8IFz00dw4JBXs/OjYgWBBJVCYbPRkRJyQhIhEBPz8pdUxzLihLPlxWWyYOeA0sICA9JxcIdygoMBAnMAUtVUlcSgIxCEMpIiIwKwpPXWt6dVE6M3UxWFFAXTVCZVZ5AiwqLxQ2OyojMANzIT0kWhBLXTMXKgV5Ky0tRFhGd2s2OhIyOXUiXFFLGHpCKAc4NyY7YDsONjk7NgU2J19hFBAZUSFCNgQtbiAhLwpGIyM/O1EhMCE0Rl4ZXSkGUkt5bmMlIRsHO2syJwFzaHUiXFFLAgELNg8fJzE6OjsOPic+fVMbIDggWl9QXBUNNx8JLzE9bFFsd2t6dRg1dTsuQBBRSjdCLAM8IGM7KwwTJSV6MB83X3VhFBBQXmcSNAogKzEBJx8OOyI9PQUgDiUtVUlcShpCLAM8IGM7KwwTJSV6MB83X19hFBAZVCgBOQd5Ji9pc1gvOTguNB8wMHsvUUcRGg8LPwM1JyQhOlpPXWt6dVE7OXsPVV1cGHpCejs1LzosPD01BxQSGVNZdXVhFFhVFgELNAcaIS8mPFhbdwg1OR4hZnsnRl9UagAgcFt1bnJ+flRGZX5vfHtzdXVhXFwXdzIWNAI3KwAmIhcUd3Z6Fh4/OidyGlZLVyowHylxfm9pdkhKd3pvZVhZdXVhFFhVFgELNAcNPCInPQgHJS40NghzaHVxGgQzGGdCeAM1YAw8OhQPOS4OJxA9JiUgRlVXWz5CZUtpRGNpblgOO2UeMAEnPRguUFUZBWcnNh40YAsgKRAKPiwyITU2JSEpeV9dXWkjNBw4NzAGICwJJ0F6dVFzPTlvdVRWSikHPUtkbiAhLwpsd2t6dRk/ewUgRlVXTGdfeAgxLzFDRFhGd2s2OhIyOXUjXVxVGHpCEQUqOiInLR1IOS4tfVMRPDktVl9YSiMlLQJ7Z0lpblhGNSI2OV8dNDgkFA0ZGhcOORI8PAYaHickPic2d3tzdXVhVllVVGkjPAQrICYsbkVGPzkqX1FzdXUjXVxVFhQLIg55c2McChELZWU0MAZ7ZXlhDAAVGHdOeFhpZ0lpblhGNSI2OV8SOSIgTUN2VhMNKEtkbjc7Ox1sd2t6dRM6OTlvZ0RMXDQtPg0qKzdpc1gwMiguOgNgezskQxgJFGdRdl51bnNgRHJGd2t6OR4wNDlhWFJVGHpCEQUqOiInLR1IOS4tfVMHMC01eFFbXStAdEs7Jy8lZ3JGd2t6ORM/ewYoTlUZBWc3HAI0fG0nKw9OZmd6ZV1zZHlhBBkzGGdCeAc7Im0dKwASd3Z6JR0yLDAzGn5YVSJoeEt5bi8rIlYkNigxMgM8IDslYEJYVjQSORk8ICAwbkVGZkF6dVFzOTctGmRcQDMhNwc2PHBpc1glOCc1J0J9MycuWWJ+em9SdEtrfnNlbkpTYmJQdVFzdTkjWB5tXT8WCx8rISgsGgoHOTgqNAM2OzY4FA0ZCE1CeEt5IiElYCwDLz8JNhA/MDFhCRBNSjIHUkt5bmMlLBRIESQ0IVFudRAvQV0XfigMLEUeITchLxUkOCc+X3tzdXVhVllVVGkyORk8IDdpc1gFPyooX1FzdXUxWFFAXTUqMQwxIiouJgwVDDs2NAg2JwhhCRBCUCtCZUsxIm9pLBEKO2tndRM6OTltFFxYWiIOeFZ5IiElM3Jsd2t6dQE/NCwkRh56UCYQOQgtKzEbKxUJISI0MksQOjsvUVNNECEXNggtJywnZlFsd2t6dVFzdXUoUhBJVCYbPRkRJyQhIhEBPz8pDgE/NCwkRm0ZTC8HNmF5bmNpblhGd2t6dVEjOTQ4UUJxUSAKNAI+Jjc6FQgKNjI/Jyx9PTl7cFVKTDUNIUNwRGNpblhGd2t6dVFzdSUtVUlcSg8LPwM1JyQhOgs9Jyc7LBQhCHsjXVxVAgMHKx8rITphZ3JGd2t6dVFzdXVhFBBJVCYbPRkRJyQhIhEBPz8pDgE/NCwkRm0ZBWcMMQdTbmNpblhGd2s/OxVZdXVhFFVXXG5oPQU9REklIRsHO2s8IB8wITwuWhBLXSoNLg4JIiIwKwojBBtyJR0yLDAzHToZGGdCMQ15Pi8oNx0UHyI9PR06Mj01R2tJVCYbPRkEbjchKxZsd2t6dVFzdXUxWFFAXTUqMQwxIiouJgwVDDs2NAg2JwhvXFwDfCIRLBk2N2tgRFhGd2t6dVFzJTkgTVVLcC4FMAcwKSs9PSMWOyojMAMOezcoWFwDfCIRLBk2N2tgRFhGd2t6dVFzJTkgTVVLcC4FMAcwKSs9PSMWOyojMAMOdWhhWllVMmdCeEs8ICdDKxYCXUE2OhIyOXUnQV5aTC4NNkssPicoOh02OyojMAMWBgVpHToZGGdCMQ15ICw9bj4KNiwpewE/NCwkRnVqaGcWMA43RGNpblhGd2t6Mx4hdSUtVUlcSmtCB0swIGM5LxEUJGMqORAqMCcJXVdRVC4FMB8qZ2MtIXJGd2t6dVFzdXVhFBBLXSoNLg4JIiIwKwojBBtyJR0yLDAzHToZGGdCeEt5biYnKnJGd2t6dVFzdSckQEVLVk1CeEt5Ky0tRFhGd2s8OgNzCnlhRFxYQSIQeAI3bio5LxEUJGMKORAqMCcyDndcTBcOORI8PDBhZ1FGMyRQdVFzdXVhFBBQXmcSNAogKzFpMEVGGyQ5NB0DOTQ4UUIZTC8HNmF5bmNpblhGd2t6dVEwJzAgQFVpVCYbPRkcHRNhPhQHLi4ofHtzdXVhFBAZGCIMPGF5bmNpKxYCXS40MXtZITQjWFUXUSkRPRktZgAmIBYDND8zOh8geXURWFFAXTURdjs1LzosPDkCMy4+bzI8OzskV0QRXjIMOx8wIS1hPhQHLi4ofHtzdXVhXVYZbSkONwo9KydpOhADOWsoMAUmJzthUV5dMmdCeEswKGMPIhkBJGUqORAqMCcEZ2AZTC8HNmF5bmNpblhGdygoMBAnMAUtVUlcSgIxCEMpIiIwKwpPXWt6dVE2OzFLUV5dEW5oUh84LC8sYBEIJC4oIVkQOjsvUVNNUSgMK0d5Hi8oNx0UJGUKORAqMCcTUV1WTi4MP1EaIS0nKxsSfy0vOxInPDovHEBVWT4HKkJTbmNpbgoDOiQsMCE/NCwkRnVqaG8SNAogKzFgRB0IM2JzX3t+eHpuFGVwAmcvGSIXbhcIDHIKOCg7OVEeGXV8FGRYWjRMFQowIHkIKhwqMi0uEgM8ICUjW0gRGhUNNAcwICRrZ3IKOCg7OVEeB3V8FGRYWjRMFQowIHkIKhw0PiwyITYhOiAxVl9BEGUuNwQtbmVpHB0EPjkuPVN6XzkuV1FVGAoreFZ5GiIrPVYrNiI0bzA3MRkkUkR+SigXKAk2NmtrBxYQMiUuOgMqd3xLWF9aWStCFS4KHmN0biwHNTh0GBA6O28AUFRrUSAKLCwrITY5LBcef2kMPAImNDkyFhkzMgouYio9KhcmKR8KMmN4FAQnOgcuWFwbFGcZDA4hOmN0blonIj81dSM8OTljGBB9XSEDLQctbn5pKBkKJC52dTIyOTkjVVNSGHpCPh43LTcgIRZOIWJQdVFzdRMtVVdKFiYXLAQLIS8lbkVGIUF6dVFzPDNhZl9VVBQHKh0wLSYKIhEDOT96IRk2O19hFBAZGGdCeBs6Ly8lZh4TOSguPB49fXxhZl9VVBQHKh0wLSYKIhEDOT9gJhQnFCA1W2JWVCsnNgo7IiYtZg5Pdy40MVhZdXVhFFVXXE0HNg8kZ0lDAzRcFi8+AR40MjkkHBJxUSMGPQULIS8lbFRGLB8/LQVzaHVjfFldXCIMeDk2Ii9pZhYJdyo0PBwyITwuWhkbFGcmPQ04Oy89bkVGMSo2JhR/dRYgWFxbWSQJeFZ5KDYnLQwPOCVyI1hZdXVhFHZVWSARdgMwKicsICoJOyd6aFElX3VhFBBQXmcwNwc1HSY7OBEFMgg2PBQ9IXU1XFVXMmdCeEt5bmNpPhsHOydyMwQ9NiEoW14REWcwNwc1HSY7OBEFMgg2PBQ9IW8yUURxUSMGPQULIS8lCxYHNSc/MVklfHUkWlQQMmdCeEs8ICdDKxYCKmJQXzwfbxQlUGNVUSMHKkN7HCwlIjwDOyojd11zLgEkTEQZBWdACgQ1ImMNKxQHLmtyJlhxeXUMXV4ZBWdSdEsULztpc1hTe2seMBcyIDk1FA0ZCGlSbUd5HCw8IBwPOSx6aFFheXUCVVxVWiYBM0tkbiU8IBsSPiQ0fQd6X3VhFBB/VCYFK0UrIS8lCh0KNjJ6aFE+NCEpGl1YQG9SdltoYmM/Z3IDOS8nfHtZGBl7dVRdejIWLAQ3ZjgdKwASd3Z6dyM8OTlhel9OGmtCHh43LWN0bh4TOSguPB49fXxLFBAZGC4EeDk2Ii8aKwoQPig/Fh06MDs1FERRXSloeEt5bmNpblgWNCo2OVk1IDsiQFlWVm9LeDk2Ii8aKwoQPig/Fh06MDs1DkJWVCtKcUs8ICdgRFhGd2t6dVFzJjAyR1lWVhUNNAcqbn5pPR0VJCI1OyM8OTkyFBsZCU1CeEt5Ky0tRB0IMzZzX3seB28AUFRtVyAFNA5xbAI8OhclOCc2MBInd3lhT2RcQDNCZUt7DzY9IVglOCc2MBIndRkuW0QbFGcmPQ04Oy89bkVGMSo2JhR/dRYgWFxbWSQJeFZ5KDYnLQwPOCVyI1hZdXVhFHZVWSARdgosOiwKIRQKMigudUxzI18kWlREEU1oFTljDyctDA0SIyQ0fQoHMC01FA0ZGgQNNAc8LTdpDxQKdwU1IlN/dRM0WlMZBWcELQU6OiomIFBPXWt6dVE6M3UNW19NayIQLgI6KwAlJx0II2suPRQ9X3VhFBAZGGdCKAg4Ii9hKA0IND8zOh97fF9hFBAZGGdCeEt5bmMlIRsHO2s2Oh4nFywIUBAEGAsNNx8KKzE/JxsDFCczMB8nezkuW0R7QQ4GUkt5bmNpblhGd2t6dRg1dTkuW0R7QQ4GeB8xKy1DblhGd2t6dVFzdXVhFBAZGCENKkswKmMgIFgWNiIoJlk/Ojo1dklwXG5CPARTbmNpblhGd2t6dVFzdXVhFBAZGGcSOwo1ImsvOxYFIyI1O1l6dRkuW0RqXTUUMQg8DS8gKxYSbTk/JAQ2JiECW1xVXSQWcAI9Z2MsIBxPXWt6dVFzdXVhFBAZGGdCeEs8ICdDblhGd2t6dVFzdXVhUV5dMmdCeEt5bmNpKxYCfkF6dVFzMDslPlVXXDpLUmEUHHkIKhwyOCw9ORR7dxQ0QF9rXSULKh8xbG9pNSwDLz96aFFxFCA1WxBrXSULKh8xbG9pCh0ANj42IVFudTMgWENcFGchOQc1LCIqJVhbdy0vOxInPDovHEYQMmdCeEsfIiIuPVYHIj81BxQxPCc1XBAEGDFoPQU9M2pDRDU0bQo+MSU8MjItURgbeTIWNyksNw0sNgw8OCU/d11zLgEkTEQZBWdAGR4tIWMLOwFGGS4iIVEJOjskFhwZfCIEOR41OmN0bh4HOzg/eVEQNDktVlFaU2dfeA0sICA9JxcIfz1zX1FzdXUHWFFeS2kDLR82DDYwAB0eIxE1OxRzaHU3PlVXXDpLUmEUHHkIKhwkIj8uOh97LgEkTEQZBWdACg47JzE9JlgoODx4eVEVIDsiFA0ZXjIMOx8wIS1hZ3JGd2t6PBdzBzAjXUJNUBQHKh0wLSYKIhEDOT96IRk2O19hFBAZGGdCeAc2LSIlbhcNd3Z6JRIyOTlpUkVXWzMLNwVxZ2MbKxoPJT8yBhQhIzwiUXNVUSIMLFE4OjcsIwgSBS44PAMnPX1oFFVXXG5oeEt5bmNpblgPMWs1PlEnPTAvFHxQWjUDKhJjACw9Jx4ff2kIMBM6JyEpFENMWyQHKxg/Oy9obFRGZGJ6MB83X3VhFBBcViNoPQU9M2pDRDUvbQo+MSU8MjItURgbeTIWNy4oOyo5DB0VI2l2dQoHMC01FA0ZGgYXLAR5CzI8JwhGFS4pIVEAOTwsUUMbFGcmPQ04Oy89bkVGMSo2JhR/dRYgWFxbWSQJeFZ5KDYnLQwPOCVyI1hZdXVhFHZVWSARdgosOiwMPw0PJwk/JgVzaHU3PlVXXDpLUmEUB3kIKhwkIj8uOh97LgEkTEQZBWdAHRosJzNpDB0VI2sUOgZxeXUHQV5aGHpCPh43LTcgIRZOfkF6dVFzPDNhfV5PXSkWNxkgHSY7OBEFMgg2PBQ9IXU1XFVXMmdCeEt5bmNpPhsHOydyMwQ9NiEoW14REWcrNh08IDcmPAE1MjksPBI2FjkoUV5NAiITLQIpDCY6OlBPdy40MVhZdXVhFFVXXE0HNg8kZ0lDY1VJeGsPHEtzAAUGZnF9fRRCDCobRC8mLRkKdx4WdUxzATQjRx5sSCAQOQ88PXkIKhwqMi0uEgM8ICUjW0gRGgUXIUsMPiQ7LxwDJGlzXx08NjQtFGVrGHpCDAo7PW0cPh8UNi8/JksSMTETXVdRTAAQNx4pLCwxZlonIj81dTMmLHdoPjpsdH0jPA8dPCw5KhcROWN4BhQ/MDY1UVRsSCAQOQ88bG9pNSwDLz96aFFxACUmRlFdXWcWN0sbOzprYlgwNicvMAJzaHUAeHxmbRclCiodCxBlbjwDMSovOQVzaHVjWEVaU2VOeCg4Ii8rLxsNd3Z6MwQ9NiEoW14RTm5oeEt5bgUlLx8VeTg/ORQwITAlYUBeSiYGPUtkbjVDKxYCKmJQXyQfbxQlUHJMTDMNNkMiGiYxOlhbd2kYIAhzBjAtUVNNXSNCDRs+PCItK1pKdw0vOxJzaHUnQV5aTC4NNkNwRGNpblgPMWsPJRYhNDEkZ1VLTi4BPSg1JyYnOlgSPy40X1FzdXVhFBAZSCQDNAdxKDYnLQwPOCVyfFEGJTIzVVRcayIQLgI6KwAlJx0II3EvOx08Nj4URFdLWSMHcC01LyQ6YAsDOy45IRQ3ACUmRlFdXW5CPQU9Z0lpblhGd2t6dT06NycgRkkDdigWMQ0gZmELIQ0BPz9gdVNze3thQF9KTDULNgxxCC8oKQtIJC42MBInMDEURFdLWSMHcUd5fWpDblhGdy40MXs2OzE8HTozbQtYGQ89DDY9OhcIfzAOMAkndWhhFnJMQWcjFCd5GzMuPBkCMjh4eVEVIDsiFA0ZXjIMOx8wIS1hZ3JGd2t6PBdzOzo1FGVJXzUDPA4KKzE/JxsDFCczMB8ndSEpUV4ZSiIWLRk3biYnKnJGd2t6IRAgPnsyRFFOVm8ELQU6OiomIFBPXWt6dVFzdXVhUl9LGBhOeAI9bionbhEWNiIoJlkSGRkeYWB+agYmHThwbicmRFhGd2t6dVFzdXVhFEBaWSsOcA0sICA9JxcIf2J6AAE0JzQlUWNcSjELOw4aIiosIAxcIiU2OhI4ACUmRlFdXW8LPEJ5Ky0tZ3JGd2t6dVFzdXVhFBBNWTQJdhw4JzdhflZWYGJQdVFzdXVhFBBcViNoeEt5bmNpblgqPikoNAMqbxsuQFlfQW9AGQc1bjY5KQoHMy4pdQEmJzYpVUNcXGZAdEtqZ0lpblhGMiU+fHs2OzE8HTozbRVYGQ89GiwuKRQDf2kbIAU8FyA4eEVaU2VOeBANKzs9bkVGdQovIR5zFyA4FHxMWyxAdEsdKyUoOxQSd3Z6MxA/JjBtFHNYVCsAOQgybn5pKA0IND8zOh97I3xhclxYXzRMOR4tIQE8NzQTNCB6aFEldTAvUE0QMhIwYio9KhcmKR8KMmN4FAQnOhc0TWNVVzMRekd5NRcsNgxGamt4FAQnOnUDQUkZaysNLBh7YmMNKx4HIicudUxzMzQtR1UVGAQDNAc7LyAibkVGMT40NgU6OjtpQhkZfisDPxh3LzY9IToTLhg2OgUgdWhhQhBcViMfcWEMHHkIKhwyOCw9ORR7dxQ0QF97TT4wNwc1HTMsKxxEe2shARQrIXV8FBJ4TTMNeCksN2MbIRQKdxgqMBQ3d3lhcFVfWTIOLEtkbiUoIgsDe2sZNB0/NzQiXxAEGCEXNggtJywnZg5Pdw02NBYgezQ0QF97TT4wNwc1HTMsKxxGamssdRQ9MShoPmVrAgYGPD82KSQlK1BEFj4uOjMmLBggU15cTGVOeBANKzs9bkVGdQovIR5zFyA4FH1YXykHLEsLLycgOwtEe2seMBcyIDk1FA0ZXiYOKw51bgAoIhQENigxdUxzMyAvV0RQVylKLkJ5CC8oKQtINj4uOjMmLBggU15cTGdfeB15Ky0tM1FsAhlgFBU3ATomU1xcEGUjLR82DDYwDRcPOWl2dQoHMC01FA0ZGgYXLAR5DDYwbjsJPiV6HB8wOjgkFhwZfCIEOR41OmN0bh4HOzg/eVEQNDktVlFaU2dfeA0sICA9JxcIfz1zdTc/NDIyGlFMTCggLRIaISonbkVGIWs/OxUufF8UZgp4XCM2Nww+IiZhbDkTIyQYIAgUOjoxFhwZQxMHIB95c2NrDw0SOGsYIAhzEjouRBB9SigSeDk4OiZrYlgiMi07IB0ndWhhUlFVSyJOeCg4Ii8rLxsNd3Z6MwQ9NiEoW14RTm5CHgc4KTBnLw0SOAkvLDY8OiVhCRBPGCIMPBZwRElkY1dJdx4Tb1EAARQVZxBteQVoNAQ6Ly9pHTRGamsONBMgewY1VURKAgYGPCc8KDcOPBcTJyk1LVlxBScuUllVXWVLUgc2LSIlbis0d3Z6ARAxJnsSQFFNS30jPA8LJyQhOj8UOD4qNx4rfXcTW1xVS2dEeDk8LCo7OhBEfkFQOR4wNDlhWFJVeygLNhh5bmNpc1g1G3EbMRUfNDckWBgbeygLNhhjbi8mLxwPOSx0e19xfF8tW1NYVGcOOgceISw5blhGd2tndSIfbxQlUHxYWiIOcEkeISw5dFgKOCo+PB80e3tvFhkzVCgBOQd5IiElFBcIMmt6dVFzaHUSeAp4XCMuOQk8ImtrFBcIMnF6OR4yMTwvUx4XFmVLUgc2LSIlbhQEOwY7LSs8OzBhFA0ZawtYGQ89AiIrKxROdQY7LVEJOjskDhBVVyYGMQU+YG1nbFFsOyQ5NB1zOTctZlVbUTUWMBh5c2MaAkInMy8WNBM2OX1jZlVbUTUWMBhjbi8mLxwPOSx0e19xfF8tW1NYVGcOOgcMPiQ7LxwDJGtndSIfbxQlUHxYWiIOcEkMPiQ7LxwDJHF6OR4yMTwvUx4XFmVLUgc2LSIlbhQEOw4rIBgjJTAlFA0ZawtYGQ89AiIrKxROdQ4rIBgjJTAlDhBVVyYGMQU+YG1nbFFsOyQ5NB1zOTctZl9VVAQXKkt5c2MaAkInMy8WNBM2OX1jZl9VVGchLRkrKy0qN0JGOyQ7MRg9MntvGhIQMk0ONwg4ImMlLBQyOD87OSM8OTkyFBAZBWcxClEYKicFLxoDO2N4AR4nNDlhZl9VVDRYeAc2LycgIB9IeWV4fHs/OjYgWBBVWisxPRgqJywnHBcKOzh6aFEAB28AUFR1WSUHNEN7HSY6PREJOWsIOh0/Jm9hBBIQMisNOwo1bi8rIj8JOy8/O1FzdXVhFBAEGBQwYio9Kg8oLB0Kf2kdOh03MDt7FFxWWSMLNgx3YG1rZ3IKOCg7OVE/NzkFXVFUVykGeEt5bmNpc1g1BXEbMRUfNDckWBgbfC4DNQQ3KnlpIhcHMyI0Ml99e3doPlxWWyYOeAc7IhUmJxxGd2t6dVFzdXV8FGNrAgYGPCc4LCYlZlowOCI+b1E/OjQlXV5eFmlMekJTIiwqLxRGOyk2EhA/NC04FBAZGGdCeFZ5HRFzDxwCGyo4MB17dxIgWFFBQX1CNAQ4KionKVZIeWlzXx08NjQtFFxbVBUDKg4qOmNpblhGd2tndSIBbxQlUHxYWiIOcEkLLzEsPQxGBSQ2OUtzOTogUFlXX2lMdklwRC8mLRkKdyc4OSM2NzwzQFh6VzQWeEtkbhAbdDkCMwc7NxQ/fXcTUVJQSjMKeCg2PTdzbhQJNi8zOxZ9e3tjHTpVVyQDNEs1LC8FOxsNGj42IVFzdXVhCRBqan0jPA8VLyEsIlBEGz45PlEeIDk1XUBVUSIQYks1ISItJxYBeWV0d1hZOToiVVwZVCUOCg47JzE9JioDNi8jdUxzBgd7dVRddCYAPQdxbBEsLBEUIyN6BxQyMSx7FFxWWSMLNgx3YG1rZ3JsemZ1elEGHG9hYHV1fRctCj95GgILRBQJNCo2dSUfdWhhYFFbS2k2PQc8Piw7OkInMy8WMBcnEicuQUBbVz9KejE2ICY6bFFsOyQ5NB1zAQdhCRBtWSURdj88IiY5IQoSbQo+MSM6Mj01c0JWTTcANxNxbA8mLRkSPiQ0JlF1dQUtVUlcSjRAcWFTGg9zDxwCBCczMRQhfXcSUVxcWzMHPDE2ICZrYlgdAy4iIVFudXcSUVxcWzNCAgQ3K2FlbjUPOWtndUB/dRggTBAEGHNSdEsdKyUoOxQSd3Z6ZF1zBzo0WlRQViBCZUtpYmMKLxQKNSo5PlFudTM0WlNNUSgMcB1wRGNpblggOyo9Jl8gMDkkV0RcXB0NNg55c2MkLwwOeS02Oh4hfSNoPlVXXDpLUmENAnkIKhwkIj8uOh97LgEkTEQZBWdADA41KzMmPAxGIyR6BhQ/MDY1UVQZYigMPUl1bgU8IBtGams8IB8wITwuWhgQMmdCeEs1ISAoIlgWODh6aFEJGhsEa2B2axwkNAo+PW06KxQDND8/MSs8OzAcPhAZGGcLPkspITBpOhADOUF6dVFzdXVhFERcVCISNxktGixhPhcVfkF6dVFzdXVhFHxQWjUDKhJjACw9Jx4ff2kOMB02JTozQFVdGDMNeDE2ICZpbFhIeWscORA0JnsyUVxcWzMHPDE2ICZlbktPXWt6dVE2OzFLUV5dRW5oUj8VdAItKjoTIz81O1koATA5QBAEGGU4NwU8bnJpZisSNjkufFN/dRM0WlMZBWcELQU6OiomIFBPdz8/ORQjOic1YF8RYggsHTQJARASfyVPdy40MQx6XwENDnFdXAUXLB82IGsyGh0eI2tndVMJOjskFAEJGmtCHh43LWN0bh4TOSguPB49fXxhQFVVXTcNKh8NIWsTATYjCBsVBipiZQhoFFVXXDpLUj8VdAItKjoTIz81O1koATA5QBAEGGU4NwU8bnF5bFRGET40NlFudTM0WlNNUSgMcEJ5OiYlKwgJJT8OOlkJGhsEa2B2axxQaDZwbiYnKgVPXR8WbzA3MRc0QERWVm8ZDA4hOmN0blo8OCU/dUJjd3lhckVXW2dfeA0sICA9JxcIf2J6IRQ/MCUuRkRtV284FyUcERMGHSNVZxZzdRQ9MShoPmR1AgYGPCksOjcmIFAdAy4iIVFudXcbW15cGHNSeEMULztgbFRGET40NlFudTM0WlNNUSgMcEJ5OiYlKwgJJT8OOlkJGhsEa2B2axxWaDZwbiYnKgVPXUEOB0sSMTEDQURNVylKIz88Njdpc1hEHz44dV5zBiUgQ14bFGckLQU6bn5pKA0IND8zOh97fHU1UVxcSCgQLD82ZhUsLQwJJXh0OxQkfWRtFAEMFGdPalhwZ2MsIBwbfkEOB0sSMTEDQURNVylKIz88Njdpc1hEGy47MRQhNzogRlRKGGpCCgorKzA9bioJOyd4eVEVIDsiFA0ZXjIMOx8wIS1hZ1gSMic/JR4hIQEuHGZcWzMNKlh3ICY+ZklRe2trYF1zeGd2HRkZXSkGJUJTGhFzDxwCFT4uIR49fS4VUUhNGHpCeic8LycsPBoJNjk+JlF+dREgXVxAGBUDKg4qOmFlbj4TOSh6aFE1IDsiQFlWVm9LeB88IiY5IQoSAyRyAxQwITozBx5XXTBKalJ1bnJ8YlhLY35zfFE2OzE8HTptan0jPA8bOzc9IRZOLB8/LQVzaHVjeFVYXCIQOgQ4PCc6blVGGiQpIVEBOjktRxIVGAEXNgh5c2MvOxYFIyI1O1l6dSEkWFVJVzUWDARxGCYqOhcUZGU0MAZ7ZGJtFAEMFGdPa0JwbiYnKgVPXR8IbzA3MRc0QERWVm8ZDA4hOmN0bloqMio+MAMxOjQzUEMZFWcwPQkwPDchPVpKdw0vOxJzaHUnQV5aTC4NNkNwbjcsIh0WODkuAR57AzAiQF9LC2kMPRxxfHplbklTe2trYlh6dTAvUE0QMk02ClEYKicLOwwSOCVyLiU2LSFhCRAbbCIOPRs2PDdpOhdGBSo0MR4+dQUtVUlcSmVOeC0sICBpc1gAIiU5IRg8O31oPhAZGGcONwg4ImMmOhADJTh6aFEoKF9hFBAZXigQeDR1bjNpJxZGPjs7PAMgfQUtVUlcSjRYHw4tHi8oNx0UJGNzfFE3Ol9hFBAZGGdCeAI/bjNpMEVGGyQ5NB0DOTQ4UUIZWSkGeBt3DSsoPBkFIy4odRA9MXUxGnNRWTUDOx88PHkPJxYCESIoJgUQPTwtUBgbcDIPOQU2JycbIRcSByooIVN6dSEpUV4zGGdCeEt5bmNpblhGIyo4ORR9PDsyUUJNECgWMA4rPW9pPlFsd2t6dVFzdXUkWlQzGGdCeA43KklpblhGPi16dh4nPTAzRxAHGHdCLAM8IElpblhGd2t6dR08NjQtFERYSiAHLEtkbiw9Jh0UJBA3NAU7eycgWlRWVW9TdEt6ITchKwoVfhZQdVFzdXVhFBBNXSsHKAQrOhcmZgwHJSw/IV8QPTQzVVNNXTVMEB40Ly0mJxw0OCQuBRAhIXsRW0NQTC4NNktybhUsLQwJJXh0OxQkfWVtFAUVGHdLcWF5bmNpblhGdwczNwMyJyx7el9NUSEbcEkNKy8sPhcUIy4+dQU8b3VjFB4XGDMDKgw8Om0HLxUDe2tpfHtzdXVhUVxKXU1CeEt5bmNpbjQPNTk7JwhpGzo1XVZAEGUsN0s2OissPFgWOyojMAMgdTMuQV5dFmVOeFhwRGNpblgDOS9QMB83KHxLPh0UF2hCDSJjbg4GGD0rEgUOdSUSF18tW1NYVGcvDktkbhcoLAtIGiQsMBw2OyF7dVRddCIELCwrITY5LBcef2kXOgc2ODAvQBIQMisNOwo1bg4ffFhbdx87NwJ9GDo3UV1cVjNYGQ89HCouJgwhJSQvJRM8LX1jZFhASy4BK0lwREkEGEInMy8JORg3MCdpFmdYVCwxKA48KmFlbgMyMjMudUxzdwIgWFsZazcHPQ97YmMEJxZGamtrY11zGDQ5FA0ZDXdSdEsdKyUoOxQSd3Z6Z0N/dQcuQV5dUSkFeFZ5fm9pDRkKOyk7NhpzaHUnQV5aTC4NNkMvZ0lpblhGESc7MgJ9IjQtX2NJXSIGeFZ5OElpblhGNjsqOQgAJTAkUBhPEU0HNg8kZ0lDAy5cFi8+Bh06MTAzHBJzTSoSCAQuKzFrYlgdAy4iIVFudXcLQV1JGBcNLw4rbG9pAxEId3Z6ZEF/dRggTBAEGHJSaEd5CiYvLw0KI2tndURjeXUTW0VXXC4MP0tkbnNlbjsHOyc4NBI4dWhhUkVXWzMLNwVxOGpDblhGdw02NBYgez80WUBpVzAHKktkbjVDblhGdyoqJR0qHyAsRBhPEU0HNg8kZ0lDAy5cFi8+FwQnITovHEttXT8WeFZ5bBEsPR0SdwY1IxQ+MDs1FhwZfjIMO0tkbiU8IBsSPiQ0fVhZdXVhFHZVWSARdhw4IigaPh0DM2tndUNhX3VhFBB/VCYFK0UzOy45HhcRMjl6aFFmZV9hFBAZWTcSNBIKPiYsKlBUZWJQdVFzdTQxRFxAcjIPKENsfmpDblhGdwczNwMyJyx7el9NUSEbcEkUITUsIx0II2soMAI2IXU1WxBdXSEDLQctbG9pfVFsMiU+KFhZXxgXBgp4XCM2Nww+IiZhbDYJFCczJVN/dS4VUUhNGHpCeiU2bgAlJwhEe2seMBcyIDk1FA0ZXiYOKw51bgAoIhQENigxdUxzMyAvV0RQVylKLkJTbmNpbj4KNiwpex88FjkoRBAEGDFoPQU9M2pDRDUjBBtgFBU3ATomU1xcEGUxNAI0KwYaHlpKdzAOMAkndWhhFmNVUSoHeC4KHmFlbjwDMSovOQVzaHUnVVxKXWtCGwo1IiEoLRNGams8IB8wITwuWhhPEU1CeEt5CC8oKQtIJCczOBQWBgVhCRBPMmdCeEssPicoOh01OyI3MDQABX1oPlVXXDpLUmEUCxAZdDkCMx81MhY/MH1jZFxYQSIQHTgJbG9pNSwDLz96aFFxBTkgTVVLGAIxCEl1bgcsKBkTOz96aFE1NDkyURwZeyYONAk4LShpc1gAIiU5IRg8O303HToZGGdCHgc4KTBnPhQHLi4oECIDdWhhQjoZGGdCLRs9LzcsHhQHLi4oECIDfXxLUV5dRW5oUkZ0YWxpGzFcdxgfASUaGxISFGR4ek0ONwg4ImMaCyw0d3Z6ARAxJnsSUURNUSkFK1EYKicbJx8OIwwoOgQjNzo5HBJqWzULKB97Z0lDHT0yBXEbMRURICE1W14RQxMHIB95c2NrGxYKOCo+dTw2OyBjGBB/TSkBeFZ5KDYnLQwPOCVyfHtzdXVhYV5VVyYGPQ95c2M9PA0DXWt6dVE1OidhaxwZWygMNkswIGMgPhkPJThyFh49OzAiQFlWVjRLeA82RGNpblhGd2t6PBdzNjovWhBYViNCOwQ3IG0KIRYIMiguMBVzIT0kWhBJWyYONEM/Oy0qOhEJOWNzdRI8Ozt7cFlKWygMNg46Omtgbh0IM2J6MB83X3VhFBBcViNoeEt5biUmPFgVOyI3MF1zCnUoWhBJWS4QK0MqIiokKzAPMCM2PBY7ISZoFFRWMmdCeEt5bmNpPB0LOD0/Bh06ODAEZ2ARSysLNQ5wRGNpblgDOS9QdVFzdTMuRhBJVCYbPRl1bhxpJxZGJyozJwJ7JTkgTVVLcC4FMAcwKSs9PVFGMyRQdVFzdXVhFBBLXSoNLg4JIiIwKwojBBtyJR0yLDAzHToZGGdCPQU9RGNpblgHJzs2LCIjMDAlHAEPEU1CeEt5LzM5IgEsIiYqfURjfF9hFBAZSCQDNAdxKDYnLQwPOCVyfFEfPDczVUJAAhIMNAQ4Kmtgbh0IM2JQdVFzdTIkQFdcVjFKcUUKIiokKyooEAc1NBU2MXV8FF5QVE0HNg8kZ0lDY1VGEhgKdQQjMTQ1URBVVygSUh84PShnPQgHICVyMwQ9NiEoW14REU1CeEt5OSsgIh1GIyopPl8kNDw1HAIQGCMNUkt5bmNpblhGPi16AB8/OjQlUVQZTC8HNksrKzc8PBZGMiU+X1FzdXVhFBAZTTcGOR88HS8gIx0jBBtyfHtzdXVhFBAZGDISPAotKxMlLwEDJQ4JBVl6X3VhFBBcViNoPQU9Z0lDY1VJeGsOHTQeEHVnFGN4bgJoDAM8IyYELxYHMC4obyI2IRkoVkJYSj5KFAI7PCI7N1FsBCosMDwyOzQmUUIDayIWFAI7PCI7N1AqPikoNAMqfF8VXFVUXQoDNgo+KzFzHR0SESQ2MRQhfXcYBltxTSVNCwcwIyYbAD9EfkEJNAc2GDQvVVdcSn0xPR8fIS8tKwpOdRJoPjkmN3oSWFlUXRUsH0Q6IS0vJx8VdWJQARk2ODAMVV5YXyIQYiopPi8wGhcyNilyARAxJnsSUURNUSkFK0JTHSI/KzUHOSo9MANpFyAoWFR6VykEMQwKKyA9JxcIfx87NwJ9BjA1QFlXXzRLUjg4OCYELxYHMC4obz08NDEAQURWVCgDPCg2ICUgKVBPXUF3eF58dRQUYH90eRMrFyV5AgwGHitsXWZ3dTAmITphZl9VVE0WORgyYDA5Lw8Ify0vOxInPDovHBkzGGdCeBwxJy8sbgwHJCB0IhA6IX0sVURRFioDIENpYHN4YlggOyo9Jl8hOjktcFVVWT5LcUs9IUlpblhGd2t6dRg1dQAvWF9YXCIGeB8xKy1pPB0SIjk0dRQ9MV9hFBAZGGdCeAI/bgUlLx8VeSovIR4BOjktFFFXXGcwNwc1HSY7OBEFMgg2PBQ9IXU1XFVXMmdCeEt5bmNpblhGdzs5NB0/fTM0WlNNUSgMcEJ5HCwlIisDJT0zNhQQOTwkWkQDSigONENwbiYnKlFsd2t6dVFzdXVhFBAZSyIRKwI2IBEmIhQVd3Z6JhQgJjwuWmJWVCsReEB5f0lpblhGd2t6dRQ9MV9hFBAZXSkGUg43KmpDRFVLdwovIR5zFjotWFVaTE0WORgyYDA5Lw8Ify0vOxInPDovHBkzGGdCeBwxJy8sbgwHJCB0IhA6IX1xGgUQGCMNUkt5bmNpblhGPi16AB8/OjQlUVQZTC8HNksrKzc8PBZGMiU+X1FzdXVhFBAZUSFCHgc4KTBnLw0SOAg1OR02NiFhVV5dGAsNNx8KKzE/JxsDFCczMB8ndSEpUV4zGGdCeEt5bmNpblhGJyg7OR17MyAvV0RQVylKcWF5bmNpblhGd2t6dVFzdXVhWF9aWStCNAl5c2MFIRcSBC4oIxgwMBYtXVVXTGkONwQtDDoAKnJGd2t6dVFzdXVhFBAZGGdCMQ15IiFpOhADOUF6dVFzdXVhFBAZGGdCeEt5bmNpbh4JJWszMVE6O3UxVVlLS28OOkJ5KixDblhGd2t6dVFzdXVhFBAZGGdCeEt5bmNpPhsHOydyMwQ9NiEoW14REWcuNwQtHSY7OBEFMgg2PBQ9IW8zUUFMXTQWGwQ1IiYqOlAPM2J6MB83fF9hFBAZGGdCeEt5bmNpblhGd2t6dRQ9MV9hFBAZGGdCeEt5bmNpblhGMiU+X1FzdXVhFBAZGGdCeA43KmpDblhGd2t6dVE2OzFLFBAZGCIMPGE8ICdgRHJLemsbIAU8dQckVllLTC9oLAoqJW06PhkROWM8IB8wITwuWhgQMmdCeEsuJiolK1gSNjgxewYyPCFpBhkZXChoeEt5bmNpblgPMWsPOx08NDEkUBBNUCIMeBk8OjY7IFgDOS9QdVFzdXVhFBBQXmckNAo+PW0oOwwJBS44PAMnPXUgWlQZaiIAMRktJhAsPA4PNC4ZORg2OyFhVV5dGBUHOgIrOisaKwoQPig/AAU6OSZhQFhcVk1CeEt5bmNpblhGd2sqNhA/OX0nQV5aTC4NNkNwRGNpblhGd2t6dVFzdXVhFBBVVyQDNEs9LzcobkVGMC4uERAnNH1oPhAZGGdCeEt5bmNpblhGd2s2OhIyOXUmW19JGHpCLAQ3Oy4rKwpOMyouNF80OjoxHRBWSmdSUkt5bmNpblhGd2t6dVFzdXUtW1NYVGcQPQkwPDchPVhbdz81OwQ+NzAzHFRYTCZMKg47JzE9JgtPdyQodUFZdXVhFBAZGGdCeEt5bmNpbhQJNCo2dRI8JiFhCRBrXSULKh8xHSY7OBEFMh4uPB0gezIkQHNWSzNKKg47JzE9JgtPXWt6dVFzdXVhFBAZGGdCeEswKGMqIQsSdyo0MVE0OjoxFA4EGCQNKx95OissIHJGd2t6dVFzdXVhFBAZGGdCeEt5bhEsLBEUIyMJMAMlPDYkd1xQXSkWYgotOiYkPgw0MikzJwU7fXxLFBAZGGdCeEt5bmNpblhGdy40MXtzdXVhFBAZGGdCeEs8ICdgRFhGd2t6dVFzMDslPhAZGGcHNg9TKy0tZ3JsemZ6FAQnOnUERUVQSGcgPRgtRDcoPRNIJDs7Ih97MyAvV0RQVylKcWF5bmNpORAPOy56IRAgPns2VVlNEHJLeA82RGNpblhGd2t6PBdzADstW1FdXSNCLAM8IGM7KwwTJSV6MB83X3VhFBAZGGdCMQ15CC8oKQtINj4uOjQiIDwxdlVKTGcDNg95By0/KxYSODkjBhQhIzwiUXNVUSIMLEstJiYnRFhGd2t6dVFzdXVhFEBaWSsOcA0sICA9JxcIf2J6HB8lMDs1W0JAayIQLgI6KwAlJx0II3E/JAQ6JRckR0QREWcHNg9wRGNpblhGd2t6MB83X3VhFBBcViNoPQU9Z0lDY1VGFj4uOlERICxhYUBeSiYGPRhTOiI6JVYVJyotO1k1IDsiQFlWVm9LUkt5bmM+JhEKMmsuNAI4eyIgXUQRCGlRcUs9IUlpblhGd2t6dRg1dQAvWF9YXCIGeB8xKy1pPB0SIjk0dRQ9MV9hFBAZGGdCeAI/bi0mOlgzJywoNBU2BjAzQllaXQQOMQ43OmM9Jh0Idyg1OwU6OyAkFFVXXE1CeEt5bmNpbhEAdw02NBYgezQ0QF97TT4uLQgybmNpblhGIyM/O1EjNjQtWBhfTSkBLAI2IGtgbi0WMDk7MRQAMCc3XVNceysLPQUtdDYnIhcFPB4qMgMyMTBpFlxMWyxAcUs8ICdgbh0IM0F6dVFzdXVhFFlfGAEOOQwqYCI8OhckIjIJOR4nJnVhFBAZTC8HNkspLSIlIlAAIiU5IRg8O31oFGVJXzUDPA4KKzE/JxsDFCczMB8nbyAvWF9aUxISPxk4KiZhbAsKOD8pd1hzMDslHRBcViNoeEt5bmNpblgPMWscORA0JnsgQURWejIbCgQ1IhA5Kx0Cdz8yMB9zJTYgWFwRXjIMOx8wIS1hZ1gzJywoNBU2BjAzQllaXQQOMQ43Onk8IBQJNCAPJRYhNDEkHBJLVysOCxs8KydrZ1gDOS9zdRQ9MV9hFBAZGGdCeAI/bgUlLx8VeSovIR4RICwMVVdXXTNCeEt5OissIFgWNCo2OVk1IDsiQFlWVm9LeD4pKTEoKh01MjksPBI2FjkoUV5NAjIMNAQ6JRY5KQoHMy5ydxwyMjskQGJYXC4XK0lwbiYnKlFGMiU+X1FzdXVhFBAZUSFCHgc4KTBnLw0SOAkvLDI8PDthFBAZGGcWMA43bjMqLxQKfy0vOxInPDovHBkZbTcFKgo9KxAsPA4PNC4ZORg2OyF7QV5VVyQJDRs+PCItK1BENCQzOzg9NjosURIQGCIMPEJ5Ky0tRFhGd2t6dVFzPDNhclxYXzRMOR4tIQE8Nz8JODt6dVFzdXU1XFVXGDcBOQc1ZiU8IBsSPiQ0fVhzACUmRlFdXRQHKh0wLSYKIhEDOT9gIB8/OjYqYUBeSiYGPUN7KSwmPjwUODsINAU2d3xhUV5dEWcHNg9TbmNpbh0IM0E/OxV6X19sGRB4TTMNeCksN2MHKwASdxE1OxRZOToiVVwZYigMPRgKKzE/JxsDFCczMB8ndWhhR1FfXRUHKR4wPCZhbCsJIjk5MFN/dXcHUVFNTTUHK0l1bmETIRYDJGl2dVMJOjskR2NcSjELOw4aIiosIAxEfkEuNAI4eyYxVUdXECEXNggtJywnZlFsd2t6dQY7PDkkFERYSyxMLwowOmt6Z1gCOEF6dVFzdXVhFFlfGBIMNAQ4KiYtbgwOMiV6JxQnICcvFFVXXE1CeEt5bmNpbhEAdw02NBYgezQ0QF97TT4sPRMtFCwnK1gHOS96Dx49MCYSUUJPUSQHGwcwKy09bgwOMiVQdVFzdXVhFBAZGGdCKAg4Ii9hKA0IND8zOh97fF9hFBAZGGdCeEt5bmNpblhGOyQ5NB1zMyAzQFhcSzNCZUsDIS0sPSsDJT0zNhQQOTwkWkQDXyIWHh4rOissPQw8OCU/fVhZdXVhFBAZGGdCeEt5bmNpbhQJNCo2dR82LSEbW15cGHpCcA0sPDchKwsSdyQodUF6dX5hBToZGGdCeEt5bmNpblhGd2t6PBdzOzA5QGpWViJCZFZ5enNpOhADOUF6dVFzdXVhFBAZGGdCeEt5bmNpbiIJOS4pBhQhIzwiUXNVUSIMLFEpOzEqJhkVMhE1OxR7OzA5QGpWViJLUkt5bmNpblhGd2t6dVFzdXUkWlQzGGdCeEt5bmNpblhGMiU+fHtzdXVhFBAZGCIMPGF5bmNpKxYCXS40MVhZX3hsFH5WeysLKEs1ISw5RAwHNSc/exg9JjAzQBh6VykMPQgtJywnPVRGBT40BhQhIzwiUR5qTCISKA49dAAmIBYDND9yMwQ9NiEoW14REU1CeEt5JyVpGxYKOCo+MBVzIT0kWhBLXTMXKgV5Ky0tRFhGd2szM1EVOTQmRx5XVwQOMRt5Ly0tbjQJNCo2BR0yLDAzGnNRWTUDOx88PGM9Jh0IXWt6dVFzdXVhUl9LGBhOeBs4PDdpJxZGPjs7PAMgfRkuV1FVaCsDIQ4rYAAhLwoHND8/J0sUMCEFUUNaXSkGOQUtPWtgZ1gCOEF6dVFzdXVhFBAZGGcLPkspLzE9dDEVFmN4FxAgMAUgRkQbEWcWMA43RGNpblhGd2t6dVFzdXVhFBBJWTUWdig4IAAmIhQPMy56aFE1NDkyUToZGGdCeEt5bmNpblgDOS9QdVFzdXVhFBBcViNoeEt5biYnKnIDOS9zfHtZeHhhZFVLSy4RLEsqPiYsKlcMIiYqdR49dSckR0BYTyloLAo7IiZnJxYVMjkufTI8OzskV0RQVykRdEsVISAoIigKNjI/J18QPTQzVVNNXTUjPA88KnkKIRYIMigufRcmOzY1XV9XECQKORlwRGNpblgSNjgxewYyPCFpBB4MEU1CeEt5IiwqLxRGPz43dUxzNj0gRgp/USkGHgIrPTcKJhEKMwQ8Fh0yJiZpFnhMVSYMNwI9bGpDblhGdyI8dRkmOHU1XFVXMmdCeEt5bmNpJx5GESc7MgJ9IjQtX2NJXSIGeBVkbnF7bgwOMiV6PQQ+ewIgWFtqSCIHPEtkbgUlLx8VeTw7ORoAJTAkUBBcViNoeEt5bmNpblgPMWscORA0JnsrQV1JaCgVPRl5MH5pe0hGIyM/O1E7IDhvfkVUSBcNLw4rbn5pCBQHMDh0PwQ+JQUuQ1VLGCIMPGF5bmNpKxYCXS40MVh6X19sGR8WGAsrDi55HRcIGitGGwQVBXsnNCYqGkNJWTAMcA0sICA9JxcIf2JQdVFzdSIpXVxcGDMDKwB3OSIgOlBXeX5zdRU8X3VhFBAZGGdCMQ15Gy0lIRkCMi96IRk2O3UzUURMSilCPQU9RGNpblhGd2t6JRIyOTlpUkVXWzMLNwVxZ0lpblhGd2t6dVFzdXUtW1NYVGcGeFZ5KSY9ChkSNmNzX1FzdXVhFBAZGGdCeAc2LSIlbhsJPiUpdVFzdWhhQF9XTSoAPRlxKm0qIREIJGJ6OgNzZV9hFBAZGGdCeEt5bmMlIRsHO2s9Oh4jdXVhFBAEGDMNNh40LCY7ZhxIMCQ1JVhzOidhBDoZGGdCeEt5bmNpblgKOCg7OVEpOjskFBAZGGdfeB82IDYkLB0Ufy90Lx49MHxhW0IZCU1CeEt5bmNpblhGd2s2OhIyOXUsVUhjVykHeEtkbjcmIA0LNS4ofRV9ODQ5bl9XXW5CNxl5f0lpblhGd2t6dVFzdXUtW1NYVGcQPQkwPDchPVhbdz81OwQ+NzAzHFQXSiIAMRktJjBgbhcUd3tQdVFzdXVhFBAZGGdCNAQ6Ly9pPBcKOwgvJ1FzaHU1W15MVSUHKkM9YDEmIhQlIjkoMB8wLHxhW0IZCE1CeEt5bmNpblhGd2s2OhIyOXU0RFdLWSMHK0tkbjcwPh1OM2UvJRYhNDEkRxkZBXpCeh84LC8sbFgHOS96MV8mJTIzVVRcS2cNKksiM0lpblhGd2t6dVFzdXUtW1NYVGcHKR4wPjMsKlhbdz8jJRR7MXskRUVQSDcHPEJ5c35pbAwHNSc/d1EyOzFhUB5cSTILKBs8KmMmPFgdKkF6dVFzdXVhFBAZGGcONwg4ImM6OhkSJGt6dVFudSE4RFURXGkRLAotPWppc0VGdT87Nx02d3UgWlQZXGkRLAotPWMmPFgdKkF6dVFzdXVhFBAZGGcONwg4ImM6PAhGd2t6dVFudSE4RFURXGkRKA46JyIlHBcKOxsoOhYhMCYyXV9XEWdfZUt7OiIrIh1Edyo0MVE3eyYxUVNQWSswNwc1HjEmKQoDJDgzOh9zOidhT00zMmdCeEt5bmNpblhGdyc4OTI8PDsyDmNcTBMHIB9xbAAmJxYVbWt4dV99dTMuRl1YTAkXNUM6ISonPVFPXWt6dVFzdXVhFBAZGCsANCw2ITNzHR0SAy4iIVlxEjouRAoZGmdMdks/ITEkLwwoIiZyMh48JXxoPhAZGGdCeEt5bmNpbhQEOxE1OxRpBjA1YFVBTG9AGx4rPCYnOlg8OCU/b1FxdXtvFEpWViJLUkt5bmNpblhGd2t6dR0xORggTGpWViJYCw4tGiYxOlBEGioidSs8OzB7FBIZFmlCNQohFCwnK1Fsd2t6dVFzdXVhFBAZVCUOCg47JzE9JgtcBC4uARQrIX1jZlVbUTUWMBhjbmFpYFZGJS44PAMnPSZoPhAZGGdCeEt5bmNpbhQEOx4qMgMyMTAyDmNcTBMHIB9xbBY5KQoHMy4pdR4kOzAlDhAbGGlMeB84LC8sAh0Ifz4qMgMyMTAyHRkzGGdCeEt5bmNpblhGOyk2EAAmPCUxUVQDayIWDA4hOmtrHRQPOi4pdRQiIDwxRFVdAmdAeEV3bjcoLBQDGy40fRQiIDwxRFVdEW5oeEt5bmNpblhGd2t6ORM/BzotWHNMSn0xPR8NKzs9Zlo0OCc2dTImJyckWlNAAmdAeEV3bjEmIhQlIjlzX3tzdXVhFBAZGGdCeEs1LC8dIQwHOxk1OR0gbwYkQGRcQDNKej82OiIlbioJOycpb1FxdXtvFFZWSioDLCUsI2s6OhkSJGUoOh0/JnUuRhAJEW5oeEt5bmNpblhGd2t6ORM/BjAyR1lWVhUNNAcqdBAsOiwDLz9ydyI2JiYoW14ZaigONBhjbmFpYFZGMSQoOBAnGyAsHENcSzQLNwULIS8lPVFPXUF6dVFzdXVhFBAZGGcONwg4ImMvOxYFIyI1O1E1OCESRFVaUSYOcAA8N29pIhkEMidzX1FzdXVhFBAZGGdCeEt5bmMlIRsHO2s/OwUhLHV8FENLSBwJPRIERGNpblhGd2t6dVFzdXVhFBBQXmcWIRs8ZiYnOgoffmtnaFFxITQjWFUbGDMKPQVTbmNpblhGd2t6dVFzdXVhFBAZGGcONwg4ImM8IAwPOxR6aFE2OyEzTR5LVysOKz43OiolAB0eI2s1J1E2OyEzTR5LVysOKz43OiolbhcUd2lld3tzdXVhFBAZGGdCeEt5bmNpblhGdzk/IQQhO3UtVVJcVGdMdkt7biondFhEd2V0dQU8JiEzXV5eEDIMLAI1EWppYFZGdWsoOh0/JndLFBAZGGdCeEt5bmNpblhGdy40MXtzdXVhFBAZGGdCeEt5bmNpPB0SIjk0dR0yNzAtFB4XGGVCMQVjbm5kbHJGd2t6dVFzdXVhFBBcViNoUkt5bmNpblhGd2t6dR0xORIuWFRcVn0xPR8NKzs9Zh4LIxgqMBI6NDlpFldWVCMHNkl1bmEOIRQCMiV4fFhZdXVhFBAZGGdCeEt5IiElChEHOiQ0MUsAMCEVUUhNECEPLDgpKyAgLxROdS8zNBw8OzFjGBAbfC4DNQQ3KmFgZ3JGd2t6dVFzdXVhFBBVWis0NwI9dBAsOiwDLz9yMxwnBiUkV1lYVG9ALgQwKmFlblowOCI+d1h6X3VhFBAZGGdCeEt5bi8rIj8HOyoiLEsAMCEVUUhNECEPLDgpKyAgLxROdSw7ORArLHdtFBJ+WSsDIBJ7Z2pDRFhGd2t6dVFzdXVhFFlfGDQWOR8qYDEoPB0VIxk1OR1zNDslFENNWTMRdhk4PCY6OioJOyd0Jh06ODAFVURYGDMKPQVTbmNpblhGd2t6dVFzdXVhFFxWWyYOeAI9bmNpc1gVIyouJl8hNCckR0RrVysOdhg1Jy4sChkSNmUzMVE8J3VjCxIzGGdCeEt5bmNpblhGd2t6dR08NjQtFF9dXDRCZUsqOiI9PVYUNjk/JgUBOjktGl9dXDRCNxl5f0lpblhGd2t6dVFzdXVhFBAZVCUOCgorKzA9dCsDIx8/LQV7dwcgRlVKTGcwNwc1dGNrblZIdyI+dV99dXdhHAEWGmdMdkstITA9PBEIMGM1MRUgfHVvGhAbEWVLUkt5bmNpblhGd2t6dRQ9MV9LFBAZGGdCeEt5bmNpJx5GBS44PAMnPQYkRkZQWyI3LAI1PWM9Jh0IXWt6dVFzdXVhFBAZGGdCeEs1ISAoIlgFODgudUxzBzAjXUJNUBQHKh0wLSYcOhEKJGU9MAUQOiY1HEJcWi4QLAMqZ2MmPFhWXWt6dVFzdXVhFBAZGGdCeEs1ISAoIlgKIigxGAQ/dWhhZlVbUTUWMDg8PDUgLR0zIyI2Jl80MCENQVNSdTIOLAIpIiosPFAUMikzJwU7JnxhW0IZCU1CeEt5bmNpblhGd2t6dVFzOTctZlVbUTUWMCg2PTdzHR0SAy4iIVlxBzAjXUJNUGchNxgtdGNrblZIdy01JxwyIRs0WRhaVzQWcUt3YGNrbh8JODt4fHtzdXVhFBAZGGdCeEt5bmNpIhoKGz45PjwmOSF7Z1VNbCIaLEN7AjYqJVgrIicuPAE/PDAzDhBBGmdMdksqOjEgIB9IMSQoOBAnfXdkGgJfGmtCNB46JQ48IlFPXWt6dVFzdXVhFBAZGGdCeEs1LC8bKxoPJT8yBxQyMSx7Z1VNbCIaLEN7HCYrJwoSP2sIMBA3LG9hFhAXFmdKPwQ2PmN3c1gFODgudRA9MXVjbXVqGmcNKkt7AAxpZhYDMi96d1F9e3UnW0JUWTMsLQZxIyI9JlYLNjNyZV1zNjoyQBAUGCANNxtwZ2NnYFhEfmlzfHtzdXVhFBAZGGdCeEs8ICdDblhGd2t6dVE2OzFoPhAZGGcHNg9TKy0tZ3JsGyI4JxAhLG8PW0RQXj5Kejg1Jy4sbiooEGsJNgM6JSFhWF9YXCIGeUsJPCY6PVg0PiwyITInJzlhUl9LGBIrdkl1bnZgRA=='
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
