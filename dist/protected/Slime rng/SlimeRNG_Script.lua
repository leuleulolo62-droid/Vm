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
-- substring patterns (tools sometimes suffix/version their GUI names)
local SPY_GUI = { "dex", "remotespy", "remote spy", "simplespy", "hydroxide", "spygui", "infiniteyield" }
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
				local nm = string.lower(c.Name)
				for _, pat in ipairs(SPY_GUI) do
					if string.find(nm, pat, 1, true) then return true, "GUI: " .. c.Name end
				end
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
		local n = 0
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
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
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
				if o.kick ~= false then
					pcall(function()
						local lp = game:GetService("Players").LocalPlayer
						lp:Kick(o.kickMessage or ("Tamper detected (" .. tostring(name) .. ")"))
					end)
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

local __k = 'KaA2BBPjkn2583cSoczF5vCh'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
