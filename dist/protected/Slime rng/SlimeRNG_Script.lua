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

local __k = '9RnOen8y6peGXnjcStlFSKGC'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
