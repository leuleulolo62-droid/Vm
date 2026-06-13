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

local __k = 'BgUEoaKYLiuYCiOiX2HYb7BR'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
