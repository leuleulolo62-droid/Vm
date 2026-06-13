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
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
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

local __k = '9KEYy1ot1hYF56jyRVzL0OjF'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, antiSpy = { kick = true, halt = true } })
