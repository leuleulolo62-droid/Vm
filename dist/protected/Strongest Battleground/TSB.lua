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

local __k = 'IjXwKsq7OVQ9iq2McqRFNBOf'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-bRE474jYMeDS
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2, watermark = 'Y2k-bRE474jYMeDS', neuterAC = true, antiSpy = { kick = true, halt = true } })
