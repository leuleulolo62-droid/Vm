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

local __k = 'jZ8NCdsPp7QxsCrBcxQN3htg'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2, antiSpy = { kick = true, halt = true } })
