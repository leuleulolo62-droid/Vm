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

local __k = '5bKGTw46mqYT3LtGrMYUxl7d'
local __p = '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GkYYKBEsNXUuBUUQQAMnDjoHQUIgEDc1VCkGZ09tPjQVCQ0jUBYYIiYBXVUIWXsCWj4AMhMhEDsIGUMpVAwqIDEFFh9nHTY3UiBUERs/LSAZAGIXUBBrZ3RXFBZQUT41XilOABc5CjAKGl4HUEppET0FQEMMHQwnVj5WbnghNjYZABcoWgEqKwQbVU8IA3l0E2xUZ09tCTkZFVIWRkwHKDcWWGYBECAxQUZ+LhRtNzoMTFAFWAdxDic7W1cJFD18GmwALxcjeTIZAVJKeQ0qIzETDmEMGC18GmwRKRZHU3hVTNXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipDxAXHllHWw3CDwLEBJyQRpE1/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9k8zE0dnkpefdu8DojqL01/fbpcHn1qP9ezU7UC0YZzEiNzMRCxdZFRk2TRcYWlAEFncTcgExGDwMFBBYTApEFzYjInQkQEQCHz4xQDhUBRM5LTkdC0ULQAwvNHZ9d1kDFzAzHRw4BjEIBhw8TBdECEJ6d2BDDQFbQG1iAEY3KBwrMDJWL2UhdDYEFXRXFBZQUXsNWikYIxsjPnU5HkMXF2gIKDoRXVFDIhoGehwgGCQIC3VFTBVVG1Jld3Z9d1kDFzAzHRk9GCAICRpYTBdECEJpLyADREVXXnYmUjtaIBs5MSAaGUQB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o67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipDxAXHlgHWw1EiYCeQc5K3MreS5mBBU5d3MhUbvUp2wSLgAoKnUpTEAMUAxrCzUEQGQIEDogEy0AMwBtOj0ZAlABRkIkKXQaTRYOGTgmOWFZZ5DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpYDe17bipNT44bvBo67h15DYybft/NXxpWgnKDcWWBYsBC07YS0TIx0hNXVFTExEZhYqMzFXCRYWe3l0E2wRKRMvNTAcTBdEFV9rITUbR1NBe3l0E2wQIh4sIHVYTBdEFV9rd3pHARpNUXl0HmFUNxM4KjBYDVEQUBBrIzEDUVUZGDczEz4VIBYiNTlYDlICWhAuZyQFUUUeGDczEx1+Z1JteTgRAmQUVAEiKTNXCRZdX214E2xUZ1JgdHUcA1lDQUItLiYSFFAMAi0xQWwALxMjeSEQBUREHQM9KD0TFEUdEDR0XyMbNwFkUyhUTGgIVBE/AT0FURZQUWl4ExMXKBwjeWhYAl4IFR9BTTgYV1cBUT8hXS8ALh0jeTcRAlMpTDAqIDAYWFpFWFN0E2xULhRtGCAMA2UFUgYkKzhZa1UCHzd0RyQRKVIMLCEXPlYDUQ0nK3ooV1kDH2MQWj8XKBwjPDYMRB5fFSM+MzslVVEJHjU4HRMXKBwjeWhYAl4IFQclI15XFBZNHTY3UiBUJBosK3lYMxtE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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
