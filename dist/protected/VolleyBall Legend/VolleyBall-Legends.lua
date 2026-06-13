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

local __k = 'fw1hjjmkfvlBb6028wvjLWkz'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, antiSpy = { kick = true, halt = true } })
