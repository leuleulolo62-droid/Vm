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

local __k = 'UP54i4wvmL7N5TPG3uec6a9m'
local __p = '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UT0jM1IbBgYeABVNN3kVRgxAAgQDbB8vFXlwJRpbKAJRD1AZIDRQFAxaE3xnYRpu18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amaxRAdWMbFCt1OzpNrrfaFTI5KVdVCQpABBkPNDxZGElEBRMJJVQ6FTgxKVccCwQ8TBRNt8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9rqLe18HApablh/amg6z9t8Wl1vykleP9RhpjFR0dF3wnMSJ4NQNNIThQFAtVGxpNJURuVDozL1wHAAcWDldNIThQFApYHhMDOBdmRjEiMVYHRSBwE1gAMH1GTQdXBFYEOB5iFSc/TR5YRSJFElwANzxMeABaEhcfGlIiWjc5M0pVDBAWAFUaNClGFFkaVyEIbFQhWCQlM1ZVEwZaDloEISkVVhAUBBcAPFsnWzNwN1wGDBdfDlcee1pZWwpVG1YvLVsiFWlwPDlVRUMWPlUMJiRlWxoUV1ZNbApuWz08azlVRUMWPlUMJiRhXQpfV1ZNbApuBXhaZxNVRTxABFUCNjlBTUkUV1ZQbGErViA/NQBbCwZBSRBBX3AVFEkZWlYuLVQmUDBwNVYTABFTD1oIJnDXtP0UFgACJVNuRjcxKV0cCwQWNlYfPiNFVQpRVxMbKUU3FRw1JkEBBwZXFRlFY2D2o0ZHXnxNbBduajcxJFsQAS5ZBVwB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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, antiSpy = { kick = true, halt = true } })
