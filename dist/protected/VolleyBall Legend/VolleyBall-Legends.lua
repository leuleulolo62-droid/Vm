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

local __k = 'yb2UoxsvoDskfvWVNHLrIJ9k'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-WGGgCGWY4WkW
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, watermark = 'Y2k-WGGgCGWY4WkW', neuterAC = true, antiSpy = { kick = true, halt = true } })
