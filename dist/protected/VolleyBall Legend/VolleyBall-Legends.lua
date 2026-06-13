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

local __k = 'wn7mP0ydeOaZtwX4vgUp76jg'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, neuterAC = true, antiSpy = { kick = true, halt = true } })
