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
-- substring patterns (tools sometimes suffix/version their GUI names)
local SPY_GUI = { "dex", "remotespy", "remote spy", "simplespy", "hydroxide", "spygui", "infiniteyield" }
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
				local nm = string.lower(c.Name)
				for _, pat in ipairs(SPY_GUI) do
					if string.find(nm, pat, 1, true) then return true, "GUI: " .. c.Name end
				end
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
		local n = 0
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
				pcall(onDetect, hits[1].name, hits[1].detail)
				return
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
				if o.kick ~= false then
					pcall(function()
						local lp = game:GetService("Players").LocalPlayer
						lp:Kick(o.kickMessage or ("Tamper detected (" .. tostring(name) .. ")"))
					end)
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

local __k = 'JrvvgQoBZjzmgHXmpkbiH0Aw'
local __p = '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'
local __src = Crypt.open(__p, __k)
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, antiSpy = { kick = true, halt = true } })
