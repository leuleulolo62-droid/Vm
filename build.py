#!/usr/bin/env python3
"""
Vm bundler / applier.

Executors have no file-based `require`, so the modular src/ files are inlined
into one self-contained runtime, and each script is wrapped (encrypted payload
+ runtime) into a single protected .lua.

Usage:
  python build.py runtime
      -> dist/vm_runtime.lua            (bundled VM only; for testing)
  python build.py wrap <in.lua> <out.lua> [name]
      -> a protected single-file script
  python build.py all [scripts_dir] [out_dir]
      -> wrap every *.lua under scripts_dir (default ../Scripts), payload EMBEDDED
  python build.py deliver [scripts_dir] [out_dir]
      -> server-side delivery: upload each script's blob to your worker and emit
         payload-FREE files (a leaked file has no script). Needs Y2K_ADMIN_SECRET.
"""
import os, re, sys, random, string, base64

HERE = os.path.dirname(os.path.abspath(__file__))
SRC  = os.path.join(HERE, "src")
DIST = os.path.join(HERE, "dist")
MODULE_ORDER = ["Crypt", "Secure", "Environment", "Integrity", "Stealth", "Memory",
                "Defense", "Neuter", "License", "Vm"]

def read_module(name):
    with open(os.path.join(SRC, name + ".lua"), "r", encoding="utf-8") as f:
        s = f.read()
    # inline require(script.Parent.X) -> X (the outer local)
    s = re.sub(r'require\(\s*script\.Parent\.(\w+)\s*\)', r'\1', s)
    return s

def bundle_runtime():
    parts = ["-- Vm protection runtime (bundled). Do not edit by hand.\n"]
    for name in MODULE_ORDER:
        body = read_module(name)
        parts.append(f"local {name} = (function()\n{body}\nend)()\n")
    parts.append("return Vm\n")
    return "".join(parts)

# ---- XOR + base64 (mirror of Crypt.seal so the bundle's Crypt.open recovers it)
def xor(data: bytes, key: bytes) -> bytes:
    return bytes(b ^ key[i % len(key)] for i, b in enumerate(data))

def fnv1a(s: bytes) -> int:
    h = 2166136261
    for b in s:
        h ^= b
        h = (h * 16777619) % 4294967296
    return h

def randkey(n=24):
    return "".join(random.choice(string.ascii_letters + string.digits) for _ in range(n))

# optional license/watermark config (vmconfig.json next to build.py). Example:
# { "license": { "endpoint": "https://you.workers.dev/check", "expiry": 0 },
#   "watermark_prefix": "Y2k" }
def load_config():
    p = os.path.join(HERE, "vmconfig.json")
    if os.path.exists(p):
        import json
        try:
            return json.load(open(p, "r", encoding="utf-8"))
        except Exception:
            return {}
    return {}

CONFIG = load_config()

# Optionally load the Key System UI so each protected file shows the key prompt
# FIRST (it blocks on `while not getgenv().SCRIPT_KEY`), then the VM payload runs.
def load_keysystem_ui():
    rel = CONFIG.get("keysystem_ui")
    if not rel:
        return None
    path = os.path.normpath(os.path.join(HERE, rel))
    if not os.path.exists(path):
        print("  [warn] keysystem_ui not found:", path)
        return None
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        return f.read()

KEYSYS_UI = load_keysystem_ui()

def lua_license_opts():
    lic = CONFIG.get("license")
    if not lic:
        return ""
    parts = []
    if lic.get("endpoint"): parts.append("endpoint = %r" % lic["endpoint"])
    if lic.get("expiry"):   parts.append("expiry = %d" % int(lic["expiry"]))
    if lic.get("keys"):
        keys = ", ".join("%r" % k for k in lic["keys"])
        parts.append("keys = { %s }" % keys)
    if not parts:
        return ""
    # key comes from the Key System UI (getgenv().SCRIPT_KEY) or getgenv().Key
    return (", license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, "
            "%s }" % ", ".join(parts))

def wrap_script(src_text: str, name: str, include_keyui=True, use_license=True) -> str:
    runtime = bundle_runtime().rsplit("return Vm\n", 1)[0]  # drop trailing return
    key = randkey()
    payload_b = src_text.encode("utf-8")
    sealed = base64.b64encode(xor(payload_b, key.encode())).decode()
    checksum = fnv1a(payload_b)
    # per-build watermark -> each delivered file is unique & traceable to a buyer
    watermark = (CONFIG.get("watermark_prefix", "Y2k")) + "-" + randkey(12)
    license_opts = lua_license_opts() if use_license else ""
    # the protected file: inline runtime, then decrypt+run under the Vm
    out = []
    # Key System gate FIRST. Wrapped in do...end so its locals don't blow the
    # 200-local chunk limit when combined with the runtime. It blocks until a
    # valid key sets getgenv().SCRIPT_KEY, which the VM license check then reads.
    if KEYSYS_UI and include_keyui:
        # run the UI in its own function: isolates its locals (own 200-local
        # budget) and a stray top-level `return` only exits the gate, not the
        # whole script. It blocks on `while not getgenv().SCRIPT_KEY` then returns.
        out.append("-- ===== Key System (must pass before the script runs) =====\n")
        out.append("local function __y2k_keygate()\n")
        out.append(KEYSYS_UI)
        out.append("\nend\n__y2k_keygate()\n-- ===== Protected payload =====\n")
    out.append("-- Protected with Vm runtime. Tampering halts execution.\n")
    out.append(runtime)
    out.append("\nlocal __k = %r\n" % key)
    out.append("local __p = %r\n" % sealed)
    out.append("local __src = Crypt.open(__p, __k)\n")
    # antiSpy on by default: kicks on Dex / RemoteSpy / Infinite Yield / hooked http
    # / namecall. The reliable Dex(weak-table)+RemoteSpy(gc-spike) probes run THROTTLED
    # (every ~15s). NOTE: those probes fire a remote / force GC -> they add game-AC
    # surface. For an AC-heavy game (e.g. Rivals) wrap that one with
    # antiSpy={kick=true,remote=false,dex=false} to rely on IY/GUI/http/namecall only.
    out.append("-- watermark: %s\n" % watermark)
    out.append(
        "return Vm.run(__src, { name = %r, checksum = %d, interval = 2, watermark = %r, "
        "neuterAC = true, antiSpy = { kick = true, halt = true }%s })\n"
        % (name, checksum, watermark, license_opts))
    return "".join(out)

import urllib.request, urllib.parse

WORKER_URL = (CONFIG.get("worker") or "https://y2k-keys.y2kscript.workers.dev").rstrip("/")

def _post(path, name, body):
    secret = os.environ.get("Y2K_ADMIN_SECRET", "")
    if not secret:
        raise SystemExit("deliver mode needs your admin secret:  set Y2K_ADMIN_SECRET=... before running")
    url = (WORKER_URL + path + "?secret=" + urllib.parse.quote(secret)
           + "&name=" + urllib.parse.quote(name, safe=""))
    req = urllib.request.Request(url, data=body.encode(), method="POST",
                                 headers={"content-type": "text/plain",
                                          # Cloudflare blocks the default Python-urllib UA (err 1010)
                                          "user-agent": "Mozilla/5.0 (Y2k-build)"})
    with urllib.request.urlopen(req, timeout=25) as r:
        return r.read().decode()

def upload_blob(name, blob):   # the VM+script bundle  -> /deliver (key-gated)
    return _post("/upload", name, blob)

def upload_loader(name, text): # the key-box bootstrap -> /loader (public one-liner)
    return _post("/uploader", name, text)

# STEALTH DELIVERY. The hosted file is a tiny BOOTSTRAP: only the key UI (which
# must be visible since it runs before a key exists) + a few lines that fetch the
# full protected BUNDLE (VM runtime + script) from your server and run it -- only
# after the key validates. So the link reveals no VM internals and no script.
#
# Returns (bootstrap_text, bundle_text):
#   - bundle_text  -> upload to /upload (lives on the server, key-gated)
#   - bootstrap_text -> the file you host / hand out
def wrap_bootstrap(src_text: str, name: str):
    # the bundle = full protected runtime WITHOUT the key UI and WITHOUT a license
    # check (the bootstrap already gated the key); it just runs the script in the VM.
    bundle = wrap_script(src_text, name, include_keyui=False, use_license=False)
    endpoint = WORKER_URL + "/deliver?name=" + urllib.parse.quote(name, safe="")
    out = []
    if KEYSYS_UI:
        out.append("-- ===== Key System (only thing visible here) =====\n")
        out.append("local function __y2k_keygate()\n")
        out.append(KEYSYS_UI)
        out.append("\nend\n__y2k_keygate()\n")
    # tiny loader: pull the VM+script bundle from the server after the key passes
    out.append("-- The protection and the script both live on the server; they are\n")
    out.append("-- fetched and run only after the key validates. Nothing else is here.\n")
    out.append("do\n")
    out.append("  local KEY = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key\n")
    out.append("  local HWID = getgenv and getgenv().HWID\n")
    out.append("  if not HWID or HWID == '' then\n")
    out.append("    pcall(function() HWID = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)\n")
    out.append("    if not HWID then pcall(function() HWID = game:GetService('RbxAnalyticsService'):GetClientId() end) end\n")
    out.append("  end\n")
    out.append("  HWID = tostring(HWID or 'unknown')\n")
    out.append("  local HS = game:GetService('HttpService')\n")
    out.append("  local function enc(s) local ok,r = pcall(function() return HS:UrlEncode(s) end) return ok and r or s end\n")
    out.append("  local function httpGet(u)\n")
    out.append("    for _,f in ipairs({\n")
    out.append("      function() return game:HttpGetAsync(u) end,\n")
    out.append("      function() return game:HttpGet(u) end,\n")
    out.append("      function() return request and request({Url=u,Method='GET'}).Body end,\n")
    out.append("    }) do local ok,b = pcall(f) if ok and type(b)=='string' then return b end end\n")
    out.append("  end\n")
    out.append("  local url = %r .. '&key=' .. enc(tostring(KEY)) .. '&hwid=' .. enc(HWID)\n" % endpoint)
    out.append("  local body = httpGet(url)\n")
    out.append("  if not body then return warn('[Y2k] server unreachable') end\n")
    out.append("  if string.sub(body,1,3) ~= 'ok\\n' then return warn('[Y2k] ' .. tostring(body)) end\n")
    out.append("  local fn = (loadstring or load)(string.sub(body,4), '=Y2k')\n")
    out.append("  if fn then fn() else warn('[Y2k] load failed') end\n")
    out.append("end\n")
    return "".join(out), bundle

def main():
    os.makedirs(DIST, exist_ok=True)
    if len(sys.argv) < 2:
        print(__doc__); return
    cmd = sys.argv[1]

    if cmd == "runtime":
        out = os.path.join(DIST, "vm_runtime.lua")
        open(out, "w", encoding="utf-8").write(bundle_runtime())
        print("wrote", out, "(%d bytes)" % os.path.getsize(out))

    elif cmd == "wrap":
        inp, outp = sys.argv[2], sys.argv[3]
        name = sys.argv[4] if len(sys.argv) > 4 else os.path.basename(inp)
        src = open(inp, "r", encoding="utf-8", errors="replace").read()
        open(outp, "w", encoding="utf-8").write(wrap_script(src, name))
        print("wrapped", inp, "->", outp)

    elif cmd == "all":
        scripts_dir = sys.argv[2] if len(sys.argv) > 2 else os.path.normpath(
            os.path.join(HERE, "..", "Scripts"))
        out_dir = sys.argv[3] if len(sys.argv) > 3 else os.path.join(DIST, "protected")
        os.makedirs(out_dir, exist_ok=True)
        count = 0
        for root, _, files in os.walk(scripts_dir):
            for fn in files:
                if fn.lower().endswith(".lua"):
                    inp = os.path.join(root, fn)
                    rel = os.path.relpath(inp, scripts_dir)
                    name = os.path.splitext(rel)[0].replace(os.sep, "/")
                    outp = os.path.join(out_dir, rel)
                    os.makedirs(os.path.dirname(outp), exist_ok=True)
                    src = open(inp, "r", encoding="utf-8", errors="replace").read()
                    open(outp, "w", encoding="utf-8").write(wrap_script(src, name))
                    count += 1
                    print("  protected", rel)
        print("done:", count, "scripts ->", out_dir)

    elif cmd == "deliver":
        # server-side delivery: upload each script's blob, emit payload-free files
        scripts_dir = sys.argv[2] if len(sys.argv) > 2 else os.path.normpath(
            os.path.join(HERE, "..", "Scripts"))
        out_dir = sys.argv[3] if len(sys.argv) > 3 else os.path.join(DIST, "delivery")
        os.makedirs(out_dir, exist_ok=True)
        count = 0
        for root, _, files in os.walk(scripts_dir):
            for fn in files:
                if fn.lower().endswith(".lua"):
                    inp = os.path.join(root, fn)
                    rel = os.path.relpath(inp, scripts_dir)
                    name = os.path.splitext(rel)[0].replace(os.sep, "/")
                    src = open(inp, "r", encoding="utf-8", errors="replace").read()
                    bootstrap, bundle = wrap_bootstrap(src, name)
                    upload_blob(name, bundle)     # VM+script bundle -> /deliver (key-gated)
                    upload_loader(name, bootstrap)  # key box        -> /loader (public)
                    outp = os.path.join(out_dir, rel)
                    os.makedirs(os.path.dirname(outp), exist_ok=True)
                    open(outp, "w", encoding="utf-8").write(bootstrap)  # local reference copy
                    count += 1
                    enc = urllib.parse.quote(name, safe="")
                    print('  %s  ->  loadstring(game:HttpGet("%s/loader?name=%s"))()'
                          % (rel, WORKER_URL, enc))
        print("done:", count, "scripts on server. Post the one-liners above.")
    else:
        print(__doc__)

if __name__ == "__main__":
    main()
