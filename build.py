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

def wrap_script(src_text: str, name: str) -> str:
    runtime = bundle_runtime().rsplit("return Vm\n", 1)[0]  # drop trailing return
    key = randkey()
    payload_b = src_text.encode("utf-8")
    sealed = base64.b64encode(xor(payload_b, key.encode())).decode()
    checksum = fnv1a(payload_b)
    # per-build watermark -> each delivered file is unique & traceable to a buyer
    watermark = (CONFIG.get("watermark_prefix", "Y2k")) + "-" + randkey(12)
    license_opts = lua_license_opts()
    # the protected file: inline runtime, then decrypt+run under the Vm
    out = []
    # Key System gate FIRST. Wrapped in do...end so its locals don't blow the
    # 200-local chunk limit when combined with the runtime. It blocks until a
    # valid key sets getgenv().SCRIPT_KEY, which the VM license check then reads.
    if KEYSYS_UI:
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

def upload_blob(name, blob):
    secret = os.environ.get("Y2K_ADMIN_SECRET", "")
    if not secret:
        raise SystemExit("deliver mode needs your admin secret:  set Y2K_ADMIN_SECRET=... before running")
    url = (WORKER_URL + "/upload?secret=" + urllib.parse.quote(secret)
           + "&name=" + urllib.parse.quote(name, safe=""))
    req = urllib.request.Request(url, data=blob.encode(), method="POST",
                                 headers={"content-type": "text/plain",
                                          # Cloudflare blocks the default Python-urllib UA (err 1010)
                                          "user-agent": "Mozilla/5.0 (Y2k-build)"})
    with urllib.request.urlopen(req, timeout=25) as r:
        return r.read().decode()

# Delivery build: the script is NOT embedded. The file fetches the (encrypted)
# blob from your worker via opts.deliver, and only gets it if the key validates.
def wrap_script_delivery(src_text: str, name: str):
    runtime = bundle_runtime().rsplit("return Vm\n", 1)[0]
    key = randkey()
    payload_b = src_text.encode("utf-8")
    sealed = base64.b64encode(xor(payload_b, key.encode())).decode()
    checksum = fnv1a(payload_b)
    watermark = (CONFIG.get("watermark_prefix", "Y2k")) + "-" + randkey(12)
    endpoint = WORKER_URL + "/deliver?name=" + urllib.parse.quote(name, safe="")
    out = []
    if KEYSYS_UI:
        out.append("-- ===== Key System (must pass before the script runs) =====\n")
        out.append("local function __y2k_keygate()\n")
        out.append(KEYSYS_UI)
        out.append("\nend\n__y2k_keygate()\n")
    out.append("-- Protected with Vm runtime. The script is NOT in this file --\n")
    out.append("-- it is fetched from your server only after the key validates.\n")
    out.append(runtime)
    out.append("\n-- watermark: %s\n" % watermark)
    out.append(
        "return Vm.run(\"\", { name = %r, checksum = %d, interval = 2, watermark = %r, "
        "neuterAC = true, antiSpy = { kick = true, halt = true }, "
        "deliver = { endpoint = %r, "
        "key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, "
        "cryptKey = %r } })\n"
        % (name, checksum, watermark, endpoint, key))
    return "".join(out), sealed

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
                    text, blob = wrap_script_delivery(src, name)
                    resp = upload_blob(name, blob)
                    outp = os.path.join(out_dir, rel)
                    os.makedirs(os.path.dirname(outp), exist_ok=True)
                    open(outp, "w", encoding="utf-8").write(text)
                    count += 1
                    print("  delivered", rel, "->", resp)
        print("done:", count, "scripts uploaded + protected ->", out_dir)
    else:
        print(__doc__)

if __name__ == "__main__":
    main()
