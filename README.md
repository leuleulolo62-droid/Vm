# Vm — isolated protection runtime for Luau scripts

Wraps your scripts in a sealed runtime: the real executor functions are captured
into private closures **before** any spy can hook them, your script sees only
protected proxies, runs inside an isolated environment, and the runtime
self-destructs if tampered with.

> Built for protecting **your own** scripts (the Y2k hub). It hardens the runtime
> surface; see **Limitations** for what it does and does not stop.

## Layout (modular `src/`, bundled by `build.py`)
| file | role |
|---|---|
| `src/Crypt.lua` | XOR cipher, FNV-1a hash, base64, PRNG (hide embedded strings, integrity) |
| `src/Secure.lua` | **core**: capture real executor funcs → private upvalues; expose `newcclosure` proxies |
| `src/Environment.lua` | sealed sandbox `_ENV` (proxies + fall-through to real globals; locked metatable) |
| `src/Integrity.lua` | anti-tamper: capture genuineness, proxy-identity, env-seal, opaqueness, background watchdog |
| `src/Stealth.lua` | **anti-detection**: spoof `identifyexecutor`, hide hooks (`iscclosure`/`islclosure`), `checkcaller`→false, filter `getgc` to hide our objects |
| `src/Memory.lua` | **resource scope + leak/overflow guard**: tracks threads/connections, deterministic teardown, GC budget watchdog |
| `src/Defense.lua` | **anti-spy/tamper**: HTTP spy, namecall hook, remote spy, Dex, **SaveInstance guard, getgc-scan, spy globals** |
| `src/Neuter.lua` | **AC neutralizer** (opt-in): global-spoof + upvalue/table patch, honest "AC bypass fail" reporting |
| `src/License.lua` | **anti-leak**: key / HWID whitelist, expiry, server validation + server-side payload delivery |
| `src/Vm.lua` | orchestrator: `Vm.run(src, opts)` / `Vm.protect(fn, opts)` |

Anti-leak / licensing: copy `vmconfig.json.example` → `vmconfig.json`, set your
`license.endpoint` / `keys` / `expiry`, and deploy `server-example/worker.js`
(free Cloudflare Worker). Users run with `getgenv().Key = "..."` before the loader.
Each built file carries a unique **watermark** (traceable to a buyer).
| `build.py` | inlines modules into one file + wraps scripts (encrypted payload + runtime) |

## Security model — how it protects
1. **Spy/HTTP invisibility.** At load (before a spy installs hooks) Secure captures
   `request`/`http_request`/`readfile`/`HttpGet`/… into private upvalues (cloned where
   supported). Your script calls the **proxy** → the captured original, so a spy that
   later hooks the *global* `request` never sees your traffic — it bypasses the hook.
2. **Opaque proxies.** Proxies are `newcclosure`s → `iscclosure()` passes and
   `getupvalues()` is blocked, hiding the captured originals from gc/upvalue dumps.
3. **Isolation.** The script runs under a sealed `_ENV`: sensitive names resolve to
   proxies, everything else falls through to real globals (so full Luau semantics —
   functions, closures, tables, coroutines, `game`, `task`, … all work), and the
   script's global writes stay sandbox-local. The env metatable is locked
   (`getmetatable` → `"locked"`).
4. **Anti-tamper.** Startup gate + a background watchdog re-check: were the executor
   funcs already hooked at capture? were our proxies swapped? is the env metatable
   intact? are the proxies still opaque? On violation → **self-destruct**: proxies are
   wiped and execution halts with an error, so the protected logic can't continue under
   a compromised runtime.
5. **Encrypted payload.** Each protected file ships the script as `base64(xor(src,key))`
   with an FNV-1a checksum the runtime verifies before running (refuses on mismatch) —
   no plaintext source sits in the file.

## Usage
```bash
# bundle the runtime only (for testing)
python build.py runtime              # -> dist/vm_runtime.lua

# protect one script
python build.py wrap "in.lua" "out.lua" "Display Name"

# protect ALL scripts (defaults to ../../Script/Script -> dist/protected/)
python build.py all
```
Each `dist/protected/<game>/<script>.lua` is self-contained: drop it where your
`Loader.lua` currently points (or host it), and it runs protected.

### In code
```lua
local Vm = loadstring(game:HttpGet(".../vm_runtime.lua"))()
Vm.run(scriptSource, { name = "Sell a Lemon", strict = false, interval = 2 })
```
`opts`: `name`, `strict` (abort if executor funcs look pre-hooked), `interval`
(watchdog seconds), `onTamper(reason)`, `checksum` (source pin).

## Anti-detection (Stealth) — environment spoofing (full sUNC surface)
On by default (`opts.stealth ~= false`). Installed FIRST, before your script runs.
Covers the detection-relevant functions across the sUNC standard (docs.sunc.su):
- **identity**: `identifyexecutor` / `getexecutorname` → fake name or nil
- **closures**: `iscclosure`/`islclosure`/`isexecutorclosure` report *our* funcs (and
  any you `markGenuine`) as un-hooked; `checkcaller` → false; `getfunctionhash` → stable fake for ours
- **environment/gc**: `getgc`, `filtergc`, `getreg` → our objects filtered out
- **instances**: `getinstances`, `getnilinstances` → our instances filtered out
- **scripts**: `getloadedmodules`, `getrunningscripts`, `getscripts` filtered;
  `getcallingscript`/`getscriptbytecode`/`getscriptclosure`/`getscripthash`/`getsenv`
  → return nothing for scripts you `hideScript`
- **debug**: `getupvalue(s)`/`getconstant(s)`/`getproto(s)` → blank for our funcs

Uses `hookfunction` (rewrites the function object, so even a reference the AC
captured early is affected) wrapped in `newcclosure` (stays a C-closure → passes
closure-type checks). Configure via `opts.stealthOpts = { spoofName="…", spoofVersion="…" }`.

**Honest scope:** this beats ACs that read these globals at runtime and trust them.
It does **not** beat an AC that (a) fully ran before you load, (b) re-implements the
checks inside its own VM, or (c) validates server-side. It **raises the bar across
games**; it is not guaranteed immunity (e.g. Rivals' AC loads in ReplicatedFirst,
before you, and validates server-side). Mark your own cheat's hooks with
`Stealth.markGenuine(fn)` so they read as clean.

## Memory safety — no leaks, no overflow
Every run gets a **resource scope** (`Memory.new()`):
- the watchdog + any thread/connection it spawns are **tracked**, and **always**
  torn down when the script returns, errors, or trips tamper (`mem:cleanup()` →
  cancel threads, disconnect connections, force `collectgarbage("collect")`),
- object registries use **weak keys** so they never pin game objects alive,
- bookkeeping is **capped** (`MAX_TRACKED`) so the tracking itself can't grow,
- a **budget guard** polls `collectgarbage("count")`; when memory crosses
  `opts.memBudgetKB` (default ~700 MB) it forces a GC, and if it's *still* over it
  escalates to `onOverflow` → the VM halts. A runaway or hostile script can't
  balloon memory unbounded.

## Limitations (honest)
- **This is a runtime sandbox, not a bytecode VM.** Your script still runs as real
  Luau, so a determined attacker sharing the executor VM can still `getgc`/decompile
  the script's *own* bytecode. Preventing that requires a full bytecode VM (Luraph-grade)
  — a separate, much larger build. What this stops: global-hook HTTP/file spies, proxy/
  env tampering, casual inspection, and plaintext-in-file leakage.
- Protection strength depends on the executor exposing `newcclosure`, `iscclosure`,
  `clonefunction`. Missing ones degrade gracefully (proxies still bypass global hooks).
- The watchdog runs while the script runs; it stops when the script returns.

## Tests
`python block.py <file>` / `python check.py <file>` — structural validity checks
(all modules + bundle + protected outputs pass `RESULT: OK`). Run a protected file in
your executor to validate end-to-end; report any error and it's a quick fix.
