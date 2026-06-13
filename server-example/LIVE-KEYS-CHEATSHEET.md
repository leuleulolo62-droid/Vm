# Y2k Key Server — LIVE

**Worker URL:** `https://y2k-keys.y2kscript.workers.dev`
**Admin secret:** `DZAD_Pxoqgzd1utaDZC8kCPGQXXRShQHQPEyZsv_dh8`
**KV namespace id:** `e9675dd6a84b45daa95ce5603f3def3f`
**Cloudflare account:** 1a02fd454a6162e395a850459032dc3c (leuleulolo62@gmail.com)

Keys are stored **SHA-256 hashed** in KV. HWID **auto-binds** on first use and
locks after that. Everything below is just a URL you paste in a browser.

## Manage keys (paste in browser)
Replace `SECRET` with the admin secret above.

Add a key (HWID binds on the buyer's first run):
```
https://y2k-keys.y2kscript.workers.dev/add?secret=SECRET&key=ALICE-7F3K&note=alice
```
Add an expiring key (expiry = unix seconds; get one from epochconverter.com):
```
https://y2k-keys.y2kscript.workers.dev/add?secret=SECRET&key=TRIAL-1&expiry=1788300000&note=trial
```
Reset a buyer's device lock (let them move PCs):
```
https://y2k-keys.y2kscript.workers.dev/reset?secret=SECRET&key=ALICE-7F3K
```
Delete a key / inspect a key:
```
https://y2k-keys.y2kscript.workers.dev/del?secret=SECRET&key=ALICE-7F3K
https://y2k-keys.y2kscript.workers.dev/info?secret=SECRET&key=ALICE-7F3K
```

## Test key (already added)
`TESTKEY-123` — bound to `device-AAA`. Use `/reset` on it before real testing,
or `/del` it when you're done.

## Re-deploy after editing worker.js
```
cd "D:\SCRIPT PROJECT MONEY\VM\Vm\server-example"
wrangler deploy
```

## work.ink integration (LIVE)
Your `/check` now accepts **two kinds of keys**:
1. **Admin keys** you add with `/add` (permanent, paid customers).
2. **work.ink tokens** — buyers complete `https://work.ink/2Dgt/ks-int12887-kq76mlra7lo`,
   get a token, paste it in the UI. The Worker validates it with work.ink, then
   caches it (HWID-locked) for `WORKINK_TTL` seconds.

Tunables in `wrangler.toml` [vars] (re-deploy after editing):
- `WORKINK_ENABLED = "1"`  — turn work.ink tokens on/off
- `WORKINK_TTL = "86400"`  — how long a token stays good (24h). After this the
  buyer must redo the link → that's how work.ink pays you (repeat ad views).
- `WORKINK_SINGLE_USE = "1"` — burns the token on first validate (anti-share).

To test: complete your OWN work.ink link, copy the token it gives you, run the
script, paste the token in the Key System UI → should say valid.

## Wired into the UI
`UI/Y2k ui/Keysystem ui.lua` → `KEY_API` is set to the live URL.
Still TODO by you: set `KEY_LINK` to wherever buyers get a key (Linkvertise / shop / Discord).
