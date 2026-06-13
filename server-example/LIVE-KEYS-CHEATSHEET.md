# Y2k Key Server — LIVE

**Worker URL:** `https://y2k-keys.y2kscript.workers.dev`
**Admin secret:** `DZAD_Pxoqgzd1utaDZC8kCPGQXXRShQHQPEyZsv_dh8`
**KV namespace id:** `e9675dd6a84b45daa95ce5603f3def3f`
**Cloudflare account:** 1a02fd454a6162e395a850459032dc3c (leuleulolo62@gmail.com)
**work.ink link id (locked):** 4578430
**work.ink key page (set as link Destination):** `https://y2k-keys.y2kscript.workers.dev/token?t={TOKEN}`

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

How it's secured:
- Validation is **server-to-server** (your Worker → work.ink over HTTPS). The
  client never decides validity, so it can't fake an `ok`.
- API key `dd317465-...` is stored as an **encrypted Cloudflare secret**
  (`WORKINK_API_KEY`), never in any file. Sent as a bearer header to work.ink.
- `deleteToken=1` burns each token on first use (anti-share).
- HWID auto-binds → token locked to one device.
- Optional **link lock**: only tokens from YOUR link are accepted (see below).

Tunables in `wrangler.toml` [vars] (re-deploy after editing):
- `WORKINK_ENABLED = "1"`   — turn work.ink tokens on/off
- `WORKINK_TTL = "86400"`   — how long a validated token grants access (24h).
  After this the buyer redoes the link → repeat ad views = your payout.
- `WORKINK_SINGLE_USE = "1"`— burn the token on first validate.
- `WORKINK_LINK_ID = ""`    — empty = accept any work.ink token. Set to your
  link's numeric id to reject tokens from any other link (see "Lock to your link").

### Lock to your link (do this once)
1. Complete your own link, copy the token (don't run it anywhere yet).
2. Peek it (does NOT burn it):
   `https://y2k-keys.y2kscript.workers.dev/wink?secret=SECRET&token=YOUR_TOKEN`
3. Read `info.linkId` (a number) from the JSON.
4. Put that number in `wrangler.toml` → `WORKINK_LINK_ID = "10345"`, then
   `wrangler deploy`. Now only YOUR link's tokens work.

To test the live flow: complete your link → copy token → run the script → paste
the token in the Key System UI → should validate.

## Wired into the UI
`UI/Y2k ui/Keysystem ui.lua` → `KEY_API` is set to the live URL.
Still TODO by you: set `KEY_LINK` to wherever buyers get a key (Linkvertise / shop / Discord).
