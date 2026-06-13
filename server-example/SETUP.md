# Y2k Key Server — Cloudflare Worker + KV (free)

Server-side key validation. Keys are stored **hashed** (SHA-256) in KV, HWID
**auto-binds** on first use, expiry supported. Plaintext keys never sit at rest.

## 1. Install Wrangler (one time)
```
npm install -g wrangler
wrangler login
```

## 2. Create the KV namespace
```
wrangler kv:namespace create KEYS
```
Copy the printed `id` into **`wrangler.toml`** → `[[kv_namespaces]] id = "..."`.

## 3. Set your admin secret
Edit `wrangler.toml` `ADMIN_SECRET` to a long random string, **or** (better):
```
wrangler secret put ADMIN_SECRET
```

## 4. Deploy
```
wrangler deploy
```
You'll get a URL like `https://y2k-keys.YOURNAME.workers.dev`.

## 5. Point the Key System at it
In `UI/Y2k ui/Keysystem ui.lua` set:
```lua
local KEY_API  = "https://y2k-keys.YOURNAME.workers.dev"
local KEY_LINK = "https://your-key-getter-link"
```

## 6. Manage keys (admin endpoints — need ?secret=ADMIN_SECRET)
Add a key (HWID auto-binds on the buyer's first use):
```
https://y2k-keys.YOURNAME.workers.dev/add?secret=ADMIN&key=ALICE-7F3K&note=alice
```
Add an expiring key (expiry = unix seconds; 0 = never):
```
.../add?secret=ADMIN&key=TRIAL-1&expiry=1767225600&note=trial
```
Reset a buyer's device lock (let them rebind):
```
.../reset?secret=ADMIN&key=ALICE-7F3K
```
Delete / inspect:
```
.../del?secret=ADMIN&key=ALICE-7F3K
.../info?secret=ADMIN&key=ALICE-7F3K
```

## How validation works
- Client (Key System) → `GET /check?key=KEY&hwid=HWID`
- Server hashes the key, looks it up in KV, checks expiry, binds/checks HWID,
  returns `ok` / `invalid` / `expired` / `hwid mismatch`.
- On `ok`, the UI sets `getgenv().SCRIPT_KEY` and your VM-protected script runs.

## Security notes
- Keys in KV are **SHA-256 hashes** → a KV dump shows only hashes.
- Transit is **HTTPS** → keys aren't visible on the wire.
- Keep `ADMIN_SECRET` private (use `wrangler secret put`, not the toml, for prod).
- Free tier: 100k reads/day, 1k writes/day — plenty for a key system.
