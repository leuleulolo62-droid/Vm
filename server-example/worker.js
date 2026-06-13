// ============================================================================
//  Y2k Key Server  --  Cloudflare Worker + KV
//  Server-side key validation with SHA-256 key hashing, HWID auto-binding,
//  expiry, and admin endpoints. Keys are stored HASHED in KV (a KV dump shows
//  only hashes), and transmitted over HTTPS, so plaintext keys never sit at rest.
//
//  Endpoints:
//    GET  /check?key=KEY&hwid=HWID                -> "ok" | "invalid" | "expired" | "hwid mismatch"
//    GET  /deliver?key=KEY&hwid=HWID&name=SCRIPT  -> "ok\n<blob>" if key valid (server-side delivery)
//    POST /upload?secret=ADMIN&name=SCRIPT        -> store a script's (encrypted) blob (body = blob)
//    GET  /scripts?secret=ADMIN                   -> list uploaded script names
//    GET  /delscript?secret=ADMIN&name=SCRIPT     -> remove an uploaded script
//    GET  /add?secret=ADMIN&key=KEY[&expiry=UNIX][&hwid=][&note=]   -> add/update a key
//    GET  /del?secret=ADMIN&key=KEY               -> delete a key
//    GET  /reset?secret=ADMIN&key=KEY             -> clear a key's HWID (let buyer rebind)
//    GET  /info?secret=ADMIN&key=KEY              -> view a key record
//
//  Setup: see SETUP.md in this folder.
// ============================================================================

async function sha256(str) {
  const buf = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(str));
  return [...new Uint8Array(buf)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

// Call work.ink's token validator. Returns the parsed JSON (with .valid and
// .info.linkId) or null on network error. del=true burns the token (single use).
// The API key (if set) is sent as a bearer header — work.ink ignores it on this
// endpoint, but it keeps your account attached for any future authed features.
async function winkFetch(token, env, del) {
  try {
    const q = del ? "?deleteToken=1" : "";
    const headers = { accept: "application/json" };
    if (env.WORKINK_API_KEY) headers["Authorization"] = "Bearer " + env.WORKINK_API_KEY;
    const r = await fetch(
      "https://work.ink/_api/v2/token/isValid/" + encodeURIComponent(token) + q,
      { headers }
    );
    if (!r.ok) return null;
    return await r.json();
  } catch (e) {
    return null;
  }
}

function txt(s, status = 200) {
  return new Response(String(s), {
    status,
    headers: { "content-type": "text/plain", "cache-control": "no-store" },
  });
}

// Is this a person opening the URL in a browser (vs Roblox's HttpGet)? Browsers
// send Sec-Fetch-Mode: navigate and Accept: text/html on navigation; the Roblox
// executor sends neither. So this is a clean, false-positive-free discriminator.
function isBrowser(request) {
  const sfm = (request.headers.get("sec-fetch-mode") || "").toLowerCase();
  const accept = (request.headers.get("accept") || "").toLowerCase();
  return sfm === "navigate" || accept.includes("text/html");
}

function trollPage() {
  const body = `<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Access denied</title>
<style>
*{box-sizing:border-box}html,body{height:100%;margin:0}
body{background:#000;color:#eaf0ff;font-family:'Segoe UI',system-ui,-apple-system,Arial,sans-serif;
overflow:hidden;display:flex;align-items:center;justify-content:center}
.bg{position:fixed;inset:-8%;z-index:0;background:url('/asset?name=bg') center/cover no-repeat;
filter:blur(42px) brightness(.42) saturate(1.15);transform:scale(1.12)}
.bg:after{content:"";position:absolute;inset:0;background:radial-gradient(ellipse at center,rgba(0,0,0,.2),rgba(0,0,0,.78))}
.card{position:relative;z-index:1;text-align:center;padding:46px 48px 40px;border-radius:26px;
background:rgba(8,10,20,.38);backdrop-filter:blur(22px) saturate(140%);-webkit-backdrop-filter:blur(22px) saturate(140%);
border:1px solid rgba(150,180,255,.16);box-shadow:0 30px 90px rgba(0,0,0,.65),inset 0 1px 0 rgba(255,255,255,.06)}
.logo{width:104px;height:104px;margin:0 auto 24px;border-radius:24px;
background:url('/asset?name=bg');background-size:300%;background-position:47% 49%;
box-shadow:0 10px 40px rgba(60,110,255,.45),inset 0 0 0 1px rgba(180,210,255,.25)}
h1{margin:0;font-size:24px;font-weight:600;letter-spacing:.14em;text-transform:uppercase;
background:linear-gradient(180deg,#fff,#9bc0ff);-webkit-background-clip:text;background-clip:text;color:transparent}
p{margin:12px 0 0;color:#7e8bb5;font-size:13px;letter-spacing:.04em}
.ic{width:78px;height:78px;display:block;margin:0 auto 24px}
.icx{fill:#d9586e;filter:drop-shadow(0 0 6px rgba(220,90,110,.28));opacity:.92}
</style></head>
<body><div class="bg"></div>
<div class="card">
<svg class="ic icx" viewBox="0 0 16 16"><path d="M16 8A8 8 0 1 1 0 8a8 8 0 0 1 16 0M5.354 4.646a.5.5 0 1 0-.708.708L7.293 8l-2.647 2.646a.5.5 0 0 0 .708.708L8 8.707l2.646 2.647a.5.5 0 0 0 .708-.708L8.707 8l2.647-2.646a.5.5 0 0 0-.708-.708L8 7.293z"/></svg>
<h1>Access denied</h1><p>this file is protected</p></div>
</body></html>`;
  return new Response(body, { status: 403, headers: { "content-type": "text/html; charset=utf-8", "cache-control": "no-store" } });
}

// Shared key validation used by BOTH /check and /deliver. Returns one of:
// "ok" | "invalid" | "expired" | "hwid mismatch" | "wrong link" | "no key".
// Handles admin keys (KV) and work.ink tokens (validated + cached), HWID bind.
async function validateKey(key, hwid, env, KV) {
  if (!key) return "no key";
  const h = await sha256(key);
  let raw = await KV.get("k:" + h);

  if (!raw) {
    const winkOn = env.WORKINK_ENABLED === "1" || env.WORKINK_ENABLED === "true";
    if (!winkOn) return "invalid";
    const del = env.WORKINK_SINGLE_USE !== "0";
    const d = await winkFetch(key, env, del);
    if (!d || d.valid !== true) return "invalid";
    const wantLink = (env.WORKINK_LINK_ID || "").trim();
    const gotLink = String((d.info && d.info.linkId) || "");
    if (wantLink && gotLink !== wantLink) return "wrong link";
    const ttl = parseInt(env.WORKINK_TTL || "86400", 10);
    const rec = { hwid: "", expiry: Math.floor(Date.now() / 1000) + ttl, note: "workink", linkId: gotLink };
    await KV.put("k:" + h, JSON.stringify(rec), { expirationTtl: ttl });
    raw = JSON.stringify(rec);
  }
  const rec = JSON.parse(raw);

  if (rec.expiry && rec.expiry !== 0 && Date.now() / 1000 > rec.expiry) return "expired";
  if (rec.hwid && rec.hwid !== "") {
    if (rec.hwid !== hwid) return "hwid mismatch";
  } else {
    rec.hwid = hwid;
    const opts = {};
    if (rec.expiry && rec.expiry !== 0) {
      const left = rec.expiry - Math.floor(Date.now() / 1000);
      if (left > 60) opts.expirationTtl = left;
    }
    await KV.put("k:" + h, JSON.stringify(rec), opts);
  }
  return "ok";
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const path = url.pathname.replace(/\/+$/, "") || "/";
    const q = url.searchParams;
    const KV = env.KEYS; // KV namespace binding (see wrangler.toml)
    if (!KV) return txt("server misconfigured: no KV binding", 500);

    // ---- public: the "here's your key" page work.ink redirects to ---------
    // Set your work.ink link DESTINATION to:
    //   https://y2k-keys.y2kscript.workers.dev/token?t={TOKEN}
    // work.ink swaps {TOKEN} for the real token; this page shows it to the buyer.
    if (path === "/token") {
      const token = q.get("t") || q.get("token") || "";
      const safe = token.replace(/[^A-Za-z0-9\-]/g, ""); // tokens are uuid-ish
      const body = `<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Your key</title><style>
*{box-sizing:border-box}html,body{height:100%;margin:0}
body{background:#000;color:#eaf0ff;font-family:'Segoe UI',system-ui,-apple-system,Arial,sans-serif;
overflow:hidden;display:flex;align-items:center;justify-content:center}
.bg{position:fixed;inset:-8%;z-index:0;background:url('/asset?name=bg') center/cover no-repeat;
filter:blur(42px) brightness(.42) saturate(1.15);transform:scale(1.12)}
.bg:after{content:"";position:absolute;inset:0;background:radial-gradient(ellipse at center,rgba(0,0,0,.2),rgba(0,0,0,.78))}
.card{position:relative;z-index:1;width:92%;max-width:430px;text-align:center;padding:40px 34px 34px;border-radius:26px;
background:rgba(8,10,20,.4);backdrop-filter:blur(22px) saturate(140%);-webkit-backdrop-filter:blur(22px) saturate(140%);
border:1px solid rgba(150,180,255,.16);box-shadow:0 30px 90px rgba(0,0,0,.65),inset 0 1px 0 rgba(255,255,255,.06)}
.logo{width:72px;height:72px;margin:0 auto 18px;border-radius:18px;background:url('/asset?name=bg');
background-size:300%;background-position:47% 49%;box-shadow:0 8px 30px rgba(60,110,255,.4),inset 0 0 0 1px rgba(180,210,255,.25)}
h1{margin:0;font-size:18px;font-weight:600;letter-spacing:.12em;text-transform:uppercase;color:#eaf2ff}
.sub{color:#7e8bb5;font-size:13px;margin:8px 0 22px}
.keywrap{position:relative}
.key{user-select:all;background:rgba(0,0,0,.35);border:1px solid rgba(140,170,255,.2);border-radius:12px;
padding:15px 46px 15px 15px;font-family:ui-monospace,Consolas,monospace;font-size:15px;word-break:break-all;color:#bfe0ff;text-align:left}
.clip{position:absolute;top:9px;right:9px;width:auto;margin:0;background:rgba(255,255,255,.06);border:1px solid rgba(140,170,255,.2);
border-radius:9px;padding:7px;cursor:pointer;line-height:0;transition:.15s}
.clip:hover{background:rgba(120,150,255,.2)}.clip:active{transform:scale(.92)}.clip svg{width:16px;height:16px;fill:#bfe0ff}
button{margin-top:16px;width:100%;padding:13px;border:0;border-radius:12px;cursor:pointer;color:#fff;font-size:15px;
font-weight:600;letter-spacing:.04em;background:linear-gradient(180deg,#4f7bff,#3550e6);box-shadow:0 8px 26px rgba(60,90,255,.4)}
button:active{transform:scale(.99)}.ok{margin-top:10px;color:#86f0b0;font-size:13px;height:16px}
.bad{color:#ff8ea2;font-size:14px;margin-top:8px}
.ic{width:64px;height:64px;display:block;margin:0 auto 20px}
.ick{fill:#8fb8ff;filter:drop-shadow(0 0 18px rgba(100,150,255,.5))}
</style></head><body><div class="bg"></div><div class="card">
<svg class="ic ick" viewBox="0 0 16 16"><path d="M3.5 11.5a3.5 3.5 0 1 1 3.163-5H14L15.5 8 14 9.5l-1-1-1 1-1-1-1 1-1-1-1 1H6.663a3.5 3.5 0 0 1-3.163 2M2.5 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2"/></svg>
${safe
  ? `<h1>Your key</h1><div class="sub">paste it into the script</div>
     <div class="keywrap">
       <div class="key" id="k">${safe}</div>
       <button class="clip" title="Copy" onclick="cp()"><svg viewBox="0 0 16 16"><path d="M4 1.5H3a2 2 0 0 0-2 2V14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V3.5a2 2 0 0 0-2-2h-1v1h1a1 1 0 0 1 1 1V14a1 1 0 0 1-1 1H3a1 1 0 0 1-1-1V3.5a1 1 0 0 1 1-1h1z"/><path d="M9.5 1a.5.5 0 0 1 .5.5v1a.5.5 0 0 1-.5.5h-3a.5.5 0 0 1-.5-.5v-1a.5.5 0 0 1 .5-.5zm-3-1A1.5 1.5 0 0 0 5 1.5v1A1.5 1.5 0 0 0 6.5 4h3A1.5 1.5 0 0 0 11 2.5v-1A1.5 1.5 0 0 0 9.5 0z"/></svg></button>
     </div>
     <button onclick="cp()">Copy key</button>
     <div class="ok" id="o"></div>
     <script>function cp(){navigator.clipboard.writeText('${safe}').then(function(){document.getElementById('o').textContent='Copied'})}</script>`
  : `<h1>No key found</h1><p class="bad">Open this page by finishing the key link.</p>`}
</div></body></html>`;
      return new Response(body, { headers: { "content-type": "text/html; charset=utf-8", "cache-control": "no-store" } });
    }

    // ---- public: validate a key ------------------------------------------
    if (path === "/check") {
      return txt(await validateKey(q.get("key") || "", q.get("hwid") || "", env, KV));
    }

    // ---- public: SERVER-SIDE DELIVERY ------------------------------------
    // The protected file has NO script inside it -- it asks here for the real
    // (encrypted) payload, and only gets it if the key validates. A leaked file
    // is just a key-checker with nothing to extract.
    //   GET /deliver?key=KEY&hwid=HWID&name=SCRIPT  -> "ok\n<blob>" | "<reason>"
    if (path === "/deliver") {
      if (isBrowser(request)) return trollPage();
      const name = q.get("name") || "";
      if (!name) return txt("no name");
      const status = await validateKey(q.get("key") || "", q.get("hwid") || "", env, KV);
      if (status !== "ok") return txt(status); // invalid / expired / hwid mismatch / wrong link
      const blob = await KV.get("script:" + name);
      if (blob === null) return txt("no script"); // not uploaded yet
      return txt("ok\n" + blob); // License.deliver() splits at the first newline
    }

    // ---- public: serve the UI library (ObsidianUi) from Cloudflare instead of
    // GitHub raw. It's an open-source UI lib (not your script), so it's public.
    //   GET /lib?f=Library.lua  ->  the file's contents
    if (path === "/lib") {
      if (isBrowser(request)) return trollPage();
      const f = q.get("f") || "";
      if (!f) return txt("no f");
      const v = await KV.get("lib:" + f);
      if (v === null) return txt("not found", 404);
      return txt(v);
    }

    // ---- public: serve a hosted image (your Y2k logo) for the web pages ----
    //   GET /asset?name=bg  -> the image bytes
    if (path === "/asset") {
      const name = q.get("name") || "";
      const b64 = await KV.get("asset:" + name);
      if (!b64) return txt("not found", 404);
      const bin = Uint8Array.from(atob(b64), (c) => c.charCodeAt(0));
      return new Response(bin, { headers: { "content-type": "image/webp", "cache-control": "public, max-age=604800" } });
    }

    // ---- public: serve the LOADER (the key-box bootstrap). You post a one-liner
    // that loadstrings this. It has no script and no secrets -- just the key box.
    //   GET /loader?name=SCRIPT  ->  the bootstrap lua
    if (path === "/loader") {
      if (isBrowser(request)) return trollPage();
      const name = q.get("name") || "";
      if (!name) return txt("no name");
      const v = await KV.get("loader:" + name);
      if (v === null) return txt("-- not found", 404);
      return txt(v);
    }

    // ---- public: THE ONE LINK. Universal loader (key box + PlaceId routing).
    // Players paste:  loadstring(game:HttpGet(".../hub"))()
    if (path === "/hub") {
      if (isBrowser(request)) return trollPage();
      const v = await KV.get("loader:hub");
      if (v === null) return txt("-- hub not built yet", 404);
      return txt(v);
    }

    // ---- admin (require ?secret=ADMIN_SECRET) ----------------------------
    const admin = q.get("secret") || "";
    const needAdmin = ["/add", "/del", "/reset", "/info", "/wink", "/upload", "/delscript", "/scripts", "/uplib", "/uploader", "/upasset"].includes(path);
    if (needAdmin && admin !== env.ADMIN_SECRET) return txt("unauthorized", 403);

    if (path === "/add") {
      const key = q.get("key");
      if (!key) return txt("need key");
      const rec = {
        hwid: q.get("hwid") || "",
        expiry: parseInt(q.get("expiry") || "0", 10) || 0,
        note: q.get("note") || "",
      };
      await KV.put("k:" + (await sha256(key)), JSON.stringify(rec));
      return txt("added: " + key);
    }
    if (path === "/del") {
      const key = q.get("key");
      if (!key) return txt("need key");
      await KV.delete("k:" + (await sha256(key)));
      return txt("deleted: " + key);
    }
    if (path === "/reset") {
      const key = q.get("key");
      if (!key) return txt("need key");
      const h = await sha256(key);
      const raw = await KV.get("k:" + h);
      if (!raw) return txt("not found");
      const rec = JSON.parse(raw);
      rec.hwid = "";
      await KV.put("k:" + h, JSON.stringify(rec));
      return txt("hwid reset: " + key);
    }
    if (path === "/info") {
      const key = q.get("key");
      if (!key) return txt("need key");
      const raw = await KV.get("k:" + (await sha256(key)));
      return txt(raw || "not found");
    }
    // Debug a work.ink token WITHOUT burning it -> shows valid + linkId so you can
    // set WORKINK_LINK_ID. Admin-only. Usage: /wink?secret=ADMIN&token=THE_TOKEN
    if (path === "/wink") {
      const token = q.get("token");
      if (!token) return txt("need token");
      const d = await winkFetch(token, env, false);
      return txt(JSON.stringify(d, null, 2));
    }
    // Store a script's (encrypted) blob so /deliver can serve it. POST body = blob.
    //   POST /upload?secret=ADMIN&name=SCRIPT   (body: the base64-xored payload)
    if (path === "/upload") {
      const name = q.get("name");
      if (!name) return txt("need name");
      if (request.method !== "POST") return txt("use POST", 405);
      const blob = await request.text();
      if (!blob) return txt("empty body");
      await KV.put("script:" + name, blob);
      return txt("uploaded: " + name + " (" + blob.length + " bytes)");
    }
    if (path === "/delscript") {
      const name = q.get("name");
      if (!name) return txt("need name");
      await KV.delete("script:" + name);
      return txt("script deleted: " + name);
    }
    if (path === "/scripts") {
      const list = await KV.list({ prefix: "script:" });
      const names = list.keys.map((k) => k.name.replace(/^script:/, ""));
      return txt(names.length ? names.join("\n") : "(no scripts uploaded)");
    }
    // Upload a UI-library file (served publicly by /lib). POST body = file text.
    //   POST /uplib?secret=ADMIN&f=Library.lua
    if (path === "/uplib") {
      const f = q.get("f");
      if (!f) return txt("need f");
      if (request.method !== "POST") return txt("use POST", 405);
      const body = await request.text();
      await KV.put("lib:" + f, body);
      return txt("lib uploaded: " + f + " (" + body.length + " bytes)");
    }
    // Upload the loader/bootstrap (served publicly by /loader). POST body = lua.
    //   POST /uploader?secret=ADMIN&name=SCRIPT
    if (path === "/uploader") {
      const name = q.get("name");
      if (!name) return txt("need name");
      if (request.method !== "POST") return txt("use POST", 405);
      const body = await request.text();
      await KV.put("loader:" + name, body);
      return txt("loader uploaded: " + name + " (" + body.length + " bytes)");
    }
    // Upload an image (body = base64 of the file) served by /asset.
    //   POST /upasset?secret=ADMIN&name=bg   (body: base64 image)
    if (path === "/upasset") {
      const name = q.get("name");
      if (!name) return txt("need name");
      if (request.method !== "POST") return txt("use POST", 405);
      const b64 = (await request.text()).trim();
      await KV.put("asset:" + name, b64);
      return txt("asset uploaded: " + name + " (" + b64.length + " b64 chars)");
    }

    return txt("Y2k key server online");
  },
};
