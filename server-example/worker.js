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
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Access Denied</title>
<style>
*{box-sizing:border-box}html,body{height:100%;margin:0}
body{background:#04040a;color:#dfe8ff;font-family:'Segoe UI',system-ui,Arial,sans-serif;
overflow:hidden;display:flex;align-items:center;justify-content:center}
/* Y2k chrome glow background (blurred blobs) */
.bg{position:fixed;inset:-20%;z-index:0;filter:blur(70px) saturate(160%);opacity:.9}
.bg span{position:absolute;border-radius:50%}
.b1{width:46vw;height:46vw;left:-6vw;top:-8vw;background:radial-gradient(circle,#5a3bff,transparent 70%)}
.b2{width:52vw;height:52vw;right:-10vw;top:-12vw;background:radial-gradient(circle,#2e6bff,transparent 70%)}
.b3{width:48vw;height:48vw;left:8vw;bottom:-16vw;background:radial-gradient(circle,#7b2bff,transparent 70%)}
.b4{width:40vw;height:40vw;right:2vw;bottom:-12vw;background:radial-gradient(circle,#22d3ff,transparent 70%)}
/* sparkle stars */
.star{position:fixed;z-index:1;opacity:.8;filter:drop-shadow(0 0 8px #6aa8ff)}
.card{position:relative;z-index:2;text-align:center;padding:38px 30px;border-radius:24px;
background:rgba(10,12,26,.45);backdrop-filter:blur(14px);-webkit-backdrop-filter:blur(14px);
border:1px solid rgba(150,180,255,.18);box-shadow:0 20px 80px rgba(0,0,0,.6);max-width:520px}
.troll{width:190px;height:190px;animation:wob 2.4s ease-in-out infinite}
@keyframes wob{0%,100%{transform:rotate(-5deg) translateY(0)}50%{transform:rotate(5deg) translateY(-6px)}}
.row{display:flex;align-items:center;justify-content:center;gap:10px;margin-top:14px}
.bi{width:30px;height:30px;fill:#ff5b7f;filter:drop-shadow(0 0 10px #ff3b6b)}
h1{font-size:27px;margin:6px 14px 0;background:linear-gradient(180deg,#eaf2ff,#7fa8ff);
-webkit-background-clip:text;background-clip:text;color:transparent}
p{color:#aab6e0;font-size:18px;margin:10px 0 0}.sub{color:#5a6590;font-size:13px;margin-top:16px}
</style></head>
<body>
<div class="bg"><span class="b1"></span><span class="b2"></span><span class="b3"></span><span class="b4"></span></div>
${[["8%","16%",34],["88%","22%",26],["16%","78%",22],["80%","74%",30],["50%","10%",18]].map(
  ([l,t,s])=>`<svg class="star" style="left:${l};top:${t}" width="${s}" height="${s}" viewBox="0 0 24 24"><path fill="#bfe0ff" d="M12 0c1.2 6.4 4.4 9.6 12 12c-7.6 2.4-10.8 5.6-12 12c-1.2-6.4-4.4-9.6-12-12C7.6 9.6 10.8 6.4 12 0Z"/></svg>`).join("")}
<div class="card">
  <svg class="troll" viewBox="0 0 220 220" xmlns="http://www.w3.org/2000/svg">
    <defs><linearGradient id="cr" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0" stop-color="#eaf3ff"/><stop offset=".4" stop-color="#5aa0ff"/>
      <stop offset=".7" stop-color="#3b5bff"/><stop offset="1" stop-color="#bda0ff"/>
    </linearGradient></defs>
    <path d="M110 14c52 0 92 36 92 86 0 56-44 106-92 106S18 156 18 100C18 50 58 14 110 14Z"
          fill="url(#cr)" stroke="#dff0ff" stroke-width="4"/>
    <path d="M52 86c14-16 40-16 52 0-16-7-36-7-52 0Z" fill="#06060e"/>
    <path d="M116 86c14-16 40-16 52 0-16-7-36-7-52 0Z" fill="#06060e"/>
    <path d="M44 128c40 44 92 44 132 0-8 30-40 50-66 50s-58-20-66-50Z" fill="#06060e"/>
    <path d="M44 128c40 26 92 26 132 0" fill="none" stroke="#06060e" stroke-width="6" stroke-linecap="round"/>
  </svg>
  <div class="row">
    <svg class="bi" viewBox="0 0 16 16"><path d="M8 15A7 7 0 1 1 8 1a7 7 0 0 1 0 14m0 1A8 8 0 1 0 8 0a8 8 0 0 0 0 16"/><path d="M11.354 4.646a.5.5 0 0 0-.708 0l-6 6a.5.5 0 0 0 .708.708l6-6a.5.5 0 0 0 0-.708"/></svg>
    <h1>Access refused — you can't access this file</h1>
  </div>
  <p>Skid is not good lil bro</p>
  <div class="sub">nice try though</div>
</div>
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
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Your Key</title><style>
*{box-sizing:border-box}body{margin:0;font-family:system-ui,Segoe UI,Arial,sans-serif;
background:#0b0b14;color:#e7e7f5;display:flex;min-height:100vh;align-items:center;justify-content:center}
.card{background:#15151f;border:1px solid #2a2a3a;border-radius:16px;padding:28px;max-width:440px;width:92%;
box-shadow:0 12px 40px rgba(0,0,0,.5);text-align:center}
h1{margin:0 0 6px;font-size:20px}p{color:#9a9ab0;margin:6px 0 18px;font-size:14px}
.key{user-select:all;background:#0b0b14;border:1px dashed #3a3a55;border-radius:10px;padding:14px;
font-family:ui-monospace,Consolas,monospace;font-size:15px;word-break:break-all;color:#8fe3a0}
button{margin-top:16px;width:100%;padding:12px;border:0;border-radius:10px;cursor:pointer;
background:#6c5ce7;color:#fff;font-size:15px;font-weight:600}button:active{transform:scale(.99)}
.ok{margin-top:10px;color:#8fe3a0;font-size:13px;height:16px}.bad{color:#ff7b7b}
</style></head><body><div class="card">
${safe
  ? `<h1>✅ Your key</h1><p>Copy this and paste it into the script.</p>
     <div class="key" id="k">${safe}</div>
     <button onclick="navigator.clipboard.writeText('${safe}').then(()=>{document.getElementById('o').textContent='Copied!'})">Copy key</button>
     <div class="ok" id="o"></div>`
  : `<h1>⚠️ No key found</h1><p class="bad">This page must be opened by finishing the work.ink link. Go back and complete it.</p>`}
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
    const needAdmin = ["/add", "/del", "/reset", "/info", "/wink", "/upload", "/delscript", "/scripts", "/uplib", "/uploader"].includes(path);
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

    return txt("Y2k key server online");
  },
};
