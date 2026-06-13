// ============================================================================
//  Y2k Key Server  --  Cloudflare Worker + KV
//  Server-side key validation with SHA-256 key hashing, HWID auto-binding,
//  expiry, and admin endpoints. Keys are stored HASHED in KV (a KV dump shows
//  only hashes), and transmitted over HTTPS, so plaintext keys never sit at rest.
//
//  Endpoints:
//    GET /check?key=KEY&hwid=HWID                 -> "ok" | "invalid" | "expired" | "hwid mismatch"
//    GET /add?secret=ADMIN&key=KEY[&expiry=UNIX][&hwid=][&note=]   -> add/update a key
//    GET /del?secret=ADMIN&key=KEY                -> delete a key
//    GET /reset?secret=ADMIN&key=KEY              -> clear a key's HWID (let buyer rebind)
//    GET /info?secret=ADMIN&key=KEY               -> view a key record
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
      const key = q.get("key") || "";
      const hwid = q.get("hwid") || "";
      if (!key) return txt("no key");
      const h = await sha256(key);
      let raw = await KV.get("k:" + h);

      // Not a pre-added admin key? It might be a work.ink token. Validate it
      // with work.ink; on success cache it (HWID-lockable) for WORKINK_TTL secs
      // so the buyer keeps access until the token window expires and must redo
      // the link. This gives ad-revenue (work.ink) + your HWID lock together.
      if (!raw) {
        const winkOn = env.WORKINK_ENABLED === "1" || env.WORKINK_ENABLED === "true";
        if (!winkOn) return txt("invalid");
        const del = env.WORKINK_SINGLE_USE !== "0";
        const d = await winkFetch(key, env, del);
        if (!d || d.valid !== true) return txt("invalid");
        // Lock to YOUR link: only tokens minted by your work.ink link are accepted.
        const wantLink = (env.WORKINK_LINK_ID || "").trim();
        const gotLink = String((d.info && d.info.linkId) || "");
        if (wantLink && gotLink !== wantLink) return txt("wrong link");
        const ttl = parseInt(env.WORKINK_TTL || "86400", 10);
        const rec = { hwid: "", expiry: Math.floor(Date.now() / 1000) + ttl, note: "workink", linkId: gotLink };
        await KV.put("k:" + h, JSON.stringify(rec), { expirationTtl: ttl });
        raw = JSON.stringify(rec);
      }
      const rec = JSON.parse(raw);

      if (rec.expiry && rec.expiry !== 0 && Date.now() / 1000 > rec.expiry) {
        return txt("expired");
      }
      if (rec.hwid && rec.hwid !== "") {
        if (rec.hwid !== hwid) return txt("hwid mismatch");
      } else {
        // first use -> bind this device (keep any TTL so work.ink caches expire)
        rec.hwid = hwid;
        const opts = {};
        if (rec.expiry && rec.expiry !== 0) {
          const left = rec.expiry - Math.floor(Date.now() / 1000);
          if (left > 60) opts.expirationTtl = left;
        }
        await KV.put("k:" + h, JSON.stringify(rec), opts);
      }
      return txt("ok"); // the Lua provider treats this as KEY_VALID
    }

    // ---- admin (require ?secret=ADMIN_SECRET) ----------------------------
    const admin = q.get("secret") || "";
    const needAdmin = ["/add", "/del", "/reset", "/info", "/wink"].includes(path);
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

    return txt("Y2k key server online");
  },
};
