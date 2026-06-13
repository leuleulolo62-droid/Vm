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

// Validate a work.ink key-system token. Returns true if the buyer really
// completed the link. deleteToken=1 makes the token single-use (anti-share).
async function validateWorkink(token, env) {
  try {
    const single = env.WORKINK_SINGLE_USE === "0" ? "" : "?deleteToken=1";
    const r = await fetch(
      "https://work.ink/_api/v2/token/isValid/" + encodeURIComponent(token) + single,
      { headers: { accept: "application/json" } }
    );
    if (!r.ok) return false;
    const d = await r.json();
    return !!(d && d.valid === true);
  } catch (e) {
    return false;
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
        if (winkOn && (await validateWorkink(key, env))) {
          const ttl = parseInt(env.WORKINK_TTL || "86400", 10);
          const rec = { hwid: "", expiry: Math.floor(Date.now() / 1000) + ttl, note: "workink" };
          await KV.put("k:" + h, JSON.stringify(rec), { expirationTtl: ttl });
          raw = JSON.stringify(rec);
        } else {
          return txt("invalid");
        }
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
    const needAdmin = ["/add", "/del", "/reset", "/info"].includes(path);
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

    return txt("Y2k key server online");
  },
};
