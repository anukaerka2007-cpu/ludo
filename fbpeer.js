// FbPeer — PeerJS-тэй ижил хэлбэртэй (on/connect/send/close/destroy) жижиг сан.
// Мессежийг Firebase Realtime Database-ээр (REST + EventSource, HTTPS 443 порт) дамжуулдаг тул
// WebRTC хаагддаг мобайл дата, сургуулийн Wi-Fi зэрэг сүлжээнд ч ажиллана.
//
// Өгөгдлийн бүтэц:
//   peers/<id>  = { alive: <тоо> }      — амьд эсэхийн тэмдэг (15 сек тутам шинэчилнэ)
//   inbox/<id>/<pushId> = { from, k, cid, s }  — тухайн peer рүү ирсэн мессежүүд
"use strict";
(function () {
    const BEAT_MS = 15000, WATCH_MS = 15000, DEAD_MS = 50000;
    const rid = () => Math.random().toString(36).slice(2, 10) + Date.now().toString(36);
    const base = () => String(window.LUDO_FIREBASE_URL || "").replace(/\/+$/, "");
    const url = path => base() + "/" + path + ".json";
    const live = new Set();

    class Emitter {
        constructor() { this._h = {}; }
        on(e, f) { (this._h[e] = this._h[e] || []).push(f); return this; }
        emit(e, ...a) { (this._h[e] || []).slice().forEach(f => { try { f(...a); } catch (err) { console.error(err); } }); }
    }

    class FbConn extends Emitter {
        constructor(p, remote, cid) {
            super();
            this._p = p; this.peer = remote; this.cid = cid;
            this.open = false; this.closed = false;
            p._conns[cid] = this;
        }
        _setOpen() { if (this.open || this.closed) return; this.open = true; this.emit("open"); }
        send(d) { if (!this.closed) this._p._post(this.peer, { k: "data", cid: this.cid, s: JSON.stringify(d) }); }
        close() {
            if (this.closed) return;
            this._p._post(this.peer, { k: "close", cid: this.cid });
            this._remoteClosed();
        }
        _remoteClosed() {
            if (this.closed) return;
            this.closed = true; this.open = false;
            delete this._p._conns[this.cid];
            this.emit("close");
        }
    }

    class FbPeer extends Emitter {
        constructor(id) {
            super();
            if (typeof id !== "string") id = undefined;          // PeerJS шиг: эхний аргумент тохиргоо байж болно
            this._fixed = !!id;
            this.id = id || "g" + rid();
            this._conns = {}; this._seen = new Set(); this._q = Promise.resolve();
            this.disconnected = false; this.destroyed = false;
            live.add(this);
            this._start();
        }
        async _req(method, path, body) {
            const r = await fetch(url(path), {
                method, headers: body === undefined ? undefined : { "Content-Type": "application/json" },
                body: body === undefined ? undefined : JSON.stringify(body)
            });
            if (!r.ok) throw new Error("HTTP " + r.status);
            return r.json();
        }
        _err(type, msg) { const e = new Error(msg || type); e.type = type; this.emit("error", e); }
        async _start() {
            try {
                if (this._fixed) {                                 // өрөөний код давхцаж байгаа эсэх
                    const cur = await this._req("GET", "peers/" + this.id);
                    if (cur && Math.abs(Date.now() - (cur.alive || 0)) < 60000) { this._err("unavailable-id", "ID is taken"); return; }
                }
                await this._req("DELETE", "inbox/" + this.id);
                await this._beat();
                if (this.destroyed) return;
                this._listen();
                this._beatT = setInterval(() => { this._beat().catch(() => {}); }, BEAT_MS);
                this.emit("open", this.id);
            } catch (e) {
                if (!this.destroyed) this._err("network", "Firebase-д холбогдож чадсангүй");
            }
        }
        _beat() { return this._req("PUT", "peers/" + this.id, { alive: Date.now() }); }
        _listen() {
            const es = this._es = new EventSource(url("inbox/" + this.id));
            const take = (path, data) => {
                if (data == null) return;
                if (path === "/") Object.keys(data).sort().forEach(k => this._msg(k, data[k]));
                else { const parts = path.split("/"); if (parts.length === 2) this._msg(parts[1], data); }
            };
            const onEv = ev => { let m; try { m = JSON.parse(ev.data); } catch (e) { return; } if (m) take(m.path, m.data); };
            es.addEventListener("put", onEv);
            es.addEventListener("patch", onEv);
            // EventSource тасарвал өөрөө дахин холбогдоно; давхардсан мессежийг _seen шүүнэ
        }
        _msg(key, m) {
            if (this._seen.has(key) || !m || typeof m !== "object") return;
            this._seen.add(key);
            if (m.k === "connect") {
                const c = new FbConn(this, m.from, m.cid);
                this.emit("connection", c);
                this._post(m.from, { k: "accepted", cid: m.cid });
                this._watch(c);
                setTimeout(() => c._setOpen(), 0);
                return;
            }
            const c = this._conns[m.cid];
            if (!c) return;
            if (m.k === "accepted") c._setOpen();
            else if (m.k === "data") { let d; try { d = JSON.parse(m.s); } catch (e) { return; } c.emit("data", d); }
            else if (m.k === "close") c._remoteClosed();
        }
        _post(to, msg) {                                           // дарааллыг хадгалахын тулд нэг нэгээр нь илгээнэ
            msg.from = this.id;
            this._q = this._q.then(() => this._req("POST", "inbox/" + to, msg)).catch(() => {});
        }
        _watch(c) {                                                // нөгөө тал амьд эсэхийг шалгана
            let last = null, changed = Date.now();
            const t = setInterval(async () => {
                if (c.closed || this.destroyed) { clearInterval(t); return; }
                try {
                    const v = await this._req("GET", "peers/" + c.peer);
                    if (!v) { clearInterval(t); c._remoteClosed(); return; }
                    if (v.alive !== last) { last = v.alive; changed = Date.now(); }
                    else if (Date.now() - changed > DEAD_MS) { clearInterval(t); c._remoteClosed(); }
                } catch (e) {}
            }, WATCH_MS);
        }
        connect(remote) {
            const c = new FbConn(this, remote, "c" + rid());
            this._req("GET", "peers/" + remote).then(v => {
                if (!v) { delete this._conns[c.cid]; this._err("peer-unavailable", "Could not connect to peer " + remote); return; }
                this._post(remote, { k: "connect", cid: c.cid });
                this._watch(c);
            }).catch(() => this._err("network", "Firebase-д холбогдож чадсангүй"));
            return c;
        }
        reconnect() {}
        destroy() {
            if (this.destroyed) return;
            this.destroyed = true; live.delete(this);
            clearInterval(this._beatT);
            try { this._es && this._es.close(); } catch (e) {}
            Object.values(this._conns).forEach(c => { this._post(c.peer, { k: "close", cid: c.cid }); c.closed = true; });
            const id = this.id;
            this._q = this._q.then(() => fetch(url("peers/" + id), { method: "DELETE", keepalive: true })).catch(() => {});
        }
    }

    // Таб хаагдах үед бусдад мэдэгдэнэ
    window.addEventListener("pagehide", () => {
        live.forEach(p => {
            Object.values(p._conns).forEach(c => {
                try {
                    fetch(url("inbox/" + c.peer), { method: "POST", keepalive: true, headers: { "Content-Type": "application/json" },
                        body: JSON.stringify({ from: p.id, k: "close", cid: c.cid }) });
                } catch (e) {}
            });
            try { fetch(url("peers/" + p.id), { method: "DELETE", keepalive: true }); } catch (e) {}
        });
    });

    window.FbPeer = FbPeer;
})();
