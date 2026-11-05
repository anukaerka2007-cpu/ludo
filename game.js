// «Та битгий уурлаарай» — Монгол ардын тоглоом (вэб хувилбар)
// ludo_win.cpp-г JavaScript / Canvas руу хөрвүүлсэн.
// Өгөгдөл (асуулт, зам, зураг) нь data.js-д байна.
"use strict";

const W = 860, H = 660;
const CELL = 36, BX = 40, BY = 40;
const STEP = 4;

const MN_PARCH = "rgb(244,232,200)", MN_PARCH2 = "rgb(230,214,172)", MN_GRID = "rgb(180,150,90)";
const MN_ORN = "rgb(180,130,40)", MN_ORN_DK = "rgb(120,80,20)";
const MN_INK = "rgb(60,30,10)", MN_WHITE = "rgb(252,246,226)", MN_BLACK = "rgb(0,0,0)";

const PCOL = [[160, 40, 40], [40, 110, 70], [210, 160, 40], [40, 80, 150]];
const pColor = PCOL.map(c => `rgb(${c[0]},${c[1]},${c[2]})`);
const pName = ["Улаан", "Ногоон", "Шар", "Хөх"];
const pGen = ["Улааны", "Ногооны", "Шарын", "Хөхийн"];      // харьяалах тийн ялгал: «Улааны ээлж»
const modeName = ["1 vs Компьютер", "2 тоглогч", "3 тоглогч", "4 тоглогч"];
// Messenger / Facebook / Instagram зэрэг апп доторх хөтөч (WebRTC-г ихэвчлэн хаадаг)
const IN_APP_BROWSER = /FBAN|FBAV|FB_IAB|Messenger|Instagram|MicroMessenger|Snapchat|Line\//i.test(navigator.userAgent);
const FONT ='"Segoe UI","Noto Sans","Roboto",system-ui,Arial,sans-serif';

/* ====================== Тоглоомын төлөв ====================== */
const pathR = PATH_R, pathC = PATH_C;
const laneR = [[7,7,7,7,7,7], [1,2,3,4,5,6], [7,7,7,7,7,7], [13,12,11,10,9,8]];
const laneC = [[1,2,3,4,5,6], [7,7,7,7,7,7], [13,12,11,10,9,8], [7,7,7,7,7,7]];
const baseR = [[2,2,4,4], [2,2,4,4], [11,11,13,13], [11,11,13,13]];
const baseC = [[2,4,2,4], [11,13,11,13], [11,13,11,13], [2,4,2,4]];
const startIdx = [0, 13, 26, 39];
const advCells = [3, 16, 29, 42];
const retCells = [7, 20, 33, 46];
const safeCell = new Array(52).fill(0);
[0, 8, 13, 21, 26, 34, 39, 47].forEach(i => safeCell[i] = 1);
const pos = [[-1,-1,-1,-1], [-1,-1,-1,-1], [-1,-1,-1,-1], [-1,-1,-1,-1]];

const ST_INTRO = 0, ST_ROLL = 1, ST_CHOOSE = 2, ST_QUIZ = 3, ST_QRES = 4, ST_OVER = 5;
let state = ST_INTRO;
let cur = 0, dice = 0, sixCount = 0, winner = -1;
let gameMode = 3;
const isActive = [1, 1, 1, 1];
const isAI = [0, 0, 0, 0];
let movTok = [], movNew = [], nMov = 0;
let qIndex = 0, qIsAdvance = 0, qTok = 0, qNewT = 0, qSel = -1, qCorrect = 0;
let lastK = 0, capFlag = 0;
let msg = "Улааны ээлж. ENTER дарж шоо шид.";
let TIMESCALE = 1;

/* ---- Асуултын сан: урагшлах / ухрах нүдэнд тусдаа дараалал ---- */
const qpool = [{ ids: [], ord: [], pos: 0, last: -1 }, { ids: [], ord: [], pos: 0, last: -1 }];
const rnd = n => Math.floor(Math.random() * n);

function shufflePool(p) {
    p.ord = p.ids.slice();
    for (let i = p.ord.length - 1; i > 0; i--) {
        const j = rnd(i + 1);
        [p.ord[i], p.ord[j]] = [p.ord[j], p.ord[i]];
    }
    if (p.ord.length > 1 && p.ord[0] === p.last) [p.ord[0], p.ord[1]] = [p.ord[1], p.ord[0]];
    p.pos = 0;
}
function buildPools() {
    qpool.forEach(p => { p.ids = []; p.last = -1; });
    for (let i = 0; i < QBANK.length; i++) qpool[i & 1].ids.push(i);   // тэгш -> урагшлах, сондгой -> ухрах
    qpool.forEach(shufflePool);
}
function nextQuestion(adv) {
    const p = qpool[adv ? 0 : 1];
    if (p.pos >= p.ord.length) shufflePool(p);
    p.last = p.ord[p.pos++];
    return p.last;
}

function resetPositions() { for (let p = 0; p < 4; p++) for (let k = 0; k < 4; k++) pos[p][k] = -1; }

/* ---- Дүрэм ---- */
const isAdvanceCell = idx => advCells.includes(idx);
const isRetreatCell = idx => retCells.includes(idx);

function getCell(p, t) {
    if (t <= 50) { const idx = (startIdx[p] + t) % 52; return [pathR[idx], pathC[idx]]; }
    const li = t - 51; return [laneR[p][li], laneC[p][li]];
}
function legalMove(p, t, d) {          // шинэ байрлал эсвэл -2 (боломжгүй)
    if (t === -1) return (d === 6 || d === 1) ? 0 : -2;
    const n = t + d;
    return n <= 56 ? n : -2;
}
function applyCapture(p, newT) {
    let captured = 0;
    if (newT <= 50) {
        const idx = (startIdx[p] + newT) % 52;
        if (!safeCell[idx]) {
            for (let q = 0; q < 4; q++) if (q !== p && isActive[q])
                for (let j = 0; j < 4; j++) {
                    const tq = pos[q][j];
                    if (tq >= 0 && tq <= 50 && (startIdx[q] + tq) % 52 === idx) { pos[q][j] = -1; captured = 1; }
                }
        }
    }
    return captured;
}
const playerWon = p => pos[p].every(t => t === 56);
const homeCount = p => pos[p].filter(t => t === 56).length;

function applyMode() {
    for (let i = 0; i < 4; i++) { isActive[i] = 0; isAI[i] = 0; }
    if (gameMode === 0) { isActive[0] = 1; isActive[2] = 1; isAI[2] = 1; }
    else if (gameMode === 1) { isActive[0] = 1; isActive[2] = 1; }
    else if (gameMode === 2) { isActive[0] = 1; isActive[1] = 1; isActive[2] = 1; }
    else { isActive.fill(1); }
    cur = 0;
}
function nextPlayer() {
    for (let i = 1; i <= 4; i++) { const n = (cur + i) % 4; if (isActive[n]) { cur = n; return; } }
}
function finalize() {
    if (playerWon(cur)) { state = ST_OVER; winner = cur; msg = `${pName[cur]} ЯЛЛАА!`; return; }
    const finished = pos[cur][lastK] === 56;
    const extra = dice === 6 || capFlag || finished;
    if (extra) msg = `${pName[cur]} дахин шиднэ! ENTER.`;
    else { nextPlayer(); sixCount = 0; msg = `${pGen[cur]} ээлж. ENTER.`; }
    state = ST_ROLL;
}
function afterLand(k, newT) {
    lastK = k;
    pos[cur][k] = newT;
    capFlag = applyCapture(cur, newT);
    if (newT <= 50) {
        const idx = (startIdx[cur] + newT) % 52;
        if (isAdvanceCell(idx)) { state = ST_QUIZ; qIsAdvance = 1; qTok = k; qNewT = newT; qIndex = nextQuestion(1); msg = "Тусгай нүд! Асуултад хариул."; return; }
        if (isRetreatCell(idx)) { state = ST_QUIZ; qIsAdvance = 0; qTok = k; qNewT = newT; qIndex = nextQuestion(0); msg = "Тусгай нүд! Асуултад хариул."; return; }
    }
    if (capFlag) msg = "Өрсөлдөгчийг гэрт нь буцаалаа!";
    finalize();
}
function doRoll() {
    dice = rnd(6) + 1;
    if (dice === 6) sixCount++; else sixCount = 0;
    if (sixCount === 3) { msg = "3 удаа 6! Ээлж алдав."; nextPlayer(); sixCount = 0; state = ST_ROLL; return; }
    movTok = []; movNew = [];
    for (let k = 0; k < 4; k++) {
        const nt = legalMove(cur, pos[cur][k], dice);
        if (nt !== -2) { movTok.push(k); movNew.push(nt); }
    }
    nMov = movTok.length;
    if (nMov === 0) { msg = "Хөдлөх боломжгүй. ENTER."; if (dice !== 6) nextPlayer(); sixCount = 0; state = ST_ROLL; return; }
    if (nMov === 1) { afterLand(movTok[0], movNew[0]); return; }
    state = ST_CHOOSE; msg = "Хүү сонго: 1-4 дар";
}
function doChoose(tk) {
    for (let i = 0; i < nMov; i++) if (movTok[i] === tk) { afterLand(movTok[i], movNew[i]); return; }
}
function doQuizAnswer(sel) {
    qSel = sel;
    qCorrect = sel === QBANK[qIndex].ans ? 1 : 0;
    if (qCorrect) msg = qIsAdvance ? "Зөв! 4 алхам урагшилна." : "Зөв! Ухрахгүй.";
    else msg = qIsAdvance ? "Буруу. Байрандаа үлдэнэ." : "Буруу. 4 алхам ухарна.";
    state = ST_QRES;
}
function applyQuizResult() {
    let newT = qNewT;
    if (qIsAdvance) { if (qCorrect) { newT += STEP; if (newT > 50) newT = 50; } }
    else if (!qCorrect) { newT -= STEP; if (newT < 0) newT = 0; }
    pos[cur][qTok] = newT; lastK = qTok;
    if (applyCapture(cur, newT)) capFlag = 1;
    qSel = -1;
    finalize();
}

/* ---- Компьютер тоглогч ---- */
function aiPickToken() {
    let best = movTok[0], bestScore = -1000;
    for (let i = 0; i < nMov; i++) {
        const k = movTok[i], nt = movNew[i];
        let score = 0;
        if (nt === 56) score += 100;
        if (nt <= 50) {
            const idx = (startIdx[cur] + nt) % 52;
            if (!safeCell[idx]) {
                for (let q = 0; q < 4; q++) if (q !== cur && isActive[q])
                    for (let j = 0; j < 4; j++) {
                        const tq = pos[q][j];
                        if (tq >= 0 && tq <= 50 && (startIdx[q] + tq) % 52 === idx) score += 80;
                    }
            }
            if (safeCell[idx]) score += 15;
        }
        if (pos[cur][k] === -1) score += 40;
        if (nt > 50) score += 30;
        score += Math.floor(nt / 4);
        if (score > bestScore) { bestScore = score; best = k; }
    }
    return best;
}
function aiStep() {
    if (state === ST_ROLL) doRoll();
    else if (state === ST_CHOOSE) doChoose(aiPickToken());
    else if (state === ST_QUIZ) doQuizAnswer(rnd(100) < 70 ? QBANK[qIndex].ans : rnd(3));
    else if (state === ST_QRES) applyQuizResult();
}

let timer = null;
function scheduleAI() {
    clearTimeout(timer); timer = null;
    if (state === ST_OVER || state === ST_INTRO) return;
    if (state === ST_QRES) { timer = setTimeout(onTimer, 3000 * TIMESCALE); return; }
    if (!isAI[cur]) return;
    timer = setTimeout(onTimer, (state === ST_QUIZ ? 4500 : 900) * TIMESCALE);
}
function onTimer() {
    timer = null;
    if (state === ST_QRES) { applyQuizResult(); redraw(); scheduleAI(); return; }
    if (isAI[cur] && state !== ST_OVER && state !== ST_INTRO) { aiStep(); redraw(); scheduleAI(); }
}

/* ---- Үйлдлүүд (гар болон хулгана/хуруу хоёр ижил функц дуудна) ---- */
function startGame() {
    if (state !== ST_INTRO) return;
    applyMode();
    state = ST_ROLL;
    msg = `${pGen[cur]} ээлж. ENTER.`;
    scheduleAI(); redraw();
}
function resetLocal() {
    clearTimeout(timer); timer = null;
    resetPositions(); buildPools();
    for (let i = 0; i < 4; i++) { isActive[i] = 1; isAI[i] = 0; }
    dice = 0; sixCount = 0; winner = -1; capFlag = 0; qSel = -1; cur = 0; nMov = 0; movTok = []; movNew = [];
    state = ST_INTRO;
    msg = "Улааны ээлж. ENTER дарж шоо шид.";
}
function backToIntro() {
    if (online && online.role === "host") {              // онлайн өрөөндөө буцна (холболт хэвээр)
        online.started = false;
        online.conns = online.conns.filter(g => !g.gone);
    }
    resetLocal();
    redraw();
    if (online && online.role === "host") sendLobby(online);
}
// Энэ төхөөрөмжийн тоглогч одоо ээлжтэй юу?
const myTurn = () => online ? cur === online.seat : !isAI[cur];
const isGuest = () => online && online.role === "guest";
const sendHost = m => { try { online.conn.send(m); } catch (e) {} };

function humanRoll() {
    if (state !== ST_ROLL || !myTurn()) return;
    if (isGuest()) { sendHost({ t: "roll" }); return; }
    doRoll(); scheduleAI(); redraw();
}
function humanChoose(k) {
    if (state !== ST_CHOOSE || !myTurn() || !movTok.includes(k)) return;
    if (isGuest()) { sendHost({ t: "choose", k }); return; }
    doChoose(k); scheduleAI(); redraw();
}
function humanAnswer(i) {
    if (state !== ST_QUIZ || !myTurn()) return;
    if (isGuest()) { sendHost({ t: "answer", i }); return; }
    doQuizAnswer(i); scheduleAI(); redraw();
}
function continueQuiz() {
    if (state !== ST_QRES) return;
    if (isGuest()) { sendHost({ t: "cont" }); return; }
    applyQuizResult(); scheduleAI(); redraw();
}

/* ====================== Онлайн хамт тоглох (PeerJS / WebRTC) ======================
   Хост (өрөө үүсгэсэн хүн) бүх дүрмийг ажиллуулна. Бусад нь зөвхөн «шоо шид / хүү сонго /
   хариул» гэсэн үйлдлээ илгээж, хостоос ирсэн төлвийг харуулна. Сервер хэрэггүй. */
let online = null;
const ROOM_PREFIX = "mnludo-";
const CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
const makeCode = () => Array.from({ length: 4 }, () => CODE_CHARS[rnd(CODE_CHARS.length)]).join("");
const roomLink = code => location.href.split(/[?#]/)[0] + "?room=" + code;
const seatPlan = n => n === 2 ? [0, 2] : [0, 1, 2, 3].slice(0, n);

// ICE серверүүд: STUN (шууд холболт) + TURN (шууд холбогдож чадахгүй үед дамжуулагч, ялангуяа мобайл сүлжээнд)
const PEER_OPTS = { config: { sdpSemantics: "unified-plan", iceServers: [
    { urls: "stun:stun.l.google.com:19302" },
    { urls: "stun:stun.cloudflare.com:3478" },
    { urls: ["turn:eu-0.turn.peerjs.com:3478", "turn:us-0.turn.peerjs.com:3478"], username: "peerjs", credential: "peerjsp" },
    { urls: ["turn:openrelay.metered.ca:80", "turn:openrelay.metered.ca:443", "turn:openrelay.metered.ca:443?transport=tcp", "turns:openrelay.metered.ca:443?transport=tcp"],
      username: "openrelayproject", credential: "openrelayproject" }
] } };
const SIGNAL_ERRORS =["network", "server-error", "socket-error", "socket-closed"];
function netErrText(type) {
    if (SIGNAL_ERRORS.includes(type)) return "Холболтын сервертэй (0.peerjs.com) холбогдож чадсангүй. Сүлжээгээ шалгаад дахин оролдоно уу.";
    if (type === "browser-incompatible") return "Таны браузер онлайн тоглоомыг дэмжихгүй байна.";
    return "Алдаа: " + type;
}
// Холболтын серверээс тасарсан бол дахин холбогдохыг оролдоно (идэвхтэй холболтууд үүнээс үл хамаарна)
function retryReconnect(o, n) {
    if (online !== o || !o.peer || o.peer.destroyed || !o.peer.disconnected) return;
    try { o.peer.reconnect(); } catch (e) {}
    setTimeout(() => {
        if (online !== o || !o.peer || o.peer.destroyed) return;
        if (!o.peer.disconnected) { if (o.role === "host" && o.ready) o.status = ""; redraw(); return; }
        if (n < 10) retryReconnect(o, n + 1);
        else { o.status = netErrText("network"); if (!o.ready || o.role === "guest") o.failed = true; redraw(); }
    }, 2500);
}
// Онлайн байх үед дэлгэц унтарч холболт тасрахаас сэргийлнэ (дэмждэг хөтөч дээр)
let wakeLock = null;
async function keepAwake() {
    try {
        if (navigator.wakeLock && !wakeLock) {
            wakeLock = await navigator.wakeLock.request("screen");
            wakeLock.addEventListener("release", () => { wakeLock = null; });
        }
    } catch (e) {}
}
document.addEventListener("visibilitychange", () => {            // хуудас буцаж харагдахад дахин холбогдоно
    if (document.hidden || !online) return;
    keepAwake();
    if (online.peer && online.peer.disconnected && online.role === "host") retryReconnect(online, 0);
});
function leaveOnline() {
    if (wakeLock) { try { wakeLock.release(); } catch (e) {} wakeLock = null; }
    const o = online; online = null;
    if (o) { try { o.peer.destroy(); } catch (e) {} }
}
function hostRoom(tries) {
    tries = tries || 0;
    if (typeof Peer === "undefined") { alert("Онлайн сан ачаалагдсангүй. Интернэтээ шалгана уу."); return; }
    leaveOnline(); resetLocal(); keepAwake();
    const code = makeCode();
    const o = online = { role: "host", code, conns: [], seat: 0, status: "Өрөө үүсгэж байна...", ready: false, started: false };
    const peer = o.peer = new Peer(ROOM_PREFIX + code, PEER_OPTS);
    peer.on("open", () => { if (online !== o) return; o.ready = true; o.status = ""; redraw(); });
    peer.on("error", err => {
        if (online !== o) return;
        if (err.type === "unavailable-id" && !o.ready && tries < 5) { leaveOnline(); hostRoom(tries + 1); return; }
        if (o.ready && SIGNAL_ERRORS.includes(err.type)) return;      // "disconnected" үйл явдал дахин холбоно
        if (err.type === "unavailable-id") return;                    // дахин холбогдох үед түр гарна
        o.status = netErrText(err.type); if (!o.ready) o.failed = true; redraw();
    });
    peer.on("disconnected", () => {                                   // зөвхөн холболтын сервертэй тасарсан
        if (online !== o) return;
        o.status = "Сервертэй холбоо тасарлаа. Дахин холбогдож байна..."; redraw();
        retryReconnect(o, 0);
    });
    peer.on("connection", conn => onGuestConnect(o, conn));
    redraw();
}
function sendLobby(o) {
    const n = 1 + o.conns.filter(g => !g.gone).length;
    let i = 1;
    o.conns.forEach(g => { if (!g.gone) { try { g.conn.send({ t: "lobby", n, you: i }); } catch (e) {} i++; } });
    redraw();
}
function onGuestConnect(o, conn) {
    conn.on("open", () => {
        if (online !== o) { conn.close(); return; }
        if (o.started || o.conns.filter(g => !g.gone).length >= 3) {
            try { conn.send({ t: "full", started: o.started }); } catch (e) {}
            setTimeout(() => conn.close(), 400); return;
        }
        const g = { conn, seat: -1, gone: false };
        o.conns.push(g);
        conn.on("data", d => onGuestData(o, g, d));
        conn.on("close", () => onGuestGone(o, g));
        sendLobby(o);
    });
}
function onGuestGone(o, g) {
    if (online !== o || g.gone) return;
    g.gone = true;
    if (!o.started) { o.conns = o.conns.filter(x => x !== g); sendLobby(o); return; }
    isAI[g.seat] = 1;                                  // тасарсан тоглогчийг компьютер авна
    if (state !== ST_OVER) scheduleAI();
    redraw();
}
function onGuestData(o, g, d) {
    if (!o.started || !d) return;
    const s = g.seat;
    if (d.t === "roll" && state === ST_ROLL && cur === s && !isAI[s]) { doRoll(); scheduleAI(); redraw(); }
    else if (d.t === "choose" && state === ST_CHOOSE && cur === s && !isAI[s] && movTok.includes(d.k)) { doChoose(d.k); scheduleAI(); redraw(); }
    else if (d.t === "answer" && state === ST_QUIZ && cur === s && !isAI[s] && [0, 1, 2].includes(d.i)) { doQuizAnswer(d.i); scheduleAI(); redraw(); }
    else if (d.t === "cont") continueQuiz();
}
function startOnline() {
    const o = online;
    if (!o || o.role !== "host" || o.started) return;
    const live = o.conns.filter(g => !g.gone), n = 1 + live.length;
    if (n < 2) return;
    const seats = seatPlan(n);
    for (let i = 0; i < 4; i++) { isActive[i] = 0; isAI[i] = 0; }
    seats.forEach(s => isActive[s] = 1);
    o.seat = seats[0];
    live.forEach((g, i) => { g.seat = seats[i + 1]; try { g.conn.send({ t: "seat", seat: g.seat }); } catch (e) {} });
    o.conns = live; o.started = true;
    resetPositions(); buildPools();
    dice = 0; sixCount = 0; winner = -1; capFlag = 0; qSel = -1; nMov = 0; movTok = []; movNew = [];
    cur = seats[0]; state = ST_ROLL; msg = `${pGen[cur]} ээлж. ENTER.`;
    scheduleAI(); redraw();
}
let bcTimer = null;
function scheduleBroadcast() {
    if (bcTimer) return;
    bcTimer = setTimeout(() => {
        bcTimer = null;
        const o = online;
        if (!o || o.role !== "host") return;
        const snap = { t: "s", state, cur, dice, winner, pos: pos.map(a => a.slice()), isActive: isActive.slice(), isAI: isAI.slice(),
                       movTok, movNew, nMov, qIndex, qIsAdvance, qSel, qCorrect, msg };
        o.conns.forEach(g => { if (!g.gone) { try { g.conn.send(snap); } catch (e) {} } });
    }, 0);
}
function joinRoom(code) {
    code = (code || "").trim().toUpperCase();
    if (!code) return;
    if (typeof Peer === "undefined") { alert("Онлайн сан ачаалагдсангүй. Интернэтээ шалгана уу."); return; }
    leaveOnline(); resetLocal(); keepAwake();
    const o = online = { role: "guest", code, seat: -1, n: 1, idx: 0, status: "Холбогдож байна...", failed: false, connected: false };
    const peer = o.peer = new Peer(PEER_OPTS);
    peer.on("error", err => {
        if (online !== o) return;
        if (o.connected && SIGNAL_ERRORS.includes(err.type)) return;  // холбогдсоны дараа сервер шаардлагагүй
        o.failed = true;
        o.status = err.type === "peer-unavailable" ? "Өрөө олдсонгүй: " + code + ". Код зөв эсэхийг шалгаж, хост өрөөний дэлгэцээ нээлттэй байлгана уу." : netErrText(err.type);
        redraw();
    });
    peer.on("disconnected", () => {
        if (online !== o || o.connected || o.failed) return;
        retryReconnect(o, 0);
    });
    peer.on("open", () => {
        if (online !== o) return;
        o.brokerOpen = true; o.status = "Серверт холбогдлоо. Хостод холбогдож байна..."; redraw();
        const conn = o.conn = peer.connect(ROOM_PREFIX + code, { reliable: true });
        conn.on("open", () => { if (online !== o) return; o.connected = true; o.status = "Холбогдлоо. Хост эхлүүлэхийг хүлээнэ үү..."; redraw(); });
        conn.on("data", d => onHostData(o, d));
        conn.on("close", () => {
            if (online !== o || o.failed) return;
            o.failed = true; o.status = "Хостын холболт тасарлаа."; resetLocal(); redraw();
        });
    });
    setTimeout(() => {
        if (online !== o || o.connected || o.failed) return;
        o.failed = true;
        o.status = o.brokerOpen
            ? "Сервертэй холбогдсон ч хост руу шууд холбогдож чадсангүй (сүлжээ хаадаг байж магадгүй). Хоёр төхөөрөмжийг нэг Wi-Fi дээр туршиж үзнэ үү."
            : "Холболтын серверт хүрч чадсангүй. Сүлжээгээ шалгаад дахин оролдоно уу.";
        redraw();
    }, 25000);
    redraw();
}
function onHostData(o, d) {
    if (!d) return;
    if (d.t === "lobby") { o.n = d.n; o.idx = d.you; o.status = "Холбогдлоо. Хост эхлүүлэхийг хүлээнэ үү..."; }
    else if (d.t === "seat") o.seat = d.seat;
    else if (d.t === "full") { o.failed = true; o.status = d.started ? "Тоглоом аль хэдийн эхэлсэн байна." : "Өрөө дүүрсэн (дээд тал нь 4)."; }
    else if (d.t === "s") {
        state = d.state; cur = d.cur; dice = d.dice; winner = d.winner;
        for (let p = 0; p < 4; p++) { for (let k = 0; k < 4; k++) pos[p][k] = d.pos[p][k]; isActive[p] = d.isActive[p]; isAI[p] = d.isAI[p]; }
        movTok = d.movTok; movNew = d.movNew; nMov = d.nMov;
        qIndex = d.qIndex; qIsAdvance = d.qIsAdvance; qSel = d.qSel; qCorrect = d.qCorrect; msg = d.msg;
    }
    redraw();
}
function exitOnline() { leaveOnline(); resetLocal(); redraw(); }
function copyLink() {
    const o = online; if (!o) return;
    const link = roomLink(o.code);
    const done = () => { o.status = "Холбоос хуулагдлаа. Найзууддаа явуулаарай."; redraw(); };
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(link).then(done, () => prompt("Холбоос:", link));
    else prompt("Холбоос:", link);
}

/* ====================== Зураг (Canvas) ====================== */
const canvas = document.getElementById("c");
const ctx = canvas.getContext("2d");
let hits = [];          // дарагдах хэсгүүд (сүүлд нэмсэн нь дээр)
let tokHit = [];        // самбар дээрх хүүгийн байрлал

const hexv = ch => parseInt(ch, 16);

function makeSprite(w, h, fn) {
    const c = document.createElement("canvas"); c.width = w; c.height = h;
    const x = c.getContext("2d"), im = x.createImageData(w, h), d = im.data;
    for (let i = 0; i < w * h; i++) {
        const px = fn(i);
        d[4*i] = px[0]; d[4*i+1] = px[1]; d[4*i+2] = px[2]; d[4*i+3] = px[3];
    }
    x.putImageData(im, 0, 0);
    return c;
}
const embSprite = makeSprite(EMB_N, EMB_N, i => [150, 105, 30, Math.round(hexv(EMB_A[i]) / 15 * 255)]);
const knotSprite = makeSprite(KNOT_W, KNOT_H, i => [120, 80, 20, Math.round(hexv(KNOT_A[i]) / 15 * 255)]);
const shgSprite = [0, 1, 2, 3].map(s => PCOL.map(pc => makeSprite(SHG_W[s], SHG_H[s], i => {
    const a = hexv(SHG_DATA[s][2*i]) / 15, t = hexv(SHG_DATA[s][2*i + 1]) / 15;
    return [255*(1-t) + pc[0]*t, 244*(1-t) + pc[1]*t, 226*(1-t) + pc[2]*t, Math.round(a * 255)];
})));

const fnt = (px, bold) => `${bold ? 700 : 400} ${(px * 0.82).toFixed(1)}px ${FONT}`;
function mnText(x, y, text, px, col, bold, center) {
    ctx.font = fnt(px, bold);
    ctx.fillStyle = col;
    ctx.textAlign = center ? "center" : "left";
    ctx.textBaseline = "top";
    ctx.fillText(text, x, y + px * 0.1);
}
function textWidthB(text, px, bold) { ctx.font = fnt(px, bold); return ctx.measureText(text).width; }

function fillR(x1, y1, x2, y2, col) { ctx.fillStyle = col; ctx.fillRect(x1, y1, x2 - x1, y2 - y1); }
function rectLine(x1, y1, x2, y2, col, lw) {
    ctx.strokeStyle = col; ctx.lineWidth = lw || 1;
    ctx.strokeRect(x1 + 0.5, y1 + 0.5, x2 - x1 - 1, y2 - y1 - 1);
}
function line(x1, y1, x2, y2, col, lw) {
    ctx.strokeStyle = col; ctx.lineWidth = lw || 1;
    ctx.beginPath(); ctx.moveTo(x1, y1 + 0.5); ctx.lineTo(x2, y2 + 0.5); ctx.stroke();
}
function circleF(cx, cy, rad, fill, border, lw) {
    ctx.beginPath(); ctx.arc(cx, cy, rad, 0, Math.PI * 2);
    ctx.fillStyle = fill; ctx.fill();
    ctx.strokeStyle = border; ctx.lineWidth = lw || 2; ctx.stroke();
}
// Сум: ang = заах чиглэл (радиан, 0 = баруун, canvas-ийн координат). s = урт.
function drawArrowAng(cx, cy, s, ang, col) {
    const hw = s * 0.46, sw = s * 0.17, head = s * 0.5, tip = s / 2, base = -s / 2, neck = tip - head;
    ctx.save();
    ctx.translate(cx, cy); ctx.rotate(ang);
    ctx.beginPath();
    ctx.moveTo(tip, 0);
    ctx.lineTo(neck, hw); ctx.lineTo(neck, sw);
    ctx.lineTo(base, sw); ctx.lineTo(base, -sw);
    ctx.lineTo(neck, -sw); ctx.lineTo(neck, -hw);
    ctx.closePath();
    ctx.fillStyle = col; ctx.fill();
    ctx.restore();
}
// Тайлбар дахь сум: fwd = true бол баруун (урагшлах), false бол зүүн (ухрах)
const drawArrow = (cx, cy, s, fwd, col) => drawArrowAng(cx, cy, s, fwd ? 0 : Math.PI, col);
// Замын i-р нүднээс урагш (dir=1) эсвэл хойш (dir=-1) заах чиглэл
function pathAng(i, dir) {
    const j = (i + dir + 52) % 52;
    return Math.atan2(pathR[j] - pathR[i], pathC[j] - pathC[i]);
}
function darken(rgb, pct) { return `rgb(${rgb[0]*pct/100|0},${rgb[1]*pct/100|0},${rgb[2]*pct/100|0})`; }

const cxpix = c => BX + c * CELL + CELL / 2;
const cypix = r => BY + r * CELL + CELL / 2;

function cellRect(r, c, fill) {
    const x1 = BX + c * CELL, y1 = BY + r * CELL;
    fillR(x1, y1, x1 + CELL, y1 + CELL, fill);
    rectLine(x1, y1, x1 + CELL, y1 + CELL, MN_GRID);
}

/* ---- Хээ угалз ---- */
const FR_KNOT = ["#########", "........#", "###.###.#", "..#.#.#.#", "#######.#", "#.#.#...#", "#######.#", "..#.#.#.#", "..###.#.#"];
const RK = [".........#.#.", "##.###.######", ".#.#.#.#.#.#.", ".#.##########", ".#...#.#.#.#.", ".###########.", ".....#.#.#...", ".....#######.", ".......#.#.#.", ".......#.###.", ".......#.....", ".......#####.", "...........#."];

function frRect(x, y, w, h) { ctx.fillRect(x, y, w, h); }

function drawFullFrame(col, m, inset) {
    const x1 = inset, y1 = inset, x2 = W - inset, y2 = H - inset;
    ctx.fillStyle = col;
    for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) {
        if (FR_KNOT[r][c] !== "#") continue;
        for (let left = 0; left < 2; left++) for (let top = 0; top < 2; top++) {
            const x = left ? x1 + (8 - c) * m : x2 - 9 * m + c * m;
            const y = top ? y1 + r * m : y2 - 9 * m + (8 - r) * m;
            frRect(x, y, m, m);
        }
    }
    const hw = x2 - x1 - 18 * m, vh = y2 - y1 - 18 * m;
    frRect(x1 + 9*m, y1, hw, m);        frRect(x1 + 9*m, y1 + 2*m, hw, m);
    frRect(x1 + 9*m, y2 - m, hw, m);    frRect(x1 + 9*m, y2 - 3*m, hw, m);
    frRect(x1, y1 + 9*m, m, vh);        frRect(x1 + 2*m, y1 + 9*m, m, vh);
    frRect(x2 - m, y1 + 9*m, m, vh);    frRect(x2 - 3*m, y1 + 9*m, m, vh);
}

function drawKnotRing(x1, y1, x2, y2, m, col) {
    ctx.fillStyle = col;
    const K = 13;
    frRect(x1, y1, x2 - x1, m); frRect(x1, y2 - m, x2 - x1, m);
    frRect(x1, y1, m, y2 - y1); frRect(x2 - m, y1, m, y2 - y1);
    for (let fx = 0; fx < 2; fx++) for (let fy = 0; fy < 2; fy++) {
        const bx = fx ? x1 + m : x2 - m - K * m;
        const by = fy ? y2 - m - K * m : y1 + m;
        for (let r = 0; r < K; r++) for (let c = 0; c < K; c++) {
            const rr = fy ? K - 1 - r : r, cc = fx ? K - 1 - c : c;
            if (RK[rr][cc] === "#") frRect(bx + c * m, by + r * m, m, m);
        }
    }
    let a0 = x1 + m + K * m, a1 = x2 - m - K * m;
    if (a1 > a0) { frRect(a0, y1 + 2*m, a1 - a0, m); frRect(a0, y2 - 3*m, a1 - a0, m); }
    a0 = y1 + m + K * m; a1 = y2 - m - K * m;
    if (a1 > a0) { frRect(x1 + 2*m, a0, m, a1 - a0); frRect(x2 - 3*m, a0, m, a1 - a0); }
}

function drawKnotAt(cx, cy, h) {
    const sc = h / KNOT_H, dw = KNOT_W * sc;
    ctx.drawImage(knotSprite, cx - dw / 2, cy - h / 2, dw, h);
}
function drawDivider(xl, xr, cy) {
    const cx = (xl + xr) / 2;
    line(xl, cy, cx - KNOT_W / 2 - 6, cy, MN_ORN);
    line(cx + KNOT_W / 2 + 6, cy, xr, cy, MN_ORN);
    drawKnotAt(cx, cy, KNOT_H);
}

/* ---- Самбар ---- */
function drawBase(p, r0, c0) {
    const x1 = BX + c0 * CELL, y1 = BY + r0 * CELL, x2 = BX + (c0 + 6) * CELL, y2 = BY + (r0 + 6) * CELL;
    fillR(x1, y1, x2, y2, MN_WHITE);
    drawKnotRing(x1, y1, x2, y2, 4, pColor[p]);
    fillR(x1 + CELL, y1 + CELL, x2 - CELL, y2 - CELL, MN_WHITE);
    rectLine(x1 + CELL, y1 + CELL, x2 - CELL, y2 - CELL, MN_BLACK);
}
function drawCenter() {
    const x1 = BX + 6 * CELL, y1 = BY + 6 * CELL, x2 = BX + 9 * CELL, y2 = BY + 9 * CELL;
    const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
    const tris = [[[x1,y1],[x1,y2],[mx,my]], [[x1,y1],[x2,y1],[mx,my]], [[x2,y1],[x2,y2],[mx,my]], [[x1,y2],[x2,y2],[mx,my]]];
    tris.forEach((t, i) => {
        ctx.beginPath(); ctx.moveTo(t[0][0], t[0][1]); ctx.lineTo(t[1][0], t[1][1]); ctx.lineTo(t[2][0], t[2][1]); ctx.closePath();
        ctx.fillStyle = pColor[i]; ctx.fill();
        ctx.strokeStyle = MN_BLACK; ctx.lineWidth = 1; ctx.stroke();
    });
}
function drawEmblem() {
    const cx = BX + 7 * CELL + CELL / 2, cy = BY + 7 * CELL + CELL / 2, R0 = CELL * 3 / 2 - 2;
    circleF(cx, cy, R0, MN_WHITE, MN_ORN, 2);
    ctx.drawImage(embSprite, cx - EMB_N / 2, cy - EMB_N / 2, EMB_N, EMB_N);
}
function drawBoard() {
    fillR(0, 0, W, H, MN_PARCH);
    drawFullFrame(MN_ORN, 4, 2);
    drawBase(0, 0, 0); drawBase(1, 0, 9); drawBase(2, 9, 9); drawBase(3, 9, 0);
    for (let i = 0; i < 52; i++) cellRect(pathR[i], pathC[i], MN_WHITE);
    for (let p = 0; p < 4; p++) for (let i = 0; i < 6; i++) cellRect(laneR[p][i], laneC[p][i], pColor[p]);
    for (let p = 0; p < 4; p++) cellRect(pathR[startIdx[p]], pathC[startIdx[p]], pColor[p]);
    drawCenter();
    drawEmblem();
    for (let i = 0; i < 4; i++) {
        const a = advCells[i];
        cellRect(pathR[a], pathC[a], "rgb(180,245,180)");
        drawArrowAng(cxpix(pathC[a]), cypix(pathR[a]), 26, pathAng(a, 1), "rgb(0,125,30)");
        const b = retCells[i];
        cellRect(pathR[b], pathC[b], "rgb(255,195,195)");
        drawArrowAng(cxpix(pathC[b]), cypix(pathR[b]), 26, pathAng(b, -1), "rgb(190,20,20)");
    }
    for (let i = 0; i < 52; i++) if (safeCell[i]) {
        ctx.beginPath(); ctx.arc(cxpix(pathC[i]), cypix(pathR[i]), CELL / 4, 0, Math.PI * 2);
        ctx.strokeStyle = MN_BLACK; ctx.lineWidth = 1; ctx.stroke();
    }
}

/* ---- Хүү (шагай) ---- */
function drawToken(X, Y, p, label, rad) {
    const shape = (label - 1) & 3, sw = SHG_W[shape], sh = SHG_H[shape];
    const sc = rad * 2.45 / SHG_SRC, dw = sw * sc, dh = sh * sc;
    const ox = X - dw / 2, oy = Y - dh / 2 - dh / 20;

    // сүүдэр
    const ecy = Y + dh * 0.40, rx = dw * 0.46, ry = Math.max(dh * 0.13, 1.5);
    ctx.save();
    ctx.translate(X, ecy); ctx.scale(1, ry / rx);
    const g = ctx.createRadialGradient(0, 0, 0, 0, 0, rx);
    g.addColorStop(0, "rgba(0,0,0,0.30)"); g.addColorStop(0.5, "rgba(0,0,0,0.225)");
    g.addColorStop(0.8, "rgba(0,0,0,0.108)"); g.addColorStop(1, "rgba(0,0,0,0)");
    ctx.fillStyle = g; ctx.beginPath(); ctx.arc(0, 0, rx, 0, Math.PI * 2); ctx.fill();
    ctx.restore();

    ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = "high";
    ctx.drawImage(shgSprite[shape][p], ox, oy, dw, dh);

    if (rad >= 8) {
        const ldw = Math.round(sw * sc), ldh = Math.round(sh * sc);
        const lox = X - Math.floor(ldw / 2), loy = Y - Math.floor(ldh / 2) - Math.floor(ldh / 20);
        let br = Math.floor(rad * 42 / 100); if (br < 4) br = 4;
        const bx = lox + ldw - Math.floor(br / 2), by = loy + Math.floor(br / 2);
        circleF(bx, by, br, darken(PCOL[p], 70), "rgb(255,255,255)", 1);
        const fs = br * 2 + 1;
        mnText(bx, by - fs / 2, String(label), fs, "rgb(255,255,255)", 1, 1);
    }
}
function drawTokens() {
    tokHit = [];
    const cnt = Array.from({ length: 15 }, () => new Array(15).fill(0));
    const idx = Array.from({ length: 15 }, () => new Array(15).fill(0));
    for (let p = 0; p < 4; p++) {
        if (!isActive[p]) continue;
        for (let k = 0; k < 4; k++) {
            if (pos[p][k] < 0) continue;
            const [r, c] = getCell(p, pos[p][k]); cnt[r][c]++;
        }
    }
    for (let p = 0; p < 4; p++) {
        if (!isActive[p]) continue;
        for (let k = 0; k < 4; k++) {
            const t = pos[p][k];
            if (t === -1) {
                const X = BX + baseC[p][k] * CELL, Y = BY + baseR[p][k] * CELL;
                drawToken(X, Y, p, k + 1, CELL / 2 - 3);
                tokHit.push({ p, k, x: X, y: Y, r: CELL / 2 });
                continue;
            }
            const [r, c] = getCell(p, t);
            const n = cnt[r][c], i = idx[r][c]++;
            const cx = cxpix(c), cy = cypix(r);
            let X = cx, Y = cy, rad;
            if (n === 1) { rad = CELL / 2 - 5; }
            else if (n === 2) { const d = CELL / 4; X = cx + (i === 0 ? -d : d); rad = CELL / 4 - 1; }
            else if (n <= 4) { const d = CELL / 4; X = cx + (i % 2 === 0 ? -d : d); Y = cy + (Math.floor(i / 2) === 0 ? -d : d); rad = CELL / 4 - 1; }
            else if (n <= 9) { const d = CELL / 3; X = cx + (i % 3 - 1) * d; Y = cy + (Math.floor(i / 3) - 1) * d; rad = CELL / 6; }
            else { const d = CELL / 4; X = cx + (2 * (i % 4) - 3) * d / 2; Y = cy + (2 * Math.floor(i / 4) - 3) * d / 2; rad = CELL / 9; }
            drawToken(X, Y, p, k + 1, Math.floor(rad));
            tokHit.push({ p, k, x: X, y: Y, r: Math.max(rad, 9) });
        }
    }
}

/* ---- Шоо ---- */
function drawDie(x, y, v) {
    const s = 56;
    fillR(x, y, x + s, y + s, MN_WHITE);
    rectLine(x, y, x + s, y + s, MN_BLACK);
    const cx = x + s / 2, cy = y + s / 2, off = s / 4, rad = 5;
    const a = [x + off, y + off], b = [x + s - off, y + off], c = [x + off, cy], d = [x + s - off, cy];
    const e = [x + off, y + s - off], f = [x + s - off, y + s - off], m = [cx, cy];
    const dots = { 1: [m], 2: [a, f], 3: [a, m, f], 4: [a, b, e, f], 5: [a, b, m, e, f], 6: [a, b, c, d, e, f] }[v] || [];
    dots.forEach(q => circleF(q[0], q[1], rad, MN_BLACK, MN_BLACK, 1));
}

function drawWrapped(x, y, maxw, text, px, col) {
    let ln = "", n = 0;
    for (const w of text.split(" ")) {
        const test = ln ? ln + " " + w : w;
        if (ln && textWidthB(test, px, 0) > maxw) {
            mnText(x, y + n * (px + 3), ln, px, col, 0, 0); n++; ln = w;
            if (n >= 4) return;
        } else ln = test;
    }
    if (ln && n < 4) mnText(x, y + n * (px + 3), ln, px, col, 0, 0);
}

/* ---- Товч (хулгана / хуруугаар) ---- */
function button(x, y, w, h, label, px, fg, bg, border, fn, bold) {
    fillR(x, y, x + w, y + h, bg);
    rectLine(x, y, x + w, y + h, border, 2);
    mnText(x + w / 2, y + (h - px) / 2 - 1, label, px, fg, bold === undefined ? 1 : bold, 1);
    if (fn) hits.push({ x1: x, y1: y, x2: x + w, y2: y + h, fn });
}

/* ---- Баруун самбар ---- */
function drawPanel() {
    const px = BX + 15 * CELL + 20, py = BY + 8;
    const panelX1 = px - 10, panelY1 = py - 4, panelX2 = W - 42, panelY2 = H - 42;
    fillR(panelX1, panelY1, panelX2, panelY2, MN_PARCH2);
    rectLine(panelX1, panelY1, panelX2, panelY2, MN_ORN);
    mnText(px, py + 6, "Та битгий уурлаарай", 20, MN_ORN_DK, 1, 0);
    line(px, py + 46, panelX2 - 10, py + 46, MN_ORN);
    mnText(px, py + 54, "Ээлж:", 20, MN_INK, 0, 0);
    mnText(px + 64, py + 51, pName[cur], 24, pColor[cur], 1, 0);
    if (isAI[cur]) mnText(px + 64, py + 78, "(Компьютер)", 15, MN_ORN_DK, 0, 0);
    if (dice > 0) drawDie(px, py + 90, dice);
    drawWrapped(px + 70, py + 92, panelX2 - 10 - (px + 70), msg, 16, MN_INK);
    drawDivider(px, panelX2 - 10, py + 178);
    mnText(px, py + 204, "ГЭРТ ОРУУЛСАН", 15, MN_ORN_DK, 1, 0);
    let row = 0;
    for (let p = 0; p < 4; p++) {
        if (!isActive[p]) continue;
        mnText(px, py + 228 + row * 26, `${pName[p]}${isAI[p] ? " (комп)" : ""}: ${homeCount(p)}/4`, 19, pColor[p], 1, 0);
        row++;
    }
    drawDivider(px, panelX2 - 10, py + 352);

    // үйлдлийн хэсэг
    mnText(px, py + 366, "УДИРДЛАГА", 15, MN_ORN_DK, 1, 0);
    if (online && online.seat >= 0) mnText(px + 104, py + 365, "Та: " + pName[online.seat], 16, pColor[online.seat], 1, 0);
    const bw = panelX2 - 10 - px;
    if (state === ST_ROLL && myTurn()) {
        button(px, py + 388, bw, 38, "ШОО ШИДЭХ", 18, "rgb(255,248,225)", pColor[cur], MN_ORN_DK, humanRoll);
    } else if (state === ST_CHOOSE && myTurn()) {
        const w = (bw - 3 * 6) / 4;
        for (let k = 0; k < 4; k++) {
            const ok = movTok.includes(k);
            button(px + k * (w + 6), py + 388, w, 38, String(k + 1), 20, ok ? "rgb(255,248,225)" : "rgb(170,150,110)",
                   ok ? pColor[cur] : "rgb(214,198,156)", ok ? MN_ORN_DK : MN_GRID, ok ? () => humanChoose(k) : null);
        }
    } else if (isAI[cur] && state !== ST_OVER) {
        mnText(px, py + 398, "Компьютер бодож байна...", 15, MN_ORN_DK, 0, 0);
    } else if (!myTurn() && state !== ST_OVER) {
        mnText(px, py + 398, `${pGen[cur]} ээлж. Хүлээнэ үү...`, 15, MN_ORN_DK, 0, 0);
    }
    mnText(px, py + 434, "ENTER шоо · 1-4 хүү · ESC цэс", 14, MN_INK, 0, 0);
    drawArrow(px + 7, py + 486, 14, true, "rgb(0,125,30)");
    mnText(px + 20, py + 478, "ногоон - зөв бол урагшилна", 14, "rgb(0,110,40)", 0, 0);
    drawArrow(px + 7, py + 505, 14, false, "rgb(190,20,20)");
    mnText(px + 20, py + 496, "улаан - буруу бол ухарна", 14, "rgb(160,30,30)", 0, 0);
    drawKnotAt(panelX2 - 26, panelY2 - 26, 30);
}

/* ---- Асуулт ---- */
function drawQuiz() {
    const q = QBANK[qIndex];
    const x1 = 60, y1 = 410, x2 = 800, y2 = 618;
    fillR(x1, y1, x2, y2, "rgb(252,244,215)");
    rectLine(x1, y1, x2, y2, MN_ORN, 3);
    rectLine(x1 + 6, y1 + 6, x2 - 6, y2 - 6, MN_ORN_DK);
    drawKnotAt(x1 + 20, y1 + 20, 25); drawKnotAt(x2 - 20, y1 + 20, 25);
    drawKnotAt(x1 + 20, y2 - 20, 25); drawKnotAt(x2 - 20, y2 - 20, 25);
    const qTitle = qIsAdvance ? "УРАГШЛАХ АСУУЛТ" : "УХРАХ АСУУЛТ";
    mnText(x1 + 45, y1 + 14, qTitle, 22, pColor[cur], 1, 0);
    drawArrow(x1 + 45 + textWidthB(qTitle, 22, 1) + 20, y1 + 26, 22, qIsAdvance, qIsAdvance ? "rgb(0,125,30)" : "rgb(190,20,20)");
    // урт асуултыг хоёр мөр болгож тайрна
    const maxw = x2 - x1 - 90;
    if (textWidthB(q.text, 21, 1) <= maxw) mnText(x1 + 45, y1 + 46, q.text, 21, MN_INK, 1, 0);
    else {
        let l1 = "", rest = q.text.split(" ");
        while (rest.length && textWidthB(l1 + " " + rest[0], 21, 1) <= maxw) l1 += (l1 ? " " : "") + rest.shift();
        mnText(x1 + 45, y1 + 40, l1, 21, MN_INK, 1, 0);
        mnText(x1 + 45, y1 + 64, rest.join(" "), 21, MN_INK, 1, 0);
    }
    for (let i = 0; i < 3; i++) {
        const oy = y1 + 84 + i * 30;
        let tc = MN_INK;
        if (state === ST_QRES) {
            if (i === q.ans) { fillR(x1 + 50, oy - 3, x1 + 500, oy + 25, "rgb(206,238,206)"); tc = "rgb(0,110,40)"; }
            else if (i === qSel) { fillR(x1 + 50, oy - 3, x1 + 500, oy + 25, "rgb(246,206,206)"); tc = "rgb(160,30,30)"; }
        } else if (myTurn()) {
            fillR(x1 + 50, oy - 3, x1 + 500, oy + 25, "rgb(244,230,190)");
            rectLine(x1 + 50, oy - 3, x1 + 500, oy + 25, MN_GRID);
            hits.push({ x1: x1 + 50, y1: oy - 3, x2: x1 + 500, y2: oy + 25, fn: () => humanAnswer(i) });
        }
        mnText(x1 + 60, oy, `${i + 1})  ${q.o[i]}`, 19, tc, state === ST_QRES && i === q.ans ? 1 : 0, 0);
    }
    if (state === ST_QRES) {
        mnText(x1 + 45, y2 - 36, qCorrect ? "ЗӨВ!" : "БУРУУ!", 22, qCorrect ? "rgb(0,120,40)" : "rgb(170,30,30)", 1, 0);
        mnText(x1 + 150, y2 - 32, "— үргэлжлүүлэхийн тулд дар", 17, MN_ORN_DK, 0, 0);
    } else if (isAI[cur]) mnText(x1 + 45, y2 - 32, "Компьютер бодож байна...", 18, MN_ORN_DK, 0, 0);
    else if (!myTurn()) mnText(x1 + 45, y2 - 32, `${pName[cur]} хариулж байна...`, 18, MN_ORN_DK, 0, 0);
    else mnText(x1 + 45, y2 - 32, "1 / 2 / 3 эсвэл дарж хариулна уу", 18, MN_ORN_DK, 0, 0);
}

/* ---- Эхлэх дэлгэц ---- */
function drawIntro() {
    const BG = "rgb(14,20,52)", BOX = "rgb(22,30,70)", GOLD = "rgb(214,176,74)", GDK = "rgb(150,116,36)";
    const TXT = "rgb(228,224,210)", SUB = "rgb(170,168,158)", KEY = "rgb(40,50,100)";
    fillR(0, 0, W, H, BG);
    drawFullFrame(GOLD, 5, 12);

    const wd = ["Та", "битгий", "уурлаарай"], wc = [pColor[0], pColor[1], pColor[2]];
    const ww = wd.map(w => textWidthB(w, 46, 1)), sp = 18;
    let tx = W / 2 - (ww[0] + ww[1] + ww[2] + sp * 2) / 2;
    for (let i = 0; i < 3; i++) { mnText(tx, 58, wd[i], 46, wc[i], 1, 0); tx += ww[i] + sp; }
    mnText(W / 2, 118, "Монгол ардын тоглоом", 18, GOLD, 1, 1);
    mnText(W / 2, 152, "ГОРИМ СОНГОХ  (1 / 2 / 3 / 4 дар)", 17, SUB, 1, 1);

    const mw = 176, mh = 52, gap = 12, mx0 = W / 2 - (mw * 4 + gap * 3) / 2, my = 180;
    for (let i = 0; i < 4; i++) {
        const x = mx0 + i * (mw + gap), sel = gameMode === i;
        fillR(x, my, x + mw, my + mh, sel ? "rgb(46,60,120)" : BOX);
        rectLine(x, my, x + mw, my + mh, sel ? GOLD : GDK, sel ? 3 : 1);
        mnText(x + 22, my + 13, String(i + 1), 22, sel ? GOLD : SUB, 1, 1);
        mnText(x + 40, my + 16, modeName[i], 15, sel ? TXT : SUB, sel ? 1 : 0, 0);
        hits.push({ x1: x, y1: my, x2: x + mw, y2: my + mh, fn: () => { gameMode = i; redraw(); } });
    }
    const lx = 150, ly = 248;
    for (let i = 0; i < 4; i++) {
        const x = lx + i * 145;
        circleF(x, ly + 9, 8, pColor[i], "rgb(255,255,255)", 2);
        mnText(x + 16, ly, pName[i], 17, TXT, 0, 0);
    }
    mnText(W / 2, 282, "Зорилго: 4 хүүгээ замаар аваад түрүүлж гэрт оруулна.", 16, SUB, 0, 1);

    const bw = 340, bh = 150, by = 314, b1x = 70, b2x = W - 70 - bw;
    fillR(b1x, by, b1x + bw, by + bh, BOX); rectLine(b1x, by, b1x + bw, by + bh, GDK);
    mnText(b1x + 16, by + 10, "УДИРДЛАГА", 17, GOLD, 1, 0);
    [["ENTER", "Шоогоо хаях"], ["1 - 4", "Хүүгээ сонгох"], ["ESC", "Цэс рүү буцах"]].forEach((r, i) => {
        const yy = by + 42 + i * 34;
        fillR(b1x + 18, yy, b1x + 108, yy + 22, KEY); rectLine(b1x + 18, yy, b1x + 108, yy + 22, GOLD);
        mnText(b1x + 63, yy + 2, r[0], 14, TXT, 1, 1);
        mnText(b1x + 118, yy + 2, r[1], 16, TXT, 0, 0);
    });
    fillR(b2x, by, b2x + bw, by + bh, BOX); rectLine(b2x, by, b2x + bw, by + bh, GDK);
    mnText(b2x + 16, by + 10, "ДҮРЭМ", 17, GOLD, 1, 0);
    ["•  Гэрээс гарахад 1 эсвэл 6 буулгах.", "•  6 буувал дахин шиднэ, 1 бол ээлж дуусна.",
     "•  3 удаа 6 гарвал ээлж алдана.", "•  Дайсан дээр буувал гэрт нь буцаана.",
     "•  Аюулгүй нүдэн дээр баригдахгүй."].forEach((t, i) => mnText(b2x + 18, by + 40 + i * 22, t, 15, TXT, 0, 0));

    const cy2 = 474, ch = 78;
    fillR(b1x, cy2, b1x + bw, cy2 + ch, "rgb(16,46,26)"); rectLine(b1x, cy2, b1x + bw, cy2 + ch, "rgb(60,150,80)");
    drawArrow(b1x + 24, cy2 + 21, 18, true, "rgb(110,220,130)");
    mnText(b1x + 42, cy2 + 10, "УРАГШЛАХ НҮД", 17, "rgb(110,220,130)", 1, 0);
    mnText(b1x + 18, cy2 + 38, "Зөв хариулвал 4 алхам урагшилна.", 15, TXT, 0, 0);
    mnText(b1x + 18, cy2 + 56, "Буруу бол байрандаа.", 15, SUB, 0, 0);
    fillR(b2x, cy2, b2x + bw, cy2 + ch, "rgb(52,18,20)"); rectLine(b2x, cy2, b2x + bw, cy2 + ch, "rgb(180,70,70)");
    drawArrow(b2x + 24, cy2 + 21, 18, false, "rgb(240,130,130)");
    mnText(b2x + 42, cy2 + 10, "УХРАХ НҮД", 17, "rgb(240,130,130)", 1, 0);
    mnText(b2x + 18, cy2 + 38, "Буруу бол 4 алхам ухарна.", 15, TXT, 0, 0);
    mnText(b2x + 18, cy2 + 56, "Зөв бол ухрахгүй.", 15, SUB, 0, 0);

    button(W / 2 - 130, 562, 260, 42, "ЭХЛЭХ  (SPACE)", 18, GOLD, KEY, GOLD, startGame);
    button(70, 562, 220, 42, "ОНЛАЙН: өрөө үүсгэх", 15, TXT, BOX, GDK, () => hostRoom(0), 1);
    button(W - 70 - 220, 562, 220, 42, "ОНЛАЙН: өрөөнд орох", 15, TXT, BOX, GDK, () => joinRoom(prompt("Өрөөний кодыг оруулна уу:")), 1);
}

function drawOver() {
    const x1 = 160, y1 = 260, x2 = 600, y2 = 410;
    fillR(x1, y1, x2, y2, "rgb(252,244,215)");
    rectLine(x1, y1, x2, y2, MN_ORN, 3);
    rectLine(x1 + 6, y1 + 6, x2 - 6, y2 - 6, MN_ORN_DK);
    drawKnotAt(x1 + 22, y1 + 22, 28); drawKnotAt(x2 - 22, y1 + 22, 28);
    drawKnotAt(x1 + 22, y2 - 22, 28); drawKnotAt(x2 - 22, y2 - 22, 28);
    mnText((x1 + x2) / 2, y1 + 40, "ЯЛАГЧ", 28, MN_ORN_DK, 1, 1);
    mnText((x1 + x2) / 2, y1 + 78, `${pName[winner]} ЯЛЛАА!`, 40, pColor[winner], 1, 1);
    if (isGuest()) button((x1 + x2) / 2 - 90, y2 - 44, 180, 30, "Гарах", 17, "rgb(255,248,225)", MN_ORN_DK, MN_ORN, exitOnline);
    else button((x1 + x2) / 2 - 90, y2 - 44, 180, 30, online ? "Өрөө рүү буцах" : "Дахин тоглох", 17, "rgb(255,248,225)", MN_ORN_DK, MN_ORN, backToIntro);
}

/* ---- Онлайн өрөөний дэлгэц ---- */
function drawLobby() {
    const BG = "rgb(14,20,52)", BOX = "rgb(22,30,70)", GOLD = "rgb(214,176,74)", GDK = "rgb(150,116,36)";
    const TXT = "rgb(228,224,210)", SUB = "rgb(170,168,158)", KEY = "rgb(40,50,100)";
    const o = online;
    fillR(0, 0, W, H, BG);
    drawFullFrame(GOLD, 5, 12);
    const wd = ["Та", "битгий", "уурлаарай"], ww = wd.map(w => textWidthB(w, 40, 1)), sp = 16;
    let tx = W / 2 - (ww[0] + ww[1] + ww[2] + sp * 2) / 2;
    for (let i = 0; i < 3; i++) { mnText(tx, 50, wd[i], 40, pColor[i], 1, 0); tx += ww[i] + sp; }
    mnText(W / 2, 104, "ОНЛАЙН ӨРӨӨ", 18, GOLD, 1, 1);

    const host = o.role === "host";
    mnText(W / 2, 146, "Өрөөний код", 16, SUB, 1, 1);
    mnText(W / 2, 168, (host && !o.ready) ? "..." : o.code, 70, GOLD, 1, 1);
    if (host && o.ready) {
        mnText(W / 2, 258, roomLink(o.code), 14, SUB, 0, 1);
        button(W / 2 - 110, 284, 220, 34, "Холбоос хуулах", 16, GOLD, KEY, GOLD, copyLink);
    }

    const n = host ? 1 + o.conns.filter(g => !g.gone).length : o.n;
    const plan = seatPlan(Math.max(n, 2));
    const showList = host || o.connected;                    // холбогдохоос өмнө жагсаалт харуулахгүй
    if (showList) mnText(W / 2, 338, `ТОГЛОГЧИД (${n}/4)`, 16, GOLD, 1, 1);
    for (let i = 0; i < (showList ? n : 0); i++) {
        const y = 366 + i * 32, s = plan[i];
        fillR(W / 2 - 160, y, W / 2 + 160, y + 28, BOX); rectLine(W / 2 - 160, y, W / 2 + 160, y + 28, GDK);
        circleF(W / 2 - 138, y + 14, 8, pColor[s], "rgb(255,255,255)", 2);
        const me = host ? i === 0 : i === o.idx;
        mnText(W / 2 - 118, y + 4, `${i + 1}. ${pName[s]}${i === 0 ? " (хост)" : ""}${me ? " — Та" : ""}`, 17, TXT, me ? 1 : 0, 0);
    }
    if (IN_APP_BROWSER) {
        mnText(W / 2, 440, "Анхаар: Messenger / Facebook доторх хөтөч онлайн холболтыг хаадаг.", 15, "rgb(240,170,90)", 1, 1);
        mnText(W / 2, 462, "Баруун дээд буланг (⋯) дараад «Хөтчөөр нээх» (Safari / Chrome) сонгоно уу.", 15, "rgb(240,170,90)", 1, 1);
    }
    if (o.status) {                                          // урт мэдэгдлийг хэд хэдэн мөр болгож төвд харуулна
        let ln = "", y = 494;
        const col = o.failed ? "rgb(240,130,130)" : GOLD, words = o.status.split(" ");
        for (const w of words) {
            const t = ln ? ln + " " + w : w;
            if (ln && textWidthB(t, 16, 1) > 740) { mnText(W / 2, y, ln, 16, col, 1, 1); y += 22; ln = w; } else ln = t;
        }
        if (ln) mnText(W / 2, y, ln, 16, col, 1, 1);
    }
    if (host && o.ready) {
        if (n >= 2) button(W / 2 - 130, 540, 260, 42, "ЭХЛЭХ", 18, GOLD, KEY, GOLD, startOnline);
        else mnText(W / 2, 552, "Найзаа кодоор нь оруулаад дор хаяж 2 тоглогч болоорой", 15, SUB, 0, 1);
    } else if (!host && !o.failed) mnText(W / 2, 552, "Хост тоглоомыг эхлүүлэхийг хүлээж байна...", 15, SUB, 0, 1);
    button(70, 574, 170, 34, "Гарах (ESC)", 15, TXT, BOX, GDK, exitOnline, 0);
}

function draw() {
    hits = []; tokHit = [];
    document.body.style.background = state === ST_INTRO ? "rgb(14,20,52)" : MN_PARCH;
    if (state === ST_INTRO) { if (online) drawLobby(); else drawIntro(); return; }
    drawBoard();
    drawTokens();
    drawPanel();
    if (state === ST_QUIZ || state === ST_QRES) drawQuiz();
    if (state === ST_QRES) hits.push({ x1: 0, y1: 0, x2: W, y2: H, fn: continueQuiz });
    if (state === ST_OVER) drawOver();
}

/* ====================== Дэлгэцийн хэмжээ, зурах давталт ====================== */
let dirty = true, vScale = 1;
function redraw() { dirty = true; if (online && online.role === "host") scheduleBroadcast(); }
function resize() {
    const s = Math.min(innerWidth / W, innerHeight / H);
    const dpr = window.devicePixelRatio || 1;
    vScale = s;
    canvas.style.width = Math.floor(W * s) + "px";
    canvas.style.height = Math.floor(H * s) + "px";
    canvas.width = Math.round(W * s * dpr);
    canvas.height = Math.round(H * s * dpr);
    ctx.setTransform(canvas.width / W, 0, 0, canvas.height / H, 0, 0);
    dirty = true;
}
function frame() {
    if (dirty) { dirty = false; draw(); }
    requestAnimationFrame(frame);
}

/* ====================== Оролт ====================== */
function toLogical(e) {
    const r = canvas.getBoundingClientRect();
    return [(e.clientX - r.left) / r.width * W, (e.clientY - r.top) / r.height * H];
}
function hitAt(x, y) {
    for (let i = hits.length - 1; i >= 0; i--) {
        const h = hits[i];
        if (x >= h.x1 && x < h.x2 && y >= h.y1 && y < h.y2) return h;
    }
    return null;
}
canvas.addEventListener("pointerdown", e => {
    const [x, y] = toLogical(e);
    const h = hitAt(x, y);
    if (h) { e.preventDefault(); h.fn(); return; }
    if (state === ST_CHOOSE && myTurn()) {          // самбар дээрх хүүг шууд дарах
        for (const t of tokHit) {
            if (t.p === cur && movTok.includes(t.k) && Math.hypot(x - t.x, y - t.y) <= t.r) { humanChoose(t.k); return; }
        }
    }
});
canvas.addEventListener("pointermove", e => {
    const [x, y] = toLogical(e);
    canvas.style.cursor = hitAt(x, y) ? "pointer" : "default";
});

window.addEventListener("keydown", e => {
    const key = e.key;
    if (key === "Escape") {
        if (online) { if (online.role === "host" && online.started) backToIntro(); else exitOnline(); }
        else if (state !== ST_INTRO) backToIntro();
        return;
    }
    if (state === ST_INTRO) {
        if (online) return;
        if (key >= "1" && key <= "4") { gameMode = +key - 1; redraw(); }
        if (key === " " || key === "Enter") { e.preventDefault(); startGame(); }
        return;
    }
    if (state === ST_ROLL && (key === "Enter" || key === " ")) { e.preventDefault(); humanRoll(); }
    else if (state === ST_CHOOSE && key >= "1" && key <= "4") humanChoose(+key - 1);
    else if (state === ST_QUIZ && key >= "1" && key <= "3") humanAnswer(+key - 1);
    else if (state === ST_QRES) { e.preventDefault(); continueQuiz(); }
    else if (state === ST_OVER && (key === "Enter" || key === " ") && !isGuest()) { e.preventDefault(); backToIntro(); }
});

window.addEventListener("resize", resize);
resetPositions();
buildPools();
resize();
requestAnimationFrame(frame);
// ?room=КОД холбоосоор орвол шууд өрөөнд орно
try { const qr = new URLSearchParams(location.search).get("room"); if (qr) joinRoom(qr); } catch (e) {}
