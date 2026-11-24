/* =========================================================
   HONE - Main Application Script (app.js)
   ========================================================= */
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import {
  getAuth,
  onAuthStateChanged,
  signInWithEmailAndPassword,
  createUserWithEmailAndPassword,
  signOut,
  updateProfile
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js";
import {
  getFirestore,
  doc,
  getDoc,
  setDoc,
  onSnapshot,
  serverTimestamp
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";

/* =========================================================
   定数・設定
   ========================================================= */
const STORAGE_KEYS = {
  STATE: "hone_state_v1",
  PREFS: "hone_prefs_v1",
  CACHE_WORDS: "hone_words_cache_v1",
  CACHE_EXAMPLES: "hone_examples_cache_v1"
};

const DEFAULT_PREFS = {
  theme: "light-mist",
  font: "sans",
  size: "md",
  hidePosOnRed: false
};

const DEFAULT_STATE = {
  nickname: "",
  friendCode: "",
  levels: {}, // { [no]: 0 | 1 | 2 | 3 }
  studiedIdsToday: [],
  studiedDate: "",
  streakDays: 0,
  lastStudyDate: "",
  friends: [], // [{ uid, nickname, friendCode }]
  updatedAt: 0
};

const LEVEL_FILTERS = [
  { level: "all", label: "すべて" },
  { level: "0", label: "未学習" },
  { level: "1", label: "苦手" },
  { level: "2", label: "あやしい" },
  { level: "3", label: "習得済み" }
];

const PART_RANGES = [
  { label: "Part 1 (1-400)", start: 1, end: 400 },
  { label: "Part 2 (401-1000)", start: 401, end: 1000 },
  { label: "Part 3 (1001-1400)", start: 1001, end: 1400 },
  { label: "Part 4 (1401-1900)", start: 1401, end: 1900 },
  { label: "熟語・イディオム (1901-)", start: 1901, end: 99999 }
];

/* =========================================================
   Firebase 初期化（firebase-config.js がある場合は利用）
   ========================================================= */
let auth = null;
let db = null;
let firebaseReady = false;

async function initFirebaseIfAvailable() {
  try {
    const cfgModule = await import("./firebase-config.js");
    const firebaseConfig = cfgModule.firebaseConfig || cfgModule.default;
    if (!firebaseConfig || !firebaseConfig.apiKey) return false;
    const app = initializeApp(firebaseConfig);
    auth = getAuth(app);
    db = getFirestore(app);
    firebaseReady = true;
    return true;
  } catch (err) {
    console.warn("Firebase config not loaded or offline:", err);
    return false;
  }
}

/* =========================================================
   アプリ状態
   ========================================================= */
let wordsData = [];
let examplesMap = new Map();
let state = structuredClone(DEFAULT_STATE);
let prefs = structuredClone(DEFAULT_PREFS);
let currentUser = null;
let cloudUnsubscribe = null;
let syncTimer = null;

// 単語帳フィルタ・赤シート・聞き流し状態
let vocabRangeStart = 1;
let vocabRangeEnd = 200;
let vocabLevelFilter = "all";
let redMode = "none"; // "none" | "en" | "ja"
let listenState = {
  active: false,
  playing: false,
  hideEn: false,
  index: 0,
  queue: [],
  rate: 1.0,
  intervalSec: 1.4,
  timerId: null
};

// フラッシュカード・小テスト状態
let fcQueue = [];
let fcIndex = 0;
let fcFlipped = false;

let quizItems = [];
let quizIndex = 0;
let quizRevealed = false;
let quizResults = {}; // { [no]: { correct: boolean, manualLevel?: number } }

// 対戦状態
let currentBattleCode = "";
let battleState = {
  mode: "create",
  roomCode: "",
  role: "",
  questions: [],
  currentQ: 0,
  scores: {},
  answered: false,
  finished: false
};

/* =========================================================
   DOM ヘルパー
   ========================================================= */
const $ = (sel) => document.querySelector(sel);
const $$ = (sel) => Array.from(document.querySelectorAll(sel));

function todayKey() {
  const d = new Date();
  const y = d.getFullYear();
  const m = String(d.getMonth() + 1).padStart(2, "0");
  const day = String(d.getDate()).padStart(2, "0");
  return `${y}-${m}-${day}`;
}

function yesterdayKey() {
  const d = new Date(Date.now() - 86400000);
  const y = d.getFullYear();
  const m = String(d.getMonth() + 1).padStart(2, "0");
  const day = String(d.getDate()).padStart(2, "0");
  return `${y}-${m}-${day}`;
}

function showToast(msg) {
  const el = $("#toast");
  if (!el) return;
  el.textContent = msg;
  el.classList.remove("hidden");
  clearTimeout(showToast._t);
  showToast._t = setTimeout(() => el.classList.add("hidden"), 2200);
}

/* =========================================================
   ローカル永続化・設定適用
   ========================================================= */
function loadLocalPrefs() {
  try {
    const raw = localStorage.getItem(STORAGE_KEYS.PREFS);
    if (raw) prefs = { ...DEFAULT_PREFS, ...JSON.parse(raw) };
  } catch (_) {}
  applyPrefs();
}

function saveLocalPrefs() {
  try {
    localStorage.setItem(STORAGE_KEYS.PREFS, JSON.stringify(prefs));
  } catch (_) {}
}

function applyPrefs() {
  document.documentElement.setAttribute("data-theme", prefs.theme || "light-mist");
  document.body.setAttribute("data-font", prefs.font || "sans");
  document.body.setAttribute("data-size", prefs.size || "md");
  updateRedSheetClasses();
}

function loadLocalState() {
  try {
    const raw = localStorage.getItem(STORAGE_KEYS.STATE);
    if (raw) {
      state = { ...DEFAULT_STATE, ...JSON.parse(raw) };
    }
  } catch (_) {}
  normalizeDailyState();
  if (!state.friendCode) {
    state.friendCode = generateFriendCode();
  }
}

function saveLocalState(markUpdated = true) {
  if (markUpdated) state.updatedAt = Date.now();
  try {
    localStorage.setItem(STORAGE_KEYS.STATE, JSON.stringify(state));
  } catch (_) {}
  if (markUpdated && firebaseReady && currentUser) {
    scheduleCloudSync();
  }
}

function normalizeDailyState() {
  const today = todayKey();
  if (state.studiedDate !== today) {
    state.studiedDate = today;
    state.studiedIdsToday = [];
  }
  if (state.lastStudyDate && state.lastStudyDate !== today && state.lastStudyDate !== yesterdayKey()) {
    state.streakDays = 0;
  }
}

function recordStudiedWord(no) {
  normalizeDailyState();
  const key = String(no);
  if (!Array.isArray(state.studiedIdsToday)) state.studiedIdsToday = [];
  if (!state.studiedIdsToday.includes(key)) {
    state.studiedIdsToday.push(key);
    const today = todayKey();
    if (state.lastStudyDate !== today) {
      state.streakDays = state.lastStudyDate === yesterdayKey() ? (state.streakDays || 0) + 1 : 1;
      state.lastStudyDate = today;
    }
  }
}

function generateFriendCode() {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let out = "";
  for (let i = 0; i < 6; i++) {
    out += chars[Math.floor(Math.random() * chars.length)];
  }
  return out;
}

/* =========================================================
   CSV 読み込み＆パース
   ========================================================= */
function parseCsvLine(line) {
  const cols = [];
  let cur = "";
  let inQuotes = false;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === '"') {
      if (inQuotes && line[i + 1] === '"') {
        cur += '"';
        i++;
      } else {
        inQuotes = !inQuotes;
      }
    } else if (ch === "," && !inQuotes) {
      cols.push(cur.trim());
      cur = "";
    } else {
      cur += ch;
    }
  }
  cols.push(cur.trim());
  return cols;
}

function parseCsvText(text) {
  const lines = text
    .replace(/\r\n/g, "\n")
    .replace(/\r/g, "\n")
    .split("\n")
    .filter((l) => l.trim().length > 0);
  if (lines.length < 2) return [];
  const headers = parseCsvLine(lines[0]).map((h) => h.replace(/^\uFEFF/, "").trim());
  return lines.slice(1).map((line) => {
    const values = parseCsvLine(line);
    const row = {};
    headers.forEach((h, idx) => {
      row[h] = values[idx] ?? "";
    });
    return row;
  });
}

async function loadVocabularyData() {
  try {
    const [wRes, eRes] = await Promise.all([
      fetch("./data/words.csv", { cache: "no-store" }),
      fetch("./data/examples.csv", { cache: "no-store" })
    ]);
    if (!wRes.ok) throw new Error("words.csv fetch failed");
    const wText = await wRes.text();
    localStorage.setItem(STORAGE_KEYS.CACHE_WORDS, wText);

    if (eRes.ok) {
      const eText = await eRes.text();
      localStorage.setItem(STORAGE_KEYS.CACHE_EXAMPLES, eText);
      buildExamplesMap(parseCsvText(eText));
    }
    wordsData = normalizeWords(parseCsvText(wText));
  } catch (_) {
    const cachedW = localStorage.getItem(STORAGE_KEYS.CACHE_WORDS);
    const cachedE = localStorage.getItem(STORAGE_KEYS.CACHE_EXAMPLES);
    if (cachedE) buildExamplesMap(parseCsvText(cachedE));
    if (cachedW) {
      wordsData = normalizeWords(parseCsvText(cachedW));
    } else {
      wordsData = [
        { no: 1, word: "abandon", pos: "他", meanings: ["〜を捨てる", "〜を断念する"], phonetic: "/əˈbændən/", note: "" },
        { no: 2, word: "ability", pos: "名", meanings: ["能力", "才能"], phonetic: "/əˈbɪləti/", note: "" }
      ];
    }
  }

  if (wordsData.length > 0) {
    const maxNo = wordsData[wordsData.length - 1].no;
    vocabRangeStart = wordsData[0].no;
    vocabRangeEnd = Math.min(maxNo, vocabRangeStart + 199);
  }
}

function buildExamplesMap(rows) {
  examplesMap.clear();
  rows.forEach((r) => {
    const no = Number(r.no || r.id || 0);
    if (!no) return;
    examplesMap.set(no, {
      en: r.example_en || r.en || r.example || "",
      ja: r.example_ja || r.ja || r.translation || ""
    });
  });
}

function normalizeWords(rows) {
  return rows
    .map((r, idx) => {
      const no = Number(r.no || r.id || idx + 1);
      const rawMeaning = r.meanings || r.meaning || r.jp || "";
      const meanings = String(rawMeaning)
        .split(/[／/|;；\n]+/)
        .map((s) => s.trim())
        .filter(Boolean);
      return {
        no,
        word: (r.word || r.en || "").trim(),
        pos: (r.pos || r.part_of_speech || "").trim(),
        meanings: meanings.length ? meanings : [rawMeaning.trim() || "—"],
        phonetic: (r.phonetic || r.ipa || "").trim(),
        note: (r.note || r.memo || "").trim()
      };
    })
    .filter((w) => w.word)
    .sort((a, b) => a.no - b.no);
}

/* =========================================================
   Firebase 認証＆同期
   ========================================================= */
function updateSyncUi() {
  const dot = $("#syncDot");
  const label = $("#syncStatusText");
  if (!dot || !label) return;
  if (firebaseReady && currentUser) {
    dot.classList.add("online");
    label.textContent = `クラウド同期中（${state.nickname || currentUser.email || "ログイン済み"}）`;
  } else {
    dot.classList.remove("online");
    label.textContent = "ローカル保存モード（オフライン／未ログイン）";
  }
}

function scheduleCloudSync() {
  if (!firebaseReady || !currentUser) return;
  clearTimeout(syncTimer);
  syncTimer = setTimeout(async () => {
    try {
      const ref = doc(db, "users", currentUser.uid);
      await setDoc(
        ref,
        {
          nickname: state.nickname || "",
          friendCode: state.friendCode || "",
          levels: state.levels || {},
          studiedIdsToday: state.studiedIdsToday || [],
          studiedDate: state.studiedDate || todayKey(),
          streakDays: state.streakDays || 0,
          lastStudyDate: state.lastStudyDate || "",
          friends: state.friends || [],
          updatedAt: state.updatedAt || Date.now(),
          serverUpdatedAt: serverTimestamp()
        },
        { merge: true }
      );
    } catch (err) {
      console.warn("Cloud sync error:", err);
    }
  }, 500);
}

function subscribeUserDoc(uid) {
  if (cloudUnsubscribe) {
    cloudUnsubscribe();
    cloudUnsubscribe = null;
  }
  if (!firebaseReady || !db || !uid) return;
  const ref = doc(db, "users", uid);
  cloudUnsubscribe = onSnapshot(ref, (snap) => {
    if (!snap.exists()) return;
    const remote = snap.data();
    const remoteTs = Number(remote.updatedAt || 0);
    const localTs = Number(state.updatedAt || 0);
    if (remoteTs > localTs) {
      state = {
        ...DEFAULT_STATE,
        ...state,
        nickname: remote.nickname ?? state.nickname,
        friendCode: remote.friendCode || state.friendCode,
        levels: { ...(state.levels || {}), ...(remote.levels || {}) },
        studiedIdsToday: remote.studiedIdsToday || state.studiedIdsToday,
        studiedDate: remote.studiedDate || state.studiedDate,
        streakDays: remote.streakDays ?? state.streakDays,
        lastStudyDate: remote.lastStudyDate || state.lastStudyDate,
        friends: remote.friends || state.friends,
        updatedAt: remoteTs
      };
      normalizeDailyState();
      saveLocalState(false);
      renderAll();
    }
  });
}

function setupAuthListeners() {
  if (!firebaseReady || !auth) return;
  onAuthStateChanged(auth, async (user) => {
    currentUser = user;
    if (user) {
      if (!state.nickname && user.displayName) {
        state.nickname = user.displayName;
      }
      try {
        const ref = doc(db, "users", user.uid);
        const snap = await getDoc(ref);
        if (snap.exists()) {
          const remote = snap.data();
          if (Number(remote.updatedAt || 0) >= Number(state.updatedAt || 0)) {
            state = {
              ...DEFAULT_STATE,
              ...state,
              nickname: remote.nickname || state.nickname || user.displayName || "",
              friendCode: remote.friendCode || state.friendCode || generateFriendCode(),
              levels: remote.levels || state.levels || {},
              studiedIdsToday: remote.studiedIdsToday || [],
              studiedDate: remote.studiedDate || todayKey(),
              streakDays: remote.streakDays || 0,
              lastStudyDate: remote.lastStudyDate || "",
              friends: remote.friends || [],
              updatedAt: Number(remote.updatedAt || Date.now())
            };
            normalizeDailyState();
            saveLocalState(false);
          } else {
            scheduleCloudSync();
          }
        } else {
          scheduleCloudSync();
        }
      } catch (_) {}
      subscribeUserDoc(user.uid);
      hideAuthGate();
      renderAll();
    } else {
      if (cloudUnsubscribe) {
        cloudUnsubscribe();
        cloudUnsubscribe = null;
      }
    }
    updateSyncUi();
  });
}

function hideAuthGate() {
  const gate = $("#authGate");
  if (gate) gate.classList.add("hidden");
}

/* =========================================================
   画面切り替え＆ヘッダー
   ========================================================= */
function switchView(viewName) {
  $$(".view").forEach((v) => v.classList.remove("active"));
  const target = $(`#view-${viewName}`);
  if (target) target.classList.add("active");

  $$(".nav-tab").forEach((btn) => {
    btn.classList.toggle("active", btn.dataset.view === viewName);
  });

  const redBar = $("#floatingRedBar");
  if (redBar) {
    redBar.classList.toggle("hidden", viewName !== "vocab");
  }

  const backBtn = $("#headerBackBtn");
  if (backBtn) {
    backBtn.classList.toggle("is-hidden", viewName === "home");
  }

  if (viewName === "vocab") {
    renderVocabView();
  } else if (viewName === "progress") {
    renderProgressView();
  } else if (viewName === "home") {
    renderHomeView();
  } else if (viewName === "social") {
    renderSocialView();
  } else if (viewName === "settings") {
    renderSettingsView();
  }
}

/* =========================================================
   ホーム＆進捗描画
   ========================================================= */
function computeStats(list = wordsData) {
  const total = list.length;
  let lv0 = 0, lv1 = 0, lv2 = 0, lv3 = 0;
  list.forEach((w) => {
    const lv = Number(state.levels?.[w.no] || 0);
    if (lv === 3) lv3++;
    else if (lv === 2) lv2++;
    else if (lv === 1) lv1++;
    else lv0++;
  });
  const pct = total > 0 ? Math.round((lv3 / total) * 100) : 0;
  return { total, lv0, lv1, lv2, lv3, pct };
}

function updateDonut(prefix, stats) {
  const total = Math.max(1, stats.total);
  const r = 54;
  const c = 2 * Math.PI * r;

  const seg3 = c * (stats.lv3 / total);
  const seg2 = c * (stats.lv2 / total);
  const seg1 = c * (stats.lv1 / total);

  const el3 = $(`#${prefix}DonutLv3`);
  const el2 = $(`#${prefix}DonutLv2`);
  const el1 = $(`#${prefix}DonutLv1`);

  if (el3) {
    el3.setAttribute("stroke-dasharray", `${seg3} ${c}`);
    el3.setAttribute("stroke-dashoffset", "0");
  }
  if (el2) {
    el2.setAttribute("stroke-dasharray", `${seg2} ${c}`);
    el2.setAttribute("stroke-dashoffset", `${-seg3}`);
  }
  if (el1) {
    el1.setAttribute("stroke-dasharray", `${seg1} ${c}`);
    el1.setAttribute("stroke-dashoffset", `${-(seg3 + seg2)}`);
  }

  const pctEl = $(`#${prefix}Pct`);
  if (pctEl) pctEl.textContent = `${stats.pct}%`;

  const c3 = $(`#${prefix}CountLv3`);
  const c2 = $(`#${prefix}CountLv2`);
  const c1 = $(`#${prefix}CountLv1`);
  const c0 = $(`#${prefix}CountLv0`);
  if (c3) c3.textContent = stats.lv3;
  if (c2) c2.textContent = stats.lv2;
  if (c1) c1.textContent = stats.lv1;
  if (c0) c0.textContent = stats.lv0;
}

function renderHomeView() {
  normalizeDailyState();
  const stats = computeStats(wordsData);
  updateDonut("home", stats);
  const todayEl = $("#homeTodayCount");
  const streakEl = $("#homeStreakCount");
  if (todayEl) todayEl.textContent = `${(state.studiedIdsToday || []).length} 語`;
  if (streakEl) streakEl.textContent = `${state.streakDays || 0} 日`;
}

function renderProgressView() {
  normalizeDailyState();
  const stats = computeStats(wordsData);
  updateDonut("prog", stats);

  const todayEl = $("#progTodayCount");
  const streakEl = $("#progStreakCount");
  if (todayEl) todayEl.textContent = `${(state.studiedIdsToday || []).length} 語`;
  if (streakEl) streakEl.textContent = `${state.streakDays || 0} 日`;

  const container = $("#unitBarsContainer");
  if (!container) return;

  container.innerHTML = PART_RANGES.map((part) => {
    const sub = wordsData.filter((w) => w.no >= part.start && w.no <= part.end);
    if (!sub.length) return "";
    const s = computeStats(sub);
    const total = Math.max(1, s.total);
    const w3 = (s.lv3 / total) * 100;
    const w2 = (s.lv2 / total) * 100;
    const w1 = (s.lv1 / total) * 100;
    const w0 = Math.max(0, 100 - w3 - w2 - w1);
    return `
      <div class="unit-bar-item">
        <div class="unit-bar-head">
          <span>${part.label}</span>
          <span>習得済み ${s.pct}% (${s.lv3}/${s.total})</span>
        </div>
        <div class="unit-bar-track">
          <div class="unit-bar-seg lv-3" style="width:${w3}%"></div>
          <div class="unit-bar-seg lv-2" style="width:${w2}%"></div>
          <div class="unit-bar-seg lv-1" style="width:${w1}%"></div>
          <div class="unit-bar-seg lv-0" style="width:${w0}%"></div>
        </div>
      </div>
    `;
  }).join("");
}

/* =========================================================
   単語帳（文字なし横一列カラーチップ・番号右に品詞・赤シート・聞き流し）
   ========================================================= */
function renderLevelFilterChips() {
  const wrap = $("#vocabLevelFilter");
  if (!wrap) return;
  wrap.innerHTML = LEVEL_FILTERS.map((item) => {
    const active = String(vocabLevelFilter) === item.level ? " active" : "";
    return `
      <button
        type="button"
        class="level-chip${active}"
        data-level="${item.level}"
        aria-label="${item.label}"
        title="${item.label}"
      ></button>
    `;
  }).join("");

  $$("#vocabLevelFilter .level-chip").forEach((btn) => {
    btn.addEventListener("click", () => {
      vocabLevelFilter = btn.dataset.level;
      renderLevelFilterChips();
      renderVocabList();
    });
  });
}

function getFilteredVocab() {
  const start = Math.min(vocabRangeStart, vocabRangeEnd);
  const end = Math.max(vocabRangeStart, vocabRangeEnd);
  return wordsData.filter((w) => {
    if (w.no < start || w.no > end) return false;
    if (vocabLevelFilter === "all") return true;
    return Number(state.levels?.[w.no] || 0) === Number(vocabLevelFilter);
  });
}

function renderVocabView() {
  const startInp = $("#vocabRangeStart");
  const endInp = $("#vocabRangeEnd");
  const countPill = $("#vocabRangeCount");
  if (startInp) startInp.value = vocabRangeStart;
  if (endInp) endInp.value = vocabRangeEnd;

  const list = getFilteredVocab();
  if (countPill) countPill.textContent = `${list.length}語`;

  renderLevelFilterChips();
  renderVocabList(list);
  updateRedSheetClasses();
}

function renderVocabList(list = getFilteredVocab()) {
  const container = $("#vocabList");
  if (!container) return;

  if (!list.length) {
    container.innerHTML = `<div class="glass-card"><p class="sub-label">該当する単語がありません。</p></div>`;
    return;
  }

  container.innerHTML = list.map((w) => {
    const lv = Number(state.levels?.[w.no] || 0);
    const ex = examplesMap.get(w.no) || { en: "", ja: "" };
    const meaningsHtml = w.meanings
      .map((m, idx) => `<span class="vocab-meaning-line">${w.meanings.length > 1 ? `①②③④⑤`[idx] || "" : ""}${escapeHtml(m)}</span>`)
      .join("");

    return `
      <article class="vocab-item" data-no="${w.no}">
        <div class="vocab-row">
          <button type="button" class="vocab-dot-btn" data-cycle-no="${w.no}" aria-label="習熟度を変更">
            <span class="dot lv-${lv}"></span>
          </button>
          <div class="vocab-left">
            <div class="vocab-no-row">
              <span class="vocab-no">No.${w.no}</span>
              ${w.pos ? `<span class="pos-badge vocab-pos-above">${escapeHtml(w.pos)}</span>` : ""}
            </div>
            <span class="vocab-word">${escapeHtml(w.word)}</span>
          </div>
          <div class="vocab-right">
            <div class="vocab-meanings-stack">${meaningsHtml}</div>
          </div>
          <button type="button" class="vocab-detail-btn" data-toggle-no="${w.no}" aria-label="詳細を開く">
            <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2">
              <polyline points="6 9 12 15 18 9"></polyline>
            </svg>
          </button>
        </div>
        <div class="vocab-accordion">
          <div class="acc-top">
            <div class="acc-meta">
              ${w.phonetic ? `<span>${escapeHtml(w.phonetic)}</span>` : ""}
              <span>Lv.${lv}</span>
            </div>
            <button type="button" class="audio-pill" data-speak-word="${escapeHtml(w.word)}">発音</button>
          </div>
          ${ex.en ? `
            <div class="acc-block">
              <span class="acc-label">例文</span>
              <p class="acc-text">${escapeHtml(ex.en)}</p>
              ${ex.ja ? `<p class="acc-text sub-label">${escapeHtml(ex.ja)}</p>` : ""}
            </div>
          ` : ""}
          ${w.note ? `
            <div class="acc-block">
              <span class="acc-label">メモ</span>
              <p class="acc-text">${escapeHtml(w.note)}</p>
            </div>
          ` : ""}
        </div>
      </article>
    `;
  }).join("");

  $$(".vocab-dot-btn").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const no = Number(btn.dataset.cycleNo);
      const cur = Number(state.levels?.[no] || 0);
      const next = cur >= 3 ? 1 : cur + 1;
      setWordLevel(no, next);
      renderVocabList();
    });
  });

  $$(".vocab-detail-btn").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const no = btn.dataset.toggleNo;
      const card = container.querySelector(`.vocab-item[data-no="${no}"]`);
      if (card) card.classList.toggle("open");
    });
  });

  $$(".audio-pill").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      speakEnglish(btn.dataset.speakWord || "");
    });
  });

  container.querySelectorAll(".vocab-word, .vocab-meaning-line, .pos-badge").forEach((el) => {
    el.addEventListener("click", () => {
      if (redMode !== "none") {
        el.classList.toggle("revealed");
      }
    });
  });
}

function setWordLevel(no, lv) {
  state.levels[String(no)] = Number(lv);
  recordStudiedWord(no);
  saveLocalState(true);
}

function updateRedSheetClasses() {
  const listEl = $("#vocabList");
  if (!listEl) return;
  listEl.classList.remove("red-en", "red-ja", "hide-pos-on-red");
  listEl.querySelectorAll(".revealed").forEach((el) => el.classList.remove("revealed"));

  if (redMode === "en") {
    listEl.classList.add("red-en");
  } else if (redMode === "ja") {
    listEl.classList.add("red-ja");
  }
  if (prefs.hidePosOnRed && redMode !== "none") {
    listEl.classList.add("hide-pos-on-red");
  }

  const enBtn = $("#redEnBtn");
  const jaBtn = $("#redJaBtn");
  if (enBtn) enBtn.classList.toggle("active", redMode === "en");
  if (jaBtn) jaBtn.classList.toggle("active", redMode === "ja");
}

function escapeHtml(str) {
  return String(str ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

/* =========================================================
   音声読み上げ＆聞き流しモード
   ========================================================= */
function speakEnglish(text, rate = 1.0) {
  if (!text || !("speechSynthesis" in window)) return;
  try {
    window.speechSynthesis.cancel();
    const utt = new SpeechSynthesisUtterance(text);
    utt.lang = "en-US";
    utt.rate = rate;
    window.speechSynthesis.speak(utt);
  } catch (_) {}
}

function openListenMode(queue) {
  if (!queue || !queue.length) {
    showToast("対象となる単語がありません");
    return;
  }
  listenState.active = true;
  listenState.queue = queue;
  listenState.index = 0;
  listenState.playing = true;
  listenState.hideEn = false;
  listenState.rate = Number($("#vocabListenRate")?.value || 1.0);
  listenState.intervalSec = Number($("#vocabListenInterval")?.value || 1.4);

  const overlay = $("#listenOverlay");
  if (overlay) overlay.classList.remove("hidden");
  renderListenCard();
  scheduleListenNext();
}

function closeListenMode() {
  listenState.active = false;
  listenState.playing = false;
  clearTimeout(listenState.timerId);
  if ("speechSynthesis" in window) {
    try { window.speechSynthesis.cancel(); } catch (_) {}
  }
  const overlay = $("#listenOverlay");
  if (overlay) overlay.classList.add("hidden");
}

function renderListenCard() {
  const item = listenState.queue[listenState.index];
  if (!item) return;
  const counter = $("#listenCounter");
  const jaEl = $("#listenJa");
  const enWrap = $("#listenEnWrap");
  const enEl = $("#listenEn");
  const phEl = $("#listenPhonetic");
  const exEl = $("#listenExample");
  const playBtn = $("#listenPlayPauseBtn");
  const hideBtn = $("#listenHideEnBtn");

  if (counter) counter.textContent = `${listenState.index + 1} / ${listenState.queue.length}`;
  if (jaEl) jaEl.textContent = item.meanings.join(" / ");
  if (enEl) enEl.textContent = item.word;
  if (phEl) phEl.textContent = item.phonetic || "";
  if (enWrap) enWrap.style.opacity = listenState.hideEn ? "0" : "1";

  const ex = examplesMap.get(item.no);
  if (exEl) {
    exEl.textContent = ex?.en ? `${ex.en}${ex.ja ? ` — ${ex.ja}` : ""}` : "";
    exEl.classList.toggle("hidden", !ex?.en);
  }

  if (playBtn) playBtn.textContent = listenState.playing ? "一時停止" : "再生";
  if (hideBtn) hideBtn.textContent = listenState.hideEn ? "英単語を表示" : "英単語を隠す";

  $$("#listenOverlay .rate-btn").forEach((b) => {
    const lv = Number(b.dataset.rateLv);
    b.classList.toggle("selected", Number(state.levels?.[item.no] || 0) === lv);
  });

  if (listenState.playing) {
    speakEnglish(item.word, listenState.rate);
  }
}

function scheduleListenNext() {
  clearTimeout(listenState.timerId);
  if (!listenState.active || !listenState.playing) return;
  listenState.timerId = setTimeout(() => {
    if (!listenState.active || !listenState.playing) return;
    if (listenState.index + 1 < listenState.queue.length) {
      listenState.index++;
      renderListenCard();
      scheduleListenNext();
    } else {
      listenState.playing = false;
      renderListenCard();
      showToast("聞き流しが完了しました");
    }
  }, Math.max(600, listenState.intervalSec * 1000));
}

/* =========================================================
   学習（フラッシュカード・小テスト）
   ========================================================= */
function buildStudyQueue(startVal, endVal, modeVal) {
  const s = Math.min(startVal, endVal);
  const e = Math.max(startVal, endVal);
  let list = wordsData.filter((w) => w.no >= s && w.no <= e);
  if (modeVal === "weak") {
    list = list.filter((w) => Number(state.levels?.[w.no] || 0) === 1);
  } else if (modeVal === "unlearned") {
    list = list.filter((w) => Number(state.levels?.[w.no] || 0) === 0);
  }
  return list;
}

function startFlashcards() {
  const s = Number($("#fcRangeStart")?.value || 1);
  const e = Number($("#fcRangeEnd")?.value || 50);
  const mode = $("#fcFilterMode")?.value || "all";
  fcQueue = buildStudyQueue(s, e, mode);
  if (!fcQueue.length) {
    showToast("対象の単語がありません");
    return;
  }
  fcIndex = 0;
  fcFlipped = false;
  $("#studySetup")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#flashcardStage")?.classList.remove("hidden");
  renderFlashcard();
}

function renderFlashcard() {
  const item = fcQueue[fcIndex];
  if (!item) return;
  const dir = $("#fcDirection")?.value || "en-ja";
  const frontEl = $("#fcFront");
  const backEl = $("#fcBack");
  const counterEl = $("#fcCounter");
  const progEl = $("#fcProgress");

  if (counterEl) counterEl.textContent = `${fcIndex + 1} / ${fcQueue.length}`;
  if (progEl) progEl.style.width = `${((fcIndex + 1) / fcQueue.length) * 100}%`;

  const ex = examplesMap.get(item.no);
  const lv = Number(state.levels?.[item.no] || 0);

  if (frontEl) {
    const frontText = dir === "en-ja" ? item.word : item.meanings.join(" / ");
    frontEl.innerHTML = `
      <div class="fc-side">
        <div class="fc-top-bar">
          <span class="fc-no">No.${item.no}</span>
          ${item.pos ? `<span class="pos-badge">${escapeHtml(item.pos)}</span>` : ""}
        </div>
        <div class="fc-word ${dir === "ja-en" ? "is-ja" : ""}">${escapeHtml(frontText)}</div>
        <p class="fc-hint">タップして解答を表示</p>
      </div>
    `;
  }

  if (backEl) {
    backEl.innerHTML = `
      <div class="fc-side">
        <div class="fc-top-bar">
          <span class="fc-no">No.${item.no}</span>
          <button type="button" class="audio-pill" id="fcSpeakBtn">発音</button>
        </div>
        <div class="fc-back-head">
          <span class="fc-word-sm">${escapeHtml(item.word)}</span>
          ${item.phonetic ? `<span class="sub-label">${escapeHtml(item.phonetic)}</span>` : ""}
          ${item.pos ? `<span class="pos-badge">${escapeHtml(item.pos)}</span>` : ""}
        </div>
        <div class="fc-meaning-row">
          <span class="fc-meaning">${escapeHtml(item.meanings.join(" / "))}</span>
        </div>
        ${ex?.en ? `<p class="fc-example">${escapeHtml(ex.en)}${ex.ja ? `<br>${escapeHtml(ex.ja)}` : ""}</p>` : ""}
        ${item.note ? `<p class="fc-note">${escapeHtml(item.note)}</p>` : ""}
        <p class="fc-hint">タップして表面に戻る</p>
      </div>
    `;
    $("#fcSpeakBtn")?.addEventListener("click", (e) => {
      e.stopPropagation();
      speakEnglish(item.word);
    });
  }

  frontEl?.classList.toggle("hidden", fcFlipped);
  backEl?.classList.toggle("hidden", !fcFlipped);

  $$("#flashcardStage .rate-btn").forEach((b) => {
    b.classList.toggle("selected", Number(b.dataset.fcRate) === lv);
  });
}

function startQuiz() {
  const s = Number($("#quizRangeStart")?.value || 1);
  const e = Number($("#quizRangeEnd")?.value || 50);
  const mode = $("#quizFilterMode")?.value || "all";
  quizItems = buildStudyQueue(s, e, mode);
  if (!quizItems.length) {
    showToast("対象の単語がありません");
    return;
  }
  quizIndex = 0;
  quizRevealed = false;
  quizResults = {};

  $("#studySetup")?.classList.add("hidden");
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizResult")?.classList.add("hidden");
  $("#quizStage")?.classList.remove("hidden");
  renderQuizQuestion();
}

function renderQuizQuestion() {
  const item = quizItems[quizIndex];
  if (!item) return;
  const dir = $("#quizDirection")?.value || "en-ja";
  const counterEl = $("#quizCounter");
  const progEl = $("#quizProgress");
  const promptEl = $("#quizPrompt");
  const ansBox = $("#quizAnswerBox");
  const revealBtn = $("#quizRevealBtn");
  const nextBtn = $("#quizNextBtn");

  if (counterEl) counterEl.textContent = `${quizIndex + 1} / ${quizItems.length}`;
  if (progEl) progEl.style.width = `${((quizIndex + 1) / quizItems.length) * 100}%`;
  if (promptEl) promptEl.textContent = dir === "en-ja" ? item.word : item.meanings.join(" / ");

  const ansText = dir === "en-ja" ? item.meanings.join(" / ") : `${item.word}（${item.meanings.join(" / ")}）`;
  if (ansBox) {
    ansBox.textContent = ansText;
    ansBox.classList.toggle("hidden", !quizRevealed);
  }
  if (revealBtn) revealBtn.classList.toggle("hidden", quizRevealed);
  if (nextBtn) {
    nextBtn.textContent = quizIndex + 1 >= quizItems.length ? "結果を見る" : "次の問題へ";
  }

  const res = quizResults[item.no];
  $("#quizCorrectBtn")?.classList.toggle("selected", res?.correct === true);
  $("#quizWrongBtn")?.classList.toggle("selected", res?.correct === false);
}

function showQuizResult() {
  $("#quizStage")?.classList.add("hidden");
  $("#quizResult")?.classList.remove("hidden");
  const total = quizItems.length;
  const ok = Object.values(quizResults).filter((r) => r.correct).length;
  const scoreEl = $("#quizResultScore");
  if (scoreEl) scoreEl.textContent = `${ok} / ${total} 問正解`;
}

/* =========================================================
   交流（フレンド・対戦）
   ========================================================= */
function renderSocialView() {
  const nickInp = $("#nicknameInput");
  const codeEl = $("#myFriendCode");
  if (nickInp) nickInp.value = state.nickname || "";
  if (codeEl) codeEl.textContent = state.friendCode || "------";

  const listEl = $("#friendList");
  if (!listEl) return;
  const friends = state.friends || [];
  if (!friends.length) {
    listEl.innerHTML = `<p class="sub-label">まだフレンドは登録されていません。</p>`;
    return;
  }
  listEl.innerHTML = friends.map((f) => `
    <div class="friend-row">
      <div>
        <strong>${escapeHtml(f.nickname || "名前未設定")}</strong>
        <div class="sub-label">コード: ${escapeHtml(f.friendCode || "")}</div>
      </div>
      <button type="button" class="sub-btn" data-remove-friend="${escapeHtml(f.friendCode || "")}">削除</button>
    </div>
  `).join("");

  $$("[data-remove-friend]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const code = btn.dataset.removeFriend;
      state.friends = (state.friends || []).filter((x) => x.friendCode !== code);
      saveLocalState(true);
      renderSocialView();
    });
  });
}

function createBattleRoom() {
  if (wordsData.length < 4) {
    showToast("単語データが不足しています");
    return;
  }
  const code = generateFriendCode();
  const sample = [...wordsData].sort(() => Math.random() - 0.5).slice(0, 5);
  const questions = sample.map((target) => {
    const others = wordsData
      .filter((w) => w.no !== target.no)
      .sort(() => Math.random() - 0.5)
      .slice(0, 3);
    const choices = [target, ...others]
      .sort(() => Math.random() - 0.5)
      .map((c) => ({ no: c.no, text: c.meanings[0] || "—" }));
    return {
      no: target.no,
      word: target.word,
      answerNo: target.no,
      choices
    };
  });

  currentBattleCode = code;
  battleState = {
    mode: "create",
    roomCode: code,
    role: "host",
    questions,
    currentQ: 0,
    scores: { [state.nickname || "自分"]: 0 },
    answered: false,
    finished: false
  };

  $("#battleRoomCodeBox")?.classList.remove("hidden");
  const codeOut = $("#battleRoomCodeText");
  if (codeOut) codeOut.textContent = code;
  renderBattleStage();
}

function renderBattleStage() {
  const stage = $("#battleStage");
  if (!stage) return;
  stage.classList.remove("hidden");

  if (battleState.finished) {
    const entries = Object.entries(battleState.scores);
    stage.innerHTML = `
      <div class="glass-card">
        <h3 class="card-title">対戦結果</h3>
        <div class="battle-players-list">
          ${entries.map(([name, sc]) => `
            <div class="battle-player-row">
              <span>${escapeHtml(name)}</span>
              <strong>${sc} pt</strong>
            </div>
          `).join("")}
        </div>
        <button type="button" class="primary-btn full-w" id="battleRestartBtn">もう一度遊ぶ</button>
      </div>
    `;
    $("#battleRestartBtn")?.addEventListener("click", createBattleRoom);
    return;
  }

  const q = battleState.questions[battleState.currentQ];
  if (!q) return;
  const playerKey = state.nickname || "自分";

  stage.innerHTML = `
    <div class="glass-card">
      <div class="stage-meta">
        <span class="stage-counter">第 ${battleState.currentQ + 1} / ${battleState.questions.length} 問</span>
        <span class="range-pill">${battleState.scores[playerKey] || 0} pt</span>
      </div>
      <div class="quiz-prompt">${escapeHtml(q.word)}</div>
      <div class="battle-choices">
        ${q.choices.map((ch) => `
          <button type="button" class="battle-choice-btn" data-choice-no="${ch.no}">
            ${escapeHtml(ch.text)}
          </button>
        `).join("")}
      </div>
    </div>
  `;

  $$(".battle-choice-btn").forEach((btn) => {
    btn.addEventListener("click", () => {
      if (battleState.answered) return;
      battleState.answered = true;
      const picked = Number(btn.dataset.choiceNo);
      const isCorrect = picked === q.answerNo;
      if (isCorrect) {
        battleState.scores[playerKey] = (battleState.scores[playerKey] || 0) + 10;
        btn.classList.add("is-correct");
      } else {
        btn.classList.add("is-wrong");
      }
      setTimeout(() => {
        battleState.answered = false;
        if (battleState.currentQ + 1 < battleState.questions.length) {
          battleState.currentQ++;
        } else {
          battleState.finished = true;
        }
        renderBattleStage();
      }, 650);
    });
  });
}

/* =========================================================
   設定描画＆イベント登録
   ========================================================= */
function renderSettingsView() {
  $$("[data-theme-option]").forEach((btn) => {
    btn.classList.toggle("active", btn.dataset.themeOption === prefs.theme);
  });
  $$("[data-font-option]").forEach((btn) => {
    btn.classList.toggle("active", btn.dataset.fontOption === prefs.font);
  });
  $$("[data-size-option]").forEach((btn) => {
    btn.classList.toggle("active", btn.dataset.sizeOption === prefs.size);
  });
  const hidePosChk = $("#hidePosOnRedCheckbox");
  if (hidePosChk) hidePosChk.checked = Boolean(prefs.hidePosOnRed);
  updateSyncUi();
}

function bindEvents() {
  // 下部ナビ
  $$(".nav-tab").forEach((btn) => {
    btn.addEventListener("click", () => switchView(btn.dataset.view));
  });

  // ホームのクイックタイル
  $$("[data-jump-view]").forEach((btn) => {
    btn.addEventListener("click", () => switchView(btn.dataset.jumpView));
  });

  // 認証フォーム
  $("#loginBtn")?.addEventListener("click", async () => {
    const email = $("#authEmail")?.value.trim() || "";
    const pass = $("#authPassword")?.value || "";
    const errEl = $("#authError");
    if (!firebaseReady || !auth) {
      if (errEl) errEl.textContent = "Firebase設定が見つからないためローカルモードで続行します。";
      hideAuthGate();
      return;
    }
    try {
      await signInWithEmailAndPassword(auth, email, pass);
      if (errEl) errEl.textContent = "";
    } catch (e) {
      if (errEl) errEl.textContent = e.message || "ログインに失敗しました";
    }
  });

  $("#signupBtn")?.addEventListener("click", async () => {
    const email = $("#authEmail")?.value.trim() || "";
    const pass = $("#authPassword")?.value || "";
    const errEl = $("#authError");
    if (!firebaseReady || !auth) {
      if (errEl) errEl.textContent = "Firebase設定が見つかりません。";
      return;
    }
    try {
      await createUserWithEmailAndPassword(auth, email, pass);
      if (errEl) errEl.textContent = "";
    } catch (e) {
      if (errEl) errEl.textContent = e.message || "新規登録に失敗しました";
    }
  });

  $("#guestContinueBtn")?.addEventListener("click", () => {
    hideAuthGate();
    showToast("ローカルモードで開始しました");
  });

  $("#logoutBtn")?.addEventListener("click", async () => {
    if (firebaseReady && auth && currentUser) {
      await signOut(auth);
      currentUser = null;
      updateSyncUi();
      showToast("ログアウトしました");
    }
  });

  // 単語帳範囲入力
  $("#vocabRangeStart")?.addEventListener("change", (e) => {
    vocabRangeStart = Math.max(1, Number(e.target.value || 1));
    renderVocabView();
  });
  $("#vocabRangeEnd")?.addEventListener("change", (e) => {
    vocabRangeEnd = Math.max(1, Number(e.target.value || 200));
    renderVocabView();
  });

  // 単語帳の聞き流し開始
  $("#vocabListenStartBtn")?.addEventListener("click", () => {
    openListenMode(getFilteredVocab());
  });

  // 赤シートバー
  $("#redEnBtn")?.addEventListener("click", () => {
    redMode = redMode === "en" ? "none" : "en";
    updateRedSheetClasses();
  });
  $("#redJaBtn")?.addEventListener("click", () => {
    redMode = redMode === "ja" ? "none" : "ja";
    updateRedSheetClasses();
  });

  // 聞き流しコントロール
  $("#listenCloseBtn")?.addEventListener("click", closeListenMode);
  $("#listenPlayPauseBtn")?.addEventListener("click", () => {
    listenState.playing = !listenState.playing;
    renderListenCard();
    if (listenState.playing) scheduleListenNext();
    else clearTimeout(listenState.timerId);
  });
  $("#listenPrevBtn")?.addEventListener("click", () => {
    if (listenState.index > 0) {
      listenState.index--;
      renderListenCard();
      scheduleListenNext();
    }
  });
  $("#listenNextBtn")?.addEventListener("click", () => {
    if (listenState.index + 1 < listenState.queue.length) {
      listenState.index++;
      renderListenCard();
      scheduleListenNext();
    }
  });
  $("#listenHideEnBtn")?.addEventListener("click", () => {
    listenState.hideEn = !listenState.hideEn;
    renderListenCard();
  });
  $("#listenSpeakAgainBtn")?.addEventListener("click", () => {
    const item = listenState.queue[listenState.index];
    if (item) speakEnglish(item.word, listenState.rate);
  });
  $$("#listenOverlay .rate-btn").forEach((btn) => {
    btn.addEventListener("click", () => {
      const item = listenState.queue[listenState.index];
      if (!item) return;
      setWordLevel(item.no, Number(btn.dataset.rateLv));
      renderListenCard();
    });
  });

  // 学習モード切替（フラッシュカード／小テスト）
  $$("[data-study-tab]").forEach((btn) => {
    btn.addEventListener("click", () => {
      $$("[data-study-tab]").forEach((b) => b.classList.remove("active"));
      btn.classList.add("active");
      const tab = btn.dataset.studyTab;
      $("#fcSetupBox")?.classList.toggle("hidden", tab !== "fc");
      $("#quizSetupBox")?.classList.toggle("hidden", tab !== "quiz");
    });
  });

  $("#startFlashcardBtn")?.addEventListener("click", startFlashcards);
  $("#fcFront")?.addEventListener("click", () => {
    fcFlipped = true;
    renderFlashcard();
  });
  $("#fcBack")?.addEventListener("click", () => {
    fcFlipped = false;
    renderFlashcard();
  });
  $("#fcPrevBtn")?.addEventListener("click", () => {
    if (fcIndex > 0) {
      fcIndex--;
      fcFlipped = false;
      renderFlashcard();
    }
  });
  $("#fcNextBtn")?.addEventListener("click", () => {
    if (fcIndex + 1 < fcQueue.length) {
      fcIndex++;
      fcFlipped = false;
      renderFlashcard();
    } else {
      $("#flashcardStage")?.classList.add("hidden");
      $("#studySetup")?.classList.remove("hidden");
      showToast("フラッシュカード完了！");
    }
  });
  $$("#flashcardStage .rate-btn").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const item = fcQueue[fcIndex];
      if (!item) return;
      setWordLevel(item.no, Number(btn.dataset.fcRate));
      renderFlashcard();
    });
  });

  $("#startQuizBtn")?.addEventListener("click", startQuiz);
  $("#quizRevealBtn")?.addEventListener("click", () => {
    quizRevealed = true;
    renderQuizQuestion();
  });
  $("#quizCorrectBtn")?.addEventListener("click", () => {
    const item = quizItems[quizIndex];
    if (!item) return;
    quizResults[item.no] = { correct: true };
    setWordLevel(item.no, 3);
    renderQuizQuestion();
  });
  $("#quizWrongBtn")?.addEventListener("click", () => {
    const item = quizItems[quizIndex];
    if (!item) return;
    quizResults[item.no] = { correct: false };
    setWordLevel(item.no, 1);
    renderQuizQuestion();
  });
  $("#quizNextBtn")?.addEventListener("click", () => {
    if (quizIndex + 1 < quizItems.length) {
      quizIndex++;
      quizRevealed = false;
      renderQuizQuestion();
    } else {
      showQuizResult();
    }
  });
  $("#quizBackSetupBtn")?.addEventListener("click", () => {
    $("#quizResult")?.classList.add("hidden");
    $("#quizStage")?.classList.add("hidden");
    $("#studySetup")?.classList.remove("hidden");
  });

  // 交流（ニックネーム・フレンド・対戦）
  $("#saveNicknameBtn")?.addEventListener("click", async () => {
    const val = $("#nicknameInput")?.value.trim() || "";
    state.nickname = val;
    saveLocalState(true);
    if (firebaseReady && auth?.currentUser) {
      try { await updateProfile(auth.currentUser, { displayName: val }); } catch (_) {}
    }
    updateSyncUi();
    showToast("ニックネームを保存しました");
  });

  $("#addFriendBtn")?.addEventListener("click", async () => {
    const code = ($("#friendCodeInput")?.value || "").trim().toUpperCase();
    if (!code) return;
    if ((state.friends || []).some((f) => f.friendCode === code)) {
      showToast("すでに登録済みです");
      return;
    }
    state.friends.push({ uid: "", nickname: `フレンド (${code})`, friendCode: code });
    saveLocalState(true);
    if ($("#friendCodeInput")) $("#friendCodeInput").value = "";
    renderSocialView();
    showToast("フレンドを追加しました");
  });

  $("#createBattleBtn")?.addEventListener("click", createBattleRoom);

  // 設定変更
  $$("[data-theme-option]").forEach((btn) => {
    btn.addEventListener("click", () => {
      prefs.theme = btn.dataset.themeOption;
      saveLocalPrefs();
      applyPrefs();
      renderSettingsView();
    });
  });
  $$("[data-font-option]").forEach((btn) => {
    btn.addEventListener("click", () => {
      prefs.font = btn.dataset.fontOption;
      saveLocalPrefs();
      applyPrefs();
      renderSettingsView();
    });
  });
  $$("[data-size-option]").forEach((btn) => {
    btn.addEventListener("click", () => {
      prefs.size = btn.dataset.sizeOption;
      saveLocalPrefs();
      applyPrefs();
      renderSettingsView();
    });
  });
  $("#hidePosOnRedCheckbox")?.addEventListener("change", (e) => {
    prefs.hidePosOnRed = Boolean(e.target.checked);
    saveLocalPrefs();
    updateRedSheetClasses();
  });

  // スプラッシュ開始ボタン
  $("#splashStartBtn")?.addEventListener("click", () => {
    const splash = $("#splashScreen");
    if (splash) {
      splash.classList.add("fade-out");
      setTimeout(() => splash.classList.add("hidden"), 280);
    }
  });
}

function renderAll() {
  renderHomeView();
  renderVocabView();
  renderProgressView();
  renderSocialView();
  renderSettingsView();
}

/* =========================================================
   初期化エントリーポイント
   ========================================================= */
async function initApp() {
  loadLocalPrefs();
  loadLocalState();
  bindEvents();
  await loadVocabularyData();
  await initFirebaseIfAvailable();
  setupAuthListeners();
  updateSyncUi();
  renderAll();

  const statusEl = $("#splashStatus");
  if (statusEl) statusEl.textContent = "準備完了";
  const spinnerEl = $(".splash-spinner");
  if (spinnerEl) spinnerEl.classList.add("hidden");
  const startBtn = $("#splashStartBtn");
  if (startBtn) startBtn.classList.remove("hidden");
}

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    navigator.serviceWorker.register("./sw.js").catch(() => {});
  });
}

document.addEventListener("DOMContentLoaded", initApp);