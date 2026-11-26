/* =========================================================
   HONE - Main Application Script (app.js)
   英単語LEAP 全2,300語 学習PWA
   ========================================================= */
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import {
  getAuth,
  onAuthStateChanged,
  signInWithEmailAndPassword,
  createUserWithEmailAndPassword,
  sendPasswordResetEmail,
  EmailAuthProvider,
  reauthenticateWithCredential,
  verifyBeforeUpdateEmail,
  signOut,
  updateProfile
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js";
import {
  getFirestore,
  doc,
  getDoc,
  setDoc,
  updateDoc,
  collection,
  addDoc,
  query,
  where,
  getDocs,
  onSnapshot,
  serverTimestamp
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";

/* =========================================================
   定数・設定
   ========================================================= */
const STORAGE_KEYS = {
  STATE: "hone_state_v2",
  LEGACY_STATE: "hone_state_v1",
  PREFS: "hone_prefs_v2",
  LEGACY_PREFS: "hone_prefs_v1",
  CACHE_WORDS: "hone_words_cache_v2",
  CACHE_EXAMPLES: "hone_examples_cache_v2",
  GUEST_MODE: "hone_guest_mode_v1",
  DISMISS_RECOVERY: "hone_dismiss_recovery_v1"
};

const SYNTHETIC_EMAIL_DOMAINS = [
  "hone.local",
  "hone-app.local",
  "hone-app-beed6.firebaseapp.com"
];

const THEME_COLORS = {
  "mist": "#edf3f8",
  "matte-blue": "#3d607c",
  "dark-slate": "#0f172a"
};

const VIEW_TITLES = {
  home: "HONE",
  vocab: "単語帳",
  study: "学習",
  battle: "フレンド",
  progress: "記録",
  settings: "設定"
};

const DEFAULT_PREFS = {
  goalMin: 1,
  goalMax: 100,
  voiceAccent: "en-US",
  autoAudio: true,
  keepPosOnRed: true,
  fontSize: "md",
  fontFamily: "sans",
  theme: "mist"
};

const DEFAULT_STATE = {
  loginId: "",
  recoveryEmail: "",
  nickname: "",
  friendId: "",
  levels: {}, // { [no]: 0 | 1 | 2 | 3 }
  studiedIdsToday: [],
  studiedDate: "",
  streakDays: 0,
  lastStudyDate: "",
  friends: [], // [{ uid, nickname, friendId }]
  updatedAt: 0
};

const LEVEL_FILTERS = [
  { level: "all", label: "すべて" },
  { level: "0", label: "未学習" },
  { level: "1", label: "苦手" },
  { level: "2", label: "うろ覚え" },
  { level: "3", label: "定着" }
];

const PART_RANGES = [
  { label: "Part 1 (1〜400)", start: 1, end: 400 },
  { label: "Part 2 (401〜1000)", start: 401, end: 1000 },
  { label: "Part 3 (1001〜1400)", start: 1001, end: 1400 },
  { label: "Part 4 (1401〜2000)", start: 1401, end: 2000 },
  { label: "＋α (2001〜2300)", start: 2001, end: 2300 }
];

/* =========================================================
   アプリケーション状態
   ========================================================= */
let auth = null;
let db = null;
let firebaseReady = false;
let currentUser = null;
let cloudUnsubscribe = null;
let friendReqUnsubscribe = null;
let syncTimer = null;
let skipRecoveryThisSession = false;

let wordsData = [];
let wordsByNo = new Map();
let examplesMap = new Map(); // no -> [{ rawEn, en, ja }]

let state = structuredClone(DEFAULT_STATE);
let prefs = structuredClone(DEFAULT_PREFS);
let activeTab = "home";

// 単語帳状態
let vocabMin = 1;
let vocabMax = 100;
let vocabLevelFilter = "all"; // "all" | "0" | "1" | "2" | "3" | "weak"
let redEnActive = false;
let redJaActive = false;

// 学習セットアップ状態
let currentStudyMode = "flashcard"; // "flashcard" | "quiz" | "listen"

// フラッシュカード状態
let fcQueue = [];
let fcIndex = 0;
let fcFlipped = false;
let fcFormat = "en-ja";

// 小テスト状態
let quizQueue = [];
let quizIndex = 0;
let quizFormat = "spell";
let quizLayout = "single"; // "single" | "list"
let quizAnswers = {}; // { [no]: { correct: boolean, level: number } }
let quizListRevealed = false;
let quizIsRetest = false;

// スペル入力テスト状態
let spellTargetTokens = []; // [{ type: 'char', expected: 'a' } | { type: 'sep', char: '-'|' ' }]
let spellAcceptedWords = []; // ['afterward', 'afterwards']
let spellTypedChars = []; // array of typed lowercase chars matching 'char' tokens
let spellJudged = false;

// 聞き流し状態（デフォルト: 1.0x / 1.4秒 = 1400ms）
let listenState = {
  active: false,
  playing: false,
  loop: true,
  speed: 1.0,
  intervalMs: 1400,
  queue: [],
  index: 0,
  timerId: null,
  utteranceToken: 0
};

// 対戦状態
let battleRoomUnsub = null;
let battleTimerId = null;
let battleSession = {
  roomCode: "",
  isHost: false,
  localOnly: false,
  format: "en-ja",
  questions: [],
  currentIndex: 0,
  answeredCurrent: false,
  timeLeft: 10,
  players: {}
};

// フレンド詳細モーダル対象
let selectedFriend = null;

/* =========================================================
   DOM ヘルパー＆共通ユーティリティ
   ========================================================= */
const $ = (sel) => document.querySelector(sel);
const $$ = (sel) => Array.from(document.querySelectorAll(sel));

function escapeHtml(str) {
  return String(str ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function todayKey() {
  const d = new Date();
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, "0")}-${String(d.getDate()).padStart(2, "0")}`;
}

function yesterdayKey() {
  const d = new Date(Date.now() - 86400000);
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, "0")}-${String(d.getDate()).padStart(2, "0")}`;
}

function showToast(msg) {
  const el = $("#toast");
  if (!el) return;
  el.textContent = msg;
  el.classList.remove("hidden");
  clearTimeout(showToast._t);
  showToast._t = setTimeout(() => el.classList.add("hidden"), 2400);
}

function generateCode(len = 6) {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let out = "";
  for (let i = 0; i < len; i++) {
    out += chars[Math.floor(Math.random() * chars.length)];
  }
  return out;
}

function ensureFriendId(existing) {
  if (existing && /^HN-[A-Z0-9]{6}$/.test(existing)) return existing;
  if (existing && /^[A-Z0-9]{6}$/.test(existing)) return `HN-${existing}`;
  return `HN-${generateCode(6)}`;
}

function shuffleArray(arr) {
  const copy = [...arr];
  for (let i = copy.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [copy[i], copy[j]] = [copy[j], copy[i]];
  }
  return copy;
}

/* =========================================================
   設定・ローカル状態の読み書き
   ========================================================= */
function loadLocalPrefs() {
  try {
    const raw = localStorage.getItem(STORAGE_KEYS.PREFS) || localStorage.getItem(STORAGE_KEYS.LEGACY_PREFS);
    if (raw) {
      const parsed = JSON.parse(raw);
      if (parsed.theme === "light-mist") parsed.theme = "mist";
      prefs = { ...DEFAULT_PREFS, ...parsed };
    }
  } catch (_) {}
  vocabMin = prefs.goalMin || 1;
  vocabMax = prefs.goalMax || 100;
  applyPrefsToDom();
}

function saveLocalPrefs() {
  try {
    localStorage.setItem(STORAGE_KEYS.PREFS, JSON.stringify(prefs));
  } catch (_) {}
}

function applyPrefsToDom() {
  const theme = THEME_COLORS[prefs.theme] ? prefs.theme : "mist";
  document.documentElement.setAttribute("data-theme", theme);
  document.body.setAttribute("data-theme", theme);
  document.body.setAttribute("data-font", prefs.fontFamily || "sans");
  document.body.setAttribute("data-size", prefs.fontSize || "md");

  const metaTheme = $("#metaThemeColor");
  if (metaTheme) metaTheme.setAttribute("content", THEME_COLORS[theme] || "#edf3f8");

  updateRedSheetClasses();
}

function loadLocalState() {
  try {
    const raw = localStorage.getItem(STORAGE_KEYS.STATE) || localStorage.getItem(STORAGE_KEYS.LEGACY_STATE);
    if (raw) {
      const parsed = JSON.parse(raw);
      state = {
        ...DEFAULT_STATE,
        ...parsed,
        friendId: ensureFriendId(parsed.friendId || parsed.friendCode)
      };
    } else {
      state.friendId = ensureFriendId("");
    }
  } catch (_) {
    state.friendId = ensureFriendId("");
  }
  normalizeDailyState();
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

function setWordLevel(no, lv) {
  const clamped = Math.max(0, Math.min(3, Number(lv) || 0));
  state.levels[String(no)] = clamped;
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
  saveLocalState(true);
}

/* =========================================================
   CSV 読み込み＆パース（日本語ヘッダー＆英語ヘッダー両対応）
   ========================================================= */
function parseCsvRows(text) {
  const rows = [];
  let row = [];
  let cur = "";
  let inQuotes = false;
  const cleaned = String(text || "").replace(/^\uFEFF/, "");

  for (let i = 0; i < cleaned.length; i++) {
    const ch = cleaned[i];
    if (ch === '"') {
      if (inQuotes && cleaned[i + 1] === '"') {
        cur += '"';
        i++;
      } else {
        inQuotes = !inQuotes;
      }
    } else if (ch === "," && !inQuotes) {
      row.push(cur.trim());
      cur = "";
    } else if ((ch === "\n" || ch === "\r") && !inQuotes) {
      if (ch === "\r" && cleaned[i + 1] === "\n") i++;
      row.push(cur.trim());
      if (row.some((cell) => cell.length > 0)) rows.push(row);
      row = [];
      cur = "";
    } else {
      cur += ch;
    }
  }
  row.push(cur.trim());
  if (row.some((cell) => cell.length > 0)) rows.push(row);

  if (rows.length < 2) return [];
  const headers = rows[0].map((h) => h.replace(/^\uFEFF/, "").trim());
  return rows.slice(1).map((cols) => {
    const obj = {};
    headers.forEach((h, idx) => {
      obj[h] = cols[idx] ?? "";
    });
    return obj;
  });
}

function splitMeanings(raw) {
  const text = String(raw || "").trim();
  if (!text) return ["—"];
  // ①②③ などの丸数字区切りがある場合は丸数字の手前で分割
  if (/[①②③④⑤⑥⑦⑧⑨⑩]/.test(text)) {
    const parts = text
      .split(/\s*(?=[①②③④⑤⑥⑦⑧⑨⑩])/)
      .map((s) => s.trim())
      .filter(Boolean);
    if (parts.length) return parts;
  }
  const parts = text
    .split(/[／/|;；\n]+/)
    .map((s) => s.trim())
    .filter(Boolean);
  return parts.length ? parts : [text];
}

function buildExamplesMap(rows) {
  examplesMap.clear();
  rows.forEach((r) => {
    const no = Number(r["単語番号"] || r.no || r.id || 0);
    if (!no) return;
    const rawEn = (r["例文"] || r.example_en || r.en || r.example || "").trim();
    const ja = (r["日本語訳"] || r.example_ja || r.ja || r.translation || "").trim();
    if (!rawEn) return;
    const cleanEn = rawEn.replace(/\[\[([^\]]+)\]\]/g, "$1");
    if (!examplesMap.has(no)) examplesMap.set(no, []);
    examplesMap.get(no).push({ rawEn, en: cleanEn, ja });
  });
}

function normalizeWords(rows) {
  const list = rows
    .map((r, idx) => {
      const no = Number(r["単語番号"] || r.no || r.id || idx + 1);
      const word = (r["英単語"] || r.word || r.en || "").trim();
      const unit = (r["単元"] || r.unit || "").trim();
      const pos = (r["品詞"] || r.pos || r.part_of_speech || "").trim();
      const rawMeaning = (r["主な意味"] || r.meanings || r.meaning || r.jp || "").trim();
      const phonetic = (r["発音記号"] || r.phonetic || r.ipa || "").trim();
      const core = (r["コア・解説"] || r.note || r.memo || "").trim();
      const inlinePhrase = (r["フレーズ・例文"] || "").trim();

      if (inlinePhrase && !examplesMap.has(no)) {
        examplesMap.set(no, [{
          rawEn: inlinePhrase,
          en: inlinePhrase.replace(/\[\[([^\]]+)\]\]/g, "$1"),
          ja: ""
        }]);
      }

      return {
        no,
        unit,
        word,
        pos,
        rawMeaning,
        meanings: splitMeanings(rawMeaning),
        phonetic,
        note: core
      };
    })
    .filter((w) => w.no > 0 && w.word)
    .sort((a, b) => a.no - b.no);

  wordsByNo.clear();
  list.forEach((w) => wordsByNo.set(w.no, w));
  return list;
}

async function loadVocabularyData() {
  try {
    const [wRes, eRes] = await Promise.all([
      fetch("./data/words.csv"),
      fetch("./data/examples.csv")
    ]);
    if (!wRes.ok) throw new Error("words.csv fetch failed");
    const wText = await wRes.text();

    if (eRes.ok) {
      const eText = await eRes.text();
      try { localStorage.setItem(STORAGE_KEYS.CACHE_EXAMPLES, eText); } catch (_) {}
      buildExamplesMap(parseCsvRows(eText));
    }

    const parsedWords = normalizeWords(parseCsvRows(wText));
    if (!parsedWords.length) throw new Error("words.csv parsed 0 words");
    wordsData = parsedWords;
    try { localStorage.setItem(STORAGE_KEYS.CACHE_WORDS, wText); } catch (_) {}
  } catch (err) {
    console.warn("Using cached CSV fallback:", err);
    const cachedE = localStorage.getItem(STORAGE_KEYS.CACHE_EXAMPLES);
    const cachedW = localStorage.getItem(STORAGE_KEYS.CACHE_WORDS);
    if (cachedE) buildExamplesMap(parseCsvRows(cachedE));
    if (cachedW) wordsData = normalizeWords(parseCsvRows(cachedW));
  }

  const maxNo = wordsData.length ? wordsData[wordsData.length - 1].no : 2300;
  ["#vocabMin", "#vocabMax", "#studyMin", "#studyMax", "#battleMin", "#battleMax", "#setGoalMin", "#setGoalMax"].forEach((sel) => {
    const el = $(sel);
    if (el) el.max = String(maxNo);
  });
}

function formatExampleHighlightedHtml(rawEn) {
  const escaped = escapeHtml(rawEn);
  return escaped.replace(/\[\[([^\]]+)\]\]/g, '<span class="ex-highlight">$1</span>');
}

function formatExampleClozeHtml(rawEn, targetWord) {
  const escaped = escapeHtml(rawEn);
  if (/\[\[([^\]]+)\]\]/.test(escaped)) {
    return escaped.replace(/\[\[([^\]]+)\]\]/g, '<span class="cloze-blank">（　　）</span>');
  }
  if (targetWord) {
    const re = new RegExp(`\\b${targetWord.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "i");
    return escaped.replace(re, '<span class="cloze-blank">（　　）</span>');
  }
  return escaped;
}

/* =========================================================
   Firebase 初期化・認証・クラウド同期
   ========================================================= */
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
    console.warn("Firebase unavailable (offline mode):", err);
    return false;
  }
}

function isRealEmail(email) {
  if (!email || !email.includes("@")) return false;
  return !SYNTHETIC_EMAIL_DOMAINS.some((d) => email.toLowerCase().endsWith(`@${d}`));
}

function extractLoginIdFromEmail(email) {
  if (!email) return "";
  for (const domain of SYNTHETIC_EMAIL_DOMAINS) {
    const suffix = `@${domain}`;
    if (email.toLowerCase().endsWith(suffix)) {
      return email.slice(0, -suffix.length);
    }
  }
  return email;
}

async function resolveLoginEmail(rawInput) {
  const trimmed = rawInput.trim();
  if (trimmed.includes("@")) return [trimmed];

  const cleanId = trimmed.toLowerCase();
  const candidates = [];

  if (firebaseReady && db) {
    try {
      const mapSnap = await getDoc(doc(db, "usernames", cleanId));
      if (mapSnap.exists() && mapSnap.data()?.email) {
        candidates.push(mapSnap.data().email);
      }
    } catch (_) {}
  }

  SYNTHETIC_EMAIL_DOMAINS.forEach((d) => {
    const addr = `${cleanId}@${d}`;
    if (!candidates.includes(addr)) candidates.push(addr);
  });
  return candidates;
}

function updateSyncUi() {
  const dot = $("#syncDot");
  const statusText = $("#syncStatusText");
  const loginIdEl = $("#authCurrentLoginId");
  const friendIdEl = $("#authFriendId");
  const friendMyIdEl = $("#friendMyIdDisplay");
  const recoveryStatusEl = $("#authRecoveryStatus");
  const logoutBtn = $("#btnLogout");

  state.friendId = ensureFriendId(state.friendId);
  if (friendIdEl) friendIdEl.textContent = state.friendId;
  if (friendMyIdEl) friendMyIdEl.textContent = state.friendId;

  if (firebaseReady && currentUser) {
    dot?.classList.add("online");
    const dispId = state.loginId || extractLoginIdFromEmail(currentUser.email || "");
    if (statusText) statusText.textContent = `クラウド同期中（${state.nickname || dispId || "ログイン済み"}）`;
    if (loginIdEl) loginIdEl.textContent = dispId || "ログイン済み";

    const realMail = isRealEmail(currentUser.email) ? currentUser.email : state.recoveryEmail;
    if (recoveryStatusEl) {
      recoveryStatusEl.textContent = realMail ? `登録済み (${realMail})` : "未登録";
    }
    if (logoutBtn) {
      logoutBtn.textContent = "ログアウト";
      logoutBtn.style.color = "var(--lv-1)";
    }
  } else {
    dot?.classList.remove("online");
    if (statusText) statusText.textContent = "ゲスト利用中（この端末に自動保存）";
    if (loginIdEl) loginIdEl.textContent = "未ログイン";
    if (recoveryStatusEl) recoveryStatusEl.textContent = "ログイン後に設定可能";
    if (logoutBtn) {
      logoutBtn.textContent = "ログイン / 新規登録";
      logoutBtn.style.color = "var(--accent-strong)";
    }
  }
}

function buildMasterySummary() {
  const stats = computeStats(wordsData);
  return {
    total: stats.total,
    lv0: stats.lv0,
    lv1: stats.lv1,
    lv2: stats.lv2,
    lv3: stats.lv3,
    pct: stats.pct
  };
}

async function pushCloudStateNow() {
  if (!firebaseReady || !db || !currentUser) return false;
  try {
    state.friendId = ensureFriendId(state.friendId);
    const payload = {
      uid: currentUser.uid,
      loginId: state.loginId || extractLoginIdFromEmail(currentUser.email || ""),
      recoveryEmail: isRealEmail(currentUser.email) ? currentUser.email : (state.recoveryEmail || ""),
      nickname: state.nickname || currentUser.displayName || "",
      friendId: state.friendId,
      friendCode: state.friendId,
      levels: state.levels || {},
      studiedIdsToday: state.studiedIdsToday || [],
      studiedDate: state.studiedDate || todayKey(),
      streakDays: state.streakDays || 0,
      lastStudyDate: state.lastStudyDate || "",
      friends: state.friends || [],
      summary: buildMasterySummary(),
      updatedAt: state.updatedAt || Date.now(),
      serverUpdatedAt: serverTimestamp()
    };
    await setDoc(doc(db, "users", currentUser.uid), payload, { merge: true });
    if (payload.loginId && !payload.loginId.includes("@")) {
      try {
        await setDoc(doc(db, "usernames", payload.loginId.toLowerCase()), {
          uid: currentUser.uid,
          email: currentUser.email || `${payload.loginId.toLowerCase()}@${SYNTHETIC_EMAIL_DOMAINS[0]}`,
          friendId: state.friendId,
          updatedAt: serverTimestamp()
        }, { merge: true });
      } catch (_) {}
    }
    return true;
  } catch (err) {
    console.warn("Cloud sync failed:", err);
    return false;
  }
}

function scheduleCloudSync() {
  if (!firebaseReady || !currentUser) return;
  clearTimeout(syncTimer);
  syncTimer = setTimeout(() => {
    pushCloudStateNow();
  }, 500);
}

function subscribeUserDoc(uid) {
  if (cloudUnsubscribe) {
    cloudUnsubscribe();
    cloudUnsubscribe = null;
  }
  if (!firebaseReady || !db || !uid) return;
  cloudUnsubscribe = onSnapshot(doc(db, "users", uid), (snap) => {
    if (!snap.exists()) return;
    const remote = snap.data();
    const remoteTs = Number(remote.updatedAt || 0);
    const localTs = Number(state.updatedAt || 0);
    if (remoteTs > localTs) {
      state = {
        ...DEFAULT_STATE,
        ...state,
        loginId: remote.loginId || state.loginId,
        recoveryEmail: remote.recoveryEmail || state.recoveryEmail,
        nickname: remote.nickname ?? state.nickname,
        friendId: ensureFriendId(remote.friendId || remote.friendCode || state.friendId),
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

function subscribeFriendRequests(uid) {
  if (friendReqUnsubscribe) {
    friendReqUnsubscribe();
    friendReqUnsubscribe = null;
  }
  if (!firebaseReady || !db || !uid) return;
  try {
    const q = query(collection(db, "friendRequests"), where("toUid", "==", uid), where("status", "==", "pending"));
    friendReqUnsubscribe = onSnapshot(q, (snap) => {
      const reqs = [];
      snap.forEach((d) => reqs.push({ id: d.id, ...d.data() }));
      renderFriendRequests(reqs);
    }, () => {});
  } catch (_) {}
}

function setupAuthListeners() {
  if (!firebaseReady || !auth) return;
  onAuthStateChanged(auth, async (user) => {
    currentUser = user;
    if (user) {
      if (!state.loginId) {
        state.loginId = extractLoginIdFromEmail(user.email || "");
      }
      if (!state.nickname && user.displayName) {
        state.nickname = user.displayName;
      }
      try {
        const snap = await getDoc(doc(db, "users", user.uid));
        if (snap.exists()) {
          const remote = snap.data();
          if (Number(remote.updatedAt || 0) >= Number(state.updatedAt || 0)) {
            state = {
              ...DEFAULT_STATE,
              ...state,
              loginId: remote.loginId || state.loginId,
              recoveryEmail: remote.recoveryEmail || state.recoveryEmail,
              nickname: remote.nickname || state.nickname || user.displayName || "",
              friendId: ensureFriendId(remote.friendId || remote.friendCode || state.friendId),
              levels: { ...(state.levels || {}), ...(remote.levels || {}) },
              studiedIdsToday: remote.studiedIdsToday || state.studiedIdsToday,
              studiedDate: remote.studiedDate || todayKey(),
              streakDays: remote.streakDays ?? state.streakDays,
              lastStudyDate: remote.lastStudyDate || state.lastStudyDate,
              friends: remote.friends || state.friends || [],
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
      subscribeFriendRequests(user.uid);
      $("#authGate")?.classList.add("hidden");

      if (!state.nickname) {
        $("#usernameModal")?.classList.remove("hidden");
      } else {
        maybePromptRecoveryEmail();
      }
      renderAll();
    } else {
      if (cloudUnsubscribe) { cloudUnsubscribe(); cloudUnsubscribe = null; }
      if (friendReqUnsubscribe) { friendReqUnsubscribe(); friendReqUnsubscribe = null; }
      updateSyncUi();
      renderHomeView();
    }
  });
}

function maybePromptRecoveryEmail() {
  if (!currentUser) return;
  if (skipRecoveryThisSession) return;
  if (localStorage.getItem(STORAGE_KEYS.DISMISS_RECOVERY) === "1") return;
  const hasReal = isRealEmail(currentUser.email) || Boolean(state.recoveryEmail);
  if (!hasReal && $("#splashScreen")?.classList.contains("hidden")) {
    $("#recoveryPromptModal")?.classList.remove("hidden");
  }
}

/* =========================================================
   画面切り替え＆ヘッダー制御
   ========================================================= */
function switchTab(tabName) {
  activeTab = tabName;
  $$(".view").forEach((v) => v.classList.remove("active"));
  const viewEl = $(`#view-${tabName}`);
  if (viewEl) viewEl.classList.add("active");

  $$(".nav-tab").forEach((btn) => {
    btn.classList.toggle("active", btn.dataset.tab === tabName);
  });

  const titleEl = $("#headerTitle");
  if (titleEl) titleEl.textContent = VIEW_TITLES[tabName] || "HONE";

  const backBtn = $("#btnBack");
  if (backBtn) backBtn.classList.toggle("is-hidden", tabName === "home");

  const redBar = $("#floatingRedBar");
  if (redBar) redBar.classList.toggle("hidden", tabName !== "vocab");

  if (tabName === "home") renderHomeView();
  else if (tabName === "vocab") renderVocabView();
  else if (tabName === "study") openStudyPicker();
  else if (tabName === "battle") renderBattleFriendView();
  else if (tabName === "progress") renderProgressView();
  else if (tabName === "settings") renderSettingsView();
}

/* =========================================================
   ドーナツチャート＆統計描画（ホーム・進捗・フレンド詳細共通）
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

function renderDonutAndLegend(svgSel, pctSel, legendSel, stats) {
  const svg = $(svgSel);
  const pctEl = $(pctSel);
  const legendEl = $(legendSel);

  if (pctEl) pctEl.textContent = `${stats.pct}%`;

  if (svg) {
    const total = Math.max(1, stats.total);
    const r = 46;
    const c = 2 * Math.PI * r;
    const s3 = c * (stats.lv3 / total);
    const s2 = c * (stats.lv2 / total);
    const s1 = c * (stats.lv1 / total);

    svg.innerHTML = `
      <circle cx="60" cy="60" r="${r}" fill="none" stroke="rgba(148, 163, 184, 0.25)" stroke-width="14"></circle>
      <circle cx="60" cy="60" r="${r}" fill="none" stroke="var(--lv-3)" stroke-width="14"
        stroke-dasharray="${s3} ${c}" stroke-dashoffset="0"></circle>
      <circle cx="60" cy="60" r="${r}" fill="none" stroke="var(--lv-2)" stroke-width="14"
        stroke-dasharray="${s2} ${c}" stroke-dashoffset="${-s3}"></circle>
      <circle cx="60" cy="60" r="${r}" fill="none" stroke="var(--lv-1)" stroke-width="14"
        stroke-dasharray="${s1} ${c}" stroke-dashoffset="${-(s3 + s2)}"></circle>
    `;
  }

  if (legendEl) {
    legendEl.innerHTML = `
      <span class="legend-item"><span class="dot lv-3"></span>定着 ${stats.lv3}</span>
      <span class="legend-item"><span class="dot lv-2"></span>うろ覚え ${stats.lv2}</span>
      <span class="legend-item"><span class="dot lv-1"></span>苦手 ${stats.lv1}</span>
      <span class="legend-item"><span class="dot lv-0"></span>未学習 ${stats.lv0}</span>
    `;
  }
}

function renderUnitBarsInto(containerSel, levelsMap = state.levels) {
  const container = $(containerSel);
  if (!container) return;

  container.innerHTML = PART_RANGES.map((part) => {
    const sub = wordsData.filter((w) => w.no >= part.start && w.no <= part.end);
    if (!sub.length) return "";
    let lv0 = 0, lv1 = 0, lv2 = 0, lv3 = 0;
    sub.forEach((w) => {
      const lv = Number(levelsMap?.[w.no] || 0);
      if (lv === 3) lv3++;
      else if (lv === 2) lv2++;
      else if (lv === 1) lv1++;
      else lv0++;
    });
    const total = sub.length;
    const pct = Math.round((lv3 / total) * 100);
    const w3 = (lv3 / total) * 100;
    const w2 = (lv2 / total) * 100;
    const w1 = (lv1 / total) * 100;
    const w0 = Math.max(0, 100 - w3 - w2 - w1);
    return `
      <div class="unit-bar-item">
        <div class="unit-bar-head">
          <span>${escapeHtml(part.label)}</span>
          <span>定着 ${pct}% (${lv3}/${total})</span>
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

function renderHomeView() {
  normalizeDailyState();
  const gMin = Math.min(prefs.goalMin || 1, prefs.goalMax || 100);
  const gMax = Math.max(prefs.goalMin || 1, prefs.goalMax || 100);
  const goalWords = wordsData.filter((w) => w.no >= gMin && w.no <= gMax);
  const stats = computeStats(goalWords);

  const greetingEl = $("#homeUserGreeting");
  if (greetingEl) {
    if (state.nickname) {
      greetingEl.textContent = `${state.nickname} さん`;
    } else if (currentUser && state.loginId) {
      greetingEl.textContent = `${state.loginId} さん`;
    } else {
      greetingEl.textContent = "今日の学習";
    }
  }

  const rangeLabel = $("#homeRangeLabel");
  if (rangeLabel) rangeLabel.textContent = `No. ${gMin} 〜 ${gMax}`;

  renderDonutAndLegend("#homeDonutSvg", "#homeMasteryPct", "#homeLegend", stats);

  const todayEl = $("#homeTodayCount");
  const streakEl = $("#homeStreakDays");
  if (todayEl) todayEl.textContent = `${(state.studiedIdsToday || []).length} 語`;
  if (streakEl) streakEl.textContent = `${state.streakDays || 0} 日`;
}

function renderProgressView() {
  normalizeDailyState();
  const stats = computeStats(wordsData);

  const totalCountEl = $("#progTotalCount");
  if (totalCountEl) totalCountEl.textContent = `全 ${stats.total.toLocaleString()} 語`;

  renderDonutAndLegend("#progDonutSvg", "#progMasteryPct", "#progLegend", stats);

  const todayEl = $("#progTodayCount");
  const streakEl = $("#progStreakDays");
  if (todayEl) todayEl.textContent = `${(state.studiedIdsToday || []).length} 語`;
  if (streakEl) streakEl.textContent = `${state.streakDays || 0} 日`;

  renderUnitBarsInto("#unitBarsContainer", state.levels);
}

/* =========================================================
   単語帳画面（文字入り横一列カラーチップ・番号右に品詞・赤シート）
   ========================================================= */
function renderLevelFilterChips() {
  const wrap = $("#vocabLevelFilter");
  if (!wrap) return;
  wrap.innerHTML = LEVEL_FILTERS.map((item) => {
    const isActive =
      vocabLevelFilter === item.level ||
      (vocabLevelFilter === "weak" && (item.level === "1" || item.level === "2"));
    return `
      <button
        type="button"
        class="level-chip${isActive ? " active" : ""}"
        data-level="${item.level}"
      >${escapeHtml(item.label)}</button>
    `;
  }).join("");

  $$("#vocabLevelFilter .level-chip").forEach((btn) => {
    btn.addEventListener("click", () => {
      vocabLevelFilter = btn.dataset.level;
      renderVocabView();
    });
  });
}

function getFilteredVocab() {
  const s = Math.min(vocabMin, vocabMax);
  const e = Math.max(vocabMin, vocabMax);
  return wordsData.filter((w) => {
    if (w.no < s || w.no > e) return false;
    if (vocabLevelFilter === "all") return true;
    const lv = Number(state.levels?.[w.no] || 0);
    if (vocabLevelFilter === "weak") return lv === 1 || lv === 2;
    return lv === Number(vocabLevelFilter);
  });
}

function renderVocabView() {
  const minInp = $("#vocabMin");
  const maxInp = $("#vocabMax");
  if (minInp) minInp.value = vocabMin;
  if (maxInp) maxInp.value = vocabMax;

  renderLevelFilterChips();
  const list = getFilteredVocab();

  const badge = $("#vocabCountBadge");
  if (badge) badge.textContent = `${list.length}語`;

  renderVocabList(list);
  updateRedSheetClasses();
}

function renderVocabList(list = getFilteredVocab()) {
  const container = $("#vocabList");
  if (!container) return;

  if (!list.length) {
    container.innerHTML = `<div class="glass-card"><p class="sub-label" style="margin:0;text-align:center;">該当する単語がありません（範囲や上のカラーチップを切り替えてください）。</p></div>`;
    return;
  }

  const levelNames = ["未学習", "苦手", "うろ覚え", "定着"];
  const speakerIcon = `<svg viewBox="0 0 24 24" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"></polygon><path d="M15.54 8.46a5 5 0 0 1 0 7.07"></path></svg>`;

  container.innerHTML = list.map((w) => {
    const lv = Number(state.levels?.[w.no] || 0);
    const exList = examplesMap.get(w.no) || [];
    const meaningsHtml = w.meanings
      .map((m) => `<span class="vocab-meaning-line">${escapeHtml(m)}</span>`)
      .join("");

    const examplesHtml = exList.length
      ? `
        <div class="acc-block">
          <span class="acc-label">フレーズ・例文</span>
          ${exList.map((ex) => `
            <p class="acc-text">${formatExampleHighlightedHtml(ex.rawEn)}</p>
            ${ex.ja ? `<p class="acc-text sub-label" style="margin-bottom:6px;">${escapeHtml(ex.ja)}</p>` : ""}
          `).join("")}
        </div>
      `
      : "";

    return `
      <article class="vocab-item" data-no="${w.no}">
        <div class="vocab-row">
          <button type="button" class="vocab-dot-btn" data-cycle-no="${w.no}" aria-label="習熟度を変更（現在: ${levelNames[lv]}）" title="タップで習熟度切替（現在: ${levelNames[lv]}）">
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
              ${w.unit ? `<span>${escapeHtml(w.unit)}</span>` : ""}
              ${w.phonetic ? `<span>${escapeHtml(w.phonetic)}</span>` : ""}
              <span>現在: ${levelNames[lv]}</span>
            </div>
            <button type="button" class="audio-pill" data-speak-word="${escapeHtml(w.word)}">${speakerIcon}<span>発音</span></button>
          </div>
          ${examplesHtml}
          ${w.note ? `
            <div class="acc-block">
              <span class="acc-label">解説・メモ</span>
              <p class="acc-text">${escapeHtml(w.note)}</p>
            </div>
          ` : ""}
          <div class="listen-rate-row" style="margin-top:10px;">
            <button type="button" class="rate-btn lv-1-btn${lv === 1 ? " selected" : ""}" data-vocab-rate="1" data-no="${w.no}">苦手</button>
            <button type="button" class="rate-btn lv-2-btn${lv === 2 ? " selected" : ""}" data-vocab-rate="2" data-no="${w.no}">うろ覚え</button>
            <button type="button" class="rate-btn lv-3-btn${lv === 3 ? " selected" : ""}" data-vocab-rate="3" data-no="${w.no}">定着</button>
          </div>
        </div>
      </article>
    `;
  }).join("");

  container.querySelectorAll(".vocab-dot-btn").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const no = Number(btn.dataset.cycleNo);
      const cur = Number(state.levels?.[no] || 0);
      const next = (cur + 1) % 4;
      setWordLevel(no, next);
      renderVocabView();
    });
  });

  container.querySelectorAll("[data-vocab-rate]").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const no = Number(btn.dataset.no);
      const lv = Number(btn.dataset.vocabRate);
      setWordLevel(no, lv);
      renderVocabView();
    });
  });

  container.querySelectorAll(".vocab-detail-btn").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const card = container.querySelector(`.vocab-item[data-no="${btn.dataset.toggleNo}"]`);
      if (card) card.classList.toggle("open");
    });
  });

  container.querySelectorAll("[data-speak-word]").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      speakEnglish(btn.dataset.speakWord || "");
    });
  });

  container.querySelectorAll(".vocab-word, .vocab-meaning-line, .pos-badge").forEach((el) => {
    el.addEventListener("click", (e) => {
      if (redEnActive || redJaActive) {
        e.stopPropagation();
        el.classList.toggle("revealed");
      }
    });
  });
}

function updateRedSheetClasses() {
  const listEl = $("#vocabList");
  if (listEl) {
    listEl.classList.toggle("red-en", redEnActive);
    listEl.classList.toggle("red-ja", redJaActive);
    listEl.classList.toggle("hide-pos-on-red", !prefs.keepPosOnRed && (redEnActive || redJaActive));
    if (!redEnActive && !redJaActive) {
      listEl.querySelectorAll(".revealed").forEach((el) => el.classList.remove("revealed"));
    }
  }
  $("#toggleRedEn")?.classList.toggle("active", redEnActive);
  $("#toggleRedJa")?.classList.toggle("active", redJaActive);
}

/* =========================================================
   音声発音＆ハンズフリー聞き流しモード（1.0x / 1.4秒間隔デフォルト）
   ========================================================= */
function speakEnglish(text, rate = 1.0, onDone = null) {
  if (!text || !("speechSynthesis" in window)) {
    if (onDone) setTimeout(onDone, 350);
    return;
  }
  try {
    window.speechSynthesis.cancel();
    const utt = new SpeechSynthesisUtterance(text);
    utt.lang = prefs.voiceAccent || "en-US";
    utt.rate = rate;
    let finished = false;
    const finishOnce = () => {
      if (finished) return;
      finished = true;
      if (onDone) onDone();
    };
    utt.onend = finishOnce;
    utt.onerror = finishOnce;
    // Web Speech API が onend を発火しないブラウザ環境向けの安全フォールバック
    setTimeout(finishOnce, Math.max(1400, Math.round((text.length * 110) / Math.max(0.6, rate)) + 700));
    window.speechSynthesis.speak(utt);
  } catch (_) {
    if (onDone) setTimeout(onDone, 350);
  }
}

function startListenOverlay(queue, speed = 1.0, intervalMs = 1400, loop = true) {
  if (!queue || !queue.length) {
    showToast("対象となる単語がありません");
    return;
  }
  clearTimeout(listenState.timerId);
  listenState.active = true;
  listenState.playing = true;
  listenState.queue = queue;
  listenState.index = 0;
  listenState.speed = Number(speed) || 1.0;
  listenState.intervalMs = Number(intervalMs) || 1400;
  listenState.loop = Boolean(loop);
  listenState.utteranceToken++;

  $("#listenOverlay")?.classList.remove("hidden");
  renderListenStep(true);
}

function closeListenOverlay() {
  listenState.active = false;
  listenState.playing = false;
  listenState.utteranceToken++;
  clearTimeout(listenState.timerId);
  if ("speechSynthesis" in window) {
    try { window.speechSynthesis.cancel(); } catch (_) {}
  }
  $("#listenOverlay")?.classList.add("hidden");
}

function renderListenStep(triggerAudio = true) {
  if (!listenState.active) return;
  const item = listenState.queue[listenState.index];
  if (!item) return;

  const total = listenState.queue.length;
  const idx = listenState.index;
  const lv = Number(state.levels?.[item.no] || 0);
  const exList = examplesMap.get(item.no) || [];
  const ex = exList[0] || null;

  const counterEl = $("#listenCounter");
  const progBar = $("#listenProgressBar");
  const noEl = $("#listenNo");
  const phaseEl = $("#listenPhaseBadge");
  const posEl = $("#listenPos");
  const jaEl = $("#listenJa");
  const enEl = $("#listenEn");
  const phEl = $("#listenPhonetic");
  const exEl = $("#listenExample");
  const playPauseBtn = $("#btnListenPlayPause");
  const speedBtn = $("#btnListenSpeedQuick");
  const loopBtn = $("#btnListenLoopQuick");

  if (counterEl) counterEl.textContent = `${idx + 1} / ${total}`;
  if (progBar) progBar.style.width = `${((idx + 1) / total) * 100}%`;
  if (noEl) noEl.textContent = `No. ${item.no}`;
  if (phaseEl) phaseEl.textContent = listenState.playing ? `再生中 (${(listenState.intervalMs / 1000).toFixed(1)}秒間隔)` : "一時停止中";
  if (posEl) {
    posEl.textContent = item.pos || "語彙";
    posEl.classList.toggle("hidden", !item.pos);
  }
  if (jaEl) jaEl.textContent = item.meanings.join(" ／ ");
  if (enEl) enEl.textContent = item.word;
  if (phEl) {
    phEl.textContent = item.phonetic || "";
    phEl.classList.toggle("hidden", !item.phonetic);
  }
  if (exEl) {
    if (ex) {
      exEl.innerHTML = `${formatExampleHighlightedHtml(ex.rawEn)}${ex.ja ? `<br><span style="font-size:0.84rem;opacity:0.88;">${escapeHtml(ex.ja)}</span>` : ""}`;
      exEl.classList.remove("hidden");
    } else {
      exEl.innerHTML = "";
      exEl.classList.add("hidden");
    }
  }

  if (playPauseBtn) playPauseBtn.textContent = listenState.playing ? "一時停止" : "再生";
  if (speedBtn) speedBtn.textContent = `速度: ${listenState.speed.toFixed(1)}x`;
  if (loopBtn) loopBtn.textContent = `リピート: ${listenState.loop ? "ON" : "OFF"}`;

  $$("[data-listen-rate]").forEach((btn) => {
    btn.classList.toggle("selected", Number(btn.dataset.listenRate) === lv);
  });

  clearTimeout(listenState.timerId);
  if (triggerAudio && listenState.playing) {
    const myToken = ++listenState.utteranceToken;
    speakEnglish(item.word, listenState.speed, () => {
      if (!listenState.active || !listenState.playing || listenState.utteranceToken !== myToken) return;
      listenState.timerId = setTimeout(() => {
        if (!listenState.active || !listenState.playing || listenState.utteranceToken !== myToken) return;
        if (listenState.index + 1 < listenState.queue.length) {
          listenState.index++;
          renderListenStep(true);
        } else if (listenState.loop) {
          listenState.index = 0;
          renderListenStep(true);
        } else {
          listenState.playing = false;
          renderListenStep(false);
          showToast("リスニングが完了しました");
        }
      }, listenState.intervalMs);
    });
  }
}

/* =========================================================
   学習画面（モード選択・セットアップ・フラッシュカード・確認テスト）
   ========================================================= */
function openStudyPicker() {
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.add("hidden");
  $("#studyPickerPanel")?.classList.remove("hidden");
}

function openStudySetupForMode(mode) {
  const sMin = $("#studyMin");
  const sMax = $("#studyMax");
  if (sMin && !sMin.dataset.touched) sMin.value = prefs.goalMin || 1;
  if (sMax && !sMax.dataset.touched) sMax.value = prefs.goalMax || 100;

  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.remove("hidden");
  setStudyModeTab(mode);
}

function updateQuizLayoutRowVisibility() {
  const fmt = $("#quizFormatSelect")?.value || "spell";
  $("#quizLayoutRow")?.classList.toggle("hidden", fmt === "spell");
}

function setStudyModeTab(mode) {
  currentStudyMode = mode;
  $("#fcOptions")?.classList.toggle("hidden", mode !== "flashcard");
  $("#quizOptions")?.classList.toggle("hidden", mode !== "quiz");
  $("#listenOptions")?.classList.toggle("hidden", mode !== "listen");

  const setupTitle = $("#studySetupTitle");
  const startBtn = $("#btnStartStudy");
  if (mode === "quiz") {
    if (setupTitle) setupTitle.textContent = "確認テストの設定";
    if (startBtn) startBtn.textContent = "確認テストをはじめる";
    updateQuizLayoutRowVisibility();
  } else if (mode === "listen") {
    if (setupTitle) setupTitle.textContent = "リスニングの設定";
    if (startBtn) startBtn.textContent = "リスニングをはじめる";
  } else {
    if (setupTitle) setupTitle.textContent = "フラッシュカードの設定";
    if (startBtn) startBtn.textContent = "フラッシュカードをはじめる";
  }
}

function exitStudyStages() {
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.remove("hidden");
}

function buildStudyCandidates() {
  const rawMin = Number($("#studyMin")?.value || 1);
  const rawMax = Number($("#studyMax")?.value || 100);
  const s = Math.min(rawMin, rawMax);
  const e = Math.max(rawMin, rawMax);
  const lvFilter = $("#studyLevelSelect")?.value || "all";
  const order = $("#studyOrderSelect")?.value || "seq";

  let list = wordsData.filter((w) => {
    if (w.no < s || w.no > e) return false;
    const lv = Number(state.levels?.[w.no] || 0);
    if (lvFilter === "all") return true;
    if (lvFilter === "unmastered") return lv < 3;
    if (lvFilter === "weak") return lv === 1 || lv === 2;
    return lv === Number(lvFilter);
  });

  if (order === "random") list = shuffleArray(list);
  return list;
}

function startSelectedStudyMode() {
  const candidates = buildStudyCandidates();
  if (!candidates.length) {
    showToast("条件に一致する単語がありません");
    return;
  }

  if (currentStudyMode === "listen") {
    const speed = Number($("#listenSpeedSelect")?.value || 1.0);
    const intervalMs = Number($("#listenIntervalSelect")?.value || 1400);
    const loop = Boolean($("#listenLoopCheck")?.checked);
    startListenOverlay(candidates, speed, intervalMs, loop);
    return;
  }

  if (currentStudyMode === "flashcard") {
    fcQueue = candidates;
    fcIndex = 0;
    fcFlipped = false;
    fcFormat = $("#fcFormatSelect")?.value || "en-ja";
    $("#studyPickerPanel")?.classList.add("hidden");
    $("#studySetupPanel")?.classList.add("hidden");
    $("#quizStage")?.classList.add("hidden");
    $("#flashcardStage")?.classList.remove("hidden");
    renderFlashcard(true);
    return;
  }

  if (currentStudyMode === "quiz") {
    const limit = Math.max(1, Number($("#quizLimitInput")?.value || 20));
    quizQueue = candidates.slice(0, limit);
    quizIndex = 0;
    quizFormat = $("#quizFormatSelect")?.value || "spell";
    quizLayout = quizFormat === "spell" ? "single" : ($("#quizLayoutSelect")?.value || "single");
    quizAnswers = {};
    quizListRevealed = false;
    quizIsRetest = false;
    openQuizStage();
  }
}

/* ---------- フラッシュカード ---------- */
function renderFlashcard(allowAutoSpeak = false) {
  const item = fcQueue[fcIndex];
  if (!item) return;

  const lv = Number(state.levels?.[item.no] || 0);
  const exList = examplesMap.get(item.no) || [];
  const ex = exList[0] || null;

  const counterEl = $("#fcCounter");
  const progEl = $("#fcProgressBar");
  if (counterEl) counterEl.textContent = `${fcIndex + 1} / ${fcQueue.length}`;
  if (progEl) progEl.style.width = `${((fcIndex + 1) / fcQueue.length) * 100}%`;

  const dotFront = $("#fcDotFront");
  if (dotFront) dotFront.className = `dot lv-${lv}`;
  if ($("#fcNoFront")) $("#fcNoFront").textContent = `No. ${item.no}`;
  if ($("#fcNoBack")) $("#fcNoBack").textContent = `No. ${item.no}`;

  const wordFront = $("#fcWordFront");
  const hintFront = $("#fcHintFront");
  if (wordFront) {
    if (fcFormat === "ja-en") {
      wordFront.textContent = item.meanings.join(" ／ ");
      wordFront.classList.add("is-ja");
      if (hintFront) hintFront.textContent = "タップで英単語を表示";
    } else if (fcFormat === "example" && ex) {
      wordFront.innerHTML = formatExampleClozeHtml(ex.rawEn, item.word);
      wordFront.classList.add("is-ja");
      if (hintFront) hintFront.textContent = "タップで解答を表示";
    } else {
      wordFront.textContent = item.word;
      wordFront.classList.remove("is-ja");
      if (hintFront) hintFront.textContent = "タップで意味を表示";
    }
  }

  if ($("#fcWordBack")) $("#fcWordBack").textContent = item.word;
  if ($("#fcPhoneticBack")) $("#fcPhoneticBack").textContent = item.phonetic || "";
  const posBack = $("#fcPosBack");
  if (posBack) {
    posBack.textContent = item.pos || "";
    posBack.classList.toggle("hidden", !item.pos);
  }
  if ($("#fcMeaningBack")) $("#fcMeaningBack").textContent = item.meanings.join(" ／ ");
  const noteBack = $("#fcNoteBack");
  if (noteBack) {
    noteBack.textContent = item.note || "";
    noteBack.classList.toggle("hidden", !item.note);
  }
  const exBack = $("#fcExampleBack");
  if (exBack) {
    if (ex) {
      exBack.innerHTML = `${formatExampleHighlightedHtml(ex.rawEn)}${ex.ja ? `<br>${escapeHtml(ex.ja)}` : ""}`;
      exBack.classList.remove("hidden");
    } else {
      exBack.innerHTML = "";
      exBack.classList.add("hidden");
    }
  }

  $("#fcFront")?.classList.toggle("hidden", fcFlipped);
  $("#fcBack")?.classList.toggle("hidden", !fcFlipped);

  $$("#fcBack [data-rate]").forEach((btn) => {
    btn.classList.toggle("selected", Number(btn.dataset.rate) === lv);
  });

  const nextBtn = $("#fcNextBtn");
  if (nextBtn) {
    nextBtn.textContent = fcIndex + 1 >= fcQueue.length ? "完了する" : "次へ";
  }

  if (allowAutoSpeak && prefs.autoAudio && fcFormat === "en-ja" && !fcFlipped) {
    speakEnglish(item.word);
  }
}

/* ---------- 小テスト（1問ずつ＆紙テスト向け一覧形式） ---------- */
function getQuizPromptAndAnswer(item, format) {
  const ex = (examplesMap.get(item.no) || [])[0] || null;
  if (format === "ja-en") {
    return {
      promptHtml: escapeHtml(item.meanings.join(" ／ ")),
      answerMain: item.word,
      answerSub: `${item.pos ? `[${item.pos}] ` : ""}${item.meanings.join(" ／ ")}`
    };
  }
  if (format === "example" && ex) {
    return {
      promptHtml: `${formatExampleClozeHtml(ex.rawEn, item.word)}${ex.ja ? `<div style="font-size:0.84rem;color:var(--text-sub);margin-top:6px;">${escapeHtml(ex.ja)}</div>` : ""}`,
      answerMain: item.word,
      answerSub: item.meanings.join(" ／ ")
    };
  }
  return {
    promptHtml: escapeHtml(item.word),
    answerMain: item.meanings.join(" ／ "),
    answerSub: `${item.pos ? `[${item.pos}] ` : ""}${ex ? ex.en : ""}`
  };
}

function openQuizStage() {
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.add("hidden");
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.remove("hidden");
  $("#quizResultBox")?.classList.add("hidden");
  $("#quizRetestBadge")?.classList.toggle("hidden", !quizIsRetest);

  if (quizFormat === "spell") {
    $("#quizSingleBox")?.classList.add("hidden");
    $("#quizListBox")?.classList.add("hidden");
    $("#quizProgressWrap")?.classList.remove("hidden");
    $("#quizSpellBox")?.classList.remove("hidden");
    renderSpellQuestion();
  } else if (quizLayout === "list") {
    $("#quizSpellBox")?.classList.add("hidden");
    $("#quizSingleBox")?.classList.add("hidden");
    $("#quizProgressWrap")?.classList.add("hidden");
    $("#quizListBox")?.classList.remove("hidden");
    renderQuizListMode();
  } else {
    $("#quizSpellBox")?.classList.add("hidden");
    $("#quizListBox")?.classList.add("hidden");
    $("#quizProgressWrap")?.classList.remove("hidden");
    $("#quizSingleBox")?.classList.remove("hidden");
    renderQuizSingleQuestion();
  }
}

/* ---------- スペル入力テスト（アプリ内専用QWERTYキーボード） ---------- */
function buildSpellTargetSpec(rawWord) {
  let cleaned = String(rawWord || "").replace(/～/g, "").trim();
  const variants = new Set();
  if (/\([a-zA-Z]+\)/.test(cleaned)) {
    const withoutOpt = cleaned.replace(/\([a-zA-Z]+\)/g, "").trim();
    const withOpt = cleaned.replace(/[()]/g, "").trim();
    variants.add(withoutOpt.replace(/[^a-zA-Z]/g, "").toLowerCase());
    variants.add(withOpt.replace(/[^a-zA-Z]/g, "").toLowerCase());
    cleaned = withoutOpt;
  } else {
    variants.add(cleaned.replace(/[^a-zA-Z]/g, "").toLowerCase());
  }

  const tokens = [];
  for (const ch of cleaned) {
    if (/[a-zA-Z]/.test(ch)) {
      tokens.push({ type: "char", expected: ch.toLowerCase() });
    } else if (ch === "-" || ch === " ") {
      tokens.push({ type: "sep", char: ch });
    }
  }
  return { tokens, accepted: Array.from(variants).filter(Boolean) };
}

function renderSpellQuestion() {
  const item = quizQueue[quizIndex];
  if (!item) return;

  const spec = buildSpellTargetSpec(item.word);
  spellTargetTokens = spec.tokens;
  spellAcceptedWords = spec.accepted;
  spellTypedChars = [];
  spellJudged = false;

  if ($("#quizMetaText")) $("#quizMetaText").textContent = `問題 ${quizIndex + 1} / ${quizQueue.length}`;
  if ($("#quizProgressBar")) $("#quizProgressBar").style.width = `${((quizIndex + 1) / quizQueue.length) * 100}%`;
  if ($("#qSpellNo")) $("#qSpellNo").textContent = `No. ${item.no}`;

  const posEl = $("#qSpellPos");
  if (posEl) {
    posEl.textContent = item.pos || "";
    posEl.classList.toggle("hidden", !item.pos);
  }
  if ($("#qSpellMeaning")) $("#qSpellMeaning").textContent = item.meanings.join(" ／ ");

  $("#qSpellAudio")?.classList.add("hidden");
  $("#qSpellFeedback")?.classList.add("hidden");
  $("#qSpellActionRow")?.classList.remove("hidden");
  $("#qSpellKeyboard")?.classList.remove("hidden");

  renderSpellSlots();
}

function renderSpellSlots(markResult = null) {
  const wrap = $("#qSpellSlots");
  if (!wrap) return;
  let charIdx = 0;
  const activeIdx = spellTypedChars.length;

  wrap.innerHTML = spellTargetTokens.map((tk) => {
    if (tk.type === "sep") {
      if (tk.char === " ") return `<span class="spell-sep is-space"></span>`;
      return `<span class="spell-sep">${escapeHtml(tk.char)}</span>`;
    }
    const myIdx = charIdx++;
    const typed = spellTypedChars[myIdx] || "";
    let cls = "spell-slot";
    if (markResult === true) cls += " is-correct";
    else if (markResult === false) cls += " is-wrong";
    else if (!spellJudged && myIdx === activeIdx) cls += " is-active";
    return `<span class="${cls}">${escapeHtml(typed)}</span>`;
  }).join("");
}

function handleSpellKeyInput(ch) {
  if (spellJudged) return;
  const maxLen = spellTargetTokens.filter((t) => t.type === "char").length;
  if (spellTypedChars.length >= maxLen) return;
  spellTypedChars.push(ch.toLowerCase());
  renderSpellSlots();
}

function handleSpellBackspace() {
  if (spellJudged || !spellTypedChars.length) return;
  spellTypedChars.pop();
  renderSpellSlots();
}

function handleSpellHint() {
  if (spellJudged) return;
  const expectedChars = spellTargetTokens.filter((t) => t.type === "char").map((t) => t.expected);
  const idx = spellTypedChars.length;
  if (idx < expectedChars.length) {
    spellTypedChars.push(expectedChars[idx]);
    renderSpellSlots();
  }
}

function evaluateSpellSubmission(giveUp = false) {
  if (spellJudged) return;
  const item = quizQueue[quizIndex];
  if (!item) return;

  const typedWord = spellTypedChars.join("").toLowerCase();
  if (!giveUp && typedWord.length === 0) {
    showToast("アルファベットを入力してください");
    return;
  }

  spellJudged = true;
  const isCorrect = !giveUp && spellAcceptedWords.includes(typedWord);
  const curLv = Number(state.levels?.[item.no] || 0);
  const nextLv = isCorrect ? (curLv >= 2 ? 3 : 2) : 1;

  quizAnswers[item.no] = { correct: isCorrect, level: nextLv };
  setWordLevel(item.no, nextLv);

  renderSpellSlots(isCorrect);
  $("#qSpellActionRow")?.classList.add("hidden");
  $("#qSpellKeyboard")?.classList.add("hidden");
  $("#qSpellAudio")?.classList.remove("hidden");
  $("#qSpellFeedback")?.classList.remove("hidden");

  const badge = $("#qSpellJudgeBadge");
  if (badge) {
    badge.textContent = isCorrect ? "○ 正解！" : "× 不正解";
    badge.className = `spell-judge-badge ${isCorrect ? "ok" : "ng"}`;
  }
  const corrEl = $("#qSpellCorrectWord");
  if (corrEl) {
    corrEl.textContent = `正解: ${item.word}`;
  }

  $$("[data-spell-lv]").forEach((btn) => {
    btn.classList.toggle("selected", Number(btn.dataset.spellLv) === nextLv);
  });

  const nextBtn = $("#qSpellNextBtn");
  if (nextBtn) {
    nextBtn.textContent = quizIndex + 1 >= quizQueue.length ? "結果を見る" : "次の問題へ";
  }

  if (prefs.autoAudio) {
    speakEnglish(item.word);
  }
}

function advanceSpellQuestion() {
  if (quizIndex + 1 < quizQueue.length) {
    quizIndex++;
    renderSpellQuestion();
  } else {
    showQuizResults();
  }
}

function renderQuizSingleQuestion() {
  const item = quizQueue[quizIndex];
  if (!item) return;

  const metaEl = $("#quizMetaText");
  const progEl = $("#quizProgressBar");
  if (metaEl) metaEl.textContent = `問題 ${quizIndex + 1} / ${quizQueue.length}`;
  if (progEl) progEl.style.width = `${((quizIndex + 1) / quizQueue.length) * 100}%`;

  if ($("#qSingleNo")) $("#qSingleNo").textContent = `No. ${item.no}`;
  const qa = getQuizPromptAndAnswer(item, quizFormat);
  if ($("#qSinglePrompt")) $("#qSinglePrompt").innerHTML = qa.promptHtml;
  if ($("#qSingleAnswerMain")) $("#qSingleAnswerMain").textContent = qa.answerMain;
  if ($("#qSingleAnswerSub")) $("#qSingleAnswerSub").textContent = qa.answerSub;

  $("#qBtnReveal")?.classList.remove("hidden");
  $("#qSingleAnswerArea")?.classList.add("hidden");
  $("#qManualPanel")?.classList.add("hidden");
  $$("[data-q-override]").forEach((b) => b.classList.remove("selected"));
}

function recordSingleQuizJudge(isCorrect, overrideLv = null) {
  const item = quizQueue[quizIndex];
  if (!item) return;
  const curLv = Number(state.levels?.[item.no] || 0);
  const nextLv = overrideLv !== null ? overrideLv : (isCorrect ? (curLv >= 2 ? 3 : 2) : 1);
  quizAnswers[item.no] = { correct: isCorrect, level: nextLv };
  setWordLevel(item.no, nextLv);

  if (quizIndex + 1 < quizQueue.length) {
    quizIndex++;
    renderQuizSingleQuestion();
  } else {
    showQuizResults();
  }
}

function renderQuizListMode() {
  const metaEl = $("#quizMetaText");
  if (metaEl) metaEl.textContent = `一覧形式（全 ${quizQueue.length} 問）`;

  const toggleBtn = $("#qListToggleAns");
  const finishBtn = $("#qListFinishBtn");
  if (toggleBtn) toggleBtn.textContent = quizListRevealed ? "解答を隠す" : "解答を表示して採点";
  finishBtn?.classList.toggle("hidden", !quizListRevealed);

  const wrap = $("#quizListItems");
  if (!wrap) return;

  const speakerIcon = `<svg viewBox="0 0 24 24" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"></polygon><path d="M15.54 8.46a5 5 0 0 1 0 7.07"></path></svg>`;

  wrap.innerHTML = quizQueue.map((item, idx) => {
    const qa = getQuizPromptAndAnswer(item, quizFormat);
    const ansState = quizAnswers[item.no];
    return `
      <div class="glass-card quiz-list-row" data-qno="${item.no}">
        <div class="fc-top-bar">
          <span class="fc-no">問${idx + 1}（No.${item.no}）${item.pos ? ` [${escapeHtml(item.pos)}]` : ""}</span>
          <button type="button" class="audio-pill" data-qlist-speak="${escapeHtml(item.word)}">${speakerIcon}<span>発音</span></button>
        </div>
        <div class="quiz-list-q">${qa.promptHtml}</div>
        ${quizListRevealed ? `
          <div class="ql-answer">
            <strong>${escapeHtml(qa.answerMain)}</strong>
            ${qa.answerSub ? `<div style="font-size:0.8rem;opacity:0.82;margin-top:2px;">${escapeHtml(qa.answerSub)}</div>` : ""}
          </div>
          <div class="ql-ox">
            <button type="button" class="ox-btn wrong${ansState?.correct === false ? " selected" : ""}" data-qlist-ox="wrong" data-no="${item.no}">× 不正解</button>
            <button type="button" class="ox-btn correct${ansState?.correct === true ? " selected" : ""}" data-qlist-ox="correct" data-no="${item.no}">○ 正解</button>
          </div>
          <div class="listen-rate-row" style="margin-top:6px;">
            <button type="button" class="rate-btn lv-1-btn${ansState?.level === 1 ? " selected" : ""}" data-qlist-lv="1" data-no="${item.no}">苦手</button>
            <button type="button" class="rate-btn lv-2-btn${ansState?.level === 2 ? " selected" : ""}" data-qlist-lv="2" data-no="${item.no}">うろ覚え</button>
            <button type="button" class="rate-btn lv-3-btn${ansState?.level === 3 ? " selected" : ""}" data-qlist-lv="3" data-no="${item.no}">定着</button>
          </div>
        ` : ""}
      </div>
    `;
  }).join("");

  wrap.querySelectorAll("[data-qlist-speak]").forEach((btn) => {
    btn.addEventListener("click", () => speakEnglish(btn.dataset.qlistSpeak || ""));
  });

  wrap.querySelectorAll("[data-qlist-ox]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const no = Number(btn.dataset.no);
      const isOk = btn.dataset.qlistOx === "correct";
      quizAnswers[no] = { correct: isOk, level: isOk ? 3 : 1 };
      renderQuizListMode();
    });
  });

  wrap.querySelectorAll("[data-qlist-lv]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const no = Number(btn.dataset.no);
      const lv = Number(btn.dataset.qlistLv);
      quizAnswers[no] = { correct: lv >= 2, level: lv };
      renderQuizListMode();
    });
  });
}

function finalizeQuizListScoring() {
  quizQueue.forEach((item) => {
    const entry = quizAnswers[item.no];
    if (entry) {
      setWordLevel(item.no, entry.level);
    } else {
      quizAnswers[item.no] = { correct: false, level: Number(state.levels?.[item.no] || 0) };
    }
  });
  showQuizResults();
}

function showQuizResults() {
  $("#quizSpellBox")?.classList.add("hidden");
  $("#quizSingleBox")?.classList.add("hidden");
  $("#quizListBox")?.classList.add("hidden");
  $("#quizProgressWrap")?.classList.add("hidden");
  $("#quizResultBox")?.classList.remove("hidden");

  const total = quizQueue.length;
  const correctCount = quizQueue.filter((item) => quizAnswers[item.no]?.correct).length;
  const wrongItems = quizQueue.filter((item) => !quizAnswers[item.no]?.correct);

  if ($("#quizResultScore")) $("#quizResultScore").textContent = `${correctCount} / ${total} 正解`;
  if ($("#quizResultNote")) {
    const pct = Math.round((correctCount / Math.max(1, total)) * 100);
    $("#quizResultNote").textContent = `正答率 ${pct}% ・ 記録に反映しました`;
  }

  const retestBtn = $("#qResultRetestBtn");
  if (retestBtn) {
    retestBtn.classList.toggle("hidden", wrongItems.length === 0);
  }
}

/* =========================================================
   交流画面（リアルタイム合言葉対戦 ＆ フレンド共有）
   ========================================================= */
function renderBattleFriendView() {
  updateSyncUi();
  renderFriendsList();
}

function buildBattleQuestions(minNo, maxNo, count, format) {
  const s = Math.min(minNo, maxNo);
  const e = Math.max(minNo, maxNo);
  const pool = wordsData.filter((w) => w.no >= s && w.no <= e);
  const source = pool.length >= 4 ? pool : wordsData;
  const picked = shuffleArray(source).slice(0, count);

  return picked.map((target) => {
    const distractors = shuffleArray(source.filter((w) => w.no !== target.no)).slice(0, 3);
    const options = shuffleArray([target, ...distractors]).map((opt) => ({
      no: opt.no,
      label: format === "ja-en" ? opt.word : opt.meanings[0] || opt.rawMeaning
    }));
    return {
      no: target.no,
      prompt: format === "ja-en" ? target.meanings.join(" ／ ") : target.word,
      answerNo: target.no,
      options
    };
  });
}

function myPlayerId() {
  return currentUser?.uid || `local_${state.friendId}`;
}

function myPlayerName() {
  return state.nickname || state.loginId || "プレイヤー";
}

async function createBattleRoomAction() {
  const minNo = Number($("#battleMin")?.value || 1);
  const maxNo = Number($("#battleMax")?.value || 100);
  const count = Number($("#battleCount")?.value || 10);
  const format = $("#battleFormat")?.value || "en-ja";
  const questions = buildBattleQuestions(minNo, maxNo, count, format);
  if (!questions.length) {
    showToast("問題を作成できませんでした");
    return;
  }

  const code = generateCode(6);
  const pid = myPlayerId();
  const players = {
    [pid]: { name: myPlayerName(), score: 0 }
  };

  battleSession = {
    roomCode: code,
    isHost: true,
    localOnly: !(firebaseReady && db && currentUser),
    format,
    questions,
    currentIndex: 0,
    answeredCurrent: false,
    timeLeft: 10,
    players
  };

  if (!battleSession.localOnly) {
    try {
      await setDoc(doc(db, "battleRooms", code), {
        roomCode: code,
        hostId: pid,
        status: "waiting",
        minNo,
        maxNo,
        count,
        format,
        questions,
        players,
        createdAt: serverTimestamp()
      });
      subscribeBattleRoom(code);
    } catch (_) {
      battleSession.localOnly = true;
    }
  }

  showBattleWaitingRoom(minNo, maxNo, count, format);
}

async function joinBattleRoomAction() {
  const code = ($("#battleJoinCodeInput")?.value || "").trim().toUpperCase();
  if (!code) {
    showToast("合言葉を入力してください");
    return;
  }
  if (!firebaseReady || !db || !currentUser) {
    showToast("合言葉参加にはログインが必要です");
    return;
  }

  try {
    const ref = doc(db, "battleRooms", code);
    const snap = await getDoc(ref);
    if (!snap.exists()) {
      showToast("ルームが見つかりません");
      return;
    }
    const data = snap.data();
    const pid = myPlayerId();
    const updatedPlayers = {
      ...(data.players || {}),
      [pid]: { name: myPlayerName(), score: data.players?.[pid]?.score || 0 }
    };
    await updateDoc(ref, { players: updatedPlayers });

    battleSession = {
      roomCode: code,
      isHost: data.hostId === pid,
      localOnly: false,
      format: data.format || "en-ja",
      questions: data.questions || [],
      currentIndex: 0,
      answeredCurrent: false,
      timeLeft: 10,
      players: updatedPlayers
    };

    showBattleWaitingRoom(data.minNo || 1, data.maxNo || 100, data.count || 10, data.format || "en-ja");
    subscribeBattleRoom(code);
  } catch (err) {
    showToast("ルーム参加に失敗しました");
  }
}

function subscribeBattleRoom(code) {
  if (battleRoomUnsub) { battleRoomUnsub(); battleRoomUnsub = null; }
  if (!firebaseReady || !db) return;
  battleRoomUnsub = onSnapshot(doc(db, "battleRooms", code), (snap) => {
    if (!snap.exists()) return;
    const data = snap.data();
    battleSession.players = data.players || battleSession.players;
    battleSession.questions = data.questions || battleSession.questions;
    renderWaitingPlayers();
    renderBattleScoreboard();

    if (data.status === "playing" && $("#battlePlayStage")?.classList.contains("hidden") && $("#battleResultBox")?.classList.contains("hidden")) {
      beginBattlePlayLoop();
    }
    if (!$("#battleResultBox")?.classList.contains("hidden")) {
      renderBattleResults();
    }
  });
}

function showBattleWaitingRoom(minNo, maxNo, count, format) {
  $("#battleLobby")?.classList.add("hidden");
  $("#battlePlayStage")?.classList.add("hidden");
  $("#battleResultBox")?.classList.add("hidden");
  $("#battleWaitingRoom")?.classList.remove("hidden");

  if ($("#battleRoomCodeDisplay")) $("#battleRoomCodeDisplay").textContent = battleSession.roomCode;
  if ($("#battleRoomMeta")) {
    const fmtLabel = format === "ja-en" ? "日本語 → 英語" : "英語 → 日本語";
    const modeNote = battleSession.localOnly ? "（一人練習モード）" : "";
    $("#battleRoomMeta").textContent = `範囲 No.${minNo}〜${maxNo} ／ ${count}問 ／ ${fmtLabel} ${modeNote}`;
  }

  $("#btnStartBattleMatch")?.classList.toggle("hidden", !battleSession.isHost);
  $("#battleWaitHint")?.classList.toggle("hidden", battleSession.isHost);
  renderWaitingPlayers();
}

function renderWaitingPlayers() {
  const wrap = $("#battlePlayersList");
  if (!wrap) return;
  const entries = Object.values(battleSession.players || {});
  wrap.innerHTML = entries.map((p) => `
    <div class="battle-player-row">
      <span>${escapeHtml(p.name)}</span>
      <span class="sub-label">参加準備OK</span>
    </div>
  `).join("");
}

async function hostStartBattleMatch() {
  if (!battleSession.localOnly && firebaseReady && db) {
    try {
      await updateDoc(doc(db, "battleRooms", battleSession.roomCode), { status: "playing" });
    } catch (_) {}
  }
  beginBattlePlayLoop();
}

function beginBattlePlayLoop() {
  $("#battleWaitingRoom")?.classList.add("hidden");
  $("#battleLobby")?.classList.add("hidden");
  $("#battleResultBox")?.classList.add("hidden");
  $("#battlePlayStage")?.classList.remove("hidden");
  battleSession.currentIndex = 0;
  renderBattleQuestion();
}

function renderBattleScoreboard() {
  const board = $("#battleScoreboard");
  if (!board) return;
  board.innerHTML = Object.values(battleSession.players || {})
    .map((p) => `<span class="battle-score-chip">${escapeHtml(p.name)}: ${p.score || 0}pt</span>`)
    .join("");
}

function renderBattleQuestion() {
  clearInterval(battleTimerId);
  const q = battleSession.questions[battleSession.currentIndex];
  if (!q) {
    finishBattleMatch();
    return;
  }

  battleSession.answeredCurrent = false;
  battleSession.timeLeft = 10;

  renderBattleScoreboard();
  if ($("#battleQCounter")) $("#battleQCounter").textContent = `${battleSession.currentIndex + 1} / ${battleSession.questions.length}`;
  if ($("#battleQNo")) $("#battleQNo").textContent = `No. ${q.no}`;
  if ($("#battlePrompt")) $("#battlePrompt").textContent = q.prompt;
  if ($("#battleTimerText")) $("#battleTimerText").textContent = "10秒";
  if ($("#battleTimerBar")) $("#battleTimerBar").style.width = "100%";

  const choicesWrap = $("#battleChoices");
  if (choicesWrap) {
    choicesWrap.innerHTML = q.options.map((opt) => `
      <button type="button" class="battle-choice-btn" data-choice-no="${opt.no}">
        ${escapeHtml(opt.label)}
      </button>
    `).join("");

    choicesWrap.querySelectorAll(".battle-choice-btn").forEach((btn) => {
      btn.addEventListener("click", () => handleBattleChoice(Number(btn.dataset.choiceNo), btn));
    });
  }

  battleTimerId = setInterval(() => {
    battleSession.timeLeft = Math.max(0, battleSession.timeLeft - 1);
    if ($("#battleTimerText")) $("#battleTimerText").textContent = `${battleSession.timeLeft}秒`;
    if ($("#battleTimerBar")) $("#battleTimerBar").style.width = `${battleSession.timeLeft * 10}%`;
    if (battleSession.timeLeft <= 0) {
      clearInterval(battleTimerId);
      advanceBattleQuestion();
    }
  }, 1000);
}

async function handleBattleChoice(pickedNo, btnEl) {
  if (battleSession.answeredCurrent) return;
  battleSession.answeredCurrent = true;
  clearInterval(battleTimerId);

  const q = battleSession.questions[battleSession.currentIndex];
  const isCorrect = pickedNo === q.answerNo;
  const pid = myPlayerId();

  if (isCorrect) {
    btnEl.classList.add("is-correct");
    const bonus = 10 + Math.max(0, battleSession.timeLeft);
    const prev = battleSession.players[pid]?.score || 0;
    battleSession.players[pid] = { name: myPlayerName(), score: prev + bonus };

    if (!battleSession.localOnly && firebaseReady && db) {
      try {
        await updateDoc(doc(db, "battleRooms", battleSession.roomCode), {
          [`players.${pid}.score`]: prev + bonus,
          [`players.${pid}.name`]: myPlayerName()
        });
      } catch (_) {}
    }
  } else {
    btnEl.classList.add("is-wrong");
    $$("#battleChoices .battle-choice-btn").forEach((b) => {
      if (Number(b.dataset.choiceNo) === q.answerNo) b.classList.add("is-correct");
    });
  }

  renderBattleScoreboard();
  setTimeout(advanceBattleQuestion, 750);
}

function advanceBattleQuestion() {
  if (battleSession.currentIndex + 1 < battleSession.questions.length) {
    battleSession.currentIndex++;
    renderBattleQuestion();
  } else {
    finishBattleMatch();
  }
}

function finishBattleMatch() {
  clearInterval(battleTimerId);
  $("#battlePlayStage")?.classList.add("hidden");
  $("#battleResultBox")?.classList.remove("hidden");
  renderBattleResults();
}

function renderBattleResults() {
  const listEl = $("#battleResultList");
  if (!listEl) return;
  const sorted = Object.values(battleSession.players || {}).sort((a, b) => (b.score || 0) - (a.score || 0));
  listEl.innerHTML = sorted.map((p, i) => `
    <div class="battle-player-row">
      <span><strong style="margin-right:6px;">${i + 1}位</strong>${escapeHtml(p.name)}</span>
      <strong>${p.score || 0} pt</strong>
    </div>
  `).join("");
}

function leaveBattleRoom() {
  clearInterval(battleTimerId);
  if (battleRoomUnsub) { battleRoomUnsub(); battleRoomUnsub = null; }
  $("#battleWaitingRoom")?.classList.add("hidden");
  $("#battlePlayStage")?.classList.add("hidden");
  $("#battleResultBox")?.classList.add("hidden");
  $("#battleLobby")?.classList.remove("hidden");
}

/* ---------- フレンド機能 ---------- */
async function sendFriendRequestAction() {
  let targetCode = ($("#friendAddInput")?.value || "").trim().toUpperCase();
  if (!targetCode) {
    showToast("相手のフレンドIDを入力してください");
    return;
  }
  if (!targetCode.startsWith("HN-")) targetCode = `HN-${targetCode}`;

  if (targetCode === state.friendId) {
    showToast("自分のフレンドIDは登録できません");
    return;
  }
  if ((state.friends || []).some((f) => f.friendId === targetCode)) {
    showToast("すでにフレンド登録済みです");
    return;
  }

  if (firebaseReady && db && currentUser) {
    try {
      const q = query(collection(db, "users"), where("friendId", "==", targetCode));
      const snap = await getDocs(q);
      if (!snap.empty) {
        const friendDoc = snap.docs[0];
        const fData = friendDoc.data();
        await addDoc(collection(db, "friendRequests"), {
          fromUid: currentUser.uid,
          fromName: myPlayerName(),
          fromFriendId: state.friendId,
          toUid: friendDoc.id,
          status: "pending",
          createdAt: serverTimestamp()
        });
        state.friends.push({
          uid: friendDoc.id,
          nickname: fData.nickname || fData.loginId || targetCode,
          friendId: targetCode
        });
        saveLocalState(true);
        if ($("#friendAddInput")) $("#friendAddInput").value = "";
        renderFriendsList();
        showToast("フレンド申請を送信し、一覧に追加しました");
        return;
      }
    } catch (_) {}
  }

  state.friends.push({
    uid: "",
    nickname: `フレンド (${targetCode})`,
    friendId: targetCode
  });
  saveLocalState(true);
  if ($("#friendAddInput")) $("#friendAddInput").value = "";
  renderFriendsList();
  showToast("フレンドIDを登録しました");
}

function renderFriendRequests(reqs = []) {
  const card = $("#friendRequestsCard");
  const listEl = $("#friendRequestsList");
  if (!card || !listEl) return;
  if (!reqs.length) {
    card.classList.add("hidden");
    return;
  }
  card.classList.remove("hidden");
  listEl.innerHTML = reqs.map((r) => `
    <div class="friend-row">
      <div>
        <strong>${escapeHtml(r.fromName || "ユーザー")}</strong>
        <div class="sub-label">${escapeHtml(r.fromFriendId || "")}</div>
      </div>
      <button type="button" class="primary-btn" data-accept-req="${r.id}">承認</button>
    </div>
  `).join("");

  listEl.querySelectorAll("[data-accept-req]").forEach((btn) => {
    btn.addEventListener("click", async () => {
      const req = reqs.find((x) => x.id === btn.dataset.acceptReq);
      if (!req) return;
      if (!(state.friends || []).some((f) => f.friendId === req.fromFriendId)) {
        state.friends.push({
          uid: req.fromUid || "",
          nickname: req.fromName || req.fromFriendId,
          friendId: req.fromFriendId
        });
        saveLocalState(true);
      }
      if (firebaseReady && db) {
        try { await updateDoc(doc(db, "friendRequests", req.id), { status: "accepted" }); } catch (_) {}
      }
      renderFriendsList();
      showToast("フレンド申請を承認しました");
    });
  });
}

function renderFriendsList() {
  const listEl = $("#friendList");
  if (!listEl) return;
  const friends = state.friends || [];
  if (!friends.length) {
    listEl.innerHTML = `<p class="setting-desc" style="text-align:center;margin:8px 0;">フレンドがまだいません</p>`;
    return;
  }
  listEl.innerHTML = friends.map((f, idx) => `
    <button type="button" class="friend-row" data-friend-idx="${idx}" style="cursor:pointer;text-align:left;">
      <div>
        <strong>${escapeHtml(f.nickname || "フレンド")}</strong>
        <div class="sub-label">${escapeHtml(f.friendId || f.friendCode || "")}</div>
      </div>
      <span class="sub-label">進捗を見る ›</span>
    </button>
  `).join("");

  listEl.querySelectorAll("[data-friend-idx]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const friend = friends[Number(btn.dataset.friendIdx)];
      if (friend) openFriendDetailModal(friend);
    });
  });
}

async function openFriendDetailModal(friend) {
  selectedFriend = friend;
  const modal = $("#friendDetailModal");
  if (!modal) return;
  modal.classList.remove("hidden");

  let remoteData = null;
  if (firebaseReady && db) {
    try {
      if (friend.uid) {
        const snap = await getDoc(doc(db, "users", friend.uid));
        if (snap.exists()) remoteData = snap.data();
      } else if (friend.friendId) {
        const q = query(collection(db, "users"), where("friendId", "==", friend.friendId));
        const snap = await getDocs(q);
        if (!snap.empty) remoteData = snap.docs[0].data();
      }
    } catch (_) {}
  }

  const name = remoteData?.nickname || friend.nickname || "フレンド";
  const fid = remoteData?.friendId || friend.friendId || "HN-XXXXXX";
  const fLevels = remoteData?.levels || {};
  const todayCnt = remoteData?.studiedDate === todayKey() ? (remoteData?.studiedIdsToday?.length || 0) : 0;
  const streak = remoteData?.streakDays || 0;

  if ($("#fdName")) $("#fdName").textContent = name;
  if ($("#fdFriendId")) $("#fdFriendId").textContent = fid;
  if ($("#fdTodayCount")) $("#fdTodayCount").textContent = `${todayCnt} 語`;
  if ($("#fdStreakDays")) $("#fdStreakDays").textContent = `${streak} 日`;

  let lv0 = 0, lv1 = 0, lv2 = 0, lv3 = 0;
  wordsData.forEach((w) => {
    const lv = Number(fLevels[w.no] || 0);
    if (lv === 3) lv3++;
    else if (lv === 2) lv2++;
    else if (lv === 1) lv1++;
    else lv0++;
  });
  const total = wordsData.length;
  const pct = total > 0 ? Math.round((lv3 / total) * 100) : 0;
  renderDonutAndLegend("#friendDonutSvg", "#friendMasteryPct", "#friendLegend", { total, lv0, lv1, lv2, lv3, pct });
  renderUnitBarsInto("#friendUnitBars", fLevels);
}

/* =========================================================
   設定画面の同期＆反映
   ========================================================= */
function renderSettingsView() {
  updateSyncUi();
  if ($("#setDisplayNameInput")) $("#setDisplayNameInput").value = state.nickname || "";
  if ($("#setGoalMin")) $("#setGoalMin").value = prefs.goalMin || 1;
  if ($("#setGoalMax")) $("#setGoalMax").value = prefs.goalMax || 100;
  if ($("#setVoiceAccent")) $("#setVoiceAccent").value = prefs.voiceAccent || "en-US";
  if ($("#setAutoAudio")) $("#setAutoAudio").checked = Boolean(prefs.autoAudio);
  if ($("#setKeepPosOnRed")) $("#setKeepPosOnRed").checked = Boolean(prefs.keepPosOnRed);
  if ($("#setFontSize")) $("#setFontSize").value = prefs.fontSize || "md";
  if ($("#setFontFamily")) $("#setFontFamily").value = prefs.fontFamily || "sans";
  if ($("#setTheme")) $("#setTheme").value = prefs.theme || "mist";
}

function renderAll() {
  updateSyncUi();
  renderHomeView();
  if (activeTab === "vocab") renderVocabView();
  if (activeTab === "progress") renderProgressView();
  if (activeTab === "battle") renderBattleFriendView();
  if (activeTab === "settings") renderSettingsView();
}

/* =========================================================
   イベントリスナー登録
   ========================================================= */
function bindEvents() {
  // スプラッシュ開始ボタン
  $("#btnSplashStart")?.addEventListener("click", () => {
    const splash = $("#splashScreen");
    if (splash) {
      splash.classList.add("fade-out");
      setTimeout(() => splash.classList.add("hidden"), 280);
    }
    const isGuest = localStorage.getItem(STORAGE_KEYS.GUEST_MODE) === "1";
    if (!currentUser && firebaseReady && !isGuest) {
      $("#authGate")?.classList.remove("hidden");
    } else if (currentUser) {
      maybePromptRecoveryEmail();
    }
  });

  // 認証ゲート
  $("#btnGateGuest")?.addEventListener("click", () => {
    try { localStorage.setItem(STORAGE_KEYS.GUEST_MODE, "1"); } catch (_) {}
    $("#authGate")?.classList.add("hidden");
    showToast("ゲスト利用で開始しました");
  });

  $("#btnGateLogin")?.addEventListener("click", async () => {
    const rawId = ($("#gateUsernameInput")?.value || "").trim();
    const pw = $("#gatePasswordInput")?.value || "";
    const errEl = $("#authGateError");
    if (!rawId || pw.length < 6) {
      if (errEl) errEl.textContent = "ログインIDと6文字以上のパスワードを入力してください。";
      return;
    }
    if (!firebaseReady || !auth) {
      if (errEl) errEl.textContent = "現在オフラインのためログインできません。下のオフライン学習をご利用ください。";
      return;
    }
    if (errEl) errEl.textContent = "サインイン中...";
    const emails = await resolveLoginEmail(rawId);
    let lastErr = null;
    for (const email of emails) {
      try {
        await signInWithEmailAndPassword(auth, email, pw);
        if (!rawId.includes("@")) state.loginId = rawId;
        saveLocalState(true);
        if (errEl) errEl.textContent = "";
        showToast("ログインしました");
        return;
      } catch (e) {
        lastErr = e;
      }
    }
    if (errEl) {
      errEl.textContent = "ログインIDまたはパスワードが正しくありません。";
      console.warn("Login failed:", lastErr);
    }
  });

  $("#btnGateSignup")?.addEventListener("click", async () => {
    const rawId = ($("#gateUsernameInput")?.value || "").trim();
    const pw = $("#gatePasswordInput")?.value || "";
    const recMail = ($("#gateRecoveryEmailInput")?.value || "").trim();
    const errEl = $("#authGateError");

    if (!/^[a-zA-Z0-9_.-]{3,20}$/.test(rawId)) {
      if (errEl) errEl.textContent = "ログインIDは半角英数字3〜20文字で入力してください。";
      return;
    }
    if (pw.length < 6) {
      if (errEl) errEl.textContent = "パスワードは6文字以上で入力してください。";
      return;
    }
    if (!firebaseReady || !auth) {
      if (errEl) errEl.textContent = "現在オフラインのため新規登録できません。";
      return;
    }

    const authEmail = recMail && recMail.includes("@")
      ? recMail
      : `${rawId.toLowerCase()}@${SYNTHETIC_EMAIL_DOMAINS[0]}`;

    if (errEl) errEl.textContent = "アカウント作成中...";
    try {
      await createUserWithEmailAndPassword(auth, authEmail, pw);
      state.loginId = rawId;
      state.recoveryEmail = recMail || "";
      state.friendId = ensureFriendId(state.friendId);
      saveLocalState(true);
      if (errEl) errEl.textContent = "";
      $("#authGate")?.classList.add("hidden");
      $("#usernameModal")?.classList.remove("hidden");
    } catch (e) {
      if (errEl) {
        errEl.textContent = e.code === "auth/email-already-in-use"
          ? "このログインIDまたはメールアドレスは既に使用されています。"
          : "新規登録に失敗しました。入力内容をご確認ください。";
      }
    }
  });

  $("#btnGateResetPw")?.addEventListener("click", async () => {
    const raw = ($("#gateRecoveryEmailInput")?.value || $("#gateUsernameInput")?.value || "").trim();
    const errEl = $("#authGateError");
    if (!raw || !raw.includes("@")) {
      if (errEl) errEl.textContent = "登録済みの再設定用メールアドレスを入力してから押してください。";
      return;
    }
    if (!firebaseReady || !auth) return;
    try {
      await sendPasswordResetEmail(auth, raw);
      if (errEl) errEl.textContent = "";
      showToast("パスワード再設定メールを送信しました");
    } catch (_) {
      if (errEl) errEl.textContent = "再設定メールの送信に失敗しました。";
    }
  });

  // 初回ニックネーム設定モーダル
  $("#btnSaveInitialUsername")?.addEventListener("click", async () => {
    const val = ($("#initialUsernameInput")?.value || "").trim();
    const errEl = $("#usernameModalError");
    if (!val || val.length > 16) {
      if (errEl) errEl.textContent = "ニックネームを1〜16文字で入力してください。";
      return;
    }
    state.nickname = val;
    saveLocalState(true);
    if (firebaseReady && auth?.currentUser) {
      try { await updateProfile(auth.currentUser, { displayName: val }); } catch (_) {}
    }
    $("#usernameModal")?.classList.add("hidden");
    renderAll();
    maybePromptRecoveryEmail();
  });

  // 再設定用メールアドレスモーダル
  $("#btnLinkRecoveryEmail")?.addEventListener("click", async () => {
    const mail = ($("#modalRecoveryEmailInput")?.value || "").trim();
    const pw = $("#modalRecoveryPwInput")?.value || "";
    const errEl = $("#recoveryModalError");
    if (!mail.includes("@") || !pw) {
      if (errEl) errEl.textContent = "メールアドレスと現在のパスワードを入力してください。";
      return;
    }
    if (!firebaseReady || !currentUser) return;
    try {
      const cred = EmailAuthProvider.credential(currentUser.email, pw);
      await reauthenticateWithCredential(currentUser, cred);
      await verifyBeforeUpdateEmail(currentUser, mail);
      state.recoveryEmail = mail;
      saveLocalState(true);
      $("#recoveryPromptModal")?.classList.add("hidden");
      updateSyncUi();
      showToast("確認メールを送信しました。メール内のリンクを開いて完了してください。");
    } catch (_) {
      if (errEl) errEl.textContent = "パスワードが異なるか、メール送信に失敗しました。";
    }
  });

  $("#btnSkipRecoveryOnce")?.addEventListener("click", () => {
    skipRecoveryThisSession = true;
    $("#recoveryPromptModal")?.classList.add("hidden");
  });

  $("#btnDismissRecoveryForever")?.addEventListener("click", () => {
    try { localStorage.setItem(STORAGE_KEYS.DISMISS_RECOVERY, "1"); } catch (_) {}
    $("#recoveryPromptModal")?.classList.add("hidden");
  });

  // ヘッダー＆下部ナビゲーション
  $("#btnBack")?.addEventListener("click", () => {
    if (activeTab === "study") {
      if (!$("#flashcardStage")?.classList.contains("hidden") || !$("#quizStage")?.classList.contains("hidden")) {
        exitStudyStages();
        return;
      }
      if (!$("#studySetupPanel")?.classList.contains("hidden")) {
        openStudyPicker();
        return;
      }
    }
    switchTab("home");
  });

  $("#btnSettings")?.addEventListener("click", () => switchTab("settings"));

  $$(".nav-tab").forEach((btn) => {
    btn.addEventListener("click", () => switchTab(btn.dataset.tab));
  });

  // ホーム画面のクイックアクションタイル
  $$(".action-tile[data-jump]").forEach((tile) => {
    tile.addEventListener("click", () => {
      const target = tile.dataset.jump;
      if (target === "study") {
        const mode = tile.dataset.mode || "flashcard";
        if ($("#studyMin")) $("#studyMin").value = prefs.goalMin || 1;
        if ($("#studyMax")) $("#studyMax").value = prefs.goalMax || 100;
        switchTab("study");
        openStudySetupForMode(mode);
      } else if (target === "vocab") {
        vocabMin = prefs.goalMin || 1;
        vocabMax = prefs.goalMax || 100;
        vocabLevelFilter = tile.dataset.filter === "weak" ? "weak" : "all";
        switchTab("vocab");
      }
    });
  });

  // 単語帳画面
  const onVocabRangeChange = () => {
    const maxAllowed = wordsData.length || 2300;
    vocabMin = Math.max(1, Math.min(maxAllowed, Number($("#vocabMin")?.value || 1)));
    vocabMax = Math.max(1, Math.min(maxAllowed, Number($("#vocabMax")?.value || 100)));
    renderVocabView();
  };
  $("#vocabMin")?.addEventListener("change", onVocabRangeChange);
  $("#vocabMax")?.addEventListener("change", onVocabRangeChange);

  $("#btnStartVocabListen")?.addEventListener("click", () => {
    const speed = Number($("#vocabListenSpeed")?.value || 1.0);
    const intervalMs = Number($("#vocabListenInterval")?.value || 1400);
    startListenOverlay(getFilteredVocab(), speed, intervalMs, true);
  });

  // 赤シート切替バー
  $("#toggleRedEn")?.addEventListener("click", () => {
    redEnActive = !redEnActive;
    updateRedSheetClasses();
  });
  $("#toggleRedJa")?.addEventListener("click", () => {
    redJaActive = !redJaActive;
    updateRedSheetClasses();
  });

  // 全画面聞き流しオーバーレイ
  $("#btnExitListen")?.addEventListener("click", closeListenOverlay);
  $("#btnListenPlayPause")?.addEventListener("click", () => {
    listenState.playing = !listenState.playing;
    if (!listenState.playing && "speechSynthesis" in window) {
      try { window.speechSynthesis.cancel(); } catch (_) {}
    }
    renderListenStep(listenState.playing);
  });
  $("#btnListenPrev")?.addEventListener("click", () => {
    if (!listenState.queue.length) return;
    listenState.index = (listenState.index - 1 + listenState.queue.length) % listenState.queue.length;
    renderListenStep(listenState.playing);
  });
  $("#btnListenNext")?.addEventListener("click", () => {
    if (!listenState.queue.length) return;
    listenState.index = (listenState.index + 1) % listenState.queue.length;
    renderListenStep(listenState.playing);
  });
  $("#btnListenSpeedQuick")?.addEventListener("click", () => {
    const speeds = [0.8, 1.0, 1.2];
    const curIdx = speeds.findIndex((s) => Math.abs(s - listenState.speed) < 0.05);
    listenState.speed = speeds[(curIdx + 1) % speeds.length];
    renderListenStep(false);
  });
  $("#btnListenLoopQuick")?.addEventListener("click", () => {
    listenState.loop = !listenState.loop;
    renderListenStep(false);
  });
  $$("[data-listen-rate]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const item = listenState.queue[listenState.index];
      if (!item) return;
      setWordLevel(item.no, Number(btn.dataset.listenRate));
      renderListenStep(false);
    });
  });

  // 学習画面モード選択＆開始
  $("#studyMin")?.addEventListener("input", (e) => { e.target.dataset.touched = "1"; });
  $("#studyMax")?.addEventListener("input", (e) => { e.target.dataset.touched = "1"; });
  $$("[data-pick-mode]").forEach((card) => {
    card.addEventListener("click", () => openStudySetupForMode(card.dataset.pickMode));
  });
  $("#btnBackToModePicker")?.addEventListener("click", openStudyPicker);
  $("#quizFormatSelect")?.addEventListener("change", updateQuizLayoutRowVisibility);
  $("#btnStartStudy")?.addEventListener("click", startSelectedStudyMode);

  // スペル入力専用キーボード＆物理キー対応
  $$("#qSpellKeyboard [data-key]").forEach((keyBtn) => {
    keyBtn.addEventListener("click", () => handleSpellKeyInput(keyBtn.dataset.key));
  });
  $("#qSpellBackBtn")?.addEventListener("click", handleSpellBackspace);
  $("#qSpellHintBtn")?.addEventListener("click", handleSpellHint);
  $("#qSpellGiveUpBtn")?.addEventListener("click", () => evaluateSpellSubmission(true));
  $("#qSpellSubmitBtn")?.addEventListener("click", () => evaluateSpellSubmission(false));
  $("#qSpellNextBtn")?.addEventListener("click", advanceSpellQuestion);
  $("#qSpellAudio")?.addEventListener("click", () => {
    const item = quizQueue[quizIndex];
    if (item) speakEnglish(item.word);
  });
  $$("[data-spell-lv]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const item = quizQueue[quizIndex];
      if (!item) return;
      const lv = Number(btn.dataset.spellLv);
      quizAnswers[item.no] = { correct: lv >= 2, level: lv };
      setWordLevel(item.no, lv);
      $$("[data-spell-lv]").forEach((b) => b.classList.toggle("selected", b === btn));
    });
  });

  window.addEventListener("keydown", (e) => {
    if (activeTab !== "study") return;
    if ($("#quizStage")?.classList.contains("hidden") || $("#quizSpellBox")?.classList.contains("hidden")) return;
    if (e.metaKey || e.ctrlKey || e.altKey) return;

    if (/^[a-zA-Z]$/.test(e.key) && !spellJudged) {
      e.preventDefault();
      handleSpellKeyInput(e.key);
    } else if (e.key === "Backspace" && !spellJudged) {
      e.preventDefault();
      handleSpellBackspace();
    } else if (e.key === "Enter") {
      e.preventDefault();
      if (!spellJudged) evaluateSpellSubmission(false);
      else advanceSpellQuestion();
    }
  });

  // フラッシュカード操作
  $("#btnExitFc")?.addEventListener("click", exitStudyStages);
  $("#flashcardBox")?.addEventListener("click", () => {
    fcFlipped = !fcFlipped;
    renderFlashcard(false);
  });
  $("#fcFrontAudioBtn")?.addEventListener("click", (e) => {
    e.stopPropagation();
    const item = fcQueue[fcIndex];
    if (item) speakEnglish(item.word);
  });
  $("#fcAudioBtn")?.addEventListener("click", (e) => {
    e.stopPropagation();
    const item = fcQueue[fcIndex];
    if (item) speakEnglish(item.word);
  });
  $$("#fcBack [data-rate]").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const item = fcQueue[fcIndex];
      if (!item) return;
      setWordLevel(item.no, Number(btn.dataset.rate));
      if (fcIndex + 1 < fcQueue.length) {
        fcIndex++;
        fcFlipped = false;
        renderFlashcard(true);
      } else {
        exitStudyStages();
        showToast("フラッシュカード学習が完了しました！");
      }
    });
  });
  $("#fcPrevBtn")?.addEventListener("click", () => {
    if (fcIndex > 0) {
      fcIndex--;
      fcFlipped = false;
      renderFlashcard(true);
    }
  });
  $("#fcNextBtn")?.addEventListener("click", () => {
    if (fcIndex + 1 < fcQueue.length) {
      fcIndex++;
      fcFlipped = false;
      renderFlashcard(true);
    } else {
      exitStudyStages();
      showToast("フラッシュカード学習が完了しました！");
    }
  });

  // 小テスト操作
  $("#btnExitQuiz")?.addEventListener("click", exitStudyStages);
  $("#qSingleAudio")?.addEventListener("click", () => {
    const item = quizQueue[quizIndex];
    if (item) speakEnglish(item.word);
  });
  $("#qBtnReveal")?.addEventListener("click", () => {
    $("#qBtnReveal")?.classList.add("hidden");
    $("#qSingleAnswerArea")?.classList.remove("hidden");
  });
  $("#qBtnWrong")?.addEventListener("click", () => recordSingleQuizJudge(false));
  $("#qBtnCorrect")?.addEventListener("click", () => recordSingleQuizJudge(true));
  $("#qManualToggleBtn")?.addEventListener("click", () => {
    $("#qManualPanel")?.classList.toggle("hidden");
  });
  $$("[data-q-override]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const lv = Number(btn.dataset.qOverride);
      recordSingleQuizJudge(lv >= 2, lv);
    });
  });

  $("#qListToggleAns")?.addEventListener("click", () => {
    quizListRevealed = !quizListRevealed;
    renderQuizListMode();
  });
  $("#qListFinishBtn")?.addEventListener("click", finalizeQuizListScoring);

  $("#qResultRetestBtn")?.addEventListener("click", () => {
    const wrong = quizQueue.filter((item) => !quizAnswers[item.no]?.correct);
    if (!wrong.length) return;
    quizQueue = wrong;
    quizIndex = 0;
    quizAnswers = {};
    quizListRevealed = false;
    quizIsRetest = true;
    openQuizStage();
  });
  $("#qResultRetryBtn")?.addEventListener("click", exitStudyStages);

  // 交流タブ（対戦／フレンド切替）
  $$("#battleSubSwitch .seg-btn").forEach((btn) => {
    btn.addEventListener("click", () => {
      const sub = btn.dataset.battleTab;
      $$("#battleSubSwitch .seg-btn").forEach((b) => b.classList.toggle("active", b === btn));
      $("#battleMatchPanel")?.classList.toggle("hidden", sub !== "match");
      $("#battleFriendPanel")?.classList.toggle("hidden", sub !== "friends");
    });
  });

  $("#btnCreateRoom")?.addEventListener("click", createBattleRoomAction);
  $("#btnJoinRoom")?.addEventListener("click", joinBattleRoomAction);
  $("#btnLeaveRoom")?.addEventListener("click", leaveBattleRoom);
  $("#btnBattleBackLobby")?.addEventListener("click", leaveBattleRoom);
  $("#btnStartBattleMatch")?.addEventListener("click", hostStartBattleMatch);
  $("#btnCopyRoomCode")?.addEventListener("click", async () => {
    if (!battleSession.roomCode) return;
    try {
      await navigator.clipboard.writeText(battleSession.roomCode);
      showToast("合言葉をコピーしました");
    } catch (_) {
      showToast(`合言葉: ${battleSession.roomCode}`);
    }
  });

  $("#btnSendFriendReq")?.addEventListener("click", sendFriendRequestAction);
  $("#btnCopyMyFriendId")?.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(state.friendId);
      showToast("フレンドIDをコピーしました");
    } catch (_) {
      showToast(`フレンドID: ${state.friendId}`);
    }
  });
  $("#btnRefreshFriends")?.addEventListener("click", () => {
    renderFriendsList();
    showToast("フレンド一覧を更新しました");
  });
  $("#btnCloseFriendModal")?.addEventListener("click", () => {
    $("#friendDetailModal")?.classList.add("hidden");
  });
  $("#btnRemoveFriend")?.addEventListener("click", () => {
    if (!selectedFriend) return;
    state.friends = (state.friends || []).filter((f) => f.friendId !== selectedFriend.friendId);
    saveLocalState(true);
    $("#friendDetailModal")?.classList.add("hidden");
    renderFriendsList();
    showToast("フレンドを解除しました");
  });

  // 設定画面
  $("#btnManualSync")?.addEventListener("click", async () => {
    if (!firebaseReady || !currentUser) {
      showToast("クラウド同期にはログインが必要です");
      return;
    }
    const ok = await pushCloudStateNow();
    showToast(ok ? "クラウドと同期しました" : "同期に失敗しました");
  });

  $("#btnOpenRecoveryModal")?.addEventListener("click", () => {
    if (!currentUser) {
      showToast("先にログインしてください");
      return;
    }
    $("#recoveryModalError").textContent = "";
    $("#recoveryPromptModal")?.classList.remove("hidden");
  });

  $("#btnUpdateDisplayName")?.addEventListener("click", async () => {
    const val = ($("#setDisplayNameInput")?.value || "").trim();
    if (!val || val.length > 16) {
      showToast("ニックネームは1〜16文字で入力してください");
      return;
    }
    state.nickname = val;
    saveLocalState(true);
    if (firebaseReady && auth?.currentUser) {
      try { await updateProfile(auth.currentUser, { displayName: val }); } catch (_) {}
    }
    renderAll();
    showToast("ニックネームを保存しました");
  });

  $("#btnLogout")?.addEventListener("click", async () => {
    if (firebaseReady && auth && currentUser) {
      await signOut(auth);
      currentUser = null;
      updateSyncUi();
      showToast("ログアウトしました");
    } else {
      $("#authGateError").textContent = "";
      $("#authGate")?.classList.remove("hidden");
    }
  });

  const onGoalRangeChange = () => {
    const maxAllowed = wordsData.length || 2300;
    prefs.goalMin = Math.max(1, Math.min(maxAllowed, Number($("#setGoalMin")?.value || 1)));
    prefs.goalMax = Math.max(1, Math.min(maxAllowed, Number($("#setGoalMax")?.value || 100)));
    vocabMin = prefs.goalMin;
    vocabMax = prefs.goalMax;
    saveLocalPrefs();
    renderHomeView();
  };
  $("#setGoalMin")?.addEventListener("change", onGoalRangeChange);
  $("#setGoalMax")?.addEventListener("change", onGoalRangeChange);

  $("#setVoiceAccent")?.addEventListener("change", (e) => {
    prefs.voiceAccent = e.target.value;
    saveLocalPrefs();
  });
  $("#setAutoAudio")?.addEventListener("change", (e) => {
    prefs.autoAudio = Boolean(e.target.checked);
    saveLocalPrefs();
  });
  $("#setKeepPosOnRed")?.addEventListener("change", (e) => {
    prefs.keepPosOnRed = Boolean(e.target.checked);
    saveLocalPrefs();
    updateRedSheetClasses();
  });
  $("#setFontSize")?.addEventListener("change", (e) => {
    prefs.fontSize = e.target.value;
    saveLocalPrefs();
    applyPrefsToDom();
  });
  $("#setFontFamily")?.addEventListener("change", (e) => {
    prefs.fontFamily = e.target.value;
    saveLocalPrefs();
    applyPrefsToDom();
  });
  $("#setTheme")?.addEventListener("change", (e) => {
    prefs.theme = e.target.value;
    saveLocalPrefs();
    applyPrefsToDom();
  });

  // CSV手動読込
  $("#csvFileInput")?.addEventListener("change", async (e) => {
    const file = e.target.files?.[0];
    if (!file) return;
    try {
      const text = await file.text();
      const rows = parseCsvRows(text);
      const parsed = normalizeWords(rows);
      if (!parsed.length) {
        showToast("有効な単語データが見つかりませんでした");
        return;
      }
      wordsData = parsed;
      try { localStorage.setItem(STORAGE_KEYS.CACHE_WORDS, text); } catch (_) {}
      renderAll();
      showToast(`${parsed.length} 語のデータを読み込みました`);
    } catch (_) {
      showToast("CSVの読み込みに失敗しました");
    }
  });

  // フィードバック送信
  $("#btnSendFeedback")?.addEventListener("click", async () => {
    const category = $("#fbCategory")?.value || "other";
    const wordNo = ($("#fbWordNo")?.value || "").trim();
    const message = ($("#fbMessage")?.value || "").trim();
    if (!message) {
      showToast("内容を入力してください");
      return;
    }
    if (firebaseReady && db) {
      try {
        await addDoc(collection(db, "feedback"), {
          category,
          wordNo,
          message,
          uid: currentUser?.uid || "guest",
          createdAt: serverTimestamp()
        });
      } catch (_) {}
    }
    if ($("#fbWordNo")) $("#fbWordNo").value = "";
    if ($("#fbMessage")) $("#fbMessage").value = "";
    showToast("フィードバックを送信しました。ありがとうございます！");
  });
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
  renderAll();

  const statusEl = $("#splashStatus");
  if (statusEl) statusEl.textContent = `準備完了（全 ${wordsData.length.toLocaleString()} 語）`;
  $("#splashSpinner")?.classList.add("hidden");
  $("#btnSplashStart")?.classList.remove("hidden");
}

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    navigator.serviceWorker.register("./sw.js").catch((err) => {
      console.warn("SW registration skipped:", err);
    });
  });
}

document.addEventListener("DOMContentLoaded", initApp);
