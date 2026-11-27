/* =========================================================
   HONE - Main Application Script (app.js)
   英単語LEAP 全2,300語 学習PWA（0msオフライン即起動＆バックグラウンド同期）
   ========================================================= */

// Firebase SDK は起動を一切ブロックしないよう、オンライン時に動的 import で遅延読み込みする
let initializeApp;
let getAuth;
let onAuthStateChanged;
let signInWithEmailAndPassword;
let createUserWithEmailAndPassword;
let sendPasswordResetEmail;
let EmailAuthProvider;
let reauthenticateWithCredential;
let verifyBeforeUpdateEmail;
let signOut;
let updateProfile;
let getFirestore;
let doc;
let getDoc;
let setDoc;
let updateDoc;
let deleteField;
let collection;
let addDoc;
let query;
let where;
let getDocs;
let onSnapshot;
let serverTimestamp;

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
  CACHE_DERIVATIVES: "hone_derivatives_cache_v1",
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
  showFirstChar: true,
  fontSize: "md",
  fontFamily: "sans",
  theme: "mist"
};

const DEFAULT_STATE = {
  ownerUid: "",
  loginId: "",
  recoveryEmail: "",
  nickname: "",
  friendId: "",
  levels: {}, // { [no]: 0 | 1 | 2 | 3 }
  streaks: {}, // { [no]: number } 確認テストでの連続正解数（3回連続で評価1段階UP）
  studyLog: {}, // { [YYYY-MM-DD]: number } 日別学習単語数（カレンダー用）
  studiedIdsToday: [],
  studiedDate: "",
  streakDays: 0,
  lastStudyDate: "",
  friends: [], // [{ uid, nickname, friendId }] 相互承認済みフレンド
  friendUids: [], // 承認済みフレンドのUID一覧
  outgoingFriendUids: [], // 自分が申請送信中の相手UID一覧
  outgoingFriends: [], // [{ uid, nickname, friendId }] 承認待ち表示用
  updatedAt: 0
};

const STREAK_TO_PROMOTE = 3;

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
let firebaseInitPromise = null;
let authListenersBound = false;
let justSignedUpInteractive = false;
let currentUser = null;
let cloudUnsubscribe = null;
let friendReqUnsubscribe = null;
let friendUsersReqUnsubscribe = null;
let syncTimer = null;
let lastSyncTimeStr = "";
let skipRecoveryThisSession = false;

let wordsData = [];
let wordsByNo = new Map();
let examplesMap = new Map(); // no -> [{ rawEn, en, ja }]
let derivativesMap = new Map(); // no -> [{ no, word, pos, meaning }]

let state = structuredClone(DEFAULT_STATE);
let prefs = structuredClone(DEFAULT_PREFS);
let activeTab = "home";

// カレンダー表示状態
const _initNow = new Date();
let calYear = _initNow.getFullYear();
let calMonth = _initNow.getMonth();
let calSelectedDate = "";

// 単語帳状態
let vocabMin = 1;
let vocabMax = 100;
let vocabSelectedLevels = new Set(); // 空の場合は「すべて」、それ以外は "0","1","2","3" の複数選択
let redEnActive = false;
let redJaActive = false;

// 学習セットアップ状態
let currentStudyMode = "flashcard"; // "flashcard" | "quiz" | "paper" | "listen"
let studySelectedLevels = new Set(); // 空の場合は「すべて」、それ以外は "0","1","2","3" の複数選択

// フラッシュカード状態
let fcQueue = [];
let fcIndex = 0;
let fcFlipped = false;
let fcFormat = "en-ja";

// 確認テスト状態
let quizQueue = [];
let quizIndex = 0;
let quizFormat = "ja-en-type"; // "ja-en-type" | "en-ja" | "example-type" | "derivative-type"
let quizShowFirstChar = true;
let quizAnswers = {}; // { [key]: { correct: boolean, level: number } }
let quizIsRetest = false;
let singleJudged = false;

// タイピング入力状態（文字数非表示・先頭1文字表示切替対応）
let spellFirstChar = "";
let spellTypedRest = "";
let spellAcceptedNormalized = []; // 小文字英字のみに正規化した許容正解リスト
let spellDisplayAnswer = "";
let spellAudioTargetWord = "";
let spellJudged = false;

// 筆記テスト状態（テスト用紙形式・タイマー・採点）
let paperQueue = [];
let paperFormat = "en-ja";
let paperGradingMode = false;
let paperMarks = {}; // { [no]: boolean } true=○, false=×
let paperTimerId = null;
let paperTimeLeftSec = 0;
let paperConfiguredTimerSec = 300;

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

// 対戦状態（スペリング早打ち：日本語→英語・例文・派生語 ＆ 1文字目表示切替対応）
let battleRoomUnsub = null;
let battleTimerId = null;
let battleSpellFirstChar = "";
let battleSpellTypedRest = "";
let battleSpellAccepted = [];
let battleSpellDisplayAns = "";
let battleSession = {
  roomCode: "",
  isHost: false,
  localOnly: false,
  format: "ja-en",
  showFirstChar: true,
  minNo: 1,
  maxNo: 100,
  count: 10,
  questions: [],
  currentIndex: 0,
  answeredCurrent: false,
  timeLeft: 15,
  players: {}
};

// 学習中ロック制御（下部ナビ・ヘッダーアイコンを隠す）
function setStudyLockMode(locked) {
  document.body.classList.toggle("study-locked", Boolean(locked));
}

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
      const normalizedLevels = extractNormalizedLevelsMap(parsed);
      state = {
        ...DEFAULT_STATE,
        ...parsed,
        levels: Object.keys(normalizedLevels).length > 0 ? normalizedLevels : (parsed.levels || {}),
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
    const toStore = { ...state, ratings: state.levels || {} };
    localStorage.setItem(STORAGE_KEYS.STATE, JSON.stringify(toStore));
  } catch (_) {}
  if (markUpdated && firebaseReady && currentUser) {
    scheduleCloudSync();
  }
}

function normalizeDailyState() {
  const today = todayKey();
  if (!state.studyLog || typeof state.studyLog !== "object") state.studyLog = {};
  if (state.studiedDate !== today) {
    state.studiedDate = today;
    state.studiedIdsToday = [];
  } else if (Array.isArray(state.studiedIdsToday) && state.studiedIdsToday.length > 0) {
    state.studyLog[today] = Math.max(Number(state.studyLog[today] || 0), state.studiedIdsToday.length);
  }
  if (state.lastStudyDate && state.lastStudyDate !== today && state.lastStudyDate !== yesterdayKey()) {
    state.streakDays = 0;
  }
  if (!calSelectedDate) calSelectedDate = today;
}

function setWordLevel(no, lv) {
  const clamped = Math.max(0, Math.min(3, Number(lv) || 0));
  state.levels[String(no)] = clamped;
  normalizeDailyState();
  const key = String(no);
  const today = todayKey();
  if (!Array.isArray(state.studiedIdsToday)) state.studiedIdsToday = [];
  if (!state.studiedIdsToday.includes(key)) {
    state.studiedIdsToday.push(key);
    if (state.lastStudyDate !== today) {
      state.streakDays = state.lastStudyDate === yesterdayKey() ? (state.streakDays || 0) + 1 : 1;
      state.lastStudyDate = today;
    }
  }
  state.studyLog[today] = Math.max(Number(state.studyLog[today] || 0), state.studiedIdsToday.length);
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

function buildDerivativesMap(rows) {
  derivativesMap.clear();
  rows.forEach((r) => {
    const no = Number(r["単語番号"] || r.no || r.id || 0);
    const word = (r["派生語"] || r.derivative || r.word || r.en || "").trim();
    const pos = (r["品詞"] || r.pos || r.part_of_speech || "").trim();
    const meaning = (r["意味"] || r["主な意味"] || r.meaning || r.ja || r.jp || "").trim();
    if (!no || !word || !meaning) return;
    if (!derivativesMap.has(no)) derivativesMap.set(no, []);
    derivativesMap.get(no).push({ no, word, pos, meaning });
  });
}

function syncMaxRangeInputs() {
  const maxNo = wordsData.length ? wordsData[wordsData.length - 1].no : 2300;
  ["#homeGoalMin", "#homeGoalMax", "#vocabMin", "#vocabMax", "#studyMin", "#studyMax", "#battleMin", "#battleMax"].forEach((sel) => {
    const el = $(sel);
    if (el) el.max = String(maxNo);
  });
}

// 起動0ms用：localStorage に保存済みのCSVキャッシュを同期読み込み
function loadCachedVocabularySync() {
  try {
    const cachedE = localStorage.getItem(STORAGE_KEYS.CACHE_EXAMPLES);
    const cachedD = localStorage.getItem(STORAGE_KEYS.CACHE_DERIVATIVES);
    const cachedW = localStorage.getItem(STORAGE_KEYS.CACHE_WORDS);
    if (cachedE) buildExamplesMap(parseCsvRows(cachedE));
    if (cachedD) buildDerivativesMap(parseCsvRows(cachedD));
    if (cachedW) {
      const parsed = normalizeWords(parseCsvRows(cachedW));
      if (parsed.length) wordsData = parsed;
    }
  } catch (_) {}
  syncMaxRangeInputs();
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
    const [wRes, eRes, dRes] = await Promise.all([
      fetch("./data/words.csv"),
      fetch("./data/examples.csv").catch(() => null),
      fetch("./data/derivatives.csv").catch(() => null)
    ]);
    if (!wRes || !wRes.ok) throw new Error("words.csv fetch failed");
    const wText = await wRes.text();

    if (eRes && eRes.ok) {
      const eText = await eRes.text();
      try { localStorage.setItem(STORAGE_KEYS.CACHE_EXAMPLES, eText); } catch (_) {}
      buildExamplesMap(parseCsvRows(eText));
    }

    if (dRes && dRes.ok) {
      const dText = await dRes.text();
      try { localStorage.setItem(STORAGE_KEYS.CACHE_DERIVATIVES, dText); } catch (_) {}
      buildDerivativesMap(parseCsvRows(dText));
    }

    const parsedWords = normalizeWords(parseCsvRows(wText));
    if (!parsedWords.length) throw new Error("words.csv parsed 0 words");
    wordsData = parsedWords;
    try { localStorage.setItem(STORAGE_KEYS.CACHE_WORDS, wText); } catch (_) {}
  } catch (err) {
    console.warn("Using cached CSV fallback:", err);
    loadCachedVocabularySync();
  }

  syncMaxRangeInputs();
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
   Firebase 初期化・認証・クラウド同期（オンライン時のみ非同期ロード）
   ========================================================= */
async function initFirebaseIfAvailable() {
  if (firebaseReady && auth && db) return true;
  if (navigator.onLine === false) return false;
  if (firebaseInitPromise) return firebaseInitPromise;

  firebaseInitPromise = (async () => {
    try {
      const [cfgModule, appMod, authMod, fsMod] = await Promise.all([
        import("./firebase-config.js"),
        import("https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js"),
        import("https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js"),
        import("https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js")
      ]);
      const firebaseConfig = cfgModule.firebaseConfig || cfgModule.default;
      if (!firebaseConfig || !firebaseConfig.apiKey) return false;

      initializeApp = appMod.initializeApp;
      getAuth = authMod.getAuth;
      onAuthStateChanged = authMod.onAuthStateChanged;
      signInWithEmailAndPassword = authMod.signInWithEmailAndPassword;
      createUserWithEmailAndPassword = authMod.createUserWithEmailAndPassword;
      sendPasswordResetEmail = authMod.sendPasswordResetEmail;
      EmailAuthProvider = authMod.EmailAuthProvider;
      reauthenticateWithCredential = authMod.reauthenticateWithCredential;
      verifyBeforeUpdateEmail = authMod.verifyBeforeUpdateEmail;
      signOut = authMod.signOut;
      updateProfile = authMod.updateProfile;

      getFirestore = fsMod.getFirestore;
      doc = fsMod.doc;
      getDoc = fsMod.getDoc;
      setDoc = fsMod.setDoc;
      updateDoc = fsMod.updateDoc;
      deleteField = fsMod.deleteField;
      collection = fsMod.collection;
      addDoc = fsMod.addDoc;
      query = fsMod.query;
      where = fsMod.where;
      getDocs = fsMod.getDocs;
      onSnapshot = fsMod.onSnapshot;
      serverTimestamp = fsMod.serverTimestamp;

      const app = initializeApp(firebaseConfig);
      auth = getAuth(app);
      db = getFirestore(app);
      firebaseReady = true;
      return true;
    } catch (err) {
      console.warn("Firebase unavailable (silent offline fallback):", err);
      firebaseInitPromise = null;
      return false;
    }
  })();

  return firebaseInitPromise;
}

async function startBackgroundFirebaseSync() {
  if (navigator.onLine === false) return false;
  try {
    const ok = await initFirebaseIfAvailable();
    if (!ok) return false;
    setupAuthListeners();
    return true;
  } catch (_) {
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
    const timeSuffix = lastSyncTimeStr ? ` ・ ${lastSyncTimeStr}` : "";
    if (statusText) statusText.textContent = `クラウド同期中（${state.nickname || dispId || "ログイン済み"}）${timeSuffix}`;
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

function nowTimeHHMM() {
  const d = new Date();
  return `${String(d.getHours()).padStart(2, "0")}:${String(d.getMinutes()).padStart(2, "0")}`;
}

function extractNormalizedLevelsMap(remote) {
  const out = {};
  if (remote?.ratings && typeof remote.ratings === "object") {
    for (const [k, v] of Object.entries(remote.ratings)) {
      const n = Number(v);
      if (!Number.isNaN(n)) out[k] = Math.max(0, Math.min(3, n));
    }
  }
  if (remote?.levels && typeof remote.levels === "object") {
    for (const [k, v] of Object.entries(remote.levels)) {
      const n = Number(v);
      if (!Number.isNaN(n)) out[k] = Math.max(0, Math.min(3, n));
    }
  }
  return out;
}

function applyRemoteSnapshotToState(remote, uid, isInitialLogin = false) {
  const sameOwner = !state.ownerUid || state.ownerUid === uid;
  const baseLocal = sameOwner ? state : structuredClone(DEFAULT_STATE);
  const remoteCombinedLevels = extractNormalizedLevelsMap(remote);
  const localUpdated = Number(baseLocal.updatedAt || 0);
  const remoteUpdated = Number(remote.updatedAt || 0);
  const preferLocalOnConflict = sameOwner && localUpdated > remoteUpdated;

  const mergedLevels = preferLocalOnConflict
    ? { ...remoteCombinedLevels, ...(baseLocal.levels || {}) }
    : { ...(baseLocal.levels || {}), ...remoteCombinedLevels };

  const mergedStreaks = preferLocalOnConflict
    ? { ...(remote.streaks || {}), ...(baseLocal.streaks || {}) }
    : { ...(baseLocal.streaks || {}), ...(remote.streaks || {}) };

  const mergedLog = { ...(baseLocal.studyLog || {}), ...(remote.studyLog || {}) };
  Object.keys(mergedLog).forEach((k) => {
    mergedLog[k] = Math.max(Number(baseLocal.studyLog?.[k] || 0), Number(remote.studyLog?.[k] || 0));
  });

  const remoteFriends = Array.isArray(remote.friends) ? remote.friends : (baseLocal.friends || []);
  const remoteFriendUids = Array.isArray(remote.friendUids)
    ? remote.friendUids
    : remoteFriends.map((f) => f.uid).filter(Boolean);

  state = {
    ...structuredClone(DEFAULT_STATE),
    ownerUid: uid,
    loginId: remote.loginId || baseLocal.loginId || extractLoginIdFromEmail(currentUser?.email || ""),
    recoveryEmail: remote.recoveryEmail || baseLocal.recoveryEmail || "",
    nickname: remote.nickname || baseLocal.nickname || currentUser?.displayName || "",
    friendId: ensureFriendId(remote.friendId || remote.friendCode || baseLocal.friendId),
    levels: mergedLevels,
    streaks: mergedStreaks,
    studyLog: mergedLog,
    studiedIdsToday: remote.studiedDate === todayKey()
      ? Array.from(new Set([...(baseLocal.studiedDate === todayKey() ? baseLocal.studiedIdsToday || [] : []), ...(remote.studiedIdsToday || [])]))
      : (baseLocal.studiedDate === todayKey() ? baseLocal.studiedIdsToday || [] : []),
    studiedDate: todayKey(),
    streakDays: Math.max(Number(remote.streakDays || 0), Number(baseLocal.streakDays || 0)),
    lastStudyDate: preferLocalOnConflict
      ? (baseLocal.lastStudyDate || remote.lastStudyDate || "")
      : (remote.lastStudyDate || baseLocal.lastStudyDate || ""),
    friends: remoteFriends,
    friendUids: remoteFriendUids,
    outgoingFriendUids: Array.isArray(remote.outgoingFriendUids) ? remote.outgoingFriendUids : (baseLocal.outgoingFriendUids || []),
    outgoingFriends: Array.isArray(remote.outgoingFriends) ? remote.outgoingFriends : (baseLocal.outgoingFriends || []),
    updatedAt: Math.max(localUpdated, remoteUpdated, Date.now())
  };

  if (!preferLocalOnConflict && remote.goalMin && remote.goalMax) {
    prefs.goalMin = Number(remote.goalMin);
    prefs.goalMax = Number(remote.goalMax);
    vocabMin = prefs.goalMin;
    vocabMax = prefs.goalMax;
    saveLocalPrefs();
  }

  normalizeDailyState();
  saveLocalState(false);
}

async function pushCloudStateNow() {
  if (!firebaseReady || !db || !currentUser) return false;
  try {
    state.ownerUid = currentUser.uid;
    state.friendId = ensureFriendId(state.friendId);
    state.friendUids = Array.from(new Set([
      ...(state.friendUids || []),
      ...(state.friends || []).map((f) => f.uid).filter(Boolean)
    ]));
    const payload = {
      uid: currentUser.uid,
      loginId: state.loginId || extractLoginIdFromEmail(currentUser.email || ""),
      recoveryEmail: isRealEmail(currentUser.email) ? currentUser.email : (state.recoveryEmail || ""),
      nickname: state.nickname || currentUser.displayName || "",
      friendId: state.friendId,
      friendCode: state.friendId,
      goalMin: prefs.goalMin || 1,
      goalMax: prefs.goalMax || 100,
      levels: state.levels || {},
      ratings: state.levels || {},
      streaks: state.streaks || {},
      studyLog: state.studyLog || {},
      studiedIdsToday: state.studiedIdsToday || [],
      studiedDate: state.studiedDate || todayKey(),
      streakDays: state.streakDays || 0,
      lastStudyDate: state.lastStudyDate || "",
      friends: state.friends || [],
      friendUids: state.friendUids || [],
      outgoingFriendUids: state.outgoingFriendUids || [],
      outgoingFriends: state.outgoingFriends || [],
      summary: buildMasterySummary(),
      updatedAt: Date.now(),
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
    lastSyncTimeStr = nowTimeHHMM();
    updateSyncUi();
    return true;
  } catch (err) {
    console.warn("Cloud sync failed:", err);
    return false;
  }
}

async function syncBidirectionalNow() {
  if (!firebaseReady || !db || !currentUser) return false;
  try {
    const snap = await getDoc(doc(db, "users", currentUser.uid));
    if (snap.exists()) {
      const remote = snap.data();
      const remoteCombinedLevels = extractNormalizedLevelsMap(remote);
      const mergedLevels = { ...remoteCombinedLevels, ...(state.levels || {}) };
      const mergedStreaks = { ...(remote.streaks || {}), ...(state.streaks || {}) };
      const mergedLog = { ...(remote.studyLog || {}), ...(state.studyLog || {}) };
      Object.keys(mergedLog).forEach((k) => {
        mergedLog[k] = Math.max(Number(remote.studyLog?.[k] || 0), Number(state.studyLog?.[k] || 0));
      });
      state.levels = mergedLevels;
      state.streaks = mergedStreaks;
      state.studyLog = mergedLog;
      if (!state.nickname && remote.nickname) state.nickname = remote.nickname;
      if (remote.friendId) state.friendId = ensureFriendId(remote.friendId);
    }
    const ok = await pushCloudStateNow();
    await checkOutgoingFriendApprovals();
    renderAll();
    return ok;
  } catch (err) {
    console.warn("Bidirectional sync error:", err);
    return false;
  }
}

function scheduleCloudSync() {
  if (!firebaseReady || !currentUser) return;
  clearTimeout(syncTimer);
  syncTimer = setTimeout(() => {
    pushCloudStateNow();
  }, 400);
}

function subscribeUserDoc(uid) {
  if (cloudUnsubscribe) {
    cloudUnsubscribe();
    cloudUnsubscribe = null;
  }
  if (!firebaseReady || !db || !uid) return;
  cloudUnsubscribe = onSnapshot(doc(db, "users", uid), (snap) => {
    if (!snap.exists()) return;
    if (snap.metadata.hasPendingWrites) return;
    const remote = snap.data();
    applyRemoteSnapshotToState(remote, uid, false);
    lastSyncTimeStr = nowTimeHHMM();
    renderAll();
  }, (err) => {
    console.warn("User snapshot listener error:", err);
  });
}

let incomingFromUsersReqs = [];
let incomingFromCollectionReqs = [];

function mergeAndRenderIncomingRequests() {
  const approvedSet = new Set([
    ...(state.friendUids || []),
    ...(state.friends || []).map((f) => f.uid).filter(Boolean)
  ]);
  const byUid = new Map();
  [...incomingFromUsersReqs, ...incomingFromCollectionReqs].forEach((r) => {
    if (!r.fromUid || r.fromUid === currentUser?.uid) return;
    if (approvedSet.has(r.fromUid)) return;
    byUid.set(r.fromUid, r);
  });
  renderFriendRequests(Array.from(byUid.values()));
}

function subscribeFriendRequests(uid) {
  if (friendReqUnsubscribe) { friendReqUnsubscribe(); friendReqUnsubscribe = null; }
  if (friendUsersReqUnsubscribe) { friendUsersReqUnsubscribe(); friendUsersReqUnsubscribe = null; }
  incomingFromUsersReqs = [];
  incomingFromCollectionReqs = [];
  if (!firebaseReady || !db || !uid) return;

  try {
    const uq = query(collection(db, "users"), where("outgoingFriendUids", "array-contains", uid));
    friendUsersReqUnsubscribe = onSnapshot(uq, (snap) => {
      const arr = [];
      snap.forEach((d) => {
        const data = d.data();
        arr.push({
          id: `user_${d.id}`,
          reqDocId: "",
          fromUid: d.id,
          fromName: data.nickname || data.loginId || "ユーザー",
          fromFriendId: data.friendId || data.friendCode || ""
        });
      });
      incomingFromUsersReqs = arr;
      mergeAndRenderIncomingRequests();
    }, () => {});
  } catch (_) {}

  try {
    const fq = query(collection(db, "friendRequests"), where("toUid", "==", uid));
    friendReqUnsubscribe = onSnapshot(fq, (snap) => {
      const arr = [];
      snap.forEach((d) => {
        const data = d.data();
        if (data.status === "pending") {
          arr.push({
            id: d.id,
            reqDocId: d.id,
            fromUid: data.fromUid || "",
            fromName: data.fromName || "ユーザー",
            fromFriendId: data.fromFriendId || ""
          });
        }
      });
      incomingFromCollectionReqs = arr;
      mergeAndRenderIncomingRequests();
    }, () => {});
  } catch (_) {}
}

function setupAuthListeners() {
  if (!firebaseReady || !auth || authListenersBound) return;
  authListenersBound = true;
  onAuthStateChanged(auth, async (user) => {
    currentUser = user;
    if (user) {
      if (state.ownerUid && state.ownerUid !== user.uid) {
        state = structuredClone(DEFAULT_STATE);
      }
      state.ownerUid = user.uid;
      if (!state.loginId) {
        state.loginId = extractLoginIdFromEmail(user.email || "");
      }
      if (!state.nickname && user.displayName) {
        state.nickname = user.displayName;
      }
      saveLocalState(false);

      try {
        const snap = await getDoc(doc(db, "users", user.uid));
        if (snap.exists()) {
          applyRemoteSnapshotToState(snap.data(), user.uid, true);
          await pushCloudStateNow();
        } else {
          await pushCloudStateNow();
        }
        await checkOutgoingFriendApprovals();
      } catch (err) {
        // バックグラウンド同期失敗時もエラー画面は出さず静かに終了
        console.warn("Background auth sync skipped:", err);
      }

      subscribeUserDoc(user.uid);
      subscribeFriendRequests(user.uid);
      $("#authGate")?.classList.add("hidden");

      if (!state.nickname && justSignedUpInteractive) {
        justSignedUpInteractive = false;
        $("#usernameModal")?.classList.remove("hidden");
      }
      renderAll();
    } else {
      if (cloudUnsubscribe) { cloudUnsubscribe(); cloudUnsubscribe = null; }
      if (friendReqUnsubscribe) { friendReqUnsubscribe(); friendReqUnsubscribe = null; }
      if (friendUsersReqUnsubscribe) { friendUsersReqUnsubscribe(); friendUsersReqUnsubscribe = null; }
      lastSyncTimeStr = "";
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
function updateBackButtonVisibility() {
  const backBtn = $("#btnBack");
  if (!backBtn) return;

  let showBack = false;
  if (activeTab === "settings") {
    showBack = true;
  } else if (activeTab === "study") {
    const onPicker = !$("#studyPickerPanel")?.classList.contains("hidden");
    showBack = !onPicker;
  } else if (activeTab === "battle") {
    const onPicker = !$("#battlePickerPanel")?.classList.contains("hidden");
    showBack = !onPicker;
  }
  backBtn.classList.toggle("is-hidden", !showBack);
}

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

  const redBar = $("#floatingRedBar");
  if (redBar) redBar.classList.toggle("hidden", tabName !== "vocab");

  if (tabName === "home") renderHomeView();
  else if (tabName === "vocab") renderVocabView();
  else if (tabName === "study") openStudyPicker();
  else if (tabName === "battle") openBattlePicker();
  else if (tabName === "progress") renderProgressView();
  else if (tabName === "settings") renderSettingsView();

  updateBackButtonVisibility();
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

  const gMinInp = $("#homeGoalMin");
  const gMaxInp = $("#homeGoalMax");
  if (gMinInp) gMinInp.value = gMin;
  if (gMaxInp) gMaxInp.value = gMax;

  renderDonutAndLegend("#homeDonutSvg", "#homeMasteryPct", "#homeLegend", stats);

  const todayEl = $("#homeTodayCount");
  const streakEl = $("#homeStreakDays");
  if (todayEl) todayEl.textContent = `${(state.studiedIdsToday || []).length} 語`;
  if (streakEl) streakEl.textContent = `${state.streakDays || 0} 日`;
}

function getHeatClass(count) {
  if (!count || count <= 0) return "cal-lv-0";
  if (count < 20) return "cal-lv-1";
  if (count < 50) return "cal-lv-2";
  if (count < 100) return "cal-lv-3";
  return "cal-lv-4";
}

function renderStudyCalendar() {
  const grid = $("#calGrid");
  const labelEl = $("#calMonthLabel");
  const infoEl = $("#calSelectedInfo");
  if (!grid || !labelEl) return;

  labelEl.textContent = `${calYear}年 ${calMonth + 1}月`;

  const firstDay = new Date(calYear, calMonth, 1).getDay();
  const daysInMonth = new Date(calYear, calMonth + 1, 0).getDate();
  const today = todayKey();
  if (!calSelectedDate) calSelectedDate = today;

  const cells = [];
  for (let i = 0; i < firstDay; i++) {
    cells.push(`<div class="cal-cell is-empty" aria-hidden="true"></div>`);
  }

  for (let d = 1; d <= daysInMonth; d++) {
    const dateKey = `${calYear}-${String(calMonth + 1).padStart(2, "0")}-${String(d).padStart(2, "0")}`;
    const cnt = dateKey === today
      ? Math.max(Number(state.studyLog?.[dateKey] || 0), (state.studiedIdsToday || []).length)
      : Number(state.studyLog?.[dateKey] || 0);
    const heat = getHeatClass(cnt);
    const isToday = dateKey === today ? " is-today" : "";
    const isSel = dateKey === calSelectedDate ? " is-selected" : "";

    cells.push(`
      <button type="button" class="cal-cell ${heat}${isToday}${isSel}" data-cal-date="${dateKey}" aria-label="${calMonth + 1}月${d}日 ${cnt}語">
        <span>${d}</span>
        ${cnt > 0 ? `<span class="cal-cell-count">${cnt}</span>` : ""}
      </button>
    `);
  }

  grid.innerHTML = cells.join("");

  grid.querySelectorAll("[data-cal-date]").forEach((btn) => {
    btn.addEventListener("click", () => {
      calSelectedDate = btn.dataset.calDate;
      renderStudyCalendar();
    });
  });

  if (infoEl && calSelectedDate) {
    const [y, m, d] = calSelectedDate.split("-").map(Number);
    const selCount = calSelectedDate === today
      ? Math.max(Number(state.studyLog?.[calSelectedDate] || 0), (state.studiedIdsToday || []).length)
      : Number(state.studyLog?.[calSelectedDate] || 0);
    const prefix = calSelectedDate === today ? `今日（${m}月${d}日）` : `${y}年${m}月${d}日`;
    infoEl.textContent = `${prefix}：${selCount} 語`;
  }
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

  renderStudyCalendar();
  renderUnitBarsInto("#unitBarsContainer", state.levels);
}

/* =========================================================
   単語帳画面（文字入り複数選択カラーチップ・番号右に品詞・赤シート）
   ========================================================= */
function toggleVocabLevelChip(lv) {
  if (lv === "all") {
    vocabSelectedLevels.clear();
  } else {
    if (vocabSelectedLevels.has(lv)) {
      vocabSelectedLevels.delete(lv);
    } else {
      vocabSelectedLevels.add(lv);
    }
    if (vocabSelectedLevels.size === 0 || vocabSelectedLevels.size === 4) {
      vocabSelectedLevels.clear();
    }
  }
  renderVocabView();
}

function renderLevelFilterChips() {
  const wrap = $("#vocabLevelFilter");
  if (!wrap) return;
  const isAll = vocabSelectedLevels.size === 0;
  wrap.innerHTML = LEVEL_FILTERS.map((item) => {
    const isActive = item.level === "all" ? isAll : (!isAll && vocabSelectedLevels.has(item.level));
    return `
      <button
        type="button"
        class="level-chip${isActive ? " active" : ""}"
        data-level="${item.level}"
      >${escapeHtml(item.label)}</button>
    `;
  }).join("");

  $$("#vocabLevelFilter .level-chip").forEach((btn) => {
    btn.addEventListener("click", () => toggleVocabLevelChip(btn.dataset.level));
  });
}

function getFilteredVocab() {
  const s = Math.min(vocabMin, vocabMax);
  const e = Math.max(vocabMin, vocabMax);
  return wordsData.filter((w) => {
    if (w.no < s || w.no > e) return false;
    if (vocabSelectedLevels.size === 0) return true;
    const lv = String(Number(state.levels?.[w.no] || 0));
    return vocabSelectedLevels.has(lv);
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
    const derivList = derivativesMap.get(w.no) || [];
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

    const derivativesHtml = derivList.length
      ? `
        <div class="acc-block">
          <span class="acc-label">派生語</span>
          <div class="deriv-list">
            ${derivList.map((d) => `
              <div class="deriv-row">
                ${d.pos ? `<span class="pos-badge">${escapeHtml(d.pos)}</span>` : ""}
                <span class="deriv-word">${escapeHtml(d.word)}</span>
                <span class="deriv-meaning">${escapeHtml(d.meaning)}</span>
              </div>
            `).join("")}
          </div>
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
          ${derivativesHtml}
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
  const enSwitch = $("#toggleRedEn");
  const jaSwitch = $("#toggleRedJa");
  if (enSwitch) {
    enSwitch.classList.toggle("active", redEnActive);
    enSwitch.setAttribute("aria-checked", String(redEnActive));
  }
  if (jaSwitch) {
    jaSwitch.classList.toggle("active", redJaActive);
    jaSwitch.setAttribute("aria-checked", String(redJaActive));
  }
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

  if (triggerAudio || !listenState.playing) {
    clearTimeout(listenState.timerId);
  }
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
   学習画面（モード選択・マルチ選択チップ・フラッシュカード・確認テスト）
   ========================================================= */
function renderStudyLevelChips() {
  const isAll = studySelectedLevels.size === 0;
  $$("#studyLevelChips [data-study-lv]").forEach((btn) => {
    const lv = btn.dataset.studyLv;
    if (lv === "all") {
      btn.classList.toggle("active", isAll);
    } else {
      btn.classList.toggle("active", !isAll && studySelectedLevels.has(lv));
    }
  });
}

function toggleStudyLevelChip(lv) {
  if (lv === "all") {
    studySelectedLevels.clear();
  } else {
    if (studySelectedLevels.has(lv)) {
      studySelectedLevels.delete(lv);
    } else {
      studySelectedLevels.add(lv);
    }
    if (studySelectedLevels.size === 0 || studySelectedLevels.size === 4) {
      studySelectedLevels.clear();
    }
  }
  renderStudyLevelChips();
}

function openStudyPicker() {
  clearInterval(paperTimerId);
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#paperReadyPanel")?.classList.add("hidden");
  $("#paperStage")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.add("hidden");
  $("#studyPickerPanel")?.classList.remove("hidden");
  updateBackButtonVisibility();
}

function openStudySetupForMode(mode) {
  clearInterval(paperTimerId);
  const sMin = $("#studyMin");
  const sMax = $("#studyMax");
  if (sMin && !sMin.dataset.touched) sMin.value = prefs.goalMin || 1;
  if (sMax && !sMax.dataset.touched) sMax.value = prefs.goalMax || 100;

  renderStudyLevelChips();
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#paperReadyPanel")?.classList.add("hidden");
  $("#paperStage")?.classList.add("hidden");
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.remove("hidden");
  setStudyModeTab(mode);
  updateBackButtonVisibility();
}

function updateQuizFirstCharVisibility() {
  const qFmt = $("#quizFormatSelect")?.value || "ja-en-type";
  const isTyping = qFmt === "ja-en-type" || qFmt === "example-type" || qFmt === "derivative-type";
  $("#quizFirstCharRow")?.classList.toggle("hidden", !isTyping);
}

function setStudyModeTab(mode) {
  currentStudyMode = mode;
  $("#fcOptions")?.classList.toggle("hidden", mode !== "flashcard");
  $("#quizOptions")?.classList.toggle("hidden", mode !== "quiz");
  $("#paperOptions")?.classList.toggle("hidden", mode !== "paper");
  $("#listenOptions")?.classList.toggle("hidden", mode !== "listen");
  // 確認テストと筆記テストはランダム出題固定のため「出題順」行を非表示
  $("#studyOrderRow")?.classList.toggle("hidden", mode === "quiz" || mode === "paper");
  if (mode === "quiz") updateQuizFirstCharVisibility();

  const setupTitle = $("#studySetupTitle");
  const startBtn = $("#btnStartStudy");
  if (mode === "quiz") {
    if (setupTitle) setupTitle.textContent = "確認テストの設定";
    if (startBtn) startBtn.textContent = "確認テストをはじめる";
  } else if (mode === "paper") {
    if (setupTitle) setupTitle.textContent = "筆記テストの設定";
    if (startBtn) startBtn.textContent = "準備OK";
  } else if (mode === "listen") {
    if (setupTitle) setupTitle.textContent = "リスニングの設定";
    if (startBtn) startBtn.textContent = "リスニングをはじめる";
  } else {
    if (setupTitle) setupTitle.textContent = "フラッシュカードの設定";
    if (startBtn) startBtn.textContent = "フラッシュカードをはじめる";
  }
}

function exitStudyStages() {
  clearInterval(paperTimerId);
  setStudyLockMode(false);
  if ("speechSynthesis" in window) {
    try { window.speechSynthesis.cancel(); } catch (_) {}
  }
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#paperReadyPanel")?.classList.add("hidden");
  $("#paperStage")?.classList.add("hidden");
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.remove("hidden");
  updateBackButtonVisibility();
}

function buildStudyCandidates() {
  const rawMin = Number($("#studyMin")?.value || 1);
  const rawMax = Number($("#studyMax")?.value || 100);
  const s = Math.min(rawMin, rawMax);
  const e = Math.max(rawMin, rawMax);
  const order = $("#studyOrderSelect")?.value || "seq";

  let list = wordsData.filter((w) => {
    if (w.no < s || w.no > e) return false;
    if (studySelectedLevels.size > 0) {
      const lv = String(Number(state.levels?.[w.no] || 0));
      if (!studySelectedLevels.has(lv)) return false;
    }
    return true;
  });

  if (currentStudyMode === "flashcard") {
    const fFmt = $("#fcFormatSelect")?.value || "en-ja";
    if (fFmt === "example") {
      list = list.filter((w) => examplesMap.has(w.no));
    }
    if (order === "random") list = shuffleArray(list);
  } else if (currentStudyMode === "quiz") {
    const qFmt = $("#quizFormatSelect")?.value || "ja-en-type";
    if (qFmt === "example-type") {
      list = list.filter((w) => examplesMap.has(w.no));
    } else if (qFmt === "derivative-type") {
      const expanded = [];
      list.forEach((w) => {
        (derivativesMap.get(w.no) || []).forEach((d, idx) => {
          expanded.push({ ...w, _deriv: d, _qKey: `${w.no}_d${idx}` });
        });
      });
      list = expanded;
    }
    list = shuffleArray(list);
  } else if (currentStudyMode === "paper") {
    const pFmt = $("#paperFormatSelect")?.value || "en-ja";
    if (pFmt === "example") {
      list = list.filter((w) => examplesMap.has(w.no));
    } else if (pFmt === "derivative") {
      const expanded = [];
      list.forEach((w) => {
        (derivativesMap.get(w.no) || []).forEach((d, idx) => {
          expanded.push({ ...w, _deriv: d, _qKey: `${w.no}_d${idx}` });
        });
      });
      list = expanded;
    }
    list = shuffleArray(list);
  } else if (order === "random") {
    list = shuffleArray(list);
  }
  return list;
}

function startSelectedStudyMode() {
  const candidates = buildStudyCandidates();
  if (!candidates.length) {
    const isExampleMode =
      (currentStudyMode === "flashcard" && $("#fcFormatSelect")?.value === "example") ||
      (currentStudyMode === "quiz" && $("#quizFormatSelect")?.value === "example-type") ||
      (currentStudyMode === "paper" && $("#paperFormatSelect")?.value === "example");
    const isDerivativeMode =
      (currentStudyMode === "quiz" && $("#quizFormatSelect")?.value === "derivative-type") ||
      (currentStudyMode === "paper" && $("#paperFormatSelect")?.value === "derivative");
    if (isExampleMode) {
      showToast("この範囲に例文データがありません（No.301〜600 に収録）");
    } else if (isDerivativeMode) {
      showToast("この範囲に派生語データがありません");
    } else {
      showToast("条件に一致する単語がありません");
    }
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
    $("#paperStage")?.classList.add("hidden");
    $("#flashcardStage")?.classList.remove("hidden");
    setStudyLockMode(true);
    renderFlashcard(true);
    return;
  }

  if (currentStudyMode === "quiz") {
    const limit = Math.max(1, Number($("#quizLimitInput")?.value || 20));
    quizQueue = candidates.slice(0, limit);
    quizIndex = 0;
    quizFormat = $("#quizFormatSelect")?.value || "ja-en-type";
    quizShowFirstChar = ($("#quizShowFirstSelect")?.value || "show") === "show";
    prefs.showFirstChar = quizShowFirstChar;
    saveLocalPrefs();
    quizAnswers = {};
    quizIsRetest = false;
    openQuizStage();
    return;
  }

  if (currentStudyMode === "paper") {
    const limit = Math.max(1, Number($("#paperLimitInput")?.value || 20));
    paperQueue = candidates.slice(0, limit);
    paperFormat = $("#paperFormatSelect")?.value || "en-ja";
    paperConfiguredTimerSec = Number($("#paperTimerSelect")?.value || 0);
    openPaperReadyScreen();
  }
}

/* ---------- フラッシュカード（スワイプ・裏面確認必須・例文前後音声対応） ---------- */
function buildExampleSpeechText(rawEn, omitBracketed = false) {
  let s = String(rawEn || "");
  if (omitBracketed) {
    s = s.replace(/\[\[[^\]]+\]\]/g, ", ");
  } else {
    s = s.replace(/\[\[([^\]]+)\]\]/g, "$1");
  }
  // 補足記号 [at] 等は除去し、(for) のような丸括弧は語を残して自然な英文にする
  s = s.replace(/\[[^\]]*\]/g, "").replace(/[()]/g, "").replace(/\s+/g, " ").trim();
  return s;
}

function getFlashcardFrontAudioText(item) {
  if (!item) return "";
  const ex = (examplesMap.get(item.no) || [])[0] || null;
  if (fcFormat === "example" && ex) {
    return buildExampleSpeechText(ex.rawEn, true);
  }
  return item.word;
}

function getFlashcardBackAudioText(item) {
  if (!item) return "";
  const ex = (examplesMap.get(item.no) || [])[0] || null;
  if (fcFormat === "example" && ex) {
    return buildExampleSpeechText(ex.rawEn, false);
  }
  return item.word;
}

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
  const frontAudioBtn = $("#fcFrontAudioBtn");
  if (frontAudioBtn) {
    frontAudioBtn.classList.toggle("hidden", fcFormat === "ja-en");
  }

  if (wordFront) {
    if (fcFormat === "ja-en") {
      wordFront.textContent = item.meanings.join(" ／ ");
      wordFront.classList.add("is-ja");
      if (hintFront) hintFront.textContent = "タップで裏面をめくる";
    } else if (fcFormat === "example" && ex) {
      wordFront.innerHTML = formatExampleClozeHtml(ex.rawEn, item.word);
      wordFront.classList.add("is-ja");
      if (hintFront) hintFront.textContent = "タップで裏面をめくる";
    } else {
      wordFront.textContent = item.word;
      wordFront.classList.remove("is-ja");
      if (hintFront) hintFront.textContent = "タップで裏面をめくる";
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

  // 裏面をめくるまで「次へ」は押せないようにする
  const nextBtn = $("#fcNextBtn");
  if (nextBtn) {
    nextBtn.disabled = !fcFlipped;
    nextBtn.textContent = fcIndex + 1 >= fcQueue.length ? "完了する" : "次へ";
  }

  if (allowAutoSpeak && prefs.autoAudio) {
    if (!fcFlipped) {
      if (fcFormat === "en-ja") {
        speakEnglish(item.word);
      } else if (fcFormat === "example" && ex) {
        speakEnglish(buildExampleSpeechText(ex.rawEn, true));
      }
    } else {
      if (fcFormat === "example" && ex) {
        speakEnglish(buildExampleSpeechText(ex.rawEn, false));
      } else if (fcFormat === "ja-en") {
        speakEnglish(item.word);
      }
    }
  }
}

function advanceFlashcardNext() {
  if (!fcFlipped) {
    showToast("裏面をめくってから次へ進めます");
    return;
  }
  if (fcIndex + 1 < fcQueue.length) {
    fcIndex++;
    fcFlipped = false;
    renderFlashcard(true);
  } else {
    exitStudyStages();
    showToast("フラッシュカード学習が完了しました！");
  }
}

/* ---------- 確認テスト＆連続正解昇格ロジック ---------- */
function applyQuizResultToMastery(no, isCorrect) {
  const key = String(no);
  const prevLv = Number(state.levels?.[key] || 0);
  if (!state.streaks) state.streaks = {};

  let nextLv = prevLv;
  let streak = Number(state.streaks[key] || 0);
  let promoted = false;
  let demoted = false;

  if (isCorrect) {
    if (prevLv >= 3) {
      nextLv = 3;
      streak = STREAK_TO_PROMOTE;
    } else {
      streak += 1;
      if (streak >= STREAK_TO_PROMOTE) {
        nextLv = prevLv <= 1 ? 2 : 3;
        streak = 0;
        promoted = true;
      }
    }
  } else {
    streak = 0;
    nextLv = prevLv === 3 ? 2 : 1;
    if (nextLv !== prevLv) demoted = true;
  }

  state.streaks[key] = streak;
  setWordLevel(no, nextLv);
  return { isCorrect, prevLv, nextLv, streak, promoted, demoted };
}

function renderStreakPill(el, info) {
  if (!el) return;
  const levelNames = ["未学習", "苦手", "うろ覚え", "定着"];
  el.classList.toggle("promoted", Boolean(info.promoted));

  if (info.promoted) {
    el.textContent = `${STREAK_TO_PROMOTE}回連続正解！「${levelNames[info.prevLv]}」→「${levelNames[info.nextLv]}」にランクUP`;
    return;
  }
  if (info.isCorrect && info.nextLv >= 3) {
    el.textContent = "現在：定着（キープ中）";
    return;
  }
  if (info.isCorrect) {
    const dots = "●".repeat(info.streak) + "○".repeat(Math.max(0, STREAK_TO_PROMOTE - info.streak));
    const targetName = info.nextLv <= 1 ? "うろ覚え" : "定着";
    const rem = Math.max(1, STREAK_TO_PROMOTE - info.streak);
    el.textContent = `${dots} あと${rem}回連続正解で「${targetName}」（現在：${levelNames[info.nextLv]}）`;
    return;
  }
  el.textContent = `連続正解リセット ・ 現在：${levelNames[info.nextLv]}`;
}

function openQuizStage() {
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.add("hidden");
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.remove("hidden");
  $("#quizResultBox")?.classList.add("hidden");
  $("#quizRetestBadge")?.classList.toggle("hidden", !quizIsRetest);
  setStudyLockMode(true);

  if (quizFormat === "ja-en-type" || quizFormat === "example-type" || quizFormat === "derivative-type") {
    $("#quizSingleBox")?.classList.add("hidden");
    $("#quizProgressWrap")?.classList.remove("hidden");
    $("#quizSpellBox")?.classList.remove("hidden");
    renderSpellQuestion();
  } else {
    $("#quizSpellBox")?.classList.add("hidden");
    $("#quizProgressWrap")?.classList.remove("hidden");
    $("#quizSingleBox")?.classList.remove("hidden");
    renderQuizSingleQuestion();
  }
}

function getQuizItemKey(item) {
  return String(item?._qKey || item?.no || "");
}

/* ---------- タイピング入力テスト（文字数非表示・先頭1文字表示切替対応） ---------- */
function buildTypingSpecForWord(rawWord, showFirstChar = true) {
  let cleaned = String(rawWord || "").replace(/～/g, "").trim();
  const accepted = new Set();

  if (/\([a-zA-Z]+\)/.test(cleaned)) {
    const withoutOpt = cleaned.replace(/\([a-zA-Z]+\)/g, "").trim();
    const withOpt = cleaned.replace(/[()]/g, "").trim();
    accepted.add(withoutOpt.replace(/[^a-zA-Z]/g, "").toLowerCase());
    accepted.add(withOpt.replace(/[^a-zA-Z]/g, "").toLowerCase());
    cleaned = withoutOpt;
  } else {
    accepted.add(cleaned.replace(/[^a-zA-Z]/g, "").toLowerCase());
  }

  const alphaOnly = cleaned.replace(/[^a-zA-Z]/g, "").toLowerCase();
  const initial = alphaOnly[0] || "";
  return {
    firstChar: showFirstChar ? initial : "",
    initialChar: initial,
    accepted: Array.from(accepted).filter(Boolean),
    displayAnswer: rawWord
  };
}

function buildTypingSpecForExample(item, showFirstChar = true) {
  const exList = examplesMap.get(item.no) || [];
  const ex = exList[Math.floor(Math.random() * exList.length)] || null;
  if (!ex) {
    const fallback = buildTypingSpecForWord(item.word, showFirstChar);
    return {
      ...fallback,
      rawCloze: item.meanings.join(" ／ "),
      promptHtml: escapeHtml(item.meanings.join(" ／ ")),
      subNote: ""
    };
  }

  const m = ex.rawEn.match(/\[\[([^\]]+)\]\]/);
  if (!m) {
    const fallback = buildTypingSpecForWord(item.word, showFirstChar);
    return {
      ...fallback,
      rawCloze: ex.en,
      promptHtml: escapeHtml(ex.en),
      subNote: ex.ja
    };
  }

  const bracketPhrase = m[1].trim();
  const wordsInBracket = bracketPhrase.split(/\s+/);
  let targetToken = wordsInBracket[0];
  if (wordsInBracket.length > 1) {
    const headInitial = (item.word[0] || "").toLowerCase();
    const matched = wordsInBracket.find((w) => w.toLowerCase().startsWith(headInitial));
    if (matched) targetToken = matched;
  }

  const alphaTarget = targetToken.replace(/[^a-zA-Z]/g, "").toLowerCase();
  const initial = alphaTarget[0] || (item.word[0] || "").toLowerCase();
  const shownFirst = showFirstChar ? initial : "";
  const blankText = shownFirst ? `${escapeHtml(shownFirst)}…` : "（　　）";

  // [[...]] 内が複数語の場合は対象語のみ空欄にし、前後の補助語はそのまま残す
  const rawReplaced = wordsInBracket
    .map((w) => (w === targetToken ? "[[blank]]" : w))
    .join(" ");
  const rawCloze = ex.rawEn.replace(/\[\[([^\]]+)\]\]/, rawReplaced);

  const replacedInside = wordsInBracket
    .map((w) => (w === targetToken ? `__BLANK__` : escapeHtml(w)))
    .join(" ");
  const fullEscaped = escapeHtml(ex.rawEn).replace(
    /\[\[([^\]]+)\]\]/,
    replacedInside.replace("__BLANK__", `<span class="cloze-blank">${blankText}</span>`)
  );

  return {
    firstChar: shownFirst,
    initialChar: initial,
    accepted: [alphaTarget],
    displayAnswer: targetToken === item.word ? targetToken : `${targetToken}（原形: ${item.word}）`,
    rawCloze,
    promptHtml: fullEscaped,
    subNote: ex.ja || item.meanings.join(" ／ ")
  };
}

function buildTypingSpecForDerivative(item, showFirstChar = true) {
  const d = item._deriv || (derivativesMap.get(item.no) || [])[0];
  if (!d) {
    const fallback = buildTypingSpecForWord(item.word, showFirstChar);
    return {
      ...fallback,
      pos: item.pos || "",
      promptText: item.meanings.join(" ／ "),
      subNote: "",
      audioWord: item.word
    };
  }
  const wSpec = buildTypingSpecForWord(d.word, showFirstChar);
  return {
    ...wSpec,
    pos: d.pos || "",
    promptText: d.meaning,
    subNote: `派生元: ${item.word}（${item.meanings[0] || ""}）`,
    displayAnswer: `${d.word}（派生元: ${item.word}）`,
    audioWord: d.word
  };
}

function renderSpellQuestion() {
  const item = quizQueue[quizIndex];
  if (!item) return;

  if ($("#quizMetaText")) $("#quizMetaText").textContent = `問題 ${quizIndex + 1} / ${quizQueue.length}`;
  if ($("#quizProgressBar")) $("#quizProgressBar").style.width = `${((quizIndex + 1) / quizQueue.length) * 100}%`;
  if ($("#qSpellNo")) $("#qSpellNo").textContent = `No. ${item.no}`;

  const posEl = $("#qSpellPos");
  const meaningEl = $("#qSpellMeaning");
  const subNoteEl = $("#qSpellSubNote");

  if (quizFormat === "example-type") {
    const exSpec = buildTypingSpecForExample(item, quizShowFirstChar);
    spellFirstChar = exSpec.firstChar;
    spellAcceptedNormalized = exSpec.accepted;
    spellDisplayAnswer = exSpec.displayAnswer;
    spellAudioTargetWord = item.word;
    if (posEl) {
      posEl.textContent = item.pos || "";
      posEl.classList.toggle("hidden", !item.pos);
    }
    if (meaningEl) meaningEl.innerHTML = exSpec.promptHtml;
    if (subNoteEl) {
      subNoteEl.textContent = exSpec.subNote;
      subNoteEl.classList.toggle("hidden", !exSpec.subNote);
    }
  } else if (quizFormat === "derivative-type") {
    const dSpec = buildTypingSpecForDerivative(item, quizShowFirstChar);
    spellFirstChar = dSpec.firstChar;
    spellAcceptedNormalized = dSpec.accepted;
    spellDisplayAnswer = dSpec.displayAnswer;
    spellAudioTargetWord = dSpec.audioWord;
    if (posEl) {
      posEl.textContent = dSpec.pos || "";
      posEl.classList.toggle("hidden", !dSpec.pos);
    }
    if (meaningEl) meaningEl.textContent = dSpec.promptText;
    if (subNoteEl) {
      subNoteEl.textContent = dSpec.subNote;
      subNoteEl.classList.toggle("hidden", !dSpec.subNote);
    }
  } else {
    const wSpec = buildTypingSpecForWord(item.word, quizShowFirstChar);
    spellFirstChar = wSpec.firstChar;
    spellAcceptedNormalized = wSpec.accepted;
    spellDisplayAnswer = wSpec.displayAnswer;
    spellAudioTargetWord = item.word;
    if (posEl) {
      posEl.textContent = item.pos || "";
      posEl.classList.toggle("hidden", !item.pos);
    }
    if (meaningEl) meaningEl.textContent = item.meanings.join(" ／ ");
    if (subNoteEl) {
      subNoteEl.textContent = "";
      subNoteEl.classList.add("hidden");
    }
  }

  spellTypedRest = "";
  spellJudged = false;

  $("#qSpellAudio")?.classList.add("hidden");
  $("#qSpellFeedback")?.classList.add("hidden");
  $("#qSpellActionRow")?.classList.remove("hidden");
  $("#qSpellKeyboard")?.classList.remove("hidden");

  renderSpellInputBox(null);
}

function renderSpellInputBox(markResult = null) {
  const box = $("#qSpellDisplayBox");
  const firstEl = $("#qSpellFirstChar");
  const restEl = $("#qSpellTypedRest");
  if (firstEl) firstEl.textContent = spellFirstChar;
  if (restEl) restEl.textContent = spellTypedRest;
  if (box) {
    box.classList.remove("is-correct", "is-wrong");
    if (markResult === true) box.classList.add("is-correct");
    else if (markResult === false) box.classList.add("is-wrong");
  }
}

function handleSpellKeyInput(ch) {
  if (spellJudged) return;
  if (spellTypedRest.length >= 24) return;
  spellTypedRest += ch.toLowerCase();
  renderSpellInputBox(null);
}

function handleSpellBackspace() {
  if (spellJudged || !spellTypedRest.length) return;
  spellTypedRest = spellTypedRest.slice(0, -1);
  renderSpellInputBox(null);
}

function handleSpellClear() {
  if (spellJudged || !spellTypedRest.length) return;
  spellTypedRest = "";
  renderSpellInputBox(null);
}

function evaluateSpellSubmission() {
  if (spellJudged) return;
  const item = quizQueue[quizIndex];
  if (!item) return;

  spellJudged = true;
  const fullNormalized = (spellFirstChar + spellTypedRest).replace(/[^a-zA-Z]/g, "").toLowerCase();
  const isCorrect = spellAcceptedNormalized.includes(fullNormalized);
  const streakInfo = applyQuizResultToMastery(item.no, isCorrect);

  quizAnswers[getQuizItemKey(item)] = { correct: isCorrect, level: streakInfo.nextLv };

  renderSpellInputBox(isCorrect);
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
    corrEl.textContent = `正解: ${spellDisplayAnswer}`;
  }
  renderStreakPill($("#qSpellStreakInfo"), streakInfo);

  const nextBtn = $("#qSpellNextBtn");
  if (nextBtn) {
    nextBtn.textContent = quizIndex + 1 >= quizQueue.length ? "結果を見る" : "次の問題へ";
  }

  if (prefs.autoAudio) {
    speakEnglish(spellAudioTargetWord || item.word);
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

/* ---------- 自己採点テスト（英単語 → 日本語） ---------- */
function renderQuizSingleQuestion() {
  const item = quizQueue[quizIndex];
  if (!item) return;
  singleJudged = false;

  const metaEl = $("#quizMetaText");
  const progEl = $("#quizProgressBar");
  if (metaEl) metaEl.textContent = `問題 ${quizIndex + 1} / ${quizQueue.length}`;
  if (progEl) progEl.style.width = `${((quizIndex + 1) / quizQueue.length) * 100}%`;

  if ($("#qSingleNo")) $("#qSingleNo").textContent = `No. ${item.no}`;
  const ex = (examplesMap.get(item.no) || [])[0] || null;
  if ($("#qSinglePrompt")) $("#qSinglePrompt").textContent = item.word;
  if ($("#qSingleAnswerMain")) $("#qSingleAnswerMain").textContent = item.meanings.join(" ／ ");
  if ($("#qSingleAnswerSub")) {
    $("#qSingleAnswerSub").textContent = `${item.pos ? `[${item.pos}] ` : ""}${ex ? ex.en : ""}`;
  }

  $("#qBtnReveal")?.classList.remove("hidden");
  $("#qSingleAnswerArea")?.classList.add("hidden");
  $("#qSingleJudgeBtns")?.classList.remove("hidden");
  $("#qSingleFeedback")?.classList.add("hidden");

  if (prefs.autoAudio) {
    speakEnglish(item.word);
  }
}

function recordSingleQuizJudge(isCorrect) {
  if (singleJudged) return;
  const item = quizQueue[quizIndex];
  if (!item) return;
  singleJudged = true;

  const streakInfo = applyQuizResultToMastery(item.no, isCorrect);
  quizAnswers[getQuizItemKey(item)] = { correct: isCorrect, level: streakInfo.nextLv };

  $("#qSingleJudgeBtns")?.classList.add("hidden");
  $("#qSingleFeedback")?.classList.remove("hidden");
  renderStreakPill($("#qSingleStreakInfo"), streakInfo);

  const nextBtn = $("#qSingleNextBtn");
  if (nextBtn) {
    nextBtn.textContent = quizIndex + 1 >= quizQueue.length ? "結果を見る" : "次の問題へ";
  }
}

function advanceSingleQuizQuestion() {
  if (quizIndex + 1 < quizQueue.length) {
    quizIndex++;
    renderQuizSingleQuestion();
  } else {
    showQuizResults();
  }
}

function showQuizResults() {
  setStudyLockMode(false);
  updateBackButtonVisibility();
  $("#quizSpellBox")?.classList.add("hidden");
  $("#quizSingleBox")?.classList.add("hidden");
  $("#quizProgressWrap")?.classList.add("hidden");
  $("#quizResultBox")?.classList.remove("hidden");

  const total = quizQueue.length;
  const correctCount = quizQueue.filter((item) => quizAnswers[getQuizItemKey(item)]?.correct).length;
  const wrongItems = quizQueue.filter((item) => !quizAnswers[getQuizItemKey(item)]?.correct);

  if ($("#quizResultScore")) $("#quizResultScore").textContent = `${correctCount} / ${total} 正解`;
  if ($("#quizResultNote")) {
    const pct = Math.round((correctCount / Math.max(1, total)) * 100);
    $("#quizResultNote").textContent = `正答率 ${pct}% ・ 3回連続正解で評価が1段階UPします`;
  }

  const retestBtn = $("#qResultRetestBtn");
  if (retestBtn) {
    retestBtn.classList.toggle("hidden", wrongItems.length === 0);
  }
}

/* ---------- 筆記テスト（スタンバイ画面 → テスト用紙形式・タイマー・採点） ---------- */
function openPaperReadyScreen() {
  clearInterval(paperTimerId);
  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.add("hidden");
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#paperStage")?.classList.add("hidden");
  $("#paperReadyPanel")?.classList.remove("hidden");

  const summaryEl = $("#paperReadySummary");
  if (summaryEl) {
    const timeText = paperConfiguredTimerSec > 0 ? `制限時間 ${Math.round(paperConfiguredTimerSec / 60)}分` : "制限時間なし";
    summaryEl.textContent = `全 ${paperQueue.length} 問 ／ ${timeText}`;
  }
  updateBackButtonVisibility();
}

function formatTimerClock(sec) {
  const m = Math.floor(sec / 60);
  const s = sec % 60;
  return `残り ${String(m).padStart(2, "0")}:${String(s).padStart(2, "0")}`;
}

function openPaperStage(timerSec = 0) {
  clearInterval(paperTimerId);
  paperGradingMode = false;
  paperMarks = {};
  paperTimeLeftSec = Math.max(0, Number(timerSec) || 0);

  $("#studyPickerPanel")?.classList.add("hidden");
  $("#studySetupPanel")?.classList.add("hidden");
  $("#paperReadyPanel")?.classList.add("hidden");
  $("#flashcardStage")?.classList.add("hidden");
  $("#quizStage")?.classList.add("hidden");
  $("#paperStage")?.classList.remove("hidden");
  setStudyLockMode(true);

  $("#paperResultBox")?.classList.add("hidden");
  $("#paperSheetBox")?.classList.remove("hidden");
  $("#paperBottomActions")?.classList.remove("hidden");
  $("#paperGradingHelper")?.classList.add("hidden");
  $("#btnPaperRevealAnswers")?.classList.remove("hidden");
  $("#btnPaperFinishScore")?.classList.add("hidden");

  if ($("#paperMetaTitle")) $("#paperMetaTitle").textContent = `筆記テスト（全 ${paperQueue.length} 問）`;

  const timerBadge = $("#paperTimerBadge");
  if (timerBadge) {
    if (paperTimeLeftSec > 0) {
      timerBadge.textContent = formatTimerClock(paperTimeLeftSec);
      timerBadge.classList.remove("hidden", "urgent");
      paperTimerId = setInterval(() => {
        paperTimeLeftSec = Math.max(0, paperTimeLeftSec - 1);
        timerBadge.textContent = formatTimerClock(paperTimeLeftSec);
        timerBadge.classList.toggle("urgent", paperTimeLeftSec <= 30);
        if (paperTimeLeftSec <= 0) {
          clearInterval(paperTimerId);
          timerBadge.textContent = "時間終了";
          showToast("制限時間が終了しました。解答を開いて採点しましょう！");
        }
      }, 1000);
    } else {
      timerBadge.classList.add("hidden");
    }
  }

  updateBackButtonVisibility();
  renderPaperSheet();
}

function getPaperItemKey(item) {
  return String(item?._qKey || item?.no || "");
}

function getPaperQuestionData(item) {
  const ex = (examplesMap.get(item.no) || [])[0] || null;
  if (paperFormat === "ja-en") {
    return {
      pos: item.pos || "",
      speakWord: item.word,
      promptHtml: escapeHtml(item.meanings.join(" ／ ")),
      answerText: item.word
    };
  }
  if (paperFormat === "derivative") {
    const d = item._deriv || (derivativesMap.get(item.no) || [])[0];
    if (d) {
      return {
        pos: d.pos || "",
        speakWord: d.word,
        promptHtml: `${escapeHtml(d.meaning)} <span class="sub-label">（派生元: ${escapeHtml(item.word)}）</span>`,
        answerText: d.word
      };
    }
  }
  if (paperFormat === "example" && ex) {
    return {
      pos: item.pos || "",
      speakWord: item.word,
      promptHtml: `${formatExampleClozeHtml(ex.rawEn, item.word)}${ex.ja ? `<div style="font-size:0.8rem;color:var(--text-sub);font-weight:600;margin-top:3px;">${escapeHtml(ex.ja)}</div>` : ""}`,
      answerText: `${item.word}（${item.meanings[0] || ""}）`
    };
  }
  return {
    pos: item.pos || "",
    speakWord: item.word,
    promptHtml: escapeHtml(item.word),
    answerText: item.meanings.join(" ／ ")
  };
}

function renderPaperSheet() {
  const listEl = $("#paperItemsList");
  if (!listEl) return;

  listEl.innerHTML = paperQueue.map((item, idx) => {
    const qData = getPaperQuestionData(item);
    const key = getPaperItemKey(item);
    const mark = paperMarks[key];
    return `
      <div class="paper-item-row" data-paper-no="${item.no}">
        <div class="paper-q-head">
          <span class="paper-q-num">問 ${idx + 1}　No.${item.no}${qData.pos ? ` [${escapeHtml(qData.pos)}]` : ""}</span>
          ${paperGradingMode ? `<button type="button" class="audio-pill" data-paper-speak="${escapeHtml(qData.speakWord)}" style="padding:3px 8px;font-size:0.7rem;">発音</button>` : ""}
        </div>
        <div class="paper-q-prompt">${qData.promptHtml}</div>
        ${!paperGradingMode
          ? `<div class="paper-write-line" aria-hidden="true"></div>`
          : `
            <div class="paper-ans-row">
              <div class="paper-ans-text">${escapeHtml(qData.answerText)}</div>
              <div class="paper-ox-btns">
                <button type="button" class="paper-ox-mini wrong${mark === false ? " selected" : ""}" data-paper-mark="wrong" data-key="${escapeHtml(key)}" aria-label="不正解">×</button>
                <button type="button" class="paper-ox-mini correct${mark === true ? " selected" : ""}" data-paper-mark="correct" data-key="${escapeHtml(key)}" aria-label="正解">○</button>
              </div>
            </div>
          `
        }
      </div>
    `;
  }).join("");

  if (paperGradingMode) {
    listEl.querySelectorAll("[data-paper-speak]").forEach((btn) => {
      btn.addEventListener("click", () => speakEnglish(btn.dataset.paperSpeak || ""));
    });
    listEl.querySelectorAll("[data-paper-mark]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const key = btn.dataset.key;
        paperMarks[key] = btn.dataset.paperMark === "correct";
        renderPaperSheet();
      });
    });
  }
}

function revealPaperAnswers() {
  clearInterval(paperTimerId);
  paperGradingMode = true;
  $("#paperGradingHelper")?.classList.remove("hidden");
  $("#btnPaperRevealAnswers")?.classList.add("hidden");
  $("#btnPaperFinishScore")?.classList.remove("hidden");
  renderPaperSheet();
}

function finishPaperScoring() {
  setStudyLockMode(false);
  updateBackButtonVisibility();
  let correctCount = 0;
  paperQueue.forEach((item) => {
    const key = getPaperItemKey(item);
    const isOk = paperMarks[key] === true;
    paperMarks[key] = isOk;
    if (isOk) correctCount++;
    applyQuizResultToMastery(item.no, isOk);
  });

  const total = paperQueue.length;
  const pct = Math.round((correctCount / Math.max(1, total)) * 100);
  const wrongCount = total - correctCount;

  $("#paperSheetBox")?.classList.add("hidden");
  $("#paperBottomActions")?.classList.add("hidden");
  $("#paperGradingHelper")?.classList.add("hidden");
  $("#paperTimerBadge")?.classList.add("hidden");
  $("#paperResultBox")?.classList.remove("hidden");

  if ($("#paperResultScore")) $("#paperResultScore").textContent = `${correctCount} / ${total} 点（${pct}%）`;
  if ($("#paperResultNote")) $("#paperResultNote").textContent = "結果を連続正解カウント・学習記録に反映しました";
  $("#btnPaperRetestWrong")?.classList.toggle("hidden", wrongCount === 0);
}

/* =========================================================
   フレンド・対戦画面（日本語→英語スペリング固定対戦 ＆ 相互承認フレンド）
   ========================================================= */
const BATTLE_FORMAT_LABELS = {
  "ja-en": "日本語 → 英語",
  "example": "例文",
  "derivative": "派生語"
};

function updateBattleAuthBanner() {
  const notice = $("#battleAuthNotice");
  if (!notice) return;
  const loggedIn = Boolean((firebaseReady && currentUser) || state.ownerUid);
  notice.classList.toggle("hidden", loggedIn);
}

function openBattlePicker() {
  leaveBattleRoom();
  $("#battleMatchPanel")?.classList.add("hidden");
  $("#battleFriendPanel")?.classList.add("hidden");
  $("#battlePickerPanel")?.classList.remove("hidden");
  const titleEl = $("#headerTitle");
  if (titleEl) titleEl.textContent = "フレンド";
  updateBackButtonVisibility();
}

function openBattleSubPanel(panelType) {
  $("#battlePickerPanel")?.classList.add("hidden");
  $("#battleMatchPanel")?.classList.toggle("hidden", panelType !== "match");
  $("#battleFriendPanel")?.classList.toggle("hidden", panelType !== "friends");
  const titleEl = $("#headerTitle");
  if (titleEl) titleEl.textContent = panelType === "match" ? "リアルタイム対戦" : "フレンド一覧";
  updateSyncUi();
  updateBattleAuthBanner();
  if (panelType === "friends") {
    checkOutgoingFriendApprovals().then(() => renderFriendsList());
    renderFriendsList();
  }
  updateBackButtonVisibility();
}

function renderBattleFriendView() {
  updateSyncUi();
  updateBattleAuthBanner();
  renderFriendsList();
}

function buildBattleQuestions(minNo, maxNo, count, format = "ja-en", showFirstChar = true) {
  const s = Math.min(minNo, maxNo);
  const e = Math.max(minNo, maxNo);

  if (format === "example") {
    const exCandidates = wordsData.filter((w) => w.no >= s && w.no <= e && examplesMap.has(w.no));
    if (!exCandidates.length) return [];
    const picked = shuffleArray(exCandidates).slice(0, count);
    return picked.map((target) => {
      const exSpec = buildTypingSpecForExample(target, showFirstChar);
      return {
        qType: "example",
        no: target.no,
        pos: target.pos || "",
        prompt: exSpec.rawCloze,
        subNote: exSpec.subNote || "",
        answerWord: exSpec.displayAnswer,
        showFirstChar: Boolean(showFirstChar),
        firstChar: exSpec.firstChar,
        initialChar: exSpec.initialChar,
        accepted: exSpec.accepted
      };
    });
  }

  if (format === "derivative") {
    const derivPool = [];
    wordsData.forEach((w) => {
      if (w.no < s || w.no > e) return;
      (derivativesMap.get(w.no) || []).forEach((d) => {
        derivPool.push({ w, d });
      });
    });
    if (!derivPool.length) return [];
    const picked = shuffleArray(derivPool).slice(0, count);
    return picked.map(({ w, d }) => {
      const spec = buildTypingSpecForWord(d.word, showFirstChar);
      return {
        qType: "derivative",
        no: w.no,
        pos: d.pos || "",
        prompt: d.meaning,
        subNote: `派生元: ${w.word}（${w.meanings[0] || ""}）`,
        answerWord: `${d.word}（派生元: ${w.word}）`,
        showFirstChar: Boolean(showFirstChar),
        firstChar: spec.firstChar,
        initialChar: spec.initialChar,
        accepted: spec.accepted
      };
    });
  }

  const pool = wordsData.filter((w) => w.no >= s && w.no <= e);
  if (!pool.length) return [];
  const picked = shuffleArray(pool).slice(0, count);

  return picked.map((target) => {
    const spec = buildTypingSpecForWord(target.word, showFirstChar);
    return {
      qType: "ja-en",
      no: target.no,
      pos: target.pos || "",
      prompt: target.meanings.join(" ／ "),
      subNote: "",
      answerWord: target.word,
      showFirstChar: Boolean(showFirstChar),
      firstChar: spec.firstChar,
      initialChar: spec.initialChar,
      accepted: spec.accepted
    };
  });
}

function myPlayerId() {
  return currentUser?.uid || state.ownerUid || `local_${state.friendId}`;
}

function myPlayerName() {
  return state.nickname || state.loginId || "プレイヤー";
}

async function createBattleRoomAction() {
  const minNo = Number($("#battleMin")?.value || 1);
  const maxNo = Number($("#battleMax")?.value || 100);
  const count = Number($("#battleCount")?.value || 10);
  const format = $("#battleFormat")?.value || "ja-en";
  const showFirstChar = ($("#battleShowFirst")?.value || "show") === "show";

  const questions = buildBattleQuestions(minNo, maxNo, count, format, showFirstChar);
  if (!questions.length) {
    if (format === "example") {
      showToast("この範囲に例文データがありません（No.301〜600 に収録）");
    } else if (format === "derivative") {
      showToast("この範囲に派生語データがありません");
    } else {
      showToast("選択した範囲に問題データがありません");
    }
    return;
  }

  if (!firebaseReady && navigator.onLine !== false) {
    await startBackgroundFirebaseSync();
  }

  const code = generateCode(6);
  const pid = myPlayerId();
  const players = {
    [pid]: { name: myPlayerName(), score: 0, progress: 0, finished: false }
  };

  battleSession = {
    roomCode: code,
    isHost: true,
    localOnly: !(firebaseReady && db && currentUser),
    format,
    showFirstChar,
    minNo: Math.min(minNo, maxNo),
    maxNo: Math.max(minNo, maxNo),
    count: questions.length,
    questions,
    currentIndex: 0,
    answeredCurrent: false,
    timeLeft: 15,
    players
  };

  if (!battleSession.localOnly) {
    try {
      await setDoc(doc(db, "battleRooms", code), {
        roomCode: code,
        hostId: pid,
        status: "waiting",
        minNo: battleSession.minNo,
        maxNo: battleSession.maxNo,
        count: battleSession.count,
        format,
        showFirstChar,
        questions,
        players,
        createdAt: serverTimestamp()
      });
      subscribeBattleRoom(code);
    } catch (err) {
      console.warn("Battle room cloud creation fallback:", err);
      battleSession.localOnly = true;
      showToast("通信できないため一人練習モードで開始します");
    }
  } else {
    showToast("一人練習モードでルームを作成しました");
  }

  showBattleWaitingRoom();
}

async function joinBattleRoomAction() {
  const code = ($("#battleJoinCodeInput")?.value || "").trim().toUpperCase();
  if (!code) {
    showToast("合言葉を入力してください");
    return;
  }
  if (!firebaseReady && navigator.onLine !== false) {
    await startBackgroundFirebaseSync();
  }
  if (!firebaseReady || !db || !currentUser) {
    showToast("合言葉での通信対戦にはログインが必要です");
    return;
  }

  try {
    const ref = doc(db, "battleRooms", code);
    const snap = await getDoc(ref);
    if (!snap.exists()) {
      showToast("ルームが見つかりません（合言葉をご確認ください）");
      return;
    }
    const data = snap.data();
    if (data.status === "finished" || data.status === "closed") {
      showToast("このルームの対戦はすでに終了しています");
      return;
    }
    const pid = myPlayerId();
    const myEntry = {
      name: myPlayerName(),
      score: data.players?.[pid]?.score || 0,
      progress: data.players?.[pid]?.progress || 0,
      finished: false
    };
    await updateDoc(ref, { [`players.${pid}`]: myEntry });

    const updatedPlayers = {
      ...(data.players || {}),
      [pid]: myEntry
    };

    battleSession = {
      roomCode: code,
      isHost: data.hostId === pid,
      localOnly: false,
      format: data.format || "ja-en",
      showFirstChar: data.showFirstChar !== false,
      minNo: data.minNo || 1,
      maxNo: data.maxNo || 100,
      count: data.count || (data.questions?.length || 10),
      questions: data.questions || [],
      currentIndex: 0,
      answeredCurrent: false,
      timeLeft: 15,
      players: updatedPlayers
    };

    showBattleWaitingRoom();
    subscribeBattleRoom(code);
    if (data.status === "playing") {
      beginBattlePlayLoop();
    }
  } catch (err) {
    console.warn("Join room error:", err);
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
    if (data.format) battleSession.format = data.format;
    if (data.showFirstChar !== undefined) battleSession.showFirstChar = Boolean(data.showFirstChar);
    if (data.minNo) battleSession.minNo = data.minNo;
    if (data.maxNo) battleSession.maxNo = data.maxNo;
    if (data.count) battleSession.count = data.count;

    if (!$("#battleWaitingRoom")?.classList.contains("hidden")) {
      updateBattleWaitingMeta();
      renderWaitingPlayers();
    }
    renderBattleScoreboard();

    if (data.status === "playing" && $("#battlePlayStage")?.classList.contains("hidden") && $("#battleResultBox")?.classList.contains("hidden")) {
      beginBattlePlayLoop();
    }
    if (!$("#battleResultBox")?.classList.contains("hidden")) {
      renderBattleResults();
    }
  }, (err) => {
    console.warn("Battle snapshot error:", err);
  });
}

function updateBattleWaitingMeta() {
  const metaEl = $("#battleRoomMeta");
  if (!metaEl) return;
  const fmtLabel = BATTLE_FORMAT_LABELS[battleSession.format] || "日本語 → 英語";
  const firstHintLabel = battleSession.showFirstChar ? "1文字目あり" : "1文字目なし";
  const modeNote = battleSession.localOnly ? " ／ 一人練習" : "";
  metaEl.textContent = `範囲 No.${battleSession.minNo}〜${battleSession.maxNo} ／ ${battleSession.count}問 ／ ${fmtLabel}（${firstHintLabel}）${modeNote}`;
}

function showBattleWaitingRoom() {
  $("#battleLobby")?.classList.add("hidden");
  $("#battlePlayStage")?.classList.add("hidden");
  $("#battleResultBox")?.classList.add("hidden");
  $("#battleWaitingRoom")?.classList.remove("hidden");

  if ($("#battleRoomCodeDisplay")) $("#battleRoomCodeDisplay").textContent = battleSession.roomCode;
  updateBattleWaitingMeta();

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
  setStudyLockMode(true);
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

function renderBattleSpellBox(markResult = null) {
  const box = $("#battleSpellDisplayBox");
  const firstEl = $("#battleSpellFirstChar");
  const restEl = $("#battleSpellTypedRest");
  if (firstEl) firstEl.textContent = battleSpellFirstChar;
  if (restEl) restEl.textContent = battleSpellTypedRest;
  if (box) {
    box.classList.remove("is-correct", "is-wrong");
    if (markResult === true) box.classList.add("is-correct");
    else if (markResult === false) box.classList.add("is-wrong");
  }
}

function renderBattleQuestion() {
  clearInterval(battleTimerId);
  const q = battleSession.questions[battleSession.currentIndex];
  if (!q) {
    finishBattleMatch();
    return;
  }

  const useFirstChar = q.showFirstChar !== undefined ? Boolean(q.showFirstChar) : Boolean(battleSession.showFirstChar);
  const fallbackSpec = !q.accepted ? buildTypingSpecForWord(q.answerWord || "", useFirstChar) : null;
  battleSpellFirstChar = useFirstChar ? (q.firstChar || q.initialChar || fallbackSpec?.firstChar || "") : "";
  battleSpellAccepted = q.accepted || fallbackSpec?.accepted || [];
  battleSpellDisplayAns = q.answerWord || "";
  battleSpellTypedRest = "";

  battleSession.answeredCurrent = false;
  battleSession.timeLeft = 15;

  renderBattleScoreboard();
  if ($("#battleQCounter")) $("#battleQCounter").textContent = `${battleSession.currentIndex + 1} / ${battleSession.questions.length}`;
  if ($("#battleQNo")) $("#battleQNo").textContent = `No. ${q.no}`;
  const posEl = $("#battleQPos");
  if (posEl) {
    posEl.textContent = q.pos || "";
    posEl.classList.toggle("hidden", !q.pos);
  }

  const promptEl = $("#battlePrompt");
  if (promptEl) {
    if (q.qType === "example" && String(q.prompt || "").includes("[[blank]]")) {
      const blankDisplay = battleSpellFirstChar ? `${escapeHtml(battleSpellFirstChar)}…` : "（　　）";
      promptEl.innerHTML = escapeHtml(q.prompt).replace("[[blank]]", `<span class="cloze-blank">${blankDisplay}</span>`);
    } else {
      promptEl.textContent = q.prompt || "";
    }
  }

  const subNoteEl = $("#battleSubNote");
  if (subNoteEl) {
    subNoteEl.textContent = q.subNote || "";
    subNoteEl.classList.toggle("hidden", !q.subNote);
  }

  if ($("#battleTimerText")) $("#battleTimerText").textContent = "15秒";
  if ($("#battleTimerBar")) $("#battleTimerBar").style.width = "100%";

  $("#battleSpellFeedback")?.classList.add("hidden");
  $("#battleSpellActionRow")?.classList.remove("hidden");
  $("#battleSpellKeyboard")?.classList.remove("hidden");
  renderBattleSpellBox(null);

  battleTimerId = setInterval(() => {
    battleSession.timeLeft = Math.max(0, battleSession.timeLeft - 1);
    if ($("#battleTimerText")) $("#battleTimerText").textContent = `${battleSession.timeLeft}秒`;
    if ($("#battleTimerBar")) $("#battleTimerBar").style.width = `${(battleSession.timeLeft / 15) * 100}%`;
    if (battleSession.timeLeft <= 0) {
      clearInterval(battleTimerId);
      submitBattleSpelling(true);
    }
  }, 1000);
}

function handleBattleKeyInput(ch) {
  if (battleSession.answeredCurrent) return;
  if (battleSpellTypedRest.length >= 24) return;
  battleSpellTypedRest += ch.toLowerCase();
  renderBattleSpellBox(null);
}

function handleBattleBackspace() {
  if (battleSession.answeredCurrent || !battleSpellTypedRest.length) return;
  battleSpellTypedRest = battleSpellTypedRest.slice(0, -1);
  renderBattleSpellBox(null);
}

function handleBattleClear() {
  if (battleSession.answeredCurrent || !battleSpellTypedRest.length) return;
  battleSpellTypedRest = "";
  renderBattleSpellBox(null);
}

async function submitBattleSpelling(timedOut = false) {
  if (battleSession.answeredCurrent) return;
  battleSession.answeredCurrent = true;
  clearInterval(battleTimerId);

  const fullNormalized = (battleSpellFirstChar + battleSpellTypedRest).replace(/[^a-zA-Z]/g, "").toLowerCase();
  const isCorrect = !timedOut && battleSpellAccepted.includes(fullNormalized);
  const pid = myPlayerId();
  let bonus = 0;

  const prev = battleSession.players[pid]?.score || 0;
  if (isCorrect) {
    bonus = 10 + Math.max(0, battleSession.timeLeft);
  }
  const nextScore = prev + bonus;
  const nextProgress = battleSession.currentIndex + 1;
  battleSession.players[pid] = {
    name: myPlayerName(),
    score: nextScore,
    progress: nextProgress,
    finished: nextProgress >= battleSession.questions.length
  };

  if (!battleSession.localOnly && firebaseReady && db) {
    try {
      await updateDoc(doc(db, "battleRooms", battleSession.roomCode), {
        [`players.${pid}.score`]: nextScore,
        [`players.${pid}.name`]: myPlayerName(),
        [`players.${pid}.progress`]: nextProgress
      });
    } catch (_) {}
  }

  renderBattleSpellBox(isCorrect);
  renderBattleScoreboard();
  $("#battleSpellActionRow")?.classList.add("hidden");
  $("#battleSpellKeyboard")?.classList.add("hidden");
  $("#battleSpellFeedback")?.classList.remove("hidden");

  const badge = $("#battleSpellJudgeBadge");
  if (badge) {
    badge.textContent = isCorrect ? `○ 正解！ (+${bonus}pt)` : (timedOut ? "時間切れ" : "× 不正解");
    badge.className = `spell-judge-badge ${isCorrect ? "ok" : "ng"}`;
  }
  if ($("#battleSpellCorrectWord")) {
    $("#battleSpellCorrectWord").textContent = `正解: ${battleSpellDisplayAns}`;
  }

  setTimeout(advanceBattleQuestion, 950);
}

function advanceBattleQuestion() {
  if (battleSession.currentIndex + 1 < battleSession.questions.length) {
    battleSession.currentIndex++;
    renderBattleQuestion();
  } else {
    finishBattleMatch();
  }
}

async function finishBattleMatch() {
  clearInterval(battleTimerId);
  setStudyLockMode(false);
  updateBackButtonVisibility();
  $("#battlePlayStage")?.classList.add("hidden");
  $("#battleResultBox")?.classList.remove("hidden");

  const pid = myPlayerId();
  if (battleSession.players[pid]) {
    battleSession.players[pid].finished = true;
  }
  if (!battleSession.localOnly && firebaseReady && db && battleSession.roomCode) {
    try {
      const updates = { [`players.${pid}.finished`]: true };
      if (battleSession.isHost) updates.status = "finished";
      await updateDoc(doc(db, "battleRooms", battleSession.roomCode), updates);
    } catch (_) {}
  }
  renderBattleResults();
}

function renderBattleResults() {
  const listEl = $("#battleResultList");
  if (!listEl) return;
  const sorted = Object.values(battleSession.players || {}).sort((a, b) => (b.score || 0) - (a.score || 0));
  listEl.innerHTML = sorted.map((p, i) => {
    const progNote = p.finished === false && p.progress !== undefined
      ? ` <span class="sub-label">（解答中 ${p.progress}/${battleSession.questions.length}）</span>`
      : "";
    return `
      <div class="battle-player-row">
        <span><strong style="margin-right:6px;">${i + 1}位</strong>${escapeHtml(p.name)}${progNote}</span>
        <strong>${p.score || 0} pt</strong>
      </div>
    `;
  }).join("");
}

function leaveBattleRoom() {
  const wasWaiting = !$("#battleWaitingRoom")?.classList.contains("hidden");
  const prevCode = battleSession.roomCode;
  const wasLocal = battleSession.localOnly;
  const wasHost = battleSession.isHost;

  clearInterval(battleTimerId);
  setStudyLockMode(false);
  if (battleRoomUnsub) { battleRoomUnsub(); battleRoomUnsub = null; }

  if (wasWaiting && !wasLocal && prevCode && firebaseReady && db) {
    const pid = myPlayerId();
    if (wasHost) {
      updateDoc(doc(db, "battleRooms", prevCode), { status: "closed" }).catch(() => {});
    } else if (deleteField) {
      updateDoc(doc(db, "battleRooms", prevCode), { [`players.${pid}`]: deleteField() }).catch(() => {});
    }
  }
  battleSession.roomCode = "";

  $("#battleWaitingRoom")?.classList.add("hidden");
  $("#battlePlayStage")?.classList.add("hidden");
  $("#battleResultBox")?.classList.add("hidden");
  $("#battleLobby")?.classList.remove("hidden");
  updateBackButtonVisibility();
}

/* ---------- フレンド機能（相互承認必須） ---------- */
async function checkOutgoingFriendApprovals() {
  if (!firebaseReady || !db || !currentUser) return;
  const pending = state.outgoingFriends || [];
  if (!pending.length) return;

  let changed = false;
  const remainingOut = [];
  const remainingUids = [];

  for (const item of pending) {
    if (!item.uid) continue;
    try {
      const snap = await getDoc(doc(db, "users", item.uid));
      if (!snap.exists()) {
        remainingOut.push(item);
        remainingUids.push(item.uid);
        continue;
      }
      const rData = snap.data();
      const approvedMe =
        (Array.isArray(rData.friendUids) && rData.friendUids.includes(currentUser.uid)) ||
        (Array.isArray(rData.friends) && rData.friends.some((f) => f.uid === currentUser.uid || f.friendId === state.friendId));

      if (approvedMe) {
        if (!(state.friends || []).some((f) => f.uid === item.uid || f.friendId === item.friendId)) {
          state.friends.push({
            uid: item.uid,
            nickname: rData.nickname || item.nickname || item.friendId,
            friendId: rData.friendId || item.friendId
          });
        }
        if (!(state.friendUids || []).includes(item.uid)) {
          state.friendUids.push(item.uid);
        }
        changed = true;
      } else {
        remainingOut.push({
          uid: item.uid,
          nickname: rData.nickname || item.nickname || item.friendId,
          friendId: rData.friendId || item.friendId
        });
        remainingUids.push(item.uid);
      }
    } catch (_) {
      remainingOut.push(item);
      remainingUids.push(item.uid);
    }
  }

  if (changed || remainingUids.length !== (state.outgoingFriendUids || []).length) {
    state.outgoingFriends = remainingOut;
    state.outgoingFriendUids = remainingUids;
    saveLocalState(true);
    await pushCloudStateNow();
  }
}

async function sendFriendRequestAction() {
  let targetCode = ($("#friendAddInput")?.value || "").trim().toUpperCase();
  if (!targetCode) {
    showToast("相手のフレンドIDを入力してください");
    return;
  }
  if (!targetCode.startsWith("HN-")) targetCode = `HN-${targetCode}`;

  if (targetCode === state.friendId) {
    showToast("自分のフレンドIDは申請できません");
    return;
  }
  if ((state.friends || []).some((f) => f.friendId === targetCode)) {
    showToast("すでにフレンド登録済みです");
    return;
  }
  if ((state.outgoingFriends || []).some((f) => f.friendId === targetCode)) {
    showToast("すでに申請済みです（相手の承認待ち）");
    return;
  }
  if (!firebaseReady || !db || !currentUser) {
    showToast("フレンド申請にはログインが必要です");
    return;
  }

  try {
    let snap = await getDocs(query(collection(db, "users"), where("friendId", "==", targetCode)));
    if (snap.empty) {
      snap = await getDocs(query(collection(db, "users"), where("friendCode", "==", targetCode)));
    }
    if (snap.empty) {
      showToast("該当するフレンドIDが見つかりません");
      return;
    }

    const friendDoc = snap.docs[0];
    const fData = friendDoc.data();
    const targetUid = friendDoc.id;
    const targetName = fData.nickname || fData.loginId || targetCode;

    // 相手がすでに自分に申請していた／自分を承認していた場合はその場で相互フレンド成立
    const alreadyRequestedMe =
      (Array.isArray(fData.outgoingFriendUids) && fData.outgoingFriendUids.includes(currentUser.uid)) ||
      (Array.isArray(fData.friendUids) && fData.friendUids.includes(currentUser.uid));

    if (alreadyRequestedMe) {
      state.friends.push({ uid: targetUid, nickname: targetName, friendId: targetCode });
      if (!state.friendUids.includes(targetUid)) state.friendUids.push(targetUid);
      saveLocalState(true);
      await pushCloudStateNow();
      if ($("#friendAddInput")) $("#friendAddInput").value = "";
      mergeAndRenderIncomingRequests();
      renderFriendsList();
      showToast(`${targetName} さんとフレンドになりました！`);
      return;
    }

    // 相手が承認するまでは outgoing（承認待ち）にのみ保持し、friends には入れない
    if (!Array.isArray(state.outgoingFriendUids)) state.outgoingFriendUids = [];
    if (!Array.isArray(state.outgoingFriends)) state.outgoingFriends = [];
    if (!state.outgoingFriendUids.includes(targetUid)) state.outgoingFriendUids.push(targetUid);
    state.outgoingFriends.push({ uid: targetUid, nickname: targetName, friendId: targetCode });

    saveLocalState(true);
    await pushCloudStateNow();

    try {
      await addDoc(collection(db, "friendRequests"), {
        fromUid: currentUser.uid,
        fromName: myPlayerName(),
        fromFriendId: state.friendId,
        toUid: targetUid,
        status: "pending",
        createdAt: serverTimestamp()
      });
    } catch (_) {}

    if ($("#friendAddInput")) $("#friendAddInput").value = "";
    renderFriendsList();
    showToast("フレンド申請を送りました（相手の承認後に閲覧できます）");
  } catch (err) {
    console.warn("Friend request error:", err);
    showToast("申請の送信に失敗しました");
  }
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
      <button type="button" class="primary-btn" data-accept-uid="${escapeHtml(r.fromUid)}">承認</button>
    </div>
  `).join("");

  listEl.querySelectorAll("[data-accept-uid]").forEach((btn) => {
    btn.addEventListener("click", async () => {
      const req = reqs.find((x) => x.fromUid === btn.dataset.acceptUid);
      if (!req) return;
      if (!(state.friends || []).some((f) => f.uid === req.fromUid || f.friendId === req.fromFriendId)) {
        state.friends.push({
          uid: req.fromUid,
          nickname: req.fromName || req.fromFriendId,
          friendId: req.fromFriendId
        });
      }
      if (!Array.isArray(state.friendUids)) state.friendUids = [];
      if (req.fromUid && !state.friendUids.includes(req.fromUid)) {
        state.friendUids.push(req.fromUid);
      }
      saveLocalState(true);
      await pushCloudStateNow();

      if (firebaseReady && db && req.reqDocId) {
        try { await updateDoc(doc(db, "friendRequests", req.reqDocId), { status: "accepted" }); } catch (_) {}
      }
      mergeAndRenderIncomingRequests();
      renderFriendsList();
      showToast("フレンド申請を承認しました");
    });
  });
}

function renderFriendsList() {
  // 1) 承認待ち（送信済み）リストの描画（タップしても進捗は見られない）
  const outCard = $("#friendPendingOutCard");
  const outList = $("#friendPendingOutList");
  const pendingOut = state.outgoingFriends || [];
  if (outCard && outList) {
    if (!pendingOut.length) {
      outCard.classList.add("hidden");
    } else {
      outCard.classList.remove("hidden");
      outList.innerHTML = pendingOut.map((p) => `
        <div class="friend-row">
          <div>
            <strong>${escapeHtml(p.nickname || "ユーザー")}</strong>
            <div class="sub-label">${escapeHtml(p.friendId || "")} ・ 承認待ち</div>
          </div>
          <button type="button" class="text-btn" data-cancel-out="${escapeHtml(p.uid)}">取消</button>
        </div>
      `).join("");

      outList.querySelectorAll("[data-cancel-out]").forEach((btn) => {
        btn.addEventListener("click", async () => {
          const targetUid = btn.dataset.cancelOut;
          state.outgoingFriends = (state.outgoingFriends || []).filter((x) => x.uid !== targetUid);
          state.outgoingFriendUids = (state.outgoingFriendUids || []).filter((u) => u !== targetUid);
          saveLocalState(true);
          await pushCloudStateNow();
          renderFriendsList();
          showToast("申請を取り消しました");
        });
      });
    }
  }

  // 2) 承認済みフレンド一覧
  const listEl = $("#friendList");
  if (!listEl) return;
  const friends = state.friends || [];
  if (!friends.length) {
    listEl.innerHTML = `<p class="setting-desc" style="text-align:center;margin:8px 0;">承認済みのフレンドがまだいません</p>`;
    return;
  }
  listEl.innerHTML = friends.map((f, idx) => `
    <button type="button" class="friend-row" data-friend-idx="${idx}" style="cursor:pointer;text-align:left;">
      <div>
        <strong>${escapeHtml(f.nickname || "フレンド")}</strong>
        <div class="sub-label">${escapeHtml(f.friendId || f.friendCode || "")}</div>
      </div>
      <span class="sub-label">記録を見る ›</span>
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
  if (!firebaseReady || !db || !currentUser) {
    showToast("フレンドの記録を表示するにはログインが必要です");
    return;
  }

  let remoteData = null;
  let remoteUid = friend.uid || "";
  try {
    if (remoteUid) {
      const snap = await getDoc(doc(db, "users", remoteUid));
      if (snap.exists()) remoteData = snap.data();
    } else if (friend.friendId) {
      const q = query(collection(db, "users"), where("friendId", "==", friend.friendId));
      const snap = await getDocs(q);
      if (!snap.empty) {
        remoteUid = snap.docs[0].id;
        remoteData = snap.docs[0].data();
      }
    }
  } catch (_) {}

  if (!remoteData) {
    showToast("フレンドのデータを取得できませんでした");
    return;
  }

  // 相互承認ガード：相手側も自分を承認済み（または申請元）でなければ閲覧不可
  const mutuallyApproved =
    (Array.isArray(remoteData.friendUids) && remoteData.friendUids.includes(currentUser.uid)) ||
    (Array.isArray(remoteData.friends) && remoteData.friends.some((f) => f.uid === currentUser.uid || f.friendId === state.friendId)) ||
    (Array.isArray(remoteData.outgoingFriendUids) && remoteData.outgoingFriendUids.includes(currentUser.uid));

  if (!mutuallyApproved) {
    showToast("相手がフレンド申請を承認すると閲覧できます");
    return;
  }

  selectedFriend = { ...friend, uid: remoteUid };
  const modal = $("#friendDetailModal");
  if (!modal) return;
  modal.classList.remove("hidden");

  const name = remoteData.nickname || friend.nickname || "フレンド";
  const fid = remoteData.friendId || friend.friendId || "HN-XXXXXX";
  const fLevels = extractNormalizedLevelsMap(remoteData);
  const todayCnt = remoteData.studiedDate === todayKey() ? (remoteData.studiedIdsToday?.length || 0) : 0;
  const streak = remoteData.streakDays || 0;

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

function hasReturningLocalSession() {
  const hasLevels = state.levels && Object.keys(state.levels).length > 0;
  return Boolean(
    localStorage.getItem(STORAGE_KEYS.GUEST_MODE) === "1" ||
    state.ownerUid ||
    state.loginId ||
    state.nickname ||
    hasLevels
  );
}

function updateAuthGateOnlineState() {
  const online = navigator.onLine !== false;
  const loginBtn = $("#btnGateLogin");
  const signupBtn = $("#btnGateSignup");
  const resetBtn = $("#btnGateResetPw");
  const guestBtn = $("#btnGateGuest");
  const uInp = $("#gateUsernameInput");
  const pInp = $("#gatePasswordInput");
  const rInp = $("#gateRecoveryEmailInput");
  const offlineBanner = $("#authOfflineBanner");
  const errEl = $("#authGateError");

  if (loginBtn) loginBtn.disabled = !online;
  if (signupBtn) signupBtn.disabled = !online;
  if (resetBtn) resetBtn.disabled = !online;
  if (uInp) uInp.disabled = !online;
  if (pInp) pInp.disabled = !online;
  if (rInp) rInp.disabled = !online;

  if (guestBtn) {
    guestBtn.disabled = false;
    guestBtn.classList.toggle("primary-btn", !online);
    guestBtn.classList.toggle("sub-btn", online);
  }
  if (offlineBanner) {
    offlineBanner.classList.toggle("hidden", online);
  }
  if (!online && errEl) {
    errEl.textContent = "";
  }
}

/* =========================================================
   イベントリスナー登録
   ========================================================= */
function bindEvents() {
  // スプラッシュ開始（ボタンまたは画面タップで即座に遷移）
  const handleSplashEnter = () => {
    const splash = $("#splashScreen");
    if (!splash || splash.classList.contains("hidden") || splash.classList.contains("fade-out")) return;
    splash.classList.add("fade-out");
    setTimeout(() => splash.classList.add("hidden"), 240);

    if (!currentUser && !hasReturningLocalSession()) {
      updateAuthGateOnlineState();
      $("#authGate")?.classList.remove("hidden");
    } else {
      $("#authGate")?.classList.add("hidden");
    }
  };
  $("#btnSplashStart")?.addEventListener("click", (e) => {
    e.stopPropagation();
    handleSplashEnter();
  });
  $("#splashScreen")?.addEventListener("click", handleSplashEnter);

  // 認証ゲート（オフライン／ゲスト開始ボタン）
  $("#btnGateGuest")?.addEventListener("click", () => {
    try { localStorage.setItem(STORAGE_KEYS.GUEST_MODE, "1"); } catch (_) {}
    saveLocalState(false);
    $("#authGate")?.classList.add("hidden");
    renderAll();
    showToast("オフライン・ゲストモードで開始しました");
  });

  $("#btnGateLogin")?.addEventListener("click", async () => {
    const rawId = ($("#gateUsernameInput")?.value || "").trim();
    const pw = $("#gatePasswordInput")?.value || "";
    const errEl = $("#authGateError");
    if (!rawId || pw.length < 6) {
      if (errEl) errEl.textContent = "ログインIDと6文字以上のパスワードを入力してください。";
      return;
    }
    if (navigator.onLine === false) {
      updateAuthGateOnlineState();
      return;
    }
    if (errEl) errEl.textContent = "サインイン中...";
    const ready = await startBackgroundFirebaseSync();
    if (!ready || !auth) {
      if (errEl) errEl.textContent = "現在通信できないためログインできません。下のオフラインモードをご利用ください。";
      return;
    }
    const emails = await resolveLoginEmail(rawId);
    let lastErr = null;
    for (const email of emails) {
      try {
        await signInWithEmailAndPassword(auth, email, pw);
        if (!rawId.includes("@")) state.loginId = rawId;
        saveLocalState(true);
        if (errEl) errEl.textContent = "";
        $("#authGate")?.classList.add("hidden");
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
    if (navigator.onLine === false) {
      updateAuthGateOnlineState();
      return;
    }

    if (errEl) errEl.textContent = "アカウント作成中...";
    const ready = await startBackgroundFirebaseSync();
    if (!ready || !auth) {
      if (errEl) errEl.textContent = "現在通信できないため新規登録できません。下のオフラインモードをご利用ください。";
      return;
    }

    const authEmail = recMail && recMail.includes("@")
      ? recMail
      : `${rawId.toLowerCase()}@${SYNTHETIC_EMAIL_DOMAINS[0]}`;

    try {
      justSignedUpInteractive = true;
      await createUserWithEmailAndPassword(auth, authEmail, pw);
      state.loginId = rawId;
      state.recoveryEmail = recMail || "";
      state.friendId = ensureFriendId(state.friendId);
      saveLocalState(true);
      if (errEl) errEl.textContent = "";
      $("#authGate")?.classList.add("hidden");
      $("#usernameModal")?.classList.remove("hidden");
    } catch (e) {
      justSignedUpInteractive = false;
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
    if (navigator.onLine === false) {
      updateAuthGateOnlineState();
      return;
    }
    const ready = await startBackgroundFirebaseSync();
    if (!ready || !auth) return;
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
      if (
        !$("#flashcardStage")?.classList.contains("hidden") ||
        !$("#quizStage")?.classList.contains("hidden") ||
        !$("#paperReadyPanel")?.classList.contains("hidden") ||
        !$("#paperStage")?.classList.contains("hidden")
      ) {
        exitStudyStages();
        return;
      }
      if (!$("#studySetupPanel")?.classList.contains("hidden")) {
        openStudyPicker();
        return;
      }
    }
    if (activeTab === "battle") {
      if (!$("#battlePickerPanel")?.classList.contains("hidden")) return;
      openBattlePicker();
      return;
    }
    switchTab("home");
  });

  $("#btnSettings")?.addEventListener("click", () => switchTab("settings"));

  $$(".nav-tab").forEach((btn) => {
    btn.addEventListener("click", () => switchTab(btn.dataset.tab));
  });

  // ホーム画面の目標範囲変更・クイックアクション・記録画面のカレンダー操作
  const onHomeGoalChange = () => {
    const maxAllowed = wordsData.length || 2300;
    prefs.goalMin = Math.max(1, Math.min(maxAllowed, Number($("#homeGoalMin")?.value || 1)));
    prefs.goalMax = Math.max(1, Math.min(maxAllowed, Number($("#homeGoalMax")?.value || 100)));
    vocabMin = prefs.goalMin;
    vocabMax = prefs.goalMax;
    const sMin = $("#studyMin");
    const sMax = $("#studyMax");
    if (sMin && !sMin.dataset.touched) sMin.value = prefs.goalMin;
    if (sMax && !sMax.dataset.touched) sMax.value = prefs.goalMax;
    saveLocalPrefs();
    scheduleCloudSync();
    renderHomeView();
  };
  $("#homeGoalMin")?.addEventListener("change", onHomeGoalChange);
  $("#homeGoalMax")?.addEventListener("change", onHomeGoalChange);

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
        vocabSelectedLevels = tile.dataset.filter === "weak" ? new Set(["1", "2"]) : new Set();
        switchTab("vocab");
      }
    });
  });

  $("#calPrevBtn")?.addEventListener("click", () => {
    calMonth--;
    if (calMonth < 0) {
      calMonth = 11;
      calYear--;
    }
    renderStudyCalendar();
  });

  $("#calNextBtn")?.addEventListener("click", () => {
    calMonth++;
    if (calMonth > 11) {
      calMonth = 0;
      calYear++;
    }
    renderStudyCalendar();
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
    const speedBtn = $("#btnListenSpeedQuick");
    if (speedBtn) speedBtn.textContent = `速度: ${listenState.speed.toFixed(1)}x`;
  });
  $("#btnListenLoopQuick")?.addEventListener("click", () => {
    listenState.loop = !listenState.loop;
    const loopBtn = $("#btnListenLoopQuick");
    if (loopBtn) loopBtn.textContent = `リピート: ${listenState.loop ? "ON" : "OFF"}`;
  });
  $$("[data-listen-rate]").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const item = listenState.queue[listenState.index];
      if (!item) return;
      const newLv = Number(btn.dataset.listenRate);
      setWordLevel(item.no, newLv);
      // 再生中タイマーや音声は一切止めず、選択表示のみ更新してそのまま自動で次へ進める
      $$("[data-listen-rate]").forEach((b) => {
        b.classList.toggle("selected", Number(b.dataset.listenRate) === newLv);
      });
    });
  });

  // 学習画面モード選択・マルチ選択チップ・開始
  $("#studyMin")?.addEventListener("input", (e) => { e.target.dataset.touched = "1"; });
  $("#studyMax")?.addEventListener("input", (e) => { e.target.dataset.touched = "1"; });
  $("#quizFormatSelect")?.addEventListener("change", updateQuizFirstCharVisibility);
  $$("[data-pick-mode]").forEach((card) => {
    card.addEventListener("click", () => openStudySetupForMode(card.dataset.pickMode));
  });
  $$("#studyLevelChips [data-study-lv]").forEach((btn) => {
    btn.addEventListener("click", () => toggleStudyLevelChip(btn.dataset.studyLv));
  });
  $("#btnStartStudy")?.addEventListener("click", startSelectedStudyMode);

  // スペル入力専用キーボード＆物理キー対応
  $$("#qSpellKeyboard [data-key]").forEach((keyBtn) => {
    keyBtn.addEventListener("click", () => handleSpellKeyInput(keyBtn.dataset.key));
  });
  $("#qSpellBackBtn")?.addEventListener("click", handleSpellBackspace);
  $("#qSpellClearBtn")?.addEventListener("click", handleSpellClear);
  $("#qSpellSubmitBtn")?.addEventListener("click", () => evaluateSpellSubmission());
  $("#qSpellNextBtn")?.addEventListener("click", advanceSpellQuestion);
  $("#qSpellAudio")?.addEventListener("click", () => {
    const item = quizQueue[quizIndex];
    if (item) speakEnglish(spellAudioTargetWord || item.word);
  });

  window.addEventListener("keydown", (e) => {
    if (e.metaKey || e.ctrlKey || e.altKey) return;

    // 1) 確認テストのタイピング入力中
    if (activeTab === "study" && !$("#quizStage")?.classList.contains("hidden") && !$("#quizSpellBox")?.classList.contains("hidden")) {
      if (/^[a-zA-Z]$/.test(e.key) && !spellJudged) {
        e.preventDefault();
        handleSpellKeyInput(e.key);
      } else if (e.key === "Backspace" && !spellJudged) {
        e.preventDefault();
        handleSpellBackspace();
      } else if (e.key === "Enter") {
        e.preventDefault();
        if (!spellJudged) evaluateSpellSubmission();
        else advanceSpellQuestion();
      }
      return;
    }

    // 2) リアルタイム対戦のタイピング入力中
    if (activeTab === "battle" && !$("#battlePlayStage")?.classList.contains("hidden")) {
      if (/^[a-zA-Z]$/.test(e.key) && !battleSession.answeredCurrent) {
        e.preventDefault();
        handleBattleKeyInput(e.key);
      } else if (e.key === "Backspace" && !battleSession.answeredCurrent) {
        e.preventDefault();
        handleBattleBackspace();
      } else if (e.key === "Enter" && !battleSession.answeredCurrent) {
        e.preventDefault();
        submitBattleSpelling(false);
      }
    }
  });

  // フラッシュカード操作（タップでめくる・裏面確認後に次へ・スワイプ対応）
  $("#btnExitFc")?.addEventListener("click", exitStudyStages);

  let fcTouchStartX = 0;
  let fcTouchStartY = 0;
  let fcSwipeHandled = false;

  const fcBoxEl = $("#flashcardBox");
  fcBoxEl?.addEventListener("touchstart", (e) => {
    const t = e.changedTouches?.[0];
    if (!t) return;
    fcTouchStartX = t.clientX;
    fcTouchStartY = t.clientY;
    fcSwipeHandled = false;
  }, { passive: true });

  fcBoxEl?.addEventListener("touchend", (e) => {
    const t = e.changedTouches?.[0];
    if (!t) return;
    const dx = t.clientX - fcTouchStartX;
    const dy = t.clientY - fcTouchStartY;
    if (Math.abs(dx) >= 48 && Math.abs(dx) > Math.abs(dy) * 1.25) {
      fcSwipeHandled = true;
      if (dx < 0) {
        advanceFlashcardNext();
      } else if (fcIndex > 0) {
        fcIndex--;
        fcFlipped = false;
        renderFlashcard(true);
      }
    }
  });

  let fcMouseDownX = null;
  let fcMouseDownY = null;
  fcBoxEl?.addEventListener("mousedown", (e) => {
    fcMouseDownX = e.clientX;
    fcMouseDownY = e.clientY;
    fcSwipeHandled = false;
  });
  fcBoxEl?.addEventListener("mouseup", (e) => {
    if (fcMouseDownX === null) return;
    const dx = e.clientX - fcMouseDownX;
    const dy = e.clientY - fcMouseDownY;
    fcMouseDownX = null;
    fcMouseDownY = null;
    if (Math.abs(dx) >= 56 && Math.abs(dx) > Math.abs(dy) * 1.25) {
      fcSwipeHandled = true;
      if (dx < 0) {
        advanceFlashcardNext();
      } else if (fcIndex > 0) {
        fcIndex--;
        fcFlipped = false;
        renderFlashcard(true);
      }
    }
  });

  fcBoxEl?.addEventListener("click", () => {
    if (fcSwipeHandled) {
      fcSwipeHandled = false;
      return;
    }
    const nextFlip = !fcFlipped;
    fcFlipped = nextFlip;
    // めくった瞬間の自動音声（特に例文穴埋めの全文再生＆日→英の発音）を発火
    renderFlashcard(nextFlip);
  });

  $("#fcFrontAudioBtn")?.addEventListener("click", (e) => {
    e.stopPropagation();
    const item = fcQueue[fcIndex];
    if (item) speakEnglish(getFlashcardFrontAudioText(item));
  });
  $("#fcAudioBtn")?.addEventListener("click", (e) => {
    e.stopPropagation();
    const item = fcQueue[fcIndex];
    if (item) speakEnglish(getFlashcardBackAudioText(item));
  });
  $$("#fcBack [data-rate]").forEach((btn) => {
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      const item = fcQueue[fcIndex];
      if (!item) return;
      setWordLevel(item.no, Number(btn.dataset.rate));
      advanceFlashcardNext();
    });
  });
  $("#fcPrevBtn")?.addEventListener("click", () => {
    if (fcIndex > 0) {
      fcIndex--;
      fcFlipped = false;
      renderFlashcard(true);
    }
  });
  $("#fcNextBtn")?.addEventListener("click", advanceFlashcardNext);

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
  $("#qSingleNextBtn")?.addEventListener("click", advanceSingleQuizQuestion);

  $("#qResultRetestBtn")?.addEventListener("click", () => {
    const wrong = shuffleArray(quizQueue.filter((item) => !quizAnswers[getQuizItemKey(item)]?.correct));
    if (!wrong.length) return;
    quizQueue = wrong;
    quizIndex = 0;
    quizAnswers = {};
    quizIsRetest = true;
    openQuizStage();
  });
  $("#qResultRetryBtn")?.addEventListener("click", exitStudyStages);

  // 筆記テスト操作
  $("#btnStartPaperActual")?.addEventListener("click", () => openPaperStage(paperConfiguredTimerSec));
  $("#btnExitPaper")?.addEventListener("click", exitStudyStages);
  $("#btnPaperRevealAnswers")?.addEventListener("click", revealPaperAnswers);
  $("#btnPaperAllCorrect")?.addEventListener("click", () => {
    paperQueue.forEach((item) => { paperMarks[getPaperItemKey(item)] = true; });
    renderPaperSheet();
  });
  $("#btnPaperFinishScore")?.addEventListener("click", finishPaperScoring);
  $("#btnPaperRetestWrong")?.addEventListener("click", () => {
    const wrong = shuffleArray(paperQueue.filter((item) => paperMarks[getPaperItemKey(item)] !== true));
    if (!wrong.length) return;
    paperQueue = wrong;
    paperConfiguredTimerSec = Number($("#paperTimerSelect")?.value || 0);
    openPaperReadyScreen();
  });
  $("#btnPaperBackSetup")?.addEventListener("click", exitStudyStages);

  // フレンドタブ（選択カード → 対戦／フレンド一覧）
  $$("[data-pick-battle]").forEach((card) => {
    card.addEventListener("click", () => openBattleSubPanel(card.dataset.pickBattle));
  });

  $("#battleMin")?.addEventListener("input", (e) => { e.target.dataset.touched = "1"; });
  $("#battleMax")?.addEventListener("input", (e) => { e.target.dataset.touched = "1"; });
  $("#battleFormat")?.addEventListener("change", () => {
    const fmt = $("#battleFormat")?.value || "ja-en";
    const minEl = $("#battleMin");
    const maxEl = $("#battleMax");
    if (minEl && maxEl && !minEl.dataset.touched && !maxEl.dataset.touched) {
      if (fmt === "example") {
        minEl.value = "301";
        maxEl.value = "400";
      } else {
        minEl.value = String(prefs.goalMin || 1);
        maxEl.value = String(prefs.goalMax || 100);
      }
    }
  });
  $("#btnBattleOpenAuth")?.addEventListener("click", () => {
    updateAuthGateOnlineState();
    if ($("#authGateError")) $("#authGateError").textContent = "";
    $("#authGate")?.classList.remove("hidden");
  });

  $("#btnCreateRoom")?.addEventListener("click", createBattleRoomAction);
  $("#btnJoinRoom")?.addEventListener("click", joinBattleRoomAction);
  $("#btnLeaveRoom")?.addEventListener("click", leaveBattleRoom);
  $("#btnExitBattlePlay")?.addEventListener("click", leaveBattleRoom);
  $("#btnBattleBackLobby")?.addEventListener("click", leaveBattleRoom);
  $("#btnStartBattleMatch")?.addEventListener("click", hostStartBattleMatch);

  // 対戦用スペリングキーボード操作
  $$("#battleSpellKeyboard [data-bkey]").forEach((keyBtn) => {
    keyBtn.addEventListener("click", () => handleBattleKeyInput(keyBtn.dataset.bkey));
  });
  $("#battleSpellBackBtn")?.addEventListener("click", handleBattleBackspace);
  $("#battleSpellClearBtn")?.addEventListener("click", handleBattleClear);
  $("#battleSpellSubmitBtn")?.addEventListener("click", () => submitBattleSpelling(false));

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
  $("#btnRefreshFriends")?.addEventListener("click", async () => {
    await checkOutgoingFriendApprovals();
    renderFriendsList();
    showToast("フレンド一覧を更新しました");
  });
  $("#btnCloseFriendModal")?.addEventListener("click", () => {
    $("#friendDetailModal")?.classList.add("hidden");
  });
  $("#btnRemoveFriend")?.addEventListener("click", async () => {
    if (!selectedFriend) return;
    state.friends = (state.friends || []).filter((f) => f.friendId !== selectedFriend.friendId && f.uid !== selectedFriend.uid);
    if (selectedFriend.uid) {
      state.friendUids = (state.friendUids || []).filter((u) => u !== selectedFriend.uid);
    }
    saveLocalState(true);
    await pushCloudStateNow();
    $("#friendDetailModal")?.classList.add("hidden");
    renderFriendsList();
    showToast("フレンドを解除しました");
  });

  // 設定画面＆ネットワーク復帰時の自動同期
  $("#btnManualSync")?.addEventListener("click", async () => {
    if (navigator.onLine === false) {
      showToast("オフラインのため同期できません");
      return;
    }
    await startBackgroundFirebaseSync();
    if (!firebaseReady || !currentUser) {
      showToast("クラウド同期にはログインが必要です");
      return;
    }
    const ok = await syncBidirectionalNow();
    showToast(ok ? "クラウドと双方向同期しました" : "同期に失敗しました（通信状態をご確認ください）");
  });

  window.addEventListener("online", async () => {
    updateAuthGateOnlineState();
    await startBackgroundFirebaseSync();
    if (firebaseReady && currentUser) syncBidirectionalNow();
  });
  window.addEventListener("offline", () => {
    updateAuthGateOnlineState();
  });
  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "visible" && navigator.onLine !== false && firebaseReady && currentUser) {
      syncBidirectionalNow();
    }
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
      state = structuredClone(DEFAULT_STATE);
      state.friendId = ensureFriendId("");
      try { localStorage.removeItem(STORAGE_KEYS.GUEST_MODE); } catch (_) {}
      saveLocalState(false);
      updateSyncUi();
      renderAll();
      showToast("ログアウトしました");
    } else {
      updateAuthGateOnlineState();
      if ($("#authGateError")) $("#authGateError").textContent = "";
      $("#authGate")?.classList.remove("hidden");
    }
  });

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

  // CSV手動読込（単語・例文・派生語をヘッダーで自動判別）
  $("#csvFileInput")?.addEventListener("change", async (e) => {
    const file = e.target.files?.[0];
    if (!file) return;
    try {
      const text = await file.text();
      const rows = parseCsvRows(text);
      if (!rows.length) {
        showToast("有効なCSVデータが見つかりませんでした");
        return;
      }
      const sample = rows[0] || {};
      if ("派生語" in sample || "derivative" in sample) {
        buildDerivativesMap(rows);
        try { localStorage.setItem(STORAGE_KEYS.CACHE_DERIVATIVES, text); } catch (_) {}
        renderAll();
        showToast(`派生語データ（${rows.length} 件）を読み込みました`);
        return;
      }
      if ("例文" in sample || "example_en" in sample) {
        buildExamplesMap(rows);
        try { localStorage.setItem(STORAGE_KEYS.CACHE_EXAMPLES, text); } catch (_) {}
        renderAll();
        showToast(`例文データ（${rows.length} 件）を読み込みました`);
        return;
      }
      const parsed = normalizeWords(rows);
      if (!parsed.length) {
        showToast("有効な単語データが見つかりませんでした");
        return;
      }
      wordsData = parsed;
      syncMaxRangeInputs();
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
   初期化エントリーポイント（0ms即起動 ＆ 非同期バックグラウンド同期）
   ========================================================= */
function updateSplashReadyLabel() {
  const statusEl = $("#splashStatus");
  if (statusEl) {
    statusEl.textContent = wordsData.length > 0
      ? `準備完了（全 ${wordsData.length.toLocaleString()} 語）`
      : "準備完了";
  }
  $("#splashSpinner")?.classList.add("hidden");
  $("#btnSplashStart")?.classList.remove("hidden");
}

function initApp() {
  // 1. アプリ起動（0ms）：localStorage から設定・ユーザー情報・学習データ（levels/ratings）・キャッシュ済みCSVを同期読み込み
  loadLocalPrefs();
  loadLocalState();
  loadCachedVocabularySync();

  if ($("#quizShowFirstSelect")) {
    $("#quizShowFirstSelect").value = prefs.showFirstChar === false ? "hide" : "show";
  }

  bindEvents();
  updateAuthGateOnlineState();
  renderAll();

  // 2. ネットワーク通信を一切待たず、0msで「タップしてはじめる」画面を即時表示
  updateSplashReadyLabel();
  $("#authGate")?.classList.add("hidden");

  // 3. ローカルCSVの最新化（非同期・UI非ブロック）
  loadVocabularyData()
    .then(() => {
      updateSplashReadyLabel();
      renderAll();
    })
    .catch(() => {});

  // 4. バックグラウンド同期（オンライン時のみ・失敗してもエラー画面を出さず静かに終了）
  if (navigator.onLine !== false) {
    startBackgroundFirebaseSync();
  }
}

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    navigator.serviceWorker.register("./sw.js").catch((err) => {
      console.warn("SW registration skipped:", err);
    });
  });
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", initApp);
} else {
  initApp();
}
