# ═══════════════════════════════════════════════════════════
# Capper's Edge v7.0 — History + Brier + CLV
# ═══════════════════════════════════════════════════════════

import os, asyncio, aiohttp, aiosqlite, json, warnings, logging, sqlite3
from datetime import datetime, timedelta, timezone
from dataclasses import dataclass, field
from typing import Optional, List, Tuple, Dict, Any
from math import exp, factorial
import numpy as np
from getpass import getpass
from tqdm import tqdm

warnings.filterwarnings("ignore")

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s │ %(levelname)-7s │ %(message)s',
    datefmt='%H:%M:%S'
)
log = logging.getLogger("CapperEdge")

# API-ключ (будет взят из секретов GitHub)
SSTATS_API_KEY = os.environ.get('SSTATS_API_KEY')
if not SSTATS_API_KEY:
    print("❌ API-ключ не найден. Убедитесь, что он добавлен в секреты GitHub.")
    raise SystemExit(1)
print("✅ API-ключ получен из переменной окружения.\n")

BASE_URL = "https://api.sstats.net"
BASE_DIR = "FootballAnalyzer"
os.makedirs(BASE_DIR, exist_ok=True)
CACHE_DB   = os.path.join(BASE_DIR, "sstats_cache.db")
HISTORY_DB = os.path.join(BASE_DIR, "capper_history.db")   # 🆕

# ═══════════════════════════════════════════════════════════
# РЕЖИМЫ
# ═══════════════════════════════════════════════════════════
DEMO_MODE            = False
LOOKAHEAD_HOURS      = 24
CACHE_TTL_HOURS      = 6
MAX_CONCURRENT_API   = 25

# 🆕 Настройки истории
RESOLVE_MIN_AGE_H     = 3     # прогноз разрешается, если с kickoff прошло ≥3ч
CLOSING_CAPTURE_LO_M  = 0     # за сколько МИНУТ до старта начинаем ловить closing
CLOSING_CAPTURE_HI_M  = 120   # до этого окна (0..120 мин)
HISTORY_ENABLED       = True

# ═══════════════════════════════════════════════════════════
# ПОРОГИ
# ═══════════════════════════════════════════════════════════
STRONG_THRESHOLD  = 74
MEDIUM_THRESHOLD  = 65
MIN_DATA_QUALITY  = 0.40
MIN_ODDS          = 1.30
MAX_ODDS          = 4.50
MAX_KELLY         = 8.0
MAX_OVERROUND     = 1.10

FORM_WEIGHT       = 0.30
ODDS_WEIGHT       = 0.50
POISSON_WEIGHT    = 0.20
FORM_XG_WEIGHT    = 0.15

_FACT = tuple(float(factorial(i)) for i in range(12))

# ═══════════════════════════════════════════════════════════
# ЛИГИ
# ═══════════════════════════════════════════════════════════
LEAGUES = {
    39: ("Premier League","ENG",1), 40: ("Championship","ENG",2),
    41: ("League 1","ENG",3), 42: ("League 2","ENG",3),
    140: ("La Liga","ESP",1), 141: ("La Liga 2","ESP",2), 142: ("Primera Fed","ESP",3),
    78: ("Bundesliga","GER",1), 79: ("Bundesliga 2","GER",2), 80: ("3. Liga","GER",3),
    135: ("Serie A","ITA",1), 136: ("Serie B","ITA",2), 137: ("Serie C","ITA",3),
    61: ("Ligue 1","FRA",1), 62: ("Ligue 2","FRA",2), 63: ("National","FRA",3),
    94: ("Primeira Liga","POR",2), 88: ("Eredivisie","NED",2), 89: ("Eerste Divisie","NED",3),
    144: ("Jupiler Pro","BEL",2), 154: ("Challenger Pro","BEL",3),
    203: ("Super Lig","TUR",2), 169: ("Super League","GRE",2), 235: ("Super League","SUI",3),
    179: ("Premiership","SCO",2), 106: ("Ekstraklasa","POL",3), 157: ("Ukr Prem","UKR",3),
    103: ("Allsvenskan","SWE",3), 119: ("Eliteserien","NOR",3), 113: ("Superliga","DEN",3),
    71: ("Brasileirao A","BRA",1), 72: ("Brasileirao B","BRA",2),
    128: ("Liga Profesional","ARG",1), 129: ("Primera Nacional","ARG",2),
    253: ("MLS","USA",1), 263: ("USL Champ","USA",2), 264: ("Liga MX","MEX",1),
    98: ("J1 League","JPN",2), 99: ("J2 League","JPN",3), 292: ("K League 1","KOR",2),
    2: ("UCL","EU",1), 3: ("UEL","EU",1), 848: ("UECL","EU",1),
    5: ("FA Cup","ENG",2), 6: ("EFL Cup","ENG",2),
    13: ("Copa del Rey","ESP",2), 12: ("Coppa Italia","ITA",2),
}

DERBY_PAIRS = {
    ("Manchester United","Manchester City"), ("Liverpool","Everton"),
    ("Arsenal","Tottenham"), ("Chelsea","Arsenal"),
    ("Real Madrid","Barcelona"), ("Atletico Madrid","Real Madrid"),
    ("Inter","Milan"), ("Milan","Juventus"), ("Roma","Lazio"),
    ("Napoli","Juventus"), ("Bayern Munich","Borussia Dortmund"),
    ("Benfica","Porto"), ("Ajax","Feyenoord"), ("PSG","Marseille"),
    ("Lyon","Marseille"), ("Galatasaray","Fenerbahce"),
    ("Besiktas","Galatasaray"), ("Celtic","Rangers"),
    ("Sparta Prague","Slavia Prague"), ("Olympiacos","Panathinaikos"),
    ("Flamengo","Fluminense"), ("Boca Juniors","River Plate"),
    ("LA Galaxy","LAFC"), ("Palmeiras","Corinthians"),
    ("Sao Paulo","Corinthians"), ("River Plate","Boca Juniors"),
    ("Independiente","Racing"),
}

def _norm_team(s: str) -> str:
    return (s or "").lower().replace(" fc", "").replace("fc ", "") \
        .replace("cf ", "").replace(".", "").strip()

_DERBY_NORM: set = set()
for _a, _b in DERBY_PAIRS:
    _DERBY_NORM.add((_norm_team(_a), _norm_team(_b)))
    _DERBY_NORM.add((_norm_team(_b), _norm_team(_a)))


# ═══════════════════════════════════════════════════════════
# DATA-КЛАССЫ
# ═══════════════════════════════════════════════════════════
@dataclass
class TeamStats:
    name: str = ""
    position: Optional[int] = None
    played: int = 0; wins: int = 0; draws: int = 0; losses: int = 0
    goals_for: int = 0; goals_against: int = 0; points: int = 0
    ppg: float = 0.0; gpg: float = 0.0; gcpg: float = 0.0
    form_string: str = ""
    form_score: float = 0.0
    form_goals_for: float = 0.0
    form_goals_against: float = 0.0

@dataclass
class MatchOdds:
    home: float = 0.0; draw: float = 0.0; away: float = 0.0
    over25: float = 0.0; under25: float = 0.0
    btts_yes: float = 0.0; btts_no: float = 0.0
    prob_home: float = 0.0; prob_draw: float = 0.0; prob_away: float = 0.0
    prob_over25: float = 0.0; prob_under25: float = 0.0
    prob_btts_yes: float = 0.0; prob_btts_no: float = 0.0
    overround_1x2: float = 0.0

@dataclass
class Prediction:
    match_time: str; league: str; league_tier: int
    home: str; away: str
    market: str; selection: str; probability: float; odds: float = 0.0
    confidence: str = ""; score: float = 0.0
    reasoning: List[str] = field(default_factory=list)
    data_quality: float = 0.0; is_derby: bool = False
    value_rating: str = ""; kelly_stake: float = 0.0
    expected_value: float = 0.0
    form_home: str = ""; form_away: str = ""
    # 🆕 для истории
    fixture_id: str = ""
    league_id: int = 0
    kickoff_utc: Optional[datetime] = None
    xg_home: float = 0.0
    xg_away: float = 0.0

@dataclass
class MatchAnalysis:
    fixture_id: str; time: datetime; league: str
    league_id: int; league_tier: int
    home: str; away: str
    home_stats: TeamStats; away_stats: TeamStats
    odds: MatchOdds; is_derby: bool = False
    data_quality: float = 0.0
    predictions: List[Prediction] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════
# УТИЛИТЫ
# ═══════════════════════════════════════════════════════════
def normalize_odds(home, draw, away) -> Optional[Tuple[float, float, float]]:
    try:
        h, d, a = float(home), float(draw), float(away)
    except (TypeError, ValueError):
        return None
    if h <= 1.0 or d <= 1.0 or a <= 1.0:
        return None
    overround = 1/h + 1/d + 1/a
    if overround <= 0:
        return None
    return (1/h)/overround*100, (1/d)/overround*100, (1/a)/overround*100

def value_rating(probability, odds):
    if odds <= 0: return "⚠️ НИЗКАЯ"
    fair = 100 / probability if probability > 0 else 999
    edge = (fair - odds) / odds * 100
    if edge > 15:   return "💎 ВЫСОКАЯ"
    elif edge > 5:  return "✅ СРЕДНЯЯ"
    return "⚠️ НИЗКАЯ"

def kelly_stake(prob, odds, fraction=0.25):
    if odds <= 1 or prob <= 0 or prob >= 1: return 0.0
    b, q = odds - 1, 1 - prob
    raw = ((b * prob) - q) / b * fraction
    return min(max(0.0, raw) * 100, MAX_KELLY)

def parse_form(form_string: str) -> Tuple[float, float, float]:
    if not form_string:
        return 0.0, 0.0, 0.0
    chars = [c.upper() for c in form_string if c.upper() in 'WDL']
    if not chars:
        return 0.0, 0.0, 0.0
    chars = chars[-5:]
    score_map = {'W': 1.0, 'D': 0.0, 'L': -1.0}
    scores = [score_map[c] for c in chars]
    n = len(scores)
    weights = [2 ** i for i in range(n)]
    total_w = sum(weights)
    weighted_score = sum(s * w for s, w in zip(scores, weights)) / total_w
    return weighted_score, 0.0, 0.0

# 🆕 Исход матча по счёту и рынку
def outcome_from_score(market: str, selection: str,
                       hg: int, ag: int) -> Optional[str]:
    """Возвращает 'win' | 'loss' | None (если рынок неизвестен)."""
    total = hg + ag
    if market == "1X2":
        if selection == "П1": return "win" if hg > ag else "loss"
        if selection == "Х":  return "win" if hg == ag else "loss"
        if selection == "П2": return "win" if ag > hg else "loss"
    elif market == "Тотал 2.5":
        if selection == "ТБ 2.5": return "win" if total > 2.5 else "loss"
        if selection == "ТМ 2.5": return "win" if total < 2.5 else "loss"
    elif market == "Обе забьют":
        if selection == "ОЗ-ДА": return "win" if hg > 0 and ag > 0 else "loss"
    return None

# 🆕 Кэф из объекта MatchOdds по рынку и выбору (для closing capture)
def odd_for_prediction(odds: MatchOdds, market: str, selection: str) -> float:
    if market == "1X2":
        if selection == "П1": return odds.home
        if selection == "Х":  return odds.draw
        if selection == "П2": return odds.away
    elif market == "Тотал 2.5":
        if selection == "ТБ 2.5": return odds.over25
        if selection == "ТМ 2.5": return odds.under25
    elif market == "Обе забьют":
        if selection == "ОЗ-ДА": return odds.btts_yes
    return 0.0


# ═══════════════════════════════════════════════════════════
# 🆕 HISTORY DB
# ═══════════════════════════════════════════════════════════
class HistoryDB:
    """Хранилище прогнозов, результатов и closing odds + метрики."""

    def __init__(self, path: str = HISTORY_DB):
        self.path = path
        self.conn: Optional[aiosqlite.Connection] = None

    async def __aenter__(self):
        self.conn = await aiosqlite.connect(self.path)
        self.conn.row_factory = aiosqlite.Row
        await self._init_schema()
        return self

    async def __aexit__(self, *args):
        if self.conn:
            await self.conn.close()

    async def _init_schema(self):
        await self.conn.execute("""
            CREATE TABLE IF NOT EXISTS predictions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at TEXT NOT NULL,
                fixture_id TEXT NOT NULL,
                kickoff_utc TEXT NOT NULL,
                league_id INTEGER, league TEXT, tier INTEGER,
                home TEXT, away TEXT,
                market TEXT NOT NULL, selection TEXT NOT NULL,
                probability REAL NOT NULL,
                odds REAL NOT NULL,
                expected_value REAL,
                kelly_stake REAL,
                score REAL,
                confidence TEXT,
                data_quality REAL,
                is_derby INTEGER,
                form_home TEXT, form_away TEXT,
                xg_home REAL, xg_away REAL,
                reasoning TEXT,
                closing_odds REAL,
                closing_captured_at TEXT,
                home_goals INTEGER, away_goals INTEGER,
                outcome TEXT,
                resolved_at TEXT,
                UNIQUE(fixture_id, market, selection)
            )
        """)
        await self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_pending "
            "ON predictions(outcome, kickoff_utc)"
        )
        await self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_fixture ON predictions(fixture_id)"
        )
        await self.conn.commit()

    # ─── SAVE ────────────────────────────────────────────
    async def save_predictions(self, preds: List[Prediction]) -> int:
        if not preds:
            return 0
        now_iso = datetime.now(timezone.utc).isoformat()
        rows = []
        for p in preds:
            if not p.fixture_id or not p.kickoff_utc:
                continue
            rows.append((
                now_iso,
                p.fixture_id,
                p.kickoff_utc.isoformat() if hasattr(p.kickoff_utc, 'isoformat') else str(p.kickoff_utc),
                p.league_id, p.league, p.league_tier,
                p.home, p.away,
                p.market, p.selection,
                p.probability, p.odds,
                p.expected_value, p.kelly_stake, p.score,
                p.confidence, p.data_quality, int(p.is_derby),
                p.form_home, p.form_away,
                p.xg_home, p.xg_away,
                json.dumps(p.reasoning, ensure_ascii=False),
            ))
        if not rows:
            return 0
        cur = await self.conn.executemany("""
            INSERT OR IGNORE INTO predictions (
                created_at, fixture_id, kickoff_utc,
                league_id, league, tier, home, away,
                market, selection, probability, odds,
                expected_value, kelly_stake, score,
                confidence, data_quality, is_derby,
                form_home, form_away, xg_home, xg_away, reasoning
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, rows)
        await self.conn.commit()
        return cur.rowcount if cur.rowcount and cur.rowcount > 0 else 0

    # ─── PENDING RESOLUTION ──────────────────────────────
    async def get_pending_resolution(self, min_age_hours: int = RESOLVE_MIN_AGE_H):
        cutoff = (datetime.now(timezone.utc)
                  - timedelta(hours=min_age_hours)).isoformat()
        cur = await self.conn.execute("""
            SELECT id, fixture_id, league_id, kickoff_utc,
                   market, selection
            FROM predictions
            WHERE outcome IS NULL AND kickoff_utc < ?
        """, (cutoff,))
        rows = await cur.fetchall()
        return [dict(r) for r in rows]

    async def update_result(self, row_id: int, hg: int, ag: int, outcome: str):
        await self.conn.execute("""
            UPDATE predictions
            SET home_goals=?, away_goals=?, outcome=?, resolved_at=?
            WHERE id=?
        """, (hg, ag, outcome, datetime.now(timezone.utc).isoformat(), row_id))
        await self.conn.commit()

    # ─── CLOSING ODDS ────────────────────────────────────
    async def get_upcoming_without_closing(self,
                                           lo_minutes: int = CLOSING_CAPTURE_LO_M,
                                           hi_minutes: int = CLOSING_CAPTURE_HI_M):
        now = datetime.now(timezone.utc)
        lo = (now + timedelta(minutes=lo_minutes)).isoformat()
        hi = (now + timedelta(minutes=hi_minutes)).isoformat()
        cur = await self.conn.execute("""
            SELECT id, fixture_id, league_id, kickoff_utc, market, selection
            FROM predictions
            WHERE closing_odds IS NULL AND outcome IS NULL
              AND kickoff_utc BETWEEN ? AND ?
        """, (lo, hi))
        rows = await cur.fetchall()
        return [dict(r) for r in rows]

    async def set_closing_odds(self, row_id: int, closing_odds: float):
        await self.conn.execute("""
            UPDATE predictions
            SET closing_odds=?, closing_captured_at=?
            WHERE id=?
        """, (closing_odds, datetime.now(timezone.utc).isoformat(), row_id))
        await self.conn.commit()

    # ─── FETCH RESOLVED ──────────────────────────────────
    async def fetch_resolved(self) -> List[Dict[str, Any]]:
        cur = await self.conn.execute("""
            SELECT id, fixture_id, kickoff_utc, league, tier, home, away,
                   market, selection, probability, odds, closing_odds,
                   kelly_stake, expected_value, confidence, data_quality,
                   is_derby, outcome, home_goals, away_goals
            FROM predictions
            WHERE outcome IS NOT NULL
            ORDER BY kickoff_utc DESC
        """)
        return [dict(r) for r in await cur.fetchall()]

    async def total_rows(self) -> Dict[str, int]:
        cur = await self.conn.execute("""
            SELECT
              COUNT(*) AS total,
              SUM(CASE WHEN outcome IS NULL THEN 1 ELSE 0 END) AS pending,
              SUM(CASE WHEN outcome IS NOT NULL THEN 1 ELSE 0 END) AS resolved,
              SUM(CASE WHEN closing_odds IS NOT NULL THEN 1 ELSE 0 END) AS with_closing
            FROM predictions
        """)
        r = await cur.fetchone()
        return dict(r) if r else {}


# ═══════════════════════════════════════════════════════════
# ОСНОВНОЙ АНАЛИЗАТОР
# ═══════════════════════════════════════════════════════════
class CapperAnalyzer:
    def __init__(self, api_key):
        self.api_key = api_key
        self.session: Optional[aiohttp.ClientSession] = None
        self.db_cache: Optional[aiosqlite.Connection] = None
        self.sem = asyncio.Semaphore(MAX_CONCURRENT_API)

    async def __aenter__(self):
        self.session = aiohttp.ClientSession(
            headers={'User-Agent': 'CapperAnalyzer/7.0'},
            timeout=aiohttp.ClientTimeout(total=30)
        )
        await self._init_db()
        return self

    async def __aexit__(self, *args):
        if self.db_cache: await self.db_cache.close()
        if self.session:  await self.session.close()

    async def _init_db(self):
        self.db_cache = await aiosqlite.connect(CACHE_DB)
        await self.db_cache.execute(
            "CREATE TABLE IF NOT EXISTS cache "
            "(key TEXT PRIMARY KEY, data TEXT, "
            "timestamp DATETIME DEFAULT CURRENT_TIMESTAMP)"
        )
        await self.db_cache.commit()

    async def _cache_get(self, key):
        cursor = await self.db_cache.execute(
            "SELECT data, timestamp FROM cache WHERE key=?", (key,)
        )
        row = await cursor.fetchone()
        if row:
            try:
                ts = datetime.strptime(row[1], '%Y-%m-%d %H:%M:%S')
                if datetime.now() - ts < timedelta(hours=CACHE_TTL_HOURS):
                    return json.loads(row[0])
            except Exception:
                pass
        return None

    async def _cache_set(self, key, data):
        await self.db_cache.execute(
            "INSERT OR REPLACE INTO cache (key, data, timestamp) VALUES (?,?,?)",
            (key, json.dumps(data), datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
        )
        await self.db_cache.commit()

    async def _fetch_api(self, endpoint, params=None):
        url = f"{BASE_URL}/{endpoint}"
        if params is None:
            params = {}
        params['apikey'] = self.api_key
        safe_params = {k: v for k, v in params.items() if k.lower() != 'apikey'}

        async with self.sem:
            for attempt in range(4):
                try:
                    async with self.session.get(url, params=params, timeout=20) as resp:
                        if resp.status == 200:
                            return await resp.json()
                        elif resp.status == 429:
                            wait = 2 ** attempt + np.random.uniform(0, 0.5)
                            tqdm.write(f"   ⏳ Rate limit, ждём {wait:.1f}с...")
                            await asyncio.sleep(wait)
                        elif resp.status in (500, 502, 503, 504):
                            await asyncio.sleep(2 ** attempt + np.random.uniform(0, 0.5))
                        else:
                            body = await resp.text()
                            log.debug(f"API {resp.status} {endpoint} "
                                      f"{safe_params} :: {body[:200]}")
                            return {}
                except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                    log.debug(f"fetch {endpoint} attempt {attempt}: {e}")
                    await asyncio.sleep(2 ** attempt)
                except Exception as e:
                    log.debug(f"fetch unexpected {endpoint}: {e}")
                    return {}
            return {}

    async def get_games(self, league_id, year):
        cache_key = f"games_{league_id}_{year}"
        cached = await self._cache_get(cache_key)
        if cached:
            return cached
        data = await self._fetch_api("Games/list", {"league": league_id, "Year": year})
        games = data.get('data', []) if isinstance(data, dict) else []
        if games:
            await self._cache_set(cache_key, games)
        return games

    # 🆕 Fresh (без кэша) — нужен для resolve/closing
    async def get_games_fresh(self, league_id, year):
        data = await self._fetch_api("Games/list", {"league": league_id, "Year": year})
        games = data.get('data', []) if isinstance(data, dict) else []
        if games:
            await self._cache_set(f"games_{league_id}_{year}", games)
        return games

    async def get_table(self, league_id, year):
        cache_key = f"table_{league_id}_{year}"
        cached = await self._cache_get(cache_key)
        if cached:
            return cached
        data = await self._fetch_api("Games/season-table",
                                     {"league": league_id, "Year": year})
        table = data.get('data', data) if isinstance(data, dict) else {}
        if table:
            await self._cache_set(cache_key, table)
        return table

    async def get_max_available_year(self, league_id):
        current_year = datetime.now(timezone.utc).year
        now = datetime.now(timezone.utc)
        years_to_check = [current_year - 1, current_year, current_year + 1, current_year + 2]

        best_year = None
        best_future_count = 0
        latest_match_date = None
        debug_info = []

        for year in years_to_check:
            games = await self.get_games(league_id, year)
            n_games = len(games) if games else 0
            future_count = 0
            latest_date = None
            if games:
                for g in games:
                    mt = self._parse_time(g.get('date', ''), date_utc=g.get('dateUtc'))
                    if mt:
                        if mt > now:
                            future_count += 1
                        if latest_date is None or mt > latest_date:
                            latest_date = mt
            debug_info.append(f"{year}:{n_games}g/{future_count}f")
            if games and n_games > 0:
                if future_count > best_future_count:
                    best_future_count = future_count
                    best_year = year
                    latest_match_date = latest_date
                elif future_count == 0 and best_future_count == 0:
                    if latest_date and (latest_match_date is None or latest_date > latest_match_date):
                        latest_match_date = latest_date
                        best_year = year

        league_name = LEAGUES.get(league_id, ("?",))[0]
        log.info(f"  🔎 {league_name} (id={league_id}): "
                 f"{' | '.join(debug_info)} → выбрали {best_year}")

        return best_year if best_year is not None else current_year + 1

    def _parse_time(self, date_str, date_utc=None) -> Optional[datetime]:
        if date_utc is not None:
            try:
                return datetime.fromtimestamp(int(date_utc), tz=timezone.utc)
            except Exception:
                pass
        if not date_str:
            return None
        s = date_str.replace('Z', '+00:00')
        try:
            dt = datetime.fromisoformat(s)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt
        except Exception:
            pass
        try:
            clean = date_str.replace('T', ' ')
            if '+' in clean: clean = clean.split('+')[0]
            elif clean.count('-') > 2: clean = clean.rsplit('-', 1)[0]
            clean = clean[:19]
            return datetime.strptime(clean, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
        except Exception:
            return None

    # 🆕 Универсальный парсер счёта
    def _extract_score(self, game) -> Optional[Tuple[int, int]]:
        for hk, ak in [('homeGoals', 'awayGoals'), ('homeScore', 'awayScore'),
                       ('scoreHome', 'scoreAway'), ('home_score', 'away_score'),
                       ('goalsHome', 'goalsAway'), ('home_goals', 'away_goals')]:
            h, a = game.get(hk), game.get(ak)
            if h is not None and a is not None:
                try:
                    return int(h), int(a)
                except (TypeError, ValueError):
                    pass
        sc = game.get('score')
        if isinstance(sc, dict):
            for hk, ak in [('home', 'away'), ('homeGoals', 'awayGoals'),
                           ('home_score', 'away_score')]:
                h, a = sc.get(hk), sc.get(ak)
                if h is not None and a is not None:
                    try:
                        return int(h), int(a)
                    except (TypeError, ValueError):
                        pass
        return None

    def _extract_stats(self, team_data, table_data) -> TeamStats:
        stats = TeamStats()
        stats.name = team_data.get('name', 'Unknown')
        team_id = str(team_data.get('id', ''))

        if isinstance(table_data, dict) and team_id in table_data:
            row = table_data[team_id]
            stats.position      = row.get('rank')
            stats.played        = row.get('totalGames', 0) or 0
            stats.wins          = row.get('wins', 0) or 0
            stats.draws         = row.get('draws', 0) or 0
            stats.losses        = row.get('loss', 0) or 0
            stats.goals_for     = row.get('goalsScored', 0) or 0
            stats.goals_against = row.get('goalsMissed', 0) or 0
            stats.points        = row.get('points', 0) or 0

            form_arr = row.get('form', []) or []
            form_map = {
                1: 'W', 0: 'D', -1: 'L',
                'W': 'W', 'D': 'D', 'L': 'L',
                'w': 'W', 'd': 'D', 'l': 'L',
                '1': 'W', '0': 'D', '-1': 'L',
            }
            stats.form_string = ''.join(
                form_map[x] for x in form_arr if x in form_map
            )

        if stats.played > 0:
            stats.ppg  = stats.points / stats.played
            stats.gpg  = stats.goals_for / stats.played
            stats.gcpg = stats.goals_against / stats.played

        if stats.form_string:
            stats.form_score, gf, ga = parse_form(stats.form_string)
            stats.form_goals_for = gf
            stats.form_goals_against = ga
        return stats

    def _extract_odds(self, game) -> MatchOdds:
        odds = MatchOdds()
        for market in game.get('odds', []) or []:
            mid = market.get('marketId')
            for odd in market.get('odds', []) or []:
                name = (odd.get('name') or '').lower().strip()
                try:
                    val = float(odd.get('value', 0))
                except (TypeError, ValueError):
                    continue
                if val <= 0: continue

                if mid == 1:
                    if name == 'home':       odds.home = val
                    elif name == 'draw':     odds.draw = val
                    elif name == 'away':     odds.away = val
                elif mid == 5:
                    if name.startswith('over'):    odds.over25 = val
                    elif name.startswith('under'): odds.under25 = val
                elif mid == 10:
                    if 'yes' in name:  odds.btts_yes = val
                    elif 'no' in name: odds.btts_no  = val

        if odds.home > 0 and odds.draw > 0 and odds.away > 0:
            odds.overround_1x2 = 1/odds.home + 1/odds.draw + 1/odds.away
            norm = normalize_odds(odds.home, odds.draw, odds.away)
            if norm:
                odds.prob_home, odds.prob_draw, odds.prob_away = norm

        if odds.over25 > 0 and odds.under25 > 0:
            ovr = 1/odds.over25 + 1/odds.under25
            if ovr > 0:
                odds.prob_over25  = (1/odds.over25)  / ovr * 100
                odds.prob_under25 = (1/odds.under25) / ovr * 100

        if odds.btts_yes > 0 and odds.btts_no > 0:
            ovr = 1/odds.btts_yes + 1/odds.btts_no
            if ovr > 0:
                odds.prob_btts_yes = (1/odds.btts_yes) / ovr * 100
                odds.prob_btts_no  = (1/odds.btts_no)  / ovr * 100
        return odds

    def _is_derby(self, home, away) -> bool:
        return (_norm_team(home), _norm_team(away)) in _DERBY_NORM

    def _calculate_expected_goals(self, home_stats, away_stats) -> Tuple[float, float]:
        h_gpg  = home_stats.gpg  if home_stats.played > 0 else 1.35
        a_gpg  = away_stats.gpg  if away_stats.played > 0 else 1.15
        h_gcpg = home_stats.gcpg if home_stats.played > 0 else 1.20
        a_gcpg = away_stats.gcpg if away_stats.played > 0 else 1.30
        AVG_HOME, AVG_AWAY, HOME_ADV = 1.45, 1.20, 1.18

        h_att = h_gpg / AVG_HOME; a_def = a_gcpg / AVG_AWAY
        a_att = a_gpg / AVG_AWAY; h_def = h_gcpg / AVG_HOME

        xg_home = h_att * a_def * AVG_HOME * HOME_ADV
        xg_away = a_att * h_def * AVG_AWAY

        h_form = home_stats.form_score
        a_form = away_stats.form_score

        xg_home *= (1 + FORM_XG_WEIGHT * h_form)
        xg_away *= (1 + FORM_XG_WEIGHT * a_form)
        xg_home *= (1 - FORM_XG_WEIGHT * 0.5 * a_form)
        xg_away *= (1 - FORM_XG_WEIGHT * 0.5 * h_form)

        return float(np.clip(xg_home, 0.3, 4.5)), float(np.clip(xg_away, 0.2, 4.0))

    def _poisson_matrix(self, xg_home, xg_away) -> Dict[str, float]:
        probs_h = np.array([exp(-xg_home) * xg_home**i / _FACT[i] for i in range(10)])
        probs_a = np.array([exp(-xg_away) * xg_away**j / _FACT[j] for j in range(10)])
        P = np.outer(probs_h, probs_a)

        i_idx, j_idx = np.indices(P.shape)
        return {
            "xg_home": xg_home, "xg_away": xg_away,
            "p_over25": float(P[(i_idx + j_idx) > 2].sum()) * 100,
            "p_btts":   float(P[(i_idx > 0) & (j_idx > 0)].sum()) * 100,
            "p_home":   float(P[i_idx > j_idx].sum()) * 100,
            "p_draw":   float(P[i_idx == j_idx].sum()) * 100,
            "p_away":   float(P[i_idx < j_idx].sum()) * 100,
        }

    @staticmethod
    def _blend(sources: List[Tuple[Optional[float], float]]) -> Optional[float]:
        total_v = 0.0; total_w = 0.0
        for value, weight in sources:
            if value is None or weight <= 0:
                continue
            total_v += value * weight
            total_w += weight
        return total_v / total_w if total_w > 0 else None

    @staticmethod
    def _form_implied_probs(a: 'MatchAnalysis') -> Dict[str, float]:
        fh = a.home_stats.form_score
        fa = a.away_stats.form_score
        diff = (fh + 0.10) - fa
        p_h_raw = 1.0 / (1.0 + np.exp(-2.2 * diff))
        p_a_raw = 1.0 - p_h_raw
        form_balance = 1.0 - min(abs(fh - fa), 1.0)
        p_d = 0.25 + 0.05 * form_balance
        scale = 1.0 - p_d
        return {
            "home": p_h_raw * scale * 100.0,
            "draw": p_d * 100.0,
            "away": p_a_raw * scale * 100.0,
        }

    async def analyze_match(self, game, league_id, league_name, league_tier, table):
        try:
            gid = str(game.get('id', ''))
            if not gid: return None
            match_time = self._parse_time(game.get('date', ''),
                                          date_utc=game.get('dateUtc'))
            if not match_time: return None

            if not DEMO_MODE:
                now = datetime.now(timezone.utc)
                if not (now <= match_time <= now + timedelta(hours=LOOKAHEAD_HOURS)):
                    return None

            home_data = game.get('homeTeam') or game.get('home') or {}
            away_data = game.get('awayTeam') or game.get('away') or {}
            if not home_data or not away_data: return None

            home_stats = self._extract_stats(home_data, table or {})
            away_stats = self._extract_stats(away_data, table or {})
            odds = self._extract_odds(game)

            has_any_odds = (
                odds.prob_home > 0 or
                (odds.over25 > 0 and odds.under25 > 0) or
                (odds.btts_yes > 0 and odds.btts_no > 0)
            )
            if not has_any_odds: return None
            if odds.overround_1x2 > MAX_OVERROUND: return None

            is_derby = self._is_derby(home_data.get('name', ''),
                                      away_data.get('name', ''))
            dq = 0.0
            if odds.prob_home > 0:      dq += 0.50
            if table and len(table) > 0: dq += 0.30
            if home_stats.form_string:  dq += 0.10
            if away_stats.form_string:  dq += 0.10
            if is_derby: dq *= 0.9
            if dq < MIN_DATA_QUALITY: return None

            analysis = MatchAnalysis(
                fixture_id=gid, time=match_time,
                league=league_name, league_id=league_id, league_tier=league_tier,
                home=home_data.get('name', '?'), away=away_data.get('name', '?'),
                home_stats=home_stats, away_stats=away_stats,
                odds=odds, is_derby=is_derby, data_quality=dq,
            )
            analysis.predictions = self._generate_predictions(analysis)
            return analysis
        except Exception as e:
            log.debug(f"analyze_match error: {e}")
            return None

    def _generate_predictions(self, a: MatchAnalysis) -> List[Prediction]:
        predictions: List[Prediction] = []
        now_str = a.time.strftime("%d.%m %H:%M")
        xg_h, xg_a = self._calculate_expected_goals(a.home_stats, a.away_stats)
        poisson = self._poisson_matrix(xg_h, xg_a)
        form_h = a.home_stats.form_string or "—"
        form_a = a.away_stats.form_string or "—"
        form_probs = self._form_implied_probs(a)

        odds_probs = (a.odds.prob_home, a.odds.prob_draw, a.odds.prob_away)
        poisson_probs = (poisson["p_home"], poisson["p_draw"], poisson["p_away"])
        form_tuple = (form_probs["home"], form_probs["draw"], form_probs["away"])
        selections = ("П1", "Х", "П2")
        odds_vals  = (a.odds.home, a.odds.draw, a.odds.away)

        for sel, o_p, p_p, f_p, odd in zip(selections, odds_probs, poisson_probs,
                                            form_tuple, odds_vals):
            blended = self._blend([
                (o_p if o_p > 0 else None, ODDS_WEIGHT),
                (p_p, POISSON_WEIGHT),
                (f_p, FORM_WEIGHT),
            ])
            if blended is None: continue
            if blended >= MEDIUM_THRESHOLD and MIN_ODDS <= odd <= MAX_ODDS:
                predictions.append(self._build_prediction(
                    a, now_str, xg_h, xg_a, "1X2", sel, blended, odd,
                    reasoning=[
                        f"📊 xG: {xg_h:.2f} — {xg_a:.2f}",
                        f"📈 Букмекер: П1 {o_p:.0f}% / Х {a.odds.prob_draw:.0f}% / П2 {a.odds.prob_away:.0f}%",
                        f"🔢 Пуассон: {poisson['p_home']:.0f}% / {poisson['p_draw']:.0f}% / {poisson['p_away']:.0f}%",
                        f"🔥 Форма: {a.home} [{form_h}] vs {a.away} [{form_a}]",
                    ],
                    form_h=form_h, form_a=form_a,
                ))

        xg_total = xg_h + xg_a

        over_sources = [(poisson["p_over25"], POISSON_WEIGHT)]
        if a.odds.prob_over25 > 0:
            over_sources.append((a.odds.prob_over25, ODDS_WEIGHT))
        prob_over = self._blend(over_sources)

        btts_sources = [(poisson["p_btts"], POISSON_WEIGHT)]
        if a.odds.prob_btts_yes > 0:
            btts_sources.append((a.odds.prob_btts_yes, ODDS_WEIGHT))
        prob_btts = self._blend(btts_sources)

        markets = [
            ("ТБ 2.5", prob_over, a.odds.over25, "Тотал 2.5"),
            ("ТМ 2.5",
             (100 - prob_over) if prob_over is not None else None,
             a.odds.under25, "Тотал 2.5"),
            ("ОЗ-ДА", prob_btts, a.odds.btts_yes, "Обе забьют"),
        ]
        for sel, prob, odd, mkt in markets:
            if prob is None or odd <= 0: continue
            if prob >= MEDIUM_THRESHOLD and MIN_ODDS <= odd <= MAX_ODDS:
                predictions.append(self._build_prediction(
                    a, now_str, xg_h, xg_a, mkt, sel, prob, odd,
                    reasoning=[f"⚽ Ожидаемые голы: {xg_total:.2f}"],
                    form_h=form_h, form_a=form_a,
                ))
        return predictions

    def _build_prediction(self, a: MatchAnalysis, now_str: str,
                          xg_h: float, xg_a: float,
                          market: str, selection: str,
                          probability: float, odd: float,
                          reasoning: List[str],
                          form_h: str, form_a: str) -> Prediction:
        return Prediction(
            match_time=now_str, league=a.league, league_tier=a.league_tier,
            home=a.home, away=a.away,
            market=market, selection=selection,
            probability=probability, odds=odd,
            confidence="🟢 СИЛЬНЫЙ" if probability >= STRONG_THRESHOLD else "🟡 СРЕДНИЙ",
            score=self._calc_score(probability, a, odd),
            reasoning=reasoning,
            data_quality=a.data_quality, is_derby=a.is_derby,
            value_rating=value_rating(probability, odd),
            kelly_stake=kelly_stake(probability/100, odd),
            expected_value=(probability/100 * odd - 1) * 100,
            form_home=form_h, form_away=form_a,
            fixture_id=a.fixture_id,
            league_id=a.league_id,
            kickoff_utc=a.time,
            xg_home=xg_h, xg_away=xg_a,
        )

    def _calc_score(self, prob, a: MatchAnalysis, odd) -> float:
        s = 0.0
        s += prob * 0.45
        s += a.data_quality * 20
        s += max(0, (3 - a.league_tier)) * 4
        s -= 12 if a.is_derby else 0
        vr = value_rating(prob, odd)
        if vr == "💎 ВЫСОКАЯ":  s += 8
        elif vr == "✅ СРЕДНЯЯ": s += 4
        if a.home_stats.form_score > 0.3 and a.away_stats.form_score < -0.3:
            s += 5
        if a.away_stats.form_score > 0.3 and a.home_stats.form_score < -0.3:
            s += 5
        return max(0.0, min(100.0, s))

    async def analyze_league(self, league_id):
        info = LEAGUES.get(league_id)
        if not info: return [], []
        name, _, tier = info
        year = await self.get_max_available_year(league_id)
        games = await self.get_games(league_id, year)
        if not games: return [], []
        if DEMO_MODE: games = games[:100]
        table = await self.get_table(league_id, year)

        tasks = [self.analyze_match(g, league_id, name, tier, table) for g in games]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        analyses = [r for r in results if isinstance(r, MatchAnalysis) and r.predictions]
        preds = [p for a in analyses for p in a.predictions]
        return analyses, preds

    def print_predictions(self, all_preds: List[Prediction], top_n=25):
        if not all_preds:
            print("\n😞 Нет прогнозов на текущее окно.\n")
            return
        all_preds.sort(
            key=lambda p: p.expected_value * max(p.data_quality, 0.1),
            reverse=True,
        )
        match_markets: Dict[str, set] = {}
        unique: List[Prediction] = []
        for p in all_preds:
            key = f"{p.home}|{p.away}"
            used = match_markets.setdefault(key, set())
            if p.market not in used and len(used) < 2:
                used.add(p.market)
                unique.append(p)

        strong = [p for p in unique if p.confidence == "🟢 СИЛЬНЫЙ"]
        medium = [p for p in unique if p.confidence == "🟡 СРЕДНИЙ"]

        print("\n" + "═" * 130)
        mode = "🎬 ДЕМО" if DEMO_MODE else f"⏰ ОКНО {LOOKAHEAD_HOURS}Ч"
        print(f"🏆 ТОП ПРОГНОЗОВ ({mode}) — {datetime.now().strftime('%d.%m.%Y %H:%M')}")
        print("═" * 130)
        header = (f"{'#':<3} {'Время':<12} {'Лига':<16} {'Матч':<30} "
                  f"{'Рынок':<10} {'Выбор':<7} {'Вер%':<5} {'Кэф':<5} "
                  f"{'EV%':<6} {'Келли':<6} {'Валуй':<12} {'Форма'}")
        print(header)
        print("─" * 130)

        idx = 0
        for group, label in [(strong, "🟢 СИЛЬНЫЕ"), (medium, "🟡 СРЕДНИЕ")]:
            if not group: continue
            print(f"\n  ── {label} ({len(group)}) ──")
            for p in group[:top_n]:
                idx += 1
                m = f"{p.home} — {p.away}"[:28]
                odds_s = f"{p.odds:.2f}" if p.odds > 0 else "  -  "
                form_s = f"[{p.form_home}] vs [{p.form_away}]"
                print(f"{idx:<3} {p.match_time:<12} {p.league:<16} {m:<30} "
                      f"{p.market:<10} {p.selection:<7} {p.probability:.0f}%  {odds_s:<5} "
                      f"{p.expected_value:+.1f}  {p.kelly_stake:.1f}%  "
                      f"{p.value_rating:<12} {form_s}")

        total     = len(unique)
        n_strong  = len(strong)
        n_value   = len([p for p in unique if p.value_rating == "💎 ВЫСОКАЯ"])
        n_leagues = len(set(p.league for p in unique))
        avg_prob  = float(np.mean([p.probability for p in unique])) if unique else 0
        avg_ev    = float(np.mean([p.expected_value for p in unique])) if unique else 0
        print(f"\n{'═' * 130}")
        print(f"📊 Итого: {total} прогнозов | 🟢 сильных: {n_strong} | "
              f"💎 валуй: {n_value} | лиг: {n_leagues} | "
              f"средняя вероятность: {avg_prob:.1f}% | средний EV: {avg_ev:+.1f}%")
        print(f"⚠️  Не является финансовой рекомендацией. Ставьте ответственно.")
        print("═" * 130)


# ═══════════════════════════════════════════════════════════
# 🆕 RESOLVE / CLOSING / METRICS
# ═══════════════════════════════════════════════════════════
async def resolve_pending_predictions(analyzer: CapperAnalyzer,
                                       history: HistoryDB) -> int:
    """Разрешает исходы для старых прогнозов через Games/list (fresh)."""
    pending = await history.get_pending_resolution()
    if not pending:
        return 0

    # Группируем по (league_id, year)
    by_league: Dict[Tuple[int, int], List[Dict[str, Any]]] = {}
    for row in pending:
        lid = row['league_id']
        if not lid: continue
        try:
            kickoff = datetime.fromisoformat(row['kickoff_utc'])
        except Exception:
            continue
        year = kickoff.year
        by_league.setdefault((lid, year), []).append(row)

    updated = 0
    for (lid, year), rows in by_league.items():
        games = await analyzer.get_games_fresh(lid, year)
        if not games:
            continue
        game_map = {str(g.get('id', '')): g for g in games}
        for row in rows:
            g = game_map.get(row['fixture_id'])
            if not g: continue
            score = analyzer._extract_score(g)
            if not score: continue
            hg, ag = score
            outcome = outcome_from_score(row['market'], row['selection'], hg, ag)
            if outcome:
                await history.update_result(row['id'], hg, ag, outcome)
                updated += 1
    return updated


async def capture_closing_odds(analyzer: CapperAnalyzer,
                                history: HistoryDB) -> int:
    """Ловит closing odds для матчей в окне за 0..120 минут до старта."""
    upcoming = await history.get_upcoming_without_closing()
    if not upcoming:
        return 0

    by_league: Dict[int, List[Dict[str, Any]]] = {}
    for row in upcoming:
        lid = row['league_id']
        if not lid: continue
        by_league.setdefault(lid, []).append(row)

    updated = 0
    for lid, rows in by_league.items():
        try:
            kickoff = datetime.fromisoformat(rows[0]['kickoff_utc'])
        except Exception:
            continue
        games = await analyzer.get_games_fresh(lid, kickoff.year)
        if not games: continue
        game_map = {str(g.get('id', '')): g for g in games}
        for row in rows:
            g = game_map.get(row['fixture_id'])
            if not g: continue
            odds = analyzer._extract_odds(g)
            closing = odd_for_prediction(odds, row['market'], row['selection'])
            if closing and closing > 0:
                await history.set_closing_odds(row['id'], closing)
                updated += 1
    return updated


# ─── Метрики ──────────────────────────────────────────────
def _brier(probs: np.ndarray, outcomes: np.ndarray) -> float:
    return float(np.mean((probs - outcomes) ** 2))

def _logloss(probs: np.ndarray, outcomes: np.ndarray) -> float:
    eps = 1e-9
    p = np.clip(probs, eps, 1 - eps)
    return float(-np.mean(outcomes * np.log(p) + (1 - outcomes) * np.log(1 - p)))

def _calibration(probs: np.ndarray, outcomes: np.ndarray,
                 n_buckets: int = 10) -> List[Dict[str, float]]:
    rows = []
    for i in range(n_buckets):
        lo, hi = i / n_buckets, (i + 1) / n_buckets
        if i == n_buckets - 1:
            mask = (probs >= lo) & (probs <= hi)
        else:
            mask = (probs >= lo) & (probs < hi)
        n = int(mask.sum())
        if n == 0: continue
        rows.append({
            "bucket": f"{int(lo*100):>2d}–{int(hi*100):<3d}%",
            "n": n,
            "avg_pred": float(probs[mask].mean() * 100),
            "actual":   float(outcomes[mask].mean() * 100),
            "diff":     float(outcomes[mask].mean() * 100 - probs[mask].mean() * 100),
        })
    return rows


async def print_history_report(history: HistoryDB, min_sample: int = 20):
    counts = await history.total_rows()
    if not counts or counts.get('total', 0) == 0:
        print("\n📚 История пуста — нечего считать.\n")
        return

    print("\n" + "═" * 90)
    print("📚 ИСТОРИЯ И МЕТРИКИ КАЧЕСТВА")
    print("═" * 90)
    print(f"  Всего записей:   {counts.get('total', 0)}")
    print(f"  Ожидают:         {counts.get('pending', 0)}")
    print(f"  Разрешено:       {counts.get('resolved', 0)}")
    print(f"  Есть closing:    {counts.get('with_closing', 0)}")

    rows = await history.fetch_resolved()
    if not rows:
        print("  ⏳ Пока нет разрешённых прогнозов — метрики появятся после первых матчей.\n")
        return

    # Массивы
    probs    = np.array([r['probability'] / 100.0 for r in rows])
    outcomes = np.array([1 if r['outcome'] == 'win' else 0 for r in rows])
    odds     = np.array([r['odds'] for r in rows])
    kelly    = np.array([(r['kelly_stake'] or 0) / 100.0 for r in rows])

    # Глобальные метрики
    brier   = _brier(probs, outcomes)
    logloss = _logloss(probs, outcomes)
    hit     = outcomes.mean() * 100

    profit_flat = np.where(outcomes == 1, odds - 1.0, -1.0)
    roi_flat    = profit_flat.mean() * 100

    total_stake = kelly.sum()
    profit_kel  = np.where(outcomes == 1, kelly * (odds - 1.0), -kelly)
    roi_kelly   = (profit_kel.sum() / total_stake * 100) if total_stake > 0 else 0.0

    print(f"\n  ── ОБЩИЕ ──")
    print(f"  N = {len(rows)}  |  Hit-rate: {hit:.1f}%  |  "
          f"Avg prob: {probs.mean()*100:.1f}%")
    print(f"  Brier score:  {brier:.4f}   (меньше = лучше; ≤0.25 — норм, ≤0.20 — хорошо)")
    print(f"  Log-loss:     {logloss:.4f}")
    print(f"  ROI (flat):   {roi_flat:+.2f}%  (по 1 ед. на ставку)")
    print(f"  ROI (Kelly):  {roi_kelly:+.2f}%  (по ¼-Келли с потолком {MAX_KELLY}%)")

    # CLV
    clv_rows = [r for r in rows
                if r.get('closing_odds') and r['closing_odds'] > 0
                and r['odds'] > 0]
    if clv_rows:
        clv_vals = np.array([
            (r['odds'] / r['closing_odds'] - 1) * 100
            for r in clv_rows
        ])
        avg_clv = clv_vals.mean()
        pos_clv = (clv_vals > 0).mean() * 100
        print(f"\n  ── CLV (n={len(clv_rows)}) ──")
        print(f"  Средний CLV:          {avg_clv:+.2f}%   "
              f"(>0 — мы обыгрываем closing line)")
        print(f"  Доля ставок с CLV>0:  {pos_clv:.1f}%   (≥55% — признак скилла)")
    else:
        print("\n  ── CLV: пока нет данных (closing odds ещё не захвачен) ──")

    # Калибровка
    print(f"\n  ── КАЛИБРОВКА (reliability) ──")
    cal = _calibration(probs, outcomes, n_buckets=10)
    if cal:
        print(f"  {'Bucket':<14} {'N':>5} {'Pred%':>8} {'Actual%':>9} {'Δ':>8}")
        for r in cal:
            sign = "✅" if abs(r['diff']) < 5 else ("⚠️" if abs(r['diff']) < 10 else "🔴")
            print(f"  {r['bucket']:<14} {r['n']:>5} {r['avg_pred']:>7.1f}% "
                  f"{r['actual']:>8.1f}% {r['diff']:>+7.1f}%  {sign}")
    if len(rows) < min_sample:
        print(f"  ⚠️ N < {min_sample} — таблица шумная, накапливай больше данных.")

    # Разбивка по рынкам
    by_market: Dict[str, List[Dict[str, Any]]] = {}
    for r in rows:
        by_market.setdefault(r['market'], []).append(r)

    print(f"\n  ── ПО РЫНКАМ ──")
    print(f"  {'Рынок':<14} {'N':>5} {'Hit%':>7} {'ROI(flat)':>11} {'Brier':>8}")
    for mkt, rws in sorted(by_market.items(),
                            key=lambda kv: -len(kv[1])):
        p = np.array([r['probability'] / 100.0 for r in rws])
        o = np.array([1 if r['outcome'] == 'win' else 0 for r in rws])
        od = np.array([r['odds'] for r in rws])
        hit_m = o.mean() * 100
        roi_m = np.where(o == 1, od - 1.0, -1.0).mean() * 100
        br_m  = _brier(p, o)
        print(f"  {mkt:<14} {len(rws):>5} {hit_m:>6.1f}% {roi_m:>+10.2f}% {br_m:>8.4f}")

    # Разбивка по уверенности
    by_conf: Dict[str, List[Dict[str, Any]]] = {}
    for r in rows:
        by_conf.setdefault(r['confidence'] or '?', []).append(r)
    if len(by_conf) > 1:
        print(f"\n  ── ПО УВЕРЕННОСТИ ──")
        print(f"  {'Группа':<16} {'N':>5} {'Hit%':>7} {'ROI(flat)':>11}")
        for conf, rws in by_conf.items():
            o = np.array([1 if r['outcome'] == 'win' else 0 for r in rws])
            od = np.array([r['odds'] for r in rws])
            roi_m = np.where(o == 1, od - 1.0, -1.0).mean() * 100
            print(f"  {conf:<16} {len(rws):>5} {o.mean()*100:>6.1f}% "
                  f"{roi_m:>+10.2f}%")

    # Последние 10 разрешённых — быстрая проверка глазами
    print(f"\n  ── ПОСЛЕДНИЕ 10 ──")
    print(f"  {'Дата':<16} {'Матч':<30} {'Рынок':<10} {'Выбор':<7} "
          f"{'Кэф':>5} {'Close':>6} {'Итог':>6} {'Счёт':>6}")
    for r in rows[:10]:
        mt = r['kickoff_utc'][:16].replace('T', ' ')
        m = f"{r['home']} — {r['away']}"[:28]
        close = f"{r['closing_odds']:.2f}" if r.get('closing_odds') else "  -  "
        res = "✅ WIN" if r['outcome'] == 'win' else "❌ LOSS"
        sc = f"{r['home_goals']}:{r['away_goals']}"
        print(f"  {mt:<16} {m:<30} {r['market']:<10} {r['selection']:<7} "
              f"{r['odds']:>5.2f} {close:>6} {res:>6} {sc:>6}")

    print("═" * 90)


# ═══════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════
async def main():
    api_key = os.environ.get('SSTATS_API_KEY')
    if not api_key:
        print("❌ API-ключ не найден.")
        return

    mode = "🎬 ДЕМО" if DEMO_MODE else f"⏰ ОКНО {LOOKAHEAD_HOURS}Ч"
    print(f"\n🔥 Capper's Edge v7.0 PRO — {mode}")
    print(f"🌍 Лиг: {len(LEAGUES)} | 📅 {datetime.now().strftime('%d.%m.%Y %H:%M')}")
    print(f"📐 Пороги: STRONG≥{STRONG_THRESHOLD}% MEDIUM≥{MEDIUM_THRESHOLD}% "
          f"DQ≥{MIN_DATA_QUALITY} Кэф [{MIN_ODDS}–{MAX_ODDS}] "
          f"Overround≤{MAX_OVERROUND}")
    print(f"⚖️  Веса: ODDS {ODDS_WEIGHT:.0%} | POISSON {POISSON_WEIGHT:.0%} | "
          f"FORM {FORM_WEIGHT:.0%} | FORM_XG {FORM_XG_WEIGHT:.0%}")
    print(f"📚 История: {'ВКЛ' if HISTORY_ENABLED else 'ВЫКЛ'} | DB: {HISTORY_DB}")
    print("═" * 80)

    async with CapperAnalyzer(api_key) as analyzer, \
               HistoryDB() as history:

        # ── A. Разрешаем старые прогнозы ──────────────────
        if HISTORY_ENABLED:
            print("\n📌 [1/4] Разрешение старых прогнозов...")
            try:
                n_res = await resolve_pending_predictions(analyzer, history)
                print(f"   ✅ Обновлено исходов: {n_res}")
            except Exception as e:
                log.error(f"resolve: {e}")

            # ── B. Захват closing odds ─────────────────────
            print("📌 [2/4] Захват closing odds (0–120 мин до старта)...")
            try:
                n_cls = await capture_closing_odds(analyzer, history)
                print(f"   ✅ Обновлено closing odds: {n_cls}")
            except Exception as e:
                log.error(f"closing: {e}")
        else:
            print("📌 История выключена — пропускаю шаги 1 и 2.")

        # ── C. Генерим новые прогнозы ─────────────────────
        print("\n📌 [3/4] Генерация прогнозов...")
        all_preds, all_analyses = [], []
        league_ids = list(LEAGUES.keys())

        # 🆕 Параллельная обработка лиг (по 5 одновременно)
        LEAGUE_PARALLEL = 5
        league_sem = asyncio.Semaphore(LEAGUE_PARALLEL)

        async def _process_one(lid):
            async with league_sem:
                try:
                    return lid, await analyzer.analyze_league(lid)
                except Exception as e:
                    log.error(f"{LEAGUES[lid][0]}: {e}")
                    return lid, ([], [])

        with tqdm(total=len(league_ids), desc="📊 Анализ лиг",
                  unit="лига", colour="green") as pbar:
            tasks = [_process_one(lid) for lid in league_ids]
            for coro in asyncio.as_completed(tasks):
                lid, (analyses, preds) = await coro
                pbar.set_description(f"📡 {LEAGUES[lid][0]}")
                all_analyses.extend(analyses)
                all_preds.extend(preds)
                pbar.update(1)

        print(f"\n{'═' * 80}")
        print(f"✅ Матчей: {len(all_analyses)}, Прогнозов: {len(all_preds)}")

        # ── D. Сохраняем в историю ────────────────────────
        if HISTORY_ENABLED and all_preds:
            print("\n📌 [4/4] Сохранение в историю...")
            try:
                n_saved = await history.save_predictions(all_preds)
                print(f"   ✅ Новых записей: {n_saved} "
                      f"(дубликаты по fixture+market+selection игнорируются)")
            except Exception as e:
                log.error(f"save: {e}")

        # ── E. Выводы ─────────────────────────────────────
        analyzer.print_predictions(all_preds, top_n=25)

        if HISTORY_ENABLED:
            await print_history_report(history)


if __name__ == "__main__":
    asyncio.run(main())
