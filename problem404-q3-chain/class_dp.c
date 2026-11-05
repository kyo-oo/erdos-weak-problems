/* class_dp.c — SOUND SCHEDULED-PRECISION CLASS-DP (C port of class_dp2.py), p=2.
 *
 * Erdos #404: g(a,2) = max over B ⊆ {a+1,...} of v2(1 + Σ_{i∈B} i!/a!).
 * EXACT port of the Python ground truth /home/z/erdos-weak-problems/problem404-q3-chain/class_dp2.py:
 *   - CP = L + slack (default 8); coins i!/a! for i in (a, imax], imax = last i with
 *     classOf(i) = v2(i!/a!) < L; unit = odd part of P_i mod 2^(CP-V).
 *   - States (t,u), u < 2^(CP-t): G = 1 + Σ(chosen P_i) = 2^t·U, U ≡ u (mod 2^(CP-t)).
 *   - Class V: sigmas = nonempty subset sums of the class's units mod 2^(CP-V) (set, no 0).
 *     For state (t,u) with t >= V:  s = ((u << (t-V)) + sigma) mod 2^(CP-V)
 *       s == 0 -> CAP sentinel (CP, 1)   [true valuation >= CP]
 *       s != 0 -> (V + v2(s), s >> v2(s))
 *     States with t < V are FROZEN -> dropped (recorded in snapshot stats only).
 *   - g = max l <= L with (max t in snapshot V) >= l for some V <= l  [exact Python replica]
 *   - first_unreach = first l with no non-sentinel state t >= l in any snapshot V <= l.
 *
 * Soundness (L52 lesson): merging on (t,u) at scheduled precision CP-t is EXACT.
 *
 * Witness extraction: backward reconstruction.  For a child (t,u) created at class V and
 * a sigma, the parent is UNIQUE: s = u << (t-V); r = (s - sigma) mod 2^(CP-V) != 0;
 * parent = (V + ctz(r), r >> ctz(r)) — exact inverse (u odd).  DFS over choices
 * (skip | sigma_j); ANY chain landing on the initial state (0,1) at class 0 is a REAL
 * witness (forward induction from (0,1) reproduces every state on the chain), and the
 * witness is re-verified independently with GMP bigints (and again in Python).
 *   Pruning: (a) tset bitmap (valuation present in snapshot V?) and (b) EXACT per-snapshot
 * membership via a disk-backed store of 64-bit state hashes (one file, per-level blocks,
 * sorted + binary-searched on demand).  With exact membership every surviving candidate
 * is a real state, so the descent is essentially backtrack-free (a completing chain is
 * real regardless; hash collisions can only add dead-end branches — never fake success,
 * since the V=0 acceptance test is the exact state (0,1) and every step is an exact
 * inverse pair).  Valuation-only pruning (pre-fix) explodes exponentially (a=2 L=254
 * exhausted 2e8 dfs nodes; with hashes the same run needs ~L nodes).
 *
 * Usage: ./class_dp A P L [slack] [--witness] [--mem MB] [--log N] [--dfs-budget N] [--no-hashstore]
 * Exit: 0 ok, 2 memory-cap/SIGTERM abort (with partial report), 3 usage/assert.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>
#include <gmp.h>

typedef uint64_t u64; typedef uint32_t u32; typedef int64_t i64; typedef int32_t i32; typedef uint8_t u8;

#ifndef WMAX
#define WMAX 96                 /* max limbs: CP <= WMAX*64 - 64 (override: -DWMAX=n) */
#endif
#define DIE(...) do { fprintf(stderr, "FATAL: " __VA_ARGS__); fprintf(stderr, "\n"); exit(3); } while (0)

static double now_sec(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9*ts.tv_nsec; }
static size_t rss_mb(void){ FILE *f = fopen("/proc/self/statm","r"); unsigned long a,b=0; if(!f) return 0; if (fscanf(f,"%lu %lu",&a,&b)!=2) b=0; fclose(f); return (size_t)(b * 4096UL / (1024*1024)); }

/* ---------------- config ---------------- */
static u64 A_, P_, L_, SLACK_, CP_;
static u32 W_;                 /* limbs holding CP bits */
static i64 V2A_;               /* v2(a!) = a - popcount(a) */
static u64 IMAX_;
static size_t mem_budget = 1000ULL << 20;
static u32 log_every = 40;
static bool do_witness = false, dump_coins = false, dump_sets = false, do_hashstore = true;
static u64 dfs_budget = 200000000ULL;

static i64 classof(u64 i){ return (i64)i - (i64)__builtin_popcountll(i) - V2A_; }  /* v2(i!/a!) */

/* ---------------- coins ---------------- */
static u32 *clsStart;          /* L+1 entries: CSR offsets into coinI/coinU */
static u64 *coinI;             /* the coin index i */
static u64 *coinU;             /* flattened units, W_ limbs each (value < 2^(CP-V), top-masked) */
static size_t ncoins;

/* ---------------- per-class sigmas (p=2: <= 2 coins/class -> <= 3 sigmas) ---------------- */
static u32 nsig;
static u32 sigmask_[8];
static u64 sigv_[8][WMAX];

static void build_sigmas(u32 V)
{
    nsig = 0;
    u32 k = (u32)(clsStart[V+1] - clsStart[V]);
    if (!k) return;
    if (k > 8) DIE("class %u has %u coins (>8) — semantics broken", V, k);
    u32 precV = (u32)(CP_ - V);
    u32 precW = (precV + 63) / 64;
    u64 topmask = (precV & 63) ? ((1ULL << (precV & 63)) - 1) : ~0ULL;
    for (u32 m = 1; m < (1u << k); m++) {
        u64 *s = sigv_[nsig];
        memset(s, 0, W_ * 8);
        for (u32 b = 0; b < k; b++) if (m & (1u << b)) {
            const u64 *u = coinU + ((size_t)clsStart[V] + b) * W_;
            u64 c = 0;
            for (u32 j = 0; j < W_; j++) {          /* s = (s + u) with mod 2^precV at the end */
                u64 r1 = s[j] + c; c = (r1 < s[j]);
                u64 r2 = r1 + u[j]; c += (r2 < r1);
                s[j] = r2;
            }
        }
        s[precW-1] &= topmask;                       /* mod 2^precV (drop carry above precV) */
        /* drop 0, dedupe */
        bool zero = true;
        for (u32 j = 0; j < W_; j++) if (s[j]) { zero = false; break; }
        if (zero) continue;
        bool dup = false;
        for (u32 j = 0; j < nsig; j++) if (!memcmp(sigv_[j], s, W_ * 8)) { dup = true; break; }
        if (dup) continue;
        sigmask_[nsig] = m; nsig++;
    }
}

/* ---------------- state table: arena + open-addressing index ---------------- */
typedef struct { u32 t, ulen; u64 limbs[]; } Entry;

static size_t g_arena_cap, g_slots_cap;
static volatile int mem_aborted = 0;
static volatile sig_atomic_t g_stop = 0;   /* SIGTERM/SIGINT -> graceful partial report */
static volatile u64 g_curV = 0;           /* last started class (for abort reports) */
static void on_stop(int sig){ (void)sig; g_stop = 1; }

typedef struct {
    u8 *arena; size_t used, arena_cap;
    u32 *slots; size_t nslots, slots_cap;
    size_t count;
} Table;

static void tbl_alloc(Table *T)
{
    T->arena_cap = g_arena_cap;
    T->arena = malloc(T->arena_cap);
    if (!T->arena) DIE("arena malloc (%zu bytes) failed", T->arena_cap);
    T->used = 0; T->count = 0;
    T->nslots = 1u << 16;
    T->slots = calloc(T->nslots, 4);
    if (!T->slots) DIE("slots calloc failed");
    T->slots_cap = g_slots_cap;
}
static void tbl_reset(Table *T)
{
    /* adaptive shrink to keep slot-memset cost proportional */
    if (T->nslots > (1u<<16) && T->nslots > 8 * (T->count + 1) * 2) {
        size_t want = 1u << 16;
        while (want < 4 * (T->count + 1) * 2) want <<= 1;
        if (want < T->nslots) {
            u32 *ns = realloc(T->slots, want * 4);
            if (ns) { T->slots = ns; T->nslots = want; }
        }
    }
    T->used = 0; T->count = 0;
    memset(T->slots, 0, T->nslots * 4);
}
static void tbl_free(Table *T){ free(T->arena); free(T->slots); }

static inline u64 hash_state(u32 t, u32 ulen, const u64 *limbs)
{
    u64 h = 0x9E3779B97F4A7C15ULL ^ ((u64)t * 0xFF51AFD7ED558CCDULL) ^ ((u64)ulen * 0xC4CEB9FE1A85EC53ULL);
    for (u32 i = 0; i < ulen; i++) h = (h ^ limbs[i]) * 0x100000001B3ULL, h ^= h >> 29;
    h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 32;
    return h;
}
static int tbl_grow(Table *T)
{
    size_t ns = T->nslots * 2;
    if (ns * 4 > T->slots_cap) { mem_aborted = 1; return 0; }
    u32 *nsl = calloc(ns, 4);
    if (!nsl) { mem_aborted = 1; return 0; }
    size_t off = 0;
    while (off < T->used) {
        Entry *e = (Entry *)(T->arena + off);
        u64 idx = hash_state(e->t, e->ulen, e->limbs) & (ns - 1);
        while (nsl[idx]) idx = (idx + 1) & (ns - 1);
        nsl[idx] = (u32)(off >> 3) + 1;
        off += 8 + 8 * e->ulen;
    }
    free(T->slots); T->slots = nsl; T->nslots = ns;
    return 1;
}
/* returns entry offset (arena), or 0 with mem_aborted=1 on cap breach */
static size_t tbl_insert(Table *T, u32 t, u32 ulen, const u64 *limbs)
{
    if ((T->count + 1) * 2 > T->nslots && !tbl_grow(T)) return 0;
    size_t need = 8 + 8 * (size_t)ulen;
    if (T->used + need > T->arena_cap) { mem_aborted = 1; return 0; }
    u64 idx = hash_state(t, ulen, limbs) & (T->nslots - 1);
    for (;; idx = (idx + 1) & (T->nslots - 1)) {
        u32 s = T->slots[idx];
        if (!s) break;
        size_t off = ((size_t)(s - 1)) << 3;
        Entry *e = (Entry *)(T->arena + off);
        if (e->t == t && e->ulen == ulen && !memcmp(e->limbs, limbs, 8 * (size_t)ulen)) return off;
    }
    size_t off = T->used;
    Entry *e = (Entry *)(T->arena + off);
    e->t = t; e->ulen = ulen;
    memcpy(e->limbs, limbs, 8 * (size_t)ulen);
    T->used += need; T->count++;
    T->slots[idx] = (u32)(off >> 3) + 1;
    return off;
}

/* ---------------- snapshot stats ---------------- */
static i64 *Aarr, *Barr;       /* [L+1]: max non-sentinel t / max t in snapshot V */
static u64 *tset;              /* [L+1] x stride: bitmap of t-values present */
static u32 stride_w;
static inline void tset_set(u32 snap, u32 t){ tset[(size_t)snap * stride_w + (t >> 6)] |= 1ULL << (t & 63); }
static inline bool tset_get(u32 snap, u32 t){ return (tset[(size_t)snap * stride_w + (t >> 6)] >> (t & 63)) & 1ULL; }

/* ---------------- hash store: exact per-snapshot membership for the witness DFS -----
 * During the forward pass every snapshot's state hashes (64-bit, of (t,ulen,limbs)) are
 * appended to one unlinked temp file (block per level, byte offsets in hoff[]).  The
 * backward DFS loads a level's block on demand, sorts it, and binary-searches.  Disk
 * cost: 8 bytes per state per level; memory cost: one level at a time.  On write
 * failure (disk full) levels above degrade to valuation-only (tset) pruning — the
 * witness stays SOUND (completion criterion is exact), only the search may slow.  */
static FILE *hf = NULL;            /* hash store file (unlinked; lives while open) */
static u64 *hoff;                  /* [L+2] byte offsets: level V block = [hoff[V], hoff[V+1]) */
static bool hstore_ok = false;     /* file open && writes healthy */
static u32 hstore_maxlevel = 0;    /* highest contiguously stored snapshot */
static u64 hstore_bytes = 0;
static u64 *hs_wbuf; static size_t hs_wcap;   /* write buffer (one level) */
static u64 *hs_buf;  static size_t hs_cap;     /* descent cache: one level, sorted */
static size_t hs_n; static i64 hs_cached = -1; static u64 hs_loads = 0;
static u64 hstore_cap_bytes = 2500ULL << 20;   /* disk cap for the hash store */

static int u64cmp(const void *a, const void *b){ u64 x = *(const u64*)a, y = *(const u64*)b; return (x > y) - (x < y); }

static void hs_load(u32 V)
{
    size_t n = (size_t)((hoff[V+1] - hoff[V]) >> 3);
    if (hs_cap < n) { hs_cap = n ? n : 1; hs_buf = realloc(hs_buf, hs_cap * 8); if (!hs_buf) DIE("hs_buf realloc"); }
    if (n) {
        if (fseek(hf, (long)hoff[V], SEEK_SET)) DIE("hs fseek");
        if (fread(hs_buf, 8, n, hf) != n) DIE("hs fread level %u", V);
    }
    qsort(hs_buf, n, 8, u64cmp);
    hs_n = n; hs_cached = (i64)V; hs_loads++;
}
static inline bool hs_contains(u64 h)
{
    size_t lo = 0, hi = hs_n;
    while (lo < hi) { size_t mid = lo + ((hi - lo) >> 1); if (hs_buf[mid] < h) lo = mid + 1; else hi = mid; }
    return lo < hs_n && hs_buf[lo] == h;
}
/* exact membership of (t,u) in snapshot V (when stored); else valuation-only fallback */
static bool snap_member(u32 V, u32 t, u32 ulen, const u64 *limbs)
{
    if (!tset_get(V, t)) return false;                 /* cheap bitmap prefilter */
    if (!hstore_ok || V > hstore_maxlevel) return true; /* degraded: valuation-only */
    if ((i64)V != hs_cached) hs_load(V);
    return hs_contains(hash_state(t, ulen, limbs));
}

/* ---------------- witness DFS ---------------- */
typedef struct { u32 t, ulen; u64 u[WMAX]; } DFrame;
static DFrame *dfr;            /* [L+2] */
static i32 *choice;            /* [L+2]: -1 none, 0 skip, j+1 = sigma j */
static u64 dfs_nodes;

/* witness targets (recorded during the forward pass) */
static bool capped = false;
static u32 capV = 0, capT = 0, capUlen = 0, capSig = 0; static u64 capU[WMAX];
static i64 bestT = 0; u32 bestV = 0xFFFFFFFFu, bestUlen = 1; static u64 bestU[WMAX];

/* scratch */
static u64 sbuf[WMAX + 2], ubuf[WMAX + 2], rbuf[WMAX + 2];

/* returns 1 on success (choices[] hold a valid chain), 0 on failure/exhaust.
 * NOTE recursion hygiene: sigv_/nsig/sigmask_ and ubuf/sbuf/rbuf are GLOBALS —
 * a recursive call clobbers them.  Each frame therefore (a) copies its input u
 * into frame-private dfr[V].u and reads ONLY from there, and (b) rebuilds the
 * class-V sigma set after every returning recursion.  Without (a)/(b) the
 * sigma loop continues over the CHILD's sigmas / a clobbered input (found by
 * audit + a=4 smoke test: dfs died after 2 nodes where a 3-node chain exists). */
static int dfs(u32 V, u32 t, u32 ulen, const u64 *u)
{
    if (t < V) return 0;                       /* not a live state of snapshot[V+1] */
    if (++dfs_nodes > dfs_budget) return 0;
    static int dfs_trace = -1; if (dfs_trace < 0) { const char *e = getenv("DFS_TRACE"); dfs_trace = e ? atoi(e) : 0; }
    if (dfs_trace) { fprintf(stderr, "ENTER V=%u t=%u ulen=%u u_hi=%llx u_lo=%llx\n", V, t, ulen,
                             ulen ? (unsigned long long)u[ulen-1] : 0ULL, ulen ? (unsigned long long)u[0] : 0ULL); }
    dfr[V].t = t; dfr[V].ulen = ulen; memcpy(dfr[V].u, u, 8 * (size_t)ulen);
    const u64 *uu = dfr[V].u;                  /* frame-private input */
    build_sigmas(V);
    if (nsig > 3) DIE("nsig=%u > 3 at V=%u — semantics broken", nsig, V);
    u32 precV = (u32)(CP_ - V), precW = (precV + 63) / 64;
    u64 topmask = (precV & 63) ? ((1ULL << (precV & 63)) - 1) : ~0ULL;
    /* candidate 0: skip — parent is the state itself, must be in snapshot[V] */
    if (V == 0) {
        if (t == 0 && ulen == 1 && uu[0] == 1) { choice[0] = 0; return 1; }
    } else {
        if (snap_member(V, t, ulen, uu)) {
            choice[V] = 0;
            if (dfs(V - 1, t, ulen, uu)) return 1;
        }
    }
    /* candidates 1..nsig: unique inverse parent per sigma */
    build_sigmas(V);                           /* restore after skip-branch recursion */
    for (u32 j = 0; j < nsig; j++) {
        /* s = uu << (t - V)  (fits in precV bits since uu < 2^(CP-t)) */
        u64 sh = (u64)t - V;
        memset(sbuf, 0, precW * 8);
        if (sh < precV) {
            u64 shL = sh >> 6, shB = sh & 63;
            if (shB == 0) { for (u32 q2 = 0; q2 < ulen; q2++) if (shL + q2 < precW) sbuf[shL + q2] = uu[q2]; }
            else {
                u64 carry = 0;
                for (u32 q2 = 0; q2 < ulen; q2++) {
                    u64 x = uu[q2];
                    if (shL + q2 < precW) sbuf[shL + q2] = (x << shB) | carry;
                    carry = x >> (64 - shB);
                }
                if (shL + ulen < precW) sbuf[shL + ulen] = carry;  /* FIX: in-range carry (was dropped!) */
            }
        } /* sh >= precV cannot happen here: t < CP, so sh = t-V <= CP-1-V < precV */
        /* r = (s - sigma) mod 2^precV  via two's complement add */
        u64 c = 1;
        for (u32 q2 = 0; q2 < precW; q2++) {
            u64 neg = ~sigv_[j][q2];
            u64 r1 = neg + c; c = (r1 < neg);
            u64 r2 = sbuf[q2] + r1; c += (r2 < sbuf[q2]);
            rbuf[q2] = r2;
        }
        rbuf[precW-1] &= topmask;
        /* r == 0 -> no parent via this sigma (proved: parent would need sh >= precV) */
        bool zero = true;
        for (u32 q2 = 0; q2 < precW; q2++) if (rbuf[q2]) { zero = false; break; }
        if (zero) continue;
        u32 lw = 0; while (!rbuf[lw]) lw++;
        u32 d = 64 * lw + (u32)__builtin_ctzll(rbuf[lw]);
        u32 tp = V + d;
        u32 dL = d >> 6, dB = d & 63, n2 = precW - dL;
        if (dB) {
            for (u32 q2 = 0; q2 < n2; q2++) {
                u64 x = rbuf[dL + q2], y = (dL + q2 + 1 < precW) ? rbuf[dL + q2 + 1] : 0;
                ubuf[q2] = (x >> dB) | (y << (64 - dB));
            }
        } else memcpy(ubuf, rbuf + dL, 8 * (size_t)n2);
        while (n2 && !ubuf[n2-1]) n2--;
        if (n2 == 0) continue;                   /* r>0 so n2>=1; paranoia */
        if (dfs_trace > 1) fprintf(stderr, "  cand V=%u j=%u tp=%u n2=%u ub0=%llx member=%d\n", V, j, tp, n2,
                                   (unsigned long long)ubuf[0], (V==0)?-1:(int)snap_member(V, tp, n2, ubuf));
        if (V == 0) {
            if (tp == 0 && n2 == 1 && ubuf[0] == 1) { choice[0] = (i32)j + 1; return 1; }
        } else {
            if (snap_member(V, tp, n2, ubuf)) {
                choice[V] = (i32)j + 1;
                if (dfs(V - 1, tp, n2, ubuf)) return 1;
                build_sigmas(V);                 /* restore clobbered sigma globals */
            }
        }
    }
    return 0;
}

/* ---------------- witness runner (normal AND abort paths) ------------------------
 * Backtracks from the recorded best/cap target; collects the coin subset B; verifies
 * v2(a! + sum_{i in B} i!) independently with GMP bigints (want = maxevent, or >= CP
 * when the target is a cap sentinel).  Any failure is FATAL (exit 3). */
static void run_witness(i64 maxevent, bool partial)
{
    if (!do_witness) return;
    dfr = malloc((L_ + 2) * sizeof(DFrame));
    choice = malloc((L_ + 2) * sizeof(i32));
    if (!dfr || !choice) DIE("dfs alloc failed");
    for (u64 i = 0; i < L_ + 2; i++) choice[i] = -1;
    dfs_nodes = 0;
    bool ok = false;
    if (capped) {
        /* chain: (capT,capU) in snapshot[capV]; fixed choice capSig at class capV */
        ok = capV == 0 ? true : dfs(capV - 1, capT, capUlen, capU);
        if (ok) choice[capV] = (i32)capSig + 1;
    } else if (bestV == 0xFFFFFFFFu) {
        ok = true;      /* maxevent = 0: empty witness */
    } else {
        ok = dfs(bestV, (u32)bestT, bestUlen, bestU);
    }
    if (!ok) {
        printf("WITNESS%s = FAILED (dfs_nodes=%" PRIu64 ", budget=%" PRIu64 ")\n", partial ? "-PARTIAL" : "", dfs_nodes, dfs_budget);
    } else {
        /* collect B */
        u64 *B = malloc((ncoins + 1) * sizeof(u64)); size_t nb = 0;
        u64 topV = capped ? (u64)capV : (u64)bestV;
        for (u64 Vv = 0; Vv <= topV; Vv++) {
            if (choice[Vv] > 0) {
                build_sigmas((u32)Vv);
                u32 m = sigmask_[choice[Vv] - 1];
                u32 kk = (u32)(clsStart[Vv+1] - clsStart[Vv]);
                for (u32 b = 0; b < kk; b++) if (m & (1u << b)) B[nb++] = coinI[clsStart[Vv] + b];
            }
        }
        /* sort + sanity */
        for (size_t i2 = 1; i2 < nb; i2++) { u64 x = B[i2]; size_t j2 = i2; while (j2 && B[j2-1] > x) { B[j2] = B[j2-1]; j2--; } B[j2] = x; }
        for (size_t i2 = 1; i2 < nb; i2++) if (B[i2] == B[i2-1]) DIE("witness has duplicate coin");
        for (size_t i2 = 0; i2 < nb; i2++) if (B[i2] <= A_ || B[i2] > IMAX_) DIE("witness coin out of range");
        /* independent GMP verification: T = a! + sum(i!) */
        mpz_t T, f;
        mpz_inits(T, f, NULL);
        mpz_fac_ui(T, (unsigned long)A_);
        for (size_t i2 = 0; i2 < nb; i2++) { mpz_fac_ui(f, (unsigned long)B[i2]); mpz_add(T, T, f); }
        u64 v2 = (u64)mpz_scan1(T, 0);
        i64 got = (i64)v2 - V2A_;
        i64 want = capped ? (i64)CP_ : maxevent;
        bool pass = capped ? (got >= want) : (got == want);
        printf("WITNESS%s = %s |B|=%zu Bmin=%" PRIu64 " Bmax=%" PRIu64 " v2(a!+sum B!)= %" PRIu64 " g-level=%" PRId64 " dfs_nodes=%" PRIu64 " hs_loads=%" PRIu64 "\n",
               partial ? "-PARTIAL" : "", pass ? "VERIFIED" : "FAILED", nb, nb ? B[0] : 0, nb ? B[nb-1] : 0, v2, got, dfs_nodes, hs_loads);
        printf("WITNESS_LIST");
        for (size_t i2 = 0; i2 < nb; i2++) printf(" %" PRIu64, B[i2]);
        printf("\n");
        if (!pass) { fprintf(stderr, "FATAL: witness verification FAILED\n"); exit(3); }
        mpz_clears(T, f, NULL);
        free(B);
    }
    free(dfr); free(choice); dfr = NULL; choice = NULL;
}

/* ---------------- main ---------------- */
int main(int argc, char **argv)
{
    if (argc < 4) {
        fprintf(stderr, "usage: %s A P L [slack] [--witness] [--mem MB] [--log N] [--dfs-budget N]\n", argv[0]);
        return 3;
    }
    A_ = strtoull(argv[1], NULL, 10);
    P_ = strtoull(argv[2], NULL, 10);
    L_ = strtoull(argv[3], NULL, 10);
    SLACK_ = (argc > 4 && argv[4][0] != '-') ? strtoull(argv[4], NULL, 10) : 8;
    for (int i = 4; i < argc; i++) {
        if (!strcmp(argv[i], "--dump-coins")) dump_coins = true;
        else if (!strcmp(argv[i], "--dump-sets")) dump_sets = true;
        else if (!strcmp(argv[i], "--witness")) do_witness = true;
        else if (!strcmp(argv[i], "--no-hashstore")) do_hashstore = false;
        else if (!strcmp(argv[i], "--mem") && i + 1 < argc) mem_budget = strtoull(argv[++i], NULL, 10) << 20;
        else if (!strcmp(argv[i], "--log") && i + 1 < argc) log_every = (u32)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--dfs-budget") && i + 1 < argc) dfs_budget = strtoull(argv[++i], NULL, 10);
        else if (argv[i][0] == '-' && i >= 5) DIE("unknown option %s", argv[i]);
    }
    if (P_ != 2) DIE("this port supports p=2 only (campaign probes are p=2)");
    if (L_ < 1) DIE("L out of range (L >= 1)");   /* upper bound enforced by the CP/WMAX check below */
    if (A_ < 2) DIE("a >= 2 required");
    CP_ = L_ + SLACK_;
    if (CP_ > WMAX * 64 - 64) DIE("CP=%llu too large for WMAX", (unsigned long long)CP_);
    W_ = (u32)((CP_ + 63) / 64);
    V2A_ = (i64)A_ - (i64)__builtin_popcountll(A_);

    double t0 = now_sec();
    setvbuf(stdout, NULL, _IOLBF, 0);
    signal(SIGTERM, on_stop); signal(SIGINT, on_stop);

    /* ---- coins (GMP, exactly like class_dp2.py) ---- */
    IMAX_ = A_ + 1;
    while (classof(IMAX_ + 1) < (i64)L_) IMAX_++;
    {
        mpz_t q, tmp;
        mpz_inits(q, tmp, NULL);
        mpz_set_ui(q, 1);
        /* pass 1: count per class */
        u32 *cnt = calloc(L_ + 1, 4);
        u64 *Vi = malloc((IMAX_ - A_ + 2) * sizeof(u64));
        size_t nkeep = 0;
        for (u64 i = A_ + 1; i <= IMAX_; i++) {
            mpz_mul_ui(q, q, i);
            mpz_mod_2exp(q, q, CP_ + 64);
            i64 V = classof(i);
            Vi[i - (A_ + 1)] = (u64)V;   /* classes are nondecreasing in i */
            if (V >= 0 && V < (i64)L_) { cnt[V]++; nkeep++; }
        }
        ncoins = nkeep;
        clsStart = calloc(L_ + 2, 4);
        size_t acc = 0;
        for (u64 V = 0; V <= L_; V++) { clsStart[V] = (u32)acc; acc += cnt[V]; }
        clsStart[L_ + 1] = (u32)acc;  /* unused guard */
        coinI = malloc((ncoins ? ncoins : 1) * sizeof(u64));
        coinU = malloc((ncoins ? ncoins : 1) * (size_t)W_ * 8);
        if (!coinI || !coinU) DIE("coin alloc failed");
        u32 *fill = malloc((L_ + 1) * 4);
        memcpy(fill, clsStart, (L_ + 1) * 4);
        mpz_set_ui(q, 1);
        for (u64 i = A_ + 1; i <= IMAX_; i++) {
            mpz_mul_ui(q, q, i);
            mpz_mod_2exp(q, q, CP_ + 64);
            i64 V = Vi[i - (A_ + 1)];
            if (V >= 0 && V < (i64)L_) {
                u32 pos = fill[V]++;
                coinI[pos] = i;
                mpz_tdiv_q_2exp(tmp, q, V);
                mpz_mod_2exp(tmp, tmp, CP_ - V);
                memset(coinU + (size_t)pos * W_, 0, (size_t)W_ * 8);
                size_t sz = mpz_size(tmp);
                if (sz > W_) DIE("unit too big");
                memcpy(coinU + (size_t)pos * W_, mpz_limbs_read(tmp), sz * 8);
            }
        }
        free(fill); free(cnt); free(Vi);
        mpz_clears(q, tmp, NULL);
        u32 maxper = 0;
        for (u64 V = 0; V < L_; V++) { u32 c = clsStart[V+1] - clsStart[V]; if (c > maxper) maxper = c; }
        if (maxper > 2)
            fprintf(stderr, "# NOTE: max coins per class = %u (expected <= 2 for p=2)\n", maxper);
    }
    if (dump_coins) {
        for (u64 V = 0; V < L_; V++) for (u32 b2 = 0; b2 < (u32)(clsStart[V+1] - clsStart[V]); b2++) {
            printf("COIN %" PRIu64 " %" PRIu64 " 0x", V, coinI[clsStart[V]+b2]);
            const u64 *uu = coinU + (size_t)(clsStart[V]+b2) * W_;
            int first = 1;
            for (int j2 = (int)W_ - 1; j2 >= 0; j2--) { if (first && !uu[j2]) continue; printf("%016" PRIx64, uu[j2]); first = 0; }
            if (first) printf("0");
            printf("\n");
        }
        return 0;
    }

    /* ---- stats arrays ---- */
    Aarr = malloc((L_ + 1) * 8); Barr = malloc((L_ + 1) * 8);
    stride_w = (u32)((CP_ + 64) / 64);
    tset = calloc((size_t)(L_ + 1) * stride_w, 8);
    if (!Aarr || !Barr || !tset) DIE("stats alloc failed");
    for (u64 V = 0; V <= L_; V++) { Aarr[V] = -1; Barr[V] = -1; }
    Aarr[0] = 0; Barr[0] = 0; tset_set(0, 0);

    /* ---- tables ---- */
    g_arena_cap = (size_t)(mem_budget * 0.44);
    g_slots_cap = (size_t)(mem_budget * 0.06);
    Table tabs[2]; int ci = 0;
    tbl_alloc(&tabs[0]); tbl_alloc(&tabs[1]);

    u64 one = 1;
    tbl_insert(&tabs[0], 0, 1, &one);
    if (mem_aborted) DIE("initial insert failed (memory?)");

    /* ---- hash store (witness support): one unlinked temp file, block per snapshot ---- */
    if (do_witness && do_hashstore) {
        hf = fopen("class_dp_hstore.tmp", "wb+");
        if (!hf) fprintf(stderr, "# hashstore: open failed — witness pruning degrades to valuation-only\n");
        else {
            unlink("class_dp_hstore.tmp");            /* inode lives while hf is open */
            setvbuf(hf, NULL, _IOFBF, 1 << 22);
            hoff = calloc(L_ + 2, 8);
            if (!hoff) DIE("hoff alloc failed");
            u64 one0 = 1, h0 = hash_state(0, 1, &one0);   /* snapshot 0 = {(0,1)} */
            hoff[0] = 0; hoff[1] = 8;
            if (fwrite(&h0, 8, 1, hf) == 1) { hstore_ok = true; hstore_maxlevel = 0; hstore_bytes = 8; }
            else fprintf(stderr, "# hashstore: initial write failed — degrading\n");
        }
    }

    /* best-event tracking (for g + witness): targets live at file scope (run_witness) */
    i64 maxevent = 0;

    size_t peak_states = 0;
    u32 nlive_sig = 0; (void)nlive_sig;

    /* ---- main class loop ---- */
    for (u64 V = 0; V < L_; V++) {
        g_curV = V;
        if (g_stop) goto memcap;
        Table *cur = &tabs[ci], *nw = &tabs[1 - ci];
        tbl_reset(nw);
        build_sigmas((u32)V);
        u32 k = (u32)(clsStart[V+1] - clsStart[V]);
        u32 precV = (u32)(CP_ - V), precW = (precV + 63) / 64;
        u64 topmask = (precV & 63) ? ((1ULL << (precV & 63)) - 1) : ~0ULL;

        size_t off = 0;
        while (off < cur->used) {
            Entry *e = (Entry *)(cur->arena + off);
            u32 t = e->t;
            if (t >= V) {
                const u64 *u = e->limbs; u32 ulen = e->ulen;
                tbl_insert(nw, t, ulen, u);
                if (mem_aborted) goto memcap;
                u64 sh = (u64)t - V;
                for (u32 j = 0; j < nsig; j++) {
                    if (sh >= precV) {
                        memcpy(sbuf, sigv_[j], (size_t)precW * 8);
                    } else {
                        u64 shL = sh >> 6, shB = sh & 63;
                        memset(sbuf, 0, precW * 8);
                        if (shB == 0) {
                            for (u32 q2 = 0; q2 < ulen; q2++) if (shL + q2 < precW) sbuf[shL + q2] = u[q2];
                        } else {
                            u64 carry = 0;
                            for (u32 q2 = 0; q2 < ulen; q2++) {
                                u64 x = u[q2];
                                if (shL + q2 < precW) sbuf[shL + q2] = (x << shB) | carry;
                                carry = x >> (64 - shB);
                            }
                            if (shL + ulen < precW) sbuf[shL + ulen] = carry;  /* FIX: in-range carry (was dropped!) */
                        } /* carry at limbs >= precW: mod drop, correct */
                        u64 c = 0;
                        for (u32 q2 = 0; q2 < precW; q2++) {
                            u64 a = sbuf[q2], b = sigv_[j][q2];
                            u64 r1 = a + c; c = (r1 < a);
                            u64 r2 = r1 + b; c += (r2 < r1);
                            sbuf[q2] = r2;
                        }
                        sbuf[precW-1] &= topmask;   /* mod 2^precV */
                    }
                    bool zero = true;
                    for (u32 q2 = 0; q2 < precW; q2++) if (sbuf[q2]) { zero = false; break; }
                    if (zero) {
                        /* CAP: true valuation >= CP */
                        tbl_insert(nw, (u32)CP_, 1, &one);
                        if (mem_aborted) goto memcap;
                        if (!capped) { capped = true; capV = (u32)V; capT = t; capUlen = ulen; capSig = j; memcpy(capU, u, 8 * (size_t)ulen); }
                        if (CP_ > (u64)maxevent) maxevent = (i64)CP_;
                    } else {
                        u32 lw = 0; while (!sbuf[lw]) lw++;
                        u32 d = 64 * lw + (u32)__builtin_ctzll(sbuf[lw]);
                        u32 t2 = (u32)V + d;
                        u32 dL = d >> 6, dB = d & 63, n2 = precW - dL;
                        if (dB) {
                            for (u32 q2 = 0; q2 < n2; q2++) {
                                u64 x = sbuf[dL + q2], y = (dL + q2 + 1 < precW) ? sbuf[dL + q2 + 1] : 0;
                                ubuf[q2] = (x >> dB) | (y << (64 - dB));
                            }
                        } else memcpy(ubuf, sbuf + dL, 8 * (size_t)n2);
                        while (n2 && !ubuf[n2-1]) n2--;
                        tbl_insert(nw, t2, n2, ubuf);
                        if (mem_aborted) goto memcap;
                        if (t2 > maxevent) { maxevent = t2; bestV = (u32)V; bestT = t2; bestUlen = n2; memcpy(bestU, ubuf, 8 * (size_t)n2); }
                    }
                }
            }
            off += 8 + 8 * (size_t)e->ulen;
        }

        /* snapshot stats (snapshot V+1 = nw) + hash-store append */
        {
            i64 Am = -1, Bm = -1;
            size_t o2 = 0;
            if (hstore_ok && nw->count > hs_wcap) {
                hs_wcap = nw->count;
                hs_wbuf = realloc(hs_wbuf, hs_wcap * 8);
                if (!hs_wbuf) DIE("hs_wbuf realloc failed");
            }
            size_t hi = 0;
            while (o2 < nw->used) {
                Entry *e = (Entry *)(nw->arena + o2);
                if (e->t > Bm) Bm = e->t;
                if (e->t < CP_ && e->t > Am) Am = e->t;
                tset_set((u32)V + 1, e->t);
                if (hstore_ok) hs_wbuf[hi++] = hash_state(e->t, e->ulen, e->limbs);
                o2 += 8 + 8 * (size_t)e->ulen;
            }
            Aarr[V + 1] = Am; Barr[V + 1] = Bm;
            if (nw->count > peak_states) peak_states = nw->count;
            if (hstore_ok) {
                u64 W = (u64)V + 1;
                u64 bytes = 8 * (u64)hi;
                bool wok = false;
                if (hstore_bytes + bytes <= hstore_cap_bytes) {
                    wok = (hi == 0) || (fwrite(hs_wbuf, 8, hi, hf) == hi);
                    if (wok) { hoff[W + 1] = hoff[W] + bytes; hstore_maxlevel = (u32)W; hstore_bytes += bytes; }
                    else fprintf(stderr, "# hashstore: write FAILED at snapshot %llu — tset fallback above\n", (unsigned long long)W);
                } else {
                    fprintf(stderr, "# hashstore: disk cap (%llu MB) hit at snapshot %llu — tset fallback above\n",
                            (unsigned long long)(hstore_cap_bytes >> 20), (unsigned long long)W);
                }
                if (!wok) hstore_ok = false;
            }
        }

        if (V % log_every == 0 || V == L_ - 1)
            printf("V=%4" PRIu64 ": coins=%2u states=%6zu maxevent=%" PRId64 "\n", V, k, nw->count, maxevent);
        if (dump_sets) {
            size_t o3 = 0;
            while (o3 < nw->used) {
                Entry *e = (Entry *)(nw->arena + o3);
                printf("S %" PRIu64 " %u 0x", V + 1, e->t);
                int first = 1;
                for (int j2 = (int)e->ulen - 1; j2 >= 0; j2--) { if (first && !e->limbs[j2]) continue; printf("%016" PRIx64, e->limbs[j2]); first = 0; }
                if (first) printf("0");
                printf("\n");
                o3 += 8 + 8 * (size_t)e->ulen;
            }
        }
        if ((V % log_every == 0 || V == L_ - 1))
            fprintf(stderr, "# [t=%.1fs] V=%" PRIu64 " states=%zu maxevent=%" PRId64 " rss=%zuMB\n",
                    now_sec() - t0, V, nw->count, maxevent, rss_mb());
        ci = 1 - ci;
    }

    /* ---- final answers (exact Python replicas) ---- */
    {
        i64 mb = INT64_MIN, g = 0;
        for (i64 l = 0; l <= (i64)L_; l++) { if (Barr[l] > mb) mb = Barr[l]; if (mb >= l) g = l; }
        i64 ma = INT64_MIN, fu = -1;
        for (i64 l = 1; l <= (i64)L_; l++) { if (Aarr[l] > ma) ma = Aarr[l]; if (ma < l) { fu = l; break; } }
        i64 g2 = maxevent < (i64)L_ ? maxevent : (i64)L_;
        printf("g(%" PRIu64 ",%" PRIu64 ") [C class_dp] = %" PRId64 "\n", A_, P_, g);
        if (fu < 0) printf("first UNREACHABLE level = > %" PRIu64 " (all 1..%" PRIu64 " reachable)\n", L_, L_);
        else        printf("first UNREACHABLE level = %" PRId64 "\n", fu);
        printf("max event valuation = %" PRId64 "\n", maxevent);
        printf("capped = %d\n", capped ? 1 : 0);
        printf("g_interval_crosscheck = %" PRId64 " %s\n", g2, (g2 == g) ? "(consistent)" : "(MISMATCH — INVESTIGATE)");
        printf("peak_states = %zu\n", peak_states);
        /* final-snapshot valuation profile (ALIVE frontier shape) */
        {
            Table *fin = &tabs[ci];
            u64 *hist = calloc((size_t)CP_ + 2, 8);
            if (hist) {
                size_t o4 = 0; u64 nst = 0; i64 tmax = -1;
                while (o4 < fin->used) {
                    Entry *e = (Entry *)(fin->arena + o4);
                    hist[e->t]++; nst++;
                    if ((i64)e->t > tmax) tmax = (i64)e->t;
                    o4 += 8 + 8 * (size_t)e->ulen;
                }
                u64 nd = 0; for (u64 t = 0; t <= CP_; t++) if (hist[t]) nd++;
                printf("final_snapshot: states=%llu distinct_t=%llu max_t=%" PRId64 "\n",
                       (unsigned long long)nst, (unsigned long long)nd, tmax);
                printf("final_t_hist:");
                for (u64 t = 0; t <= CP_; t++) if (hist[t]) printf(" %llu:%llu", (unsigned long long)t, (unsigned long long)hist[t]);
                printf("\n");
                free(hist);
            }
        }
        printf("hashstore = %s levels=0..%u bytes=%lluMB\n",
               hstore_ok ? "ok" : ((hf || hstore_bytes) ? "degraded" : "off"),
               hstore_maxlevel, (unsigned long long)(hstore_bytes >> 20));
        printf("elapsed_s = %.2f\n", now_sec() - t0);
        printf("peak_rss_mb = %zu\n", rss_mb());

        run_witness(maxevent, false);
    }
    if (hf) fclose(hf);
    tbl_free(&tabs[0]); tbl_free(&tabs[1]);
    return 0;

memcap:
    {   /* exact Python-replica answers on the truncated run (classes 0..g_curV-1 complete,
         * snapshot g_curV partially built).  Barr/Aarr beyond are -1, so the prefix-max
         * logic below is the sound "so far" statement: g = max certified reachable level,
         * fu = first level with no non-sentinel state t >= l in any completed snapshot <= l. */
        i64 mb = INT64_MIN, g = 0;
        for (i64 l = 0; l <= (i64)L_; l++) { if (Barr[l] > mb) mb = Barr[l]; if (mb >= l) g = l; }
        i64 ma = INT64_MIN, fu = -1;
        for (i64 l = 1; l <= (i64)L_; l++) { if (Aarr[l] > ma) ma = Aarr[l]; if (ma < l) { fu = l; break; } }
        const char *why = g_stop ? "SIGNAL" : "MEMCAP";
        printf("%s-ABORT at V=%llu last-complete-snapshot-states=%zu maxevent=%" PRId64 " arena_used=%zu/%zu\n",
               why, (unsigned long long)g_curV, tabs[1-ci].count, maxevent, tabs[1-ci].used, tabs[1-ci].arena_cap);
        printf("PARTIAL-RESULT (classes 0..%llu): g_certified_reachable = %" PRId64 " (sound lower bound on true g)\n",
               (unsigned long long)g_curV, g);
        if (fu < 0) printf("first UNREACHABLE level so far = none in 1..%llu\n", (unsigned long long)L_);
        else        printf("first UNREACHABLE level so far = %" PRId64 "\n", fu);
        fprintf(stderr, "%s-ABORT: V=%llu maxevent=%" PRId64 " states=%zu rss=%zuMB\n",
                why, (unsigned long long)g_curV, maxevent, tabs[1-ci].count, rss_mb());
        run_witness(maxevent, true);
    }
    if (hf) fclose(hf);
    return 2;
}
