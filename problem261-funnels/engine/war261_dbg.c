/* ============================================================================
 * war261.c — WAR-261 engine: Erdos #261 "subtract-or-double" walk
 *            frontier certification + funnel-head enumeration.
 *
 * WALK SEMANTICS (ground truth: problem261-funnels/FunnelStructure.lean,
 * problem261-funnels/funnels.py, problem261-q3bridge/walk.py):
 *   state (N, v) with 0 <= v < N.
 *   step:  v' = (2v) mod N  (modulus = CURRENT N; "take" iff 2v >= N), N' = N+1.
 *   start: n = 1 -> (3, 2);  n >= 2 -> (n+1, n);  n = 0 -> (1, 0) degenerate.
 *   DEATH: v == 0 at state (N, 0);  death modulus D = N  (Lean walkDeathAux:
 *   death is observed at the state, before stepping).
 *   n "terminates"  <=>  its walk reaches v == 0.
 *   room(n) = last_take - n = D - 1 - n.   PARITY LEMMA: D is always odd for
 *   n >= 1 (the terminal step is a take with 2v = D-1 even).  Engine asserts it.
 *
 * COALESCENCE CERTIFICATE (Lean death_fuel_mono): the death modulus is a
 * function of the state alone.  Two walks that share a state (N,v) share
 * their entire future, hence the same D.  The engine exploits this: a global
 * open-addressing table maps checkpoint states (N,v) -> walker id; a walk
 * probing a state belonging to a walker whose class already died at D is
 * certified dead at the SAME D without walking further.
 *
 * MODES
 *   war261 verify <n> <cap>
 *       Single-walk deep verifier (no table): walks n up to <cap> steps,
 *       prints death modulus D (Lean convention), last take, steps, takes,
 *       speed, terminal take moduli.  Asserts D odd and D == last_take+1.
 *   war261 batch <lo> <hi> <cap> <round0> <mult> <pbits> <ibits> <tbits>
 *               <chunk> <deaths> <merges> <snap>
 *       Batch all-n scan of [lo,hi] in chunks of <chunk> n's.  Round-based
 *       budgets (round0 steps, x<mult> per round, capped at <cap> total steps
 *       per walk).  Checkpoint probing every 2^pbits of N, table insertion
 *       every 2^ibits of N, table has 2^tbits slots.  deaths file: lines
 *       "n D" (2 fields) or "n 0 N v steps" (5 fields = UNRESOLVED at cap).
 *       merges file: "n_i n_o N" (walker n_i merged into inserter n_o's orbit
 *       at modulus N; exact merge is <= an insert-period earlier).
 *       snap file: binary resume checkpoint (per round, per chunk).
 *   war261 merge <nlist-file> <cap> <finebits> <tbits> <deaths> [merges]
 *       Merge-structure mode: walks every n in the file (one per line) with
 *       fine checkpointing (2^finebits), logging deaths + merge events.
 *   war261 refine <na> <nb> <N0> <window>
 *       Exact first-merge point of the walks of na and nb, given they share a
 *       state at modulus N0 (e.g. a merge event): re-walks both from their
 *       starts to N0 keeping the last <window> states, scans backward for the
 *       first common state.  Prints mergeN, v, and checks.
 *
 * RESOURCE DISCIPLINE: table is 2^tbits slots x 12 bytes; walkers ~58 bytes
 * per n.  Default production (tbits=23, chunk 100k): ~110 MB peak per process.
 * Compile: gcc -O3 -march=native -funroll-loops -o war261 war261.c
 * ==========================================================================*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <inttypes.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
#define NONE32 0xFFFFFFFFu

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* ========================= hash table (states) ========================= */
typedef struct { u64 *key; u32 *val; u64 mask; u64 used; u64 inslimit; int full; } Tab;
static Tab T;

static void tab_init(u64 bits) {
    u64 n = 1ULL << bits;
    T.key = (u64 *)calloc(n, sizeof(u64));        /* key 0 impossible: N >= 3 */
    T.val = (u32 *)malloc(n * sizeof(u32));
    if (!T.key || !T.val) { fprintf(stderr, "FATAL: table OOM\n"); exit(2); }
    T.mask = n - 1; T.used = 0; T.full = 0;
    T.inslimit = n * 10 / 16;                     /* stop inserting at 62.5% */
}
static inline u64 mix64(u64 x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31; return x;
}
static inline int tab_find(u64 key, u32 *out) {
    u64 i = mix64(key) & T.mask;
    for (;;) {
        u64 k = T.key[i];
        if (k == key) { *out = T.val[i]; return 1; }
        if (k == 0) return 0;
        i = (i + 1) & T.mask;
    }
}
static inline void tab_ins(u64 key, u32 val) {
    if (T.full) return;
    u64 i = mix64(key) & T.mask;
    for (;;) {
        u64 k = T.key[i];
        if (k == key) return;
        if (k == 0) {
            T.key[i] = key; T.val[i] = val;
            if (++T.used > T.inslimit) T.full = 1;
            return;
        }
        i = (i + 1) & T.mask;
    }
}

/* ========================= walkers (struct of arrays) =================== */
static u64 *wN, *wv, *wsteps, *wD, *wn;
static u32 *wpar, *whead, *wtail, *wnext;
static u8  *wst, *wlog;
static u64  WC;

#define ST_ACTIVE 0
#define ST_DEAD   1
#define ST_ALIAS  2
#define ST_UNRES  3

static FILE *df = NULL, *mf = NULL;

static void walkers_alloc(u64 c) {
    WC = c;
    wN      = (u64 *)malloc(c * 8);
    wv      = (u64 *)malloc(c * 8);
    wsteps  = (u64 *)malloc(c * 8);
    wD      = (u64 *)malloc(c * 8);
    wn      = (u64 *)malloc(c * 8);
    wpar    = (u32 *)malloc(c * 4);
    whead   = (u32 *)malloc(c * 4);
    wtail   = (u32 *)malloc(c * 4);
    wnext   = (u32 *)malloc(c * 4);
    wst     = (u8  *)malloc(c);
    wlog    = (u8  *)malloc(c);
    if (!wN || !wv || !wsteps || !wD || !wn || !wpar || !whead || !wtail ||
        !wnext || !wst || !wlog) {
        fprintf(stderr, "FATAL: walker OOM (%" PRIu64 " walkers)\n", c);
        exit(2);
    }
}
static inline u32 uf_find(u32 x) {
    while (wpar[x] != x) { wpar[x] = wpar[wpar[x]]; x = wpar[x]; }
    return x;
}

static void start_state(u64 n, u64 *N, u64 *v) {
    if (n == 0)      { *N = 1; *v = 0; }   /* degenerate (Lean: walkDeath 0 = 1) */
    else if (n == 1) { *N = 3; *v = 2; }
    else             { *N = n + 1; *v = n; }
}

/* log every not-yet-logged member of root's class as dying at D */
static void log_death_class(u32 root, u64 D) {
    for (u32 m = whead[root]; m != NONE32; m = wnext[m]) {
        if (!wlog[m]) {
            fprintf(df, "%llu %llu\n",
                    (unsigned long long)wn[m], (unsigned long long)D);
            wlog[m] = 1;
        }
    }
}

/* march walker i until total steps reach `stop` (or death / merge).
 * returns 0 = still active (budget exhausted), 1 = died, 2 = certified dead
 * (coalescence), 3 = merged into another walker's orbit.                  */
static int march(u32 i, u64 stop, u64 pbits, u64 ibits) {
    u64 N = wN[i], v = wv[i], st = wsteps[i];
    u64 pM = (1ULL << pbits) - 1, iM = (1ULL << ibits) - 1;
    u32 o = 0, r = 0;

    if (v == 0) {  /* degenerate start (n = 0) */
        wst[i] = ST_DEAD; wD[i] = N;
        log_death_class(i, N);
        return 1;
    }
    /* probe current state (insert only on the first-ever march of i) */
    if (N < (1ULL << 32)) {
        u64 key = (N << 32) | v;
        if (tab_find(key, &o)) {
            r = uf_find(o);
            if (r == i) { fprintf(stderr, "BUG: self-hit walker %u\n", i); exit(3); }
            if (wst[r] == ST_DEAD) {
                wN[i] = N; wv[i] = v; wsteps[i] = st;
                wst[i] = ST_DEAD; wD[i] = wD[r];
                log_death_class(i, wD[r]);
                return 2;
            }
            goto merge;
        } else if (st == 0) {
            tab_ins(key, i);
        }
    }
    while (st < stop) {
        u64 nextA = (N + pM) & ~pM;             /* next probe-aligned N > N */
        u64 lim = st + (nextA - N);
        if (lim > stop) lim = stop;
        u64 cnt = lim - st;
        while (cnt) {
            u64 t = v + v;
            u64 d = (t >= N) ? N : 0;           /* branchless take */
            v = t - d;
            N++; cnt--;
            if (getenv("DBG2") && ((N & 0xFFFFFF) == 0)) fprintf(stderr, "  inner i=%u N=%llu v=%llu st=%llu stop=%llu cnt=%llu\n", i, (unsigned long long)N, (unsigned long long)v, (unsigned long long)st, (unsigned long long)stop, (unsigned long long)cnt);
            if (__builtin_expect(v == 0, 0)) { st = lim - cnt; goto died; }
        }
        st = lim;
        if (st == stop) break;
        if (getenv("DBG2")) fprintf(stderr, "  aligned i=%u N=%llu v=%llu st=%llu\n", i, (unsigned long long)N, (unsigned long long)v, (unsigned long long)st);
        /* here N == nextA: probe-aligned state */
        if (N < (1ULL << 32)) {
            u64 key = (N << 32) | v;
            if (tab_find(key, &o)) {
                r = uf_find(o);
                if (r == i) { fprintf(stderr, "BUG: self-hit2 walker %u\n", i); exit(3); }
                if (wst[r] == ST_DEAD) {
                    wN[i] = N; wv[i] = v; wsteps[i] = st;
                    wst[i] = ST_DEAD; wD[i] = wD[r];
                    log_death_class(i, wD[r]);
                    return 2;
                }
                goto merge;
            } else if ((N & iM) == 0) {
                tab_ins(key, i);
            }
        }
        continue;
    merge:
        wN[i] = N; wv[i] = v; wsteps[i] = st;
        wpar[i] = r;
        if (whead[r] != NONE32) { wnext[wtail[r]] = whead[i]; wtail[r] = wtail[i]; }
        else                    { whead[r] = whead[i];        wtail[r] = wtail[i]; }
        wst[i] = ST_ALIAS;
        if (mf) fprintf(mf, "%llu %llu %llu\n",
                        (unsigned long long)wn[i], (unsigned long long)wn[o],
                        (unsigned long long)N);
        return 3;
    }
died:
    if ((N & 1) == 0) {   /* PARITY LEMMA violation = engine bug */
        fprintf(stderr, "BUG: even death modulus %llu (walker %u)\n",
                (unsigned long long)N, i);
        exit(3);
    }
    wN[i] = N; wv[i] = 0; wsteps[i] = st;
    wst[i] = ST_DEAD; wD[i] = N;
    log_death_class(i, N);
    return 1;
}

/* ============================ snapshot I/O ============================= */
static const char SNAP_MAGIC[8] = "WAR261S1";

static void snapshot_save(const char *path, u64 lo, u64 hi, u64 clo, u64 chi,
                          u64 round, u64 budget, u64 cap) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb");
    if (!f) { fprintf(stderr, "WARN: cannot write snapshot %s\n", tmp); return; }
    fwrite(SNAP_MAGIC, 8, 1, f);
    u64 hdr[8] = { lo, hi, clo, chi, round, budget, cap, WC };
    fwrite(hdr, 8, 8, f);
    fwrite(wst, 1, WC, f);
    fwrite(wlog, 1, WC, f);
    fwrite(wpar, 4, WC, f);
    fwrite(whead, 4, WC, f);
    fwrite(wtail, 4, WC, f);
    fwrite(wnext, 4, WC, f);
    fwrite(wN, 8, WC, f);
    fwrite(wv, 8, WC, f);
    fwrite(wsteps, 8, WC, f);
    fwrite(wD, 8, WC, f);
    fwrite(wn, 8, WC, f);
    fclose(f);
    if (rename(tmp, path) != 0)
        fprintf(stderr, "WARN: rename snapshot failed: %s\n", strerror(errno));
}
/* returns 1 if a matching snapshot was loaded into the walker arrays */
static int snapshot_load(const char *path, u64 lo, u64 hi, u64 *clo, u64 *chi,
                         u64 *round, u64 *budget, u64 cap) {
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    char magic[8];
    if (fread(magic, 8, 1, f) != 1 || memcmp(magic, SNAP_MAGIC, 8) != 0) {
        fprintf(stderr, "WARN: bad snapshot magic, ignoring\n"); fclose(f); return 0;
    }
    u64 hdr[8];
    if (fread(hdr, 8, 8, f) != 8) { fclose(f); return 0; }
    if (hdr[0] != lo || hdr[1] != hi || hdr[7] == 0) {
        fprintf(stderr, "WARN: snapshot range mismatch, ignoring\n"); fclose(f); return 0;
    }
    if (hdr[7] > (u64)40000000) { fclose(f); return 0; }
    walkers_alloc(hdr[7]);
    if (fread(wst, 1, WC, f) != 1 || fread(wlog, 1, WC, f) != 1 ||
        fread(wpar, 4, WC, f) != 1 || fread(whead, 4, WC, f) != 1 ||
        fread(wtail, 4, WC, f) != 1 || fread(wnext, 4, WC, f) != 1 ||
        fread(wN, 8, WC, f) != 1 || fread(wv, 8, WC, f) != 1 ||
        fread(wsteps, 8, WC, f) != 1 || fread(wD, 8, WC, f) != 1 ||
        fread(wn, 8, WC, f) != 1) {
        fprintf(stderr, "WARN: snapshot truncated, ignoring\n");
        fclose(f); return 0;
    }
    *clo = hdr[2]; *chi = hdr[3]; *round = hdr[4];
    *budget = hdr[5] < cap ? hdr[5] : cap;
    fclose(f);
    return 1;
}

/* ============================ mode: verify ============================= */
static int cmd_verify(u64 n, u64 cap) {
    u64 N, v;
    start_state(n, &N, &v);
    u64 steps = 0, takes = 0, lasttake = 0;
    u64 last8[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    int l8 = 0, died = 0;
    double t0 = now_sec();
    if (v == 0) died = 1;                         /* n = 0 degenerate */
    while (v && steps < cap) {
        u64 chunk = (cap - steps < (1ULL << 16)) ? (cap - steps) : (1ULL << 16);
        u64 c = chunk;
        while (c) {
            u64 t = v + v;
            if (t >= N) {
                v = t - N; takes++;
                lasttake = N; last8[l8++ & 7] = N;
                N++; c--;
                if (v == 0) { steps += chunk - c; died = 1; goto done; }
            } else {
                v = t; N++; c--;
            }
        }
        steps += chunk;
    }
done:;
    double el = now_sec() - t0;
    if (died) {
        if (n >= 1) {
            if (N != lasttake + 1) {
                fprintf(stderr, "BUG: D=%llu != last_take+1=%llu\n",
                        (unsigned long long)N, (unsigned long long)(lasttake + 1));
                return 3;
            }
            if ((N & 1) == 0) {
                fprintf(stderr, "BUG: even death modulus %llu\n",
                        (unsigned long long)N);
                return 3;
            }
        }
        printf("n=%llu DEAD death_modulus_D=%llu last_take=%llu steps=%llu "
               "takes=%llu room=%llu elapsed=%.3fs rate=%.0f steps/s "
               "last_takes=[",
               (unsigned long long)n, (unsigned long long)N,
               (unsigned long long)lasttake, (unsigned long long)steps,
               (unsigned long long)takes,
               (unsigned long long)(n >= 2 ? (N - 1 - n) : (N - 2)),
               el, el > 0 ? (double)steps / el : 0.0);
        for (int k = 0; k < 8; k++)
            printf("%s%llu", k ? " " : "",
                   (unsigned long long)last8[(l8 + k) & 7]);
        printf("]\n");
        return 0;
    }
    printf("n=%llu NONTERM steps>=%llu state_N=%llu v=%llu elapsed=%.3fs\n",
           (unsigned long long)n, (unsigned long long)steps,
           (unsigned long long)N, (unsigned long long)v, el);
    return 1;
}

/* ============================ mode: batch ============================== */
static int cmd_batch(u64 lo, u64 hi, u64 cap, u64 round0, u64 mult,
                     u64 pbits, u64 ibits, u64 tbits, u64 chunk,
                     const char *deaths, const char *merges, const char *snap) {
    if (round0 == 0 || mult < 2) { fprintf(stderr, "bad round0/mult\n"); return 2; }
    if (pbits == 0 || ibits < pbits || ibits > 40) { fprintf(stderr, "bad bits\n"); return 2; }
    if (chunk == 0) chunk = hi - lo + 1;
    if (chunk > 40000000) { fprintf(stderr, "chunk too large\n"); return 2; }

    tab_init(tbits);
    df = fopen(deaths, "a");
    mf = fopen(merges, "a");
    if (!df) { fprintf(stderr, "FATAL: cannot open deaths file\n"); return 2; }
    if (!mf) mf = fopen("/dev/null", "a");
    setvbuf(df, NULL, _IOFBF, 1 << 20);
    setvbuf(mf, NULL, _IOFBF, 1 << 20);

    u64 total_steps = 0, ndead = 0, nalias = 0, nunres = 0, ncert = 0;
    double t_start = now_sec();

    /* resume state */
    u64 clo = lo, chi, round = 0, budget = round0;
    int resumed = snapshot_load(snap, lo, hi, &clo, &chi, &round, &budget, cap);
    if (!resumed) { clo = lo; round = 0; budget = round0; }

    for (; clo <= hi; clo = chi + 1) {
        chi = (hi - clo < chunk) ? hi : clo + chunk - 1;
        if (!resumed) {
            walkers_alloc(chi - clo + 1);
            for (u64 i = 0; i < WC; i++) {
                u64 N, v;
                start_state(clo + i, &N, &v);
                wN[i] = N; wv[i] = v; wsteps[i] = 0; wD[i] = 0; wn[i] = clo + i;
                wpar[i] = (u32)i; whead[i] = (u32)i; wtail[i] = (u32)i;
                wnext[i] = NONE32; wst[i] = ST_ACTIVE; wlog[i] = 0;
            }
            round = 0; budget = round0;
        }
        resumed = 0;

        for (;; round++) {
            u64 stop = budget < cap ? budget : cap;
            u64 rsteps = 0;
            double t0 = now_sec();
            for (u32 i = 0; i < WC; i++) {
                if (wst[i] != ST_ACTIVE) continue;
                if (wsteps[i] >= stop) continue;
                u64 before = wsteps[i];
                if (getenv("DBG")) fprintf(stderr, "march i=%u n=%llu st=%llu\n", i, (unsigned long long)wn[i], (unsigned long long)wsteps[i]);
                int rc = march(i, stop, pbits, ibits);
                u64 d = wsteps[i] - before;
                total_steps += d; rsteps += d;
                if (rc == 1) ndead++;
                else if (rc == 2) { ndead++; ncert++; }
                else if (rc == 3) nalias++;
            }
            fflush(df); fflush(mf);
            u64 nact = 0;
            for (u64 i = 0; i < WC; i++) if (wst[i] == ST_ACTIVE) nact++;
            printf("[n=%" PRIu64 "..%" PRIu64 " round=%" PRIu64 "] budget=%" PRIu64
                   " active=%" PRIu64 " dead=%" PRIu64 " alias=%" PRIu64
                   " round_steps=%" PRIu64 " total_steps=%" PRIu64
                   " rate=%.0f/s elapsed=%.1fs table=%" PRIu64 "%s\n",
                   clo, chi, round, stop, nact, ndead, nalias, rsteps,
                   total_steps, rsteps / (now_sec() - t0 + 1e-9),
                   now_sec() - t_start, T.used, T.full ? " FULL(inserts off)" : "");
            fflush(stdout);
            u64 nbudget;
            if (budget > cap / mult) nbudget = cap;
            else nbudget = budget * mult;
            snapshot_save(snap, lo, hi, clo, chi, round + 1, nbudget, cap);
            if (nact == 0) break;
            if (budget >= cap) break;
            budget = nbudget;
        }
        /* final sweep for this chunk */
        for (u64 i = 0; i < WC; i++)
            if (wst[i] == ST_ACTIVE) wst[i] = ST_UNRES;
        for (u64 i = 0; i < WC; i++) {
            u32 r = uf_find((u32)i);
            if (wst[r] == ST_DEAD) {
                if (!wlog[i]) log_death_class(r, wD[r]);   /* safety net */
            } else if (wst[r] == ST_UNRES) {
                if (!wlog[i]) {
                    fprintf(df, "%llu 0 %llu %llu %llu\n",
                            (unsigned long long)wn[i], (unsigned long long)wN[r],
                            (unsigned long long)wv[r],
                            (unsigned long long)wsteps[r]);
                    wlog[i] = 1; nunres++;
                }
            }
        }
        fflush(df);
        printf("[chunk %" PRIu64 "..%" PRIu64 " COMPLETE] dead=%" PRIu64
               " (cert=%" PRIu64 ") alias=%" PRIu64 " unres=%" PRIu64
               " total_steps=%" PRIu64 " elapsed=%.1fs\n",
               clo, chi, ndead, ncert, nalias, nunres, total_steps,
               now_sec() - t_start);
        fflush(stdout);
        round = 0; budget = round0;
    }
    printf("[ALL DONE %llu..%llu] dead=%llu cert=%llu alias=%llu unres=%llu "
           "total_steps=%llu elapsed=%.1fs table=%llu\n",
           (unsigned long long)lo, (unsigned long long)hi,
           (unsigned long long)ndead, (unsigned long long)ncert,
           (unsigned long long)nalias, (unsigned long long)nunres,
           (unsigned long long)total_steps, now_sec() - t_start,
           (unsigned long long)T.used);
    fclose(df); fclose(mf);
    return nunres ? 1 : 0;
}

/* ============================ mode: merge ============================== */
static int cmd_merge(const char *nlist, u64 cap, u64 finebits, u64 tbits,
                     const char *deaths, const char *merges) {
    FILE *f = fopen(nlist, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", nlist); return 2; }
    static u64 ns[100000];
    u64 c = 0;
    char line[256];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        ns[c++] = strtoull(line, NULL, 10);
        if (c >= 100000) break;
    }
    fclose(f);
    walkers_alloc(c);
    for (u64 i = 0; i < c; i++) {
        u64 N, v;
        start_state(ns[i], &N, &v);
        wN[i] = N; wv[i] = v; wsteps[i] = 0; wD[i] = 0; wn[i] = ns[i];
        wpar[i] = (u32)i; whead[i] = (u32)i; wtail[i] = (u32)i;
        wnext[i] = NONE32; wst[i] = ST_ACTIVE; wlog[i] = 0;
    }
    tab_init(tbits);
    df = fopen(deaths, "a");
    mf = fopen(merges, "a");
    if (!df) return 2;
    if (!mf) mf = fopen("/dev/null", "a");
    printf("merge mode: %llu walkers, cap=%llu, finebits=%llu\n",
           (unsigned long long)c, (unsigned long long)cap,
           (unsigned long long)finebits);
    for (u32 i = 0; i < WC; i++) {
        if (wst[i] != ST_ACTIVE) continue;
        double t0 = now_sec();
        u64 before = wsteps[i];
        int rc = march(i, cap, finebits, finebits);
        printf("walker n=%llu rc=%d steps=%llu",
               (unsigned long long)wn[i], rc,
               (unsigned long long)(wsteps[i] - before));
        u32 r = uf_find(i);
        if (wst[r] == ST_DEAD)
            printf(" D=%llu", (unsigned long long)wD[r]);
        else if (wst[r] == ST_UNRES)
            printf(" UNRES");
        printf(" (%.2fs)\n", now_sec() - t0);
        fflush(stdout);
    }
    for (u64 i = 0; i < WC; i++)
        if (wst[i] == ST_ACTIVE) wst[i] = ST_UNRES;
    u64 dmin = ~0ULL, dmax = 0;
    for (u64 i = 0; i < WC; i++) {
        u32 r = uf_find((u32)i);
        if (wst[r] == ST_DEAD) {
            if (wD[r] < dmin) dmin = wD[r];
            if (wD[r] > dmax) dmax = wD[r];
            if (!wlog[i]) log_death_class(r, wD[r]);
        } else if (!wlog[i]) {
            fprintf(df, "%llu 0 %llu %llu %llu\n",
                    (unsigned long long)wn[i], (unsigned long long)wN[r],
                    (unsigned long long)wv[r], (unsigned long long)wsteps[r]);
            wlog[i] = 1;
        }
    }
    printf("SUMMARY: dead D range = [%llu, %llu]%s\n",
           (unsigned long long)dmin, (unsigned long long)dmax,
           (dmin == dmax && dmax != 0) ? "  (ALL SAME DEATH MODULUS)" : "");
    fflush(df); fclose(df); fclose(mf);
    return 0;
}

/* ============================ mode: refine ============================= */
static int cmd_refine(u64 na, u64 nb, u64 N0, u64 window) {
    if (window < 8 || window > (1ULL << 26)) { fprintf(stderr, "bad window\n"); return 2; }
    u64 *ringA = malloc(window * 8), *ringB = malloc(window * 8);
    if (!ringA || !ringB) return 2;
    u64 NA, VA, NB, VB;
    start_state(na, &NA, &VA);
    start_state(nb, &NB, &VB);
    /* walk a to N0 */
    while (NA < N0) {
        ringA[NA % window] = (NA << 32) | VA;
        u64 t = VA + VA;
        u64 d = (t >= NA) ? NA : 0;
        VA = t - d;
        NA++;
        if (VA == 0) {  /* died before N0: impossible for a real merge event */
            fprintf(stderr, "refine: walk a died at %llu before N0=%llu\n",
                    (unsigned long long)NA, (unsigned long long)N0);
            return 3;
        }
    }
    ringA[NA % window] = (NA << 32) | VA;
    while (NB < N0) {
        ringB[NB % window] = (NB << 32) | VB;
        u64 t = VB + VB;
        u64 d = (t >= NB) ? NB : 0;
        VB = t - d;
        NB++;
        if (VB == 0) {
            fprintf(stderr, "refine: walk b died at %llu before N0=%llu\n",
                    (unsigned long long)NB, (unsigned long long)N0);
            return 3;
        }
    }
    ringB[NB % window] = (NB << 32) | VB;
    if (ringA[N0 % window] != ringB[N0 % window]) {
        fprintf(stderr, "refine: walks differ at N0=%llu (bad event?)\n",
                (unsigned long long)N0);
        return 3;
    }
    u64 floorN = (na > nb ? na : nb) + 2;   /* both walks alive at N >= floorN */
    if (na == 1 || nb == 1) floorN = 4;
    u64 m = N0;
    while (m > floorN && ringA[(m - 1) % window] == ringB[(m - 1) % window]) m--;
    u64 key = ringA[m % window];
    printf("na=%llu nb=%llu hitN=%llu EXACT_MERGE_N=%llu v=%llu\n",
           (unsigned long long)na, (unsigned long long)nb,
           (unsigned long long)N0, (unsigned long long)m,
           (unsigned long long)(key & 0xFFFFFFFFULL));
    free(ringA); free(ringB);
    return 0;
}

/* ============================== main =================================== */
int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr,
            "usage: war261 verify <n> <cap>\n"
            "       war261 batch <lo> <hi> <cap> <round0> <mult> <pbits> <ibits>"
            " <tbits> <chunk> <deaths> <merges> <snap>\n"
            "       war261 merge <nlist-file> <cap> <finebits> <tbits> <deaths> [merges]\n"
            "       war261 refine <na> <nb> <N0> <window>\n");
        return 2;
    }
    if (!strcmp(argv[1], "verify"))
        return cmd_verify(strtoull(argv[2], 0, 10),
                          argc > 3 ? strtoull(argv[3], 0, 10) : 2000000000ULL);
    if (!strcmp(argv[1], "batch")) {
        if (argc < 14) { fprintf(stderr, "batch needs 12 args\n"); return 2; }
        return cmd_batch(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10),
                         strtoull(argv[4], 0, 10), strtoull(argv[5], 0, 10),
                         strtoull(argv[6], 0, 10), strtoull(argv[7], 0, 10),
                         strtoull(argv[8], 0, 10), strtoull(argv[9], 0, 10),
                         strtoull(argv[10], 0, 10), argv[11], argv[12], argv[13]);
    }
    if (!strcmp(argv[1], "merge")) {
        if (argc < 7) { fprintf(stderr, "merge needs: nlist cap finebits tbits deaths [merges]\n"); return 2; }
        return cmd_merge(argv[2], strtoull(argv[3], 0, 10),
                         strtoull(argv[4], 0, 10), strtoull(argv[5], 0, 10),
                         argv[6], argc > 7 ? argv[7] : "/dev/null");
    }
    if (!strcmp(argv[1], "refine")) {
        if (argc < 6) { fprintf(stderr, "refine needs 4 args\n"); return 2; }
        return cmd_refine(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10),
                          strtoull(argv[4], 0, 10), strtoull(argv[5], 0, 10));
    }
    fprintf(stderr, "unknown mode %s\n", argv[1]);
    return 2;
}
