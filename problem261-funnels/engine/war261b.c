/* ============================================================================
 * war261b.c — WAR-261 engine B: Erdos #261 walk — deep verifier with a
 *             PERSISTENT DEATH-CERTIFICATE TABLE + funnel-head enumerator.
 *
 * WALK SEMANTICS (ground truth, do not guess — see:
 *   problem261-funnels/FunnelStructure.lean  (walkStep / walkDeathAux / walkDeath)
 *   problem261-funnels/funnels.py            (census battery)
 *   problem261-q3bridge/walk.py              (frontier engine, same convention)):
 *   state (N, v), 0 <= v < N.
 *   step:  v' = (2v) mod N   (modulus = CURRENT N; "take" iff 2v >= N), N' = N+1.
 *   start: n = 1 -> (3, 2);  n >= 2 -> (n+1, n);  n = 0 -> (1, 0) degenerate.
 *   DEATH: v == 0 at state (N, 0); death modulus D = N (Lean convention: the
 *          death state's modulus; observed AFTER the zeroing step, i.e. the
 *          zeroing step used modulus D-1 = last_take).  n terminates <=> its
 *          walk reaches v == 0.  room(n) = last_take - n = D - 1 - n.
 *   PARITY LEMMA: D is odd for every n >= 1 (terminal step is a take with
 *          2v = D-1).  Engine asserts it; violation = engine bug.
 *
 * COALESCENCE CERTIFICATE (Lean theorem death_fuel_mono, kernel-green): the
 *   death modulus is a function of the STATE alone.  Two walks that share a
 *   state (N, v) share their entire future, hence the same D.  Therefore a
 *   persistent table mapping checkpoint states -> certified D is SOUND: any
 *   walk that reaches a certified state dies at exactly that D.  Cert file
 *   format (text, one cert per line):  "N v D".
 *
 * ALIGNMENT DISCIPLINE: all table probes/inserts happen at N aligned to
 *   2^bits (default bits = 20) plus each walk's start state.  Cert entries
 *   are emitted at exactly the same alignment, so a walk probing at 2^bits
 *   alignment always hits every inherited certificate that lies on its
 *   orbit (after coalescing, states coincide at every subsequent aligned N).
 *
 * MODES
 *   war261b sweep <lo> <hi> <cap> [outfile]
 *       Direct walks, NO tables/shortcuts (the independent baseline).
 *       Prints "n D steps" per n (D=0 => unresolved at cap) + summary.
 *   war261b deep <n> <cap> <bits> <certfile|-> <emitmin>
 *       Single-walk deep verifier.  certfile "-" = pure direct (no probing,
 *       no emission — the independent re-verification mode).  Otherwise the
 *       cert table is loaded and probed (hit => instant certification); on
 *       death/certification the walk's aligned states are appended to the
 *       cert file (if steps >= emitmin for a direct death; always for a
 *       cert-hit, extending coverage backwards).  Checkpoints to
 *       war261b.ckpt (resumable).  Prints one RESULT line.
 *   war261b deepmany <nlist> <cap> <bits> <certin|-> <certout|-> <outfile> <emitmin>
 *       Scan mode: the deep verifier over a list of n (one per line, '#'
 *       comments ok), shared in-memory cert table, per-walk RESULT lines to
 *       outfile.  Deaths are emitted to certout (append).
 *   war261b batch <lo> <hi> <cap> <round0> <mult> <bits> <tbits> <chunk>
 *                <emitmin> <deaths> <merges> <snap> <certin|-> <certout|->
 *       All-n certification of [lo,hi]: walker-table coalescence (union-find)
 *       + persistent cert table (loaded from certin at every chunk start,
 *       grown in-memory, deep direct deaths re-walked and appended to
 *       certout).  deaths file: "n D m" (m = d direct / c cert-table / w
 *       walker-merge) or "n 0 N v steps" for unresolved-at-cap.  merges file:
 *       "n_member n_target N" (merge detected at aligned N; exact merge is
 *       <= one alignment earlier).  snap: binary per-round checkpoint.
 *   war261b funnels <deathsfile> [minD [maxD]]
 *       Funnel-head enumerator: cluster walk deaths by death modulus D;
 *       report the head hierarchy (D, walk count, n-range) sorted by count,
 *       plus summary.  Optional [minD,maxD] head filter.
 *
 * RESOURCE DISCIPLINE: walker table 2^tbits slots x 12 B; cert table 2^21
 *   slots x 16 B (32 MB); walkers ~66 B/n; batch of 500k n ~ 350 MB peak.
 *   Compile: gcc -O3 -march=native -funroll-loops -o war261b war261b.c
 *   Run under: nice -n 10 ...
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
#define MAXN32 (1ULL << 32)

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void fatal(const char *msg) {
    fprintf(stderr, "FATAL: %s\n", msg);
    exit(3);
}

/* ===================== start state (Lean Kill-#2 convention) ============ */
static void start_state(u64 n, u64 *N, u64 *v) {
    if (n == 0)      { *N = 1; *v = 0; }   /* degenerate: Lean walkDeath 0 = 1 */
    else if (n == 1) { *N = 3; *v = 2; }
    else             { *N = n + 1; *v = n; }
}
static inline u64 state_key(u64 N, u64 v) { return (N << 32) | v; }

/* ===================== hash tables ====================================== */
static inline u64 mix64(u64 x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31; return x;
}

/* walker table: key -> walker id (u32) */
typedef struct { u64 *key; u32 *val; u64 mask, used, inslimit; int full; } WTab;
static WTab WT;
static void wtab_init(u64 bits) {
    u64 n = 1ULL << bits;
    WT.key = (u64 *)calloc(n, sizeof(u64));       /* key 0 impossible (N>=1) */
    WT.val = (u32 *)malloc(n * sizeof(u32));
    if (!WT.key || !WT.val) fatal("walker table OOM");
    WT.mask = n - 1; WT.used = 0; WT.full = 0;
    WT.inslimit = n * 10 / 16;
}
static inline int wtab_find(u64 key, u32 *out) {
    u64 i = mix64(key) & WT.mask;
    for (;;) {
        u64 k = WT.key[i];
        if (k == key) { *out = WT.val[i]; return 1; }
        if (k == 0) return 0;
        i = (i + 1) & WT.mask;
    }
}
static inline void wtab_ins(u64 key, u32 val) {
    if (WT.full) return;
    u64 i = mix64(key) & WT.mask;
    for (;;) {
        u64 k = WT.key[i];
        if (k == key) return;
        if (k == 0) {
            WT.key[i] = key; WT.val[i] = val;
            if (++WT.used > WT.inslimit) WT.full = 1;
            return;
        }
        i = (i + 1) & WT.mask;
    }
}

/* cert table: key -> death modulus D (u64) */
typedef struct { u64 *key; u64 *val; u64 mask, used, inslimit; int full; } CTab;
static CTab CT;
static void ctab_init(u64 bits) {
    u64 n = 1ULL << bits;
    CT.key = (u64 *)calloc(n, sizeof(u64));
    CT.val = (u64 *)malloc(n * sizeof(u64));
    if (!CT.key || !CT.val) fatal("cert table OOM");
    CT.mask = n - 1; CT.used = 0; CT.full = 0;
    CT.inslimit = n * 10 / 16;
}
/* returns 1 and sets *D on hit */
static inline int ctab_find(u64 key, u64 *D) {
    if (CT.used == 0) return 0;
    u64 i = mix64(key) & CT.mask;
    for (;;) {
        u64 k = CT.key[i];
        if (k == key) { *D = CT.val[i]; return 1; }
        if (k == 0) return 0;
        i = (i + 1) & CT.mask;
    }
}
/* insert; if the key exists with a DIFFERENT D => unsoundness => fatal */
static void ctab_ins(u64 key, u64 D) {
    if (CT.full) return;
    u64 i = mix64(key) & CT.mask;
    for (;;) {
        u64 k = CT.key[i];
        if (k == key) {
            if (CT.val[i] != D) {
                fprintf(stderr, "FATAL: cert conflict key=%llu: %llu vs %llu\n",
                        (unsigned long long)key,
                        (unsigned long long)CT.val[i],
                        (unsigned long long)D);
                exit(3);
            }
            return;
        }
        if (k == 0) {
            CT.key[i] = key; CT.val[i] = D;
            if (++CT.used > CT.inslimit) CT.full = 1;
            return;
        }
        i = (i + 1) & CT.mask;
    }
}

/* cert file: text lines "N v D" */
static u64 cert_load_file(const char *path) {
    if (!path || !strcmp(path, "-")) return 0;
    FILE *f = fopen(path, "r");
    if (!f) return 0;                       /* absent = empty */
    u64 cnt = 0, ln = 0;
    char line[256];
    while (fgets(line, sizeof line, f)) {
        ln++;
        if (line[0] == '#' || line[0] == '\n') continue;
        unsigned long long a, b, d;
        if (sscanf(line, "%llu %llu %llu", &a, &b, &d) != 3) {
            if (ln && feof(f)) break;       /* torn tail of a growing file */
            fprintf(stderr, "WARN: bad cert line %llu in %s (ignored)\n",
                    (unsigned long long)ln, path);
            continue;
        }
        u64 N = a, v = b, D = d;
        if (N == 0 || N >= MAXN32 || v >= N || D == 0 || (D & 1) == 0) {
            fprintf(stderr, "WARN: implausible cert line %s:%llu (ignored)\n",
                    path, (unsigned long long)ln);
            continue;
        }
        ctab_ins(state_key(N, v), D);
        cnt++;
    }
    fclose(f);
    return cnt;
}
static FILE *certf_out = NULL;
static void cert_out_open(const char *path) {
    if (!path || !strcmp(path, "-")) return;
    certf_out = fopen(path, "a");
    if (!certf_out) fatal("cannot open cert output file");
    setvbuf(certf_out, NULL, _IOFBF, 1 << 18);
}
static void cert_emit(u64 N, u64 v, u64 D) {
    if (N == 0 || N >= MAXN32) return;      /* keys must fit the 64-bit pack */
    ctab_ins(state_key(N, v), D);
    if (certf_out)
        fprintf(certf_out, "%llu %llu %llu\n",
                (unsigned long long)N, (unsigned long long)v,
                (unsigned long long)D);
}

/* ===================== walkers (struct of arrays) ======================= */
static u64 *wN, *wv, *wsteps, *wD, *wn;
static u32 *wpar, *whead, *wtail, *wnext;
static u8  *wst, *wlog, *wmode;
static u64  WC;

#define ST_ACTIVE 0
#define ST_DEAD   1
#define ST_ALIAS  2
#define ST_UNRES  3

static FILE *df = NULL, *mf = NULL;

static void walkers_alloc(u64 c) {
    WC = c;
    wN     = (u64 *)malloc(c * 8);
    wv     = (u64 *)malloc(c * 8);
    wsteps = (u64 *)malloc(c * 8);
    wD     = (u64 *)malloc(c * 8);
    wn     = (u64 *)malloc(c * 8);
    wpar   = (u32 *)malloc(c * 4);
    whead  = (u32 *)malloc(c * 4);
    wtail  = (u32 *)malloc(c * 4);
    wnext  = (u32 *)malloc(c * 4);
    wst    = (u8  *)malloc(c);
    wlog   = (u8  *)malloc(c);
    wmode  = (u8  *)malloc(c);
    if (!wN || !wv || !wsteps || !wD || !wn || !wpar || !whead || !wtail ||
        !wnext || !wst || !wlog || !wmode)
        fatal("walker OOM");
}
static inline u32 uf_find(u32 x) {
    while (wpar[x] != x) { wpar[x] = wpar[wpar[x]]; x = wpar[x]; }
    return x;
}

static u64 g_cnt_d = 0, g_cnt_c = 0, g_cnt_w = 0;

static void log_death_class(u32 root, u64 D) {
    /* root dies with its own mode; class members (merged walkers) die as 'w' */
    if (!wlog[root]) {
        fprintf(df, "%llu %llu %c\n",
                (unsigned long long)wn[root], (unsigned long long)D,
                (char)wmode[root]);
        wlog[root] = 1;
        if (wmode[root] == 'c') g_cnt_c++; else if (wmode[root] == 'w') g_cnt_w++;
        else g_cnt_d++;
    }
    for (u32 m = whead[root]; m != NONE32; m = wnext[m]) {
        if (m == root) continue;
        if (!wlog[m]) {
            fprintf(df, "%llu %llu w\n",
                    (unsigned long long)wn[m], (unsigned long long)D);
            wlog[m] = 1; wmode[m] = 'w'; g_cnt_w++;
        }
    }
}

/* ===================== stepping core ==================================== */
/* advance the walk (N,v) exactly cnt steps; returns 1 if it died (v hit 0)
 * during them, in which case *diedN = the death modulus and the number of
 * steps actually taken is written to *used. */
static inline int step_block(u64 *Np, u64 *vp, u64 cnt, u64 *used) {
    u64 N = *Np, v = *vp, c = cnt;
    while (c) {
        u64 t = v + v;
        u64 d = (t >= N) ? N : 0;            /* branchless take */
        v = t - d;
        N++; c--;
        if (__builtin_expect(v == 0, 0)) {
            *Np = N; *vp = v; *used = cnt - c; return 1;
        }
    }
    *Np = N; *vp = v; *used = cnt; return 0;
}

/* ===================== aligned-state collector ========================== */
typedef struct { u64 *N; u64 *v; u64 n, cap; } Col;
static void col_init(Col *c) {
    c->cap = 1 << 16; c->n = 0;
    c->N = (u64 *)malloc(c->cap * 8);
    c->v = (u64 *)malloc(c->cap * 8);
    if (!c->N || !c->v) fatal("collector OOM");
}
static void col_push(Col *c, u64 N, u64 v) {
    if (c->n == c->cap) {
        c->cap *= 2;
        c->N = (u64 *)realloc(c->N, c->cap * 8);
        c->v = (u64 *)realloc(c->v, c->cap * 8);
        if (!c->N || !c->v) fatal("collector grow OOM");
    }
    c->N[c->n] = N; c->v[c->n] = v; c->n++;
}
/* emit a walk's certs: re-walk n from its start to death D, emitting the
 * start state and every bits-aligned state; verifies the re-walk dies at D
 * (deterministic map => must match; mismatch = engine bug). */
static u64 emit_walk_certs(u64 n, u64 D, u64 bits, u64 *rewalk_steps) {
    u64 N, v, AM = (1ULL << bits) - 1;
    start_state(n, &N, &v);
    u64 steps = 0, emitted = 0;
    if (v == 0) return 0;
    if (N < MAXN32) { cert_emit(N, v, D); emitted++; }
    for (;;) {
        u64 nextA = ((N | AM) + 1) & ~AM;   /* next aligned N > N */
        u64 used;
        if (step_block(&N, &v, nextA - N, &used)) {
            if (N != D) {
                fprintf(stderr, "FATAL: re-walk of n=%llu died at %llu != %llu\n",
                        (unsigned long long)n, (unsigned long long)N,
                        (unsigned long long)D);
                exit(3);
            }
            steps += used; break;
        }
        steps += used;
        if (N < MAXN32) { cert_emit(N, v, D); emitted++; }
        if (N >= D) fatal("re-walk passed D without dying");
    }
    if (rewalk_steps) *rewalk_steps = steps;
    return emitted;
}

/* ===================== deep verifier (single / many) ==================== */
#define CKPT_MAGIC "WAR261B1"
static const char *ckpt_path = "war261b.ckpt";

static int ckpt_save(u64 n, u64 cap, u64 N, u64 v, u64 steps, Col *c) {
    FILE *f = fopen(ckpt_path, "wb");
    if (!f) return 0;
    fwrite(CKPT_MAGIC, 8, 1, f);
    u64 hdr[4] = { n, cap, N, v };
    fwrite(hdr, 8, 4, f);
    fwrite(&steps, 8, 1, f);
    fwrite(&c->n, 8, 1, f);
    if (c->n) { fwrite(c->N, 8, c->n, f); fwrite(c->v, 8, c->n, f); }
    fclose(f);
    return 1;
}
static int ckpt_load(u64 n, u64 cap, u64 *N, u64 *v, u64 *steps, Col *c) {
    FILE *f = fopen(ckpt_path, "rb");
    if (!f) return 0;
    char magic[8]; u64 hdr[4];
    int ok = fread(magic, 8, 1, f) == 1 && !memcmp(magic, CKPT_MAGIC, 8)
          && fread(hdr, 8, 4, f) == 4;
    u64 st = 0, cn = 0;
    ok = ok && fread(&st, 8, 1, f) == 1 && fread(&cn, 8, 1, f) == 1;
    if (!ok || hdr[0] != n || hdr[1] != cap || cn > (1ULL << 24)) {
        fclose(f); return 0;
    }
    *N = hdr[2]; *v = hdr[3]; *steps = st;
    c->n = 0;
    for (u64 i = 0; i < cn; i++) {
        u64 a, b;
        if (fread(&a, 8, 1, f) != 1 || fread(&b, 8, 1, f) != 1) {
            fclose(f); return 0;
        }
        col_push(c, a, b);
    }
    fclose(f);
    return 1;
}

/* one deep walk.  Returns: 0 unresolved at cap; 1 died direct; 2 certified.
 * mode/step accounting returned via pointers. Final state is reported via
 * *Nfin / *vfin in every case. */
static int deep_walk(u64 n, u64 cap, u64 bits, int use_cert, int do_emit,
                     u64 emitmin, u64 *Dout, u64 *steps_out, u64 *lasttake_out,
                     u64 *certN_out, u64 *certv_out, u64 *Nfin, u64 *vfin,
                     int quiet) {
    u64 N, v, steps = 0, AM = (1ULL << bits) - 1;
    Col col; col_init(&col);
    int resumed = ckpt_load(n, cap, &N, &v, &steps, &col);
    if (!resumed) {
        start_state(n, &N, &v);
        steps = 0;
        if (v == 0) {                       /* degenerate n = 0 */
            *Dout = N; *steps_out = 0; *lasttake_out = 0;
            remove(ckpt_path);
            return 1;
        }
    }
    if (!quiet)
        fprintf(stderr, "[deep n=%llu%s] start N=%llu v=%llu cap=%llu bits=%llu\n",
                (unsigned long long)n, resumed ? " (resumed)" : "",
                (unsigned long long)N, (unsigned long long)v,
                (unsigned long long)cap, (unsigned long long)bits);
    double t0 = now_sec();
    u64 next_ckpt = steps + (1ULL << 28), next_prog = steps + (1ULL << 30);
    int rc = 0;
    u64 D = 0, certN = 0, certv = 0;
    *Nfin = N; *vfin = v;
    if (N < MAXN32) {
        u64 key = state_key(N, v), cd;
        if (use_cert && ctab_find(key, &cd)) {
            D = cd; certN = N; certv = v; rc = 2;
            goto done;
        }
        if (!resumed) col_push(&col, N, v);
    }
    while (steps < cap) {
        u64 nextA = ((N | AM) + 1) & ~AM;
        u64 want = nextA - N;
        if (want > cap - steps) want = cap - steps;
        u64 used;
        if (step_block(&N, &v, want, &used)) {   /* died */
            steps += used;
            D = N; rc = 1;
            goto done;
        }
        steps += used;
        if (steps >= cap) break;
        /* aligned state */
        if (N < MAXN32) {
            u64 key = state_key(N, v), cd;
            if (use_cert && ctab_find(key, &cd)) {
                D = cd; certN = N; certv = v; rc = 2;
                goto done;
            }
            col_push(&col, N, v);
        }
        if (steps >= next_prog) {
            fprintf(stderr, "[deep n=%llu] N=%llu v=%llu steps=%llu "
                    "rate=%.0f/s\n",
                    (unsigned long long)n, (unsigned long long)N,
                    (unsigned long long)v, (unsigned long long)steps,
                    steps / (now_sec() - t0 + 1e-9));
            fflush(stderr);
            next_prog += 1ULL << 30;
        }
        if (steps >= next_ckpt) {
            ckpt_save(n, cap, N, v, steps, &col);
            next_ckpt += 1ULL << 28;
        }
    }
done:;
    double el = now_sec() - t0;
    u64 lasttake = 0;
    if (rc == 1) {                          /* direct death: sanity gates */
        if (n >= 1) {
            if ((D & 1) == 0) {
                fprintf(stderr, "FATAL: even death modulus %llu (n=%llu)\n",
                        (unsigned long long)D, (unsigned long long)n);
                exit(3);
            }
            if (D <= n) {
                fprintf(stderr, "FATAL: D=%llu <= n=%llu\n",
                        (unsigned long long)D, (unsigned long long)n);
                exit(3);
            }
        }
        lasttake = D - 1;
        if (do_emit && (steps >= emitmin || emitmin == 0)) {
            for (u64 i = 0; i < col.n; i++)
                cert_emit(col.N[i], col.v[i], D);
        }
    } else if (rc == 2) {
        /* certified by coalescence: the pre-hit states share the same death */
        if (do_emit)
            for (u64 i = 0; i < col.n; i++)
                cert_emit(col.N[i], col.v[i], D);
        lasttake = D - 1;
    }
    if (rc) remove(ckpt_path);
    *Dout = D; *steps_out = steps; *lasttake_out = lasttake;
    if (certN_out) *certN_out = certN;
    if (certv_out) *certv_out = certv;
    if (Nfin) *Nfin = (rc == 1) ? D : ((rc == 2) ? certN : N);
    if (vfin) *vfin = (rc == 1) ? 0 : ((rc == 2) ? certv : v);
    if (!quiet) {
        if (rc == 1)
            fprintf(stderr, "[deep n=%llu] DEAD D=%llu last_take=%llu "
                    "steps=%llu room=%llu elapsed=%.2fs rate=%.0f/s\n",
                    (unsigned long long)n, (unsigned long long)D,
                    (unsigned long long)lasttake, (unsigned long long)steps,
                    (unsigned long long)(n >= 2 ? D - 1 - n : D - 2),
                    el, el > 0 ? steps / el : 0.0);
        else if (rc == 2)
            fprintf(stderr, "[deep n=%llu] CERTIFIED at state (%llu,%llu) "
                    "D=%llu steps=%llu elapsed=%.2fs\n",
                    (unsigned long long)n, (unsigned long long)certN,
                    (unsigned long long)certv, (unsigned long long)D,
                    (unsigned long long)steps, el);
        else
            fprintf(stderr, "[deep n=%llu] UNRESOLVED at cap N=%llu v=%llu "
                    "steps=%llu elapsed=%.2fs\n",
                    (unsigned long long)n, (unsigned long long)N,
                    (unsigned long long)v, (unsigned long long)steps, el);
    }
    free(col.N); free(col.v);
    return rc;
}

static int cmd_deep(u64 n, u64 cap, u64 bits, const char *certfile,
                    u64 emitmin) {
    int use_cert = strcmp(certfile, "-") != 0;
    if (use_cert) {
        ctab_init(21);
        u64 loaded = cert_load_file(certfile);
        fprintf(stderr, "[deep] cert table: %llu entries loaded from %s\n",
                (unsigned long long)loaded, certfile);
        cert_out_open(certfile);
    }
    u64 D = 0, steps = 0, lt = 0, cN = 0, cv = 0, Nf = 0, vf = 0;
    int rc = deep_walk(n, cap, bits, use_cert, use_cert, emitmin,
                       &D, &steps, &lt, &cN, &cv, &Nf, &vf, 0);
    if (rc == 1)
        printf("RESULT n=%llu DEAD D=%llu last_take=%llu steps=%llu "
               "room=%llu mode=direct\n",
               (unsigned long long)n, (unsigned long long)D,
               (unsigned long long)lt, (unsigned long long)steps,
               (unsigned long long)(n >= 2 ? D - 1 - n : D - 2));
    else if (rc == 2)
        printf("RESULT n=%llu CERTIFIED D=%llu via_state=(%llu,%llu) "
               "steps=%llu mode=cert\n",
               (unsigned long long)n, (unsigned long long)D,
               (unsigned long long)cN, (unsigned long long)cv,
               (unsigned long long)steps);
    else
        printf("RESULT n=%llu UNRESOLVED cap=%llu state_N=%llu v=%llu "
               "steps=%llu mode=none\n",
               (unsigned long long)n, (unsigned long long)cap,
               (unsigned long long)Nf, (unsigned long long)vf,
               (unsigned long long)steps);
    if (certf_out) { fflush(certf_out); fclose(certf_out); }
    return rc == 0 ? 1 : 0;
}

static int cmd_deepmany(const char *nlist, u64 cap, u64 bits,
                        const char *certin, const char *certout,
                        const char *outfile, u64 emitmin) {
    FILE *f = fopen(nlist, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", nlist); return 2; }
    static u64 ns[1000000];
    u64 c = 0;
    char line[256];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        ns[c++] = strtoull(line, NULL, 10);
        if (c >= 1000000) break;
    }
    fclose(f);
    ctab_init(21);
    int use_cert = strcmp(certin, "-") != 0;
    u64 loaded = use_cert ? cert_load_file(certin) : 0;
    cert_out_open(certout);
    FILE *of = fopen(outfile, "a");
    if (!of) fatal("cannot open deepmany outfile");
    setvbuf(of, NULL, _IOFBF, 1 << 18);
    printf("[deepmany] %llu walks, cap=%llu, bits=%llu, certs loaded=%llu\n",
           (unsigned long long)c, (unsigned long long)cap,
           (unsigned long long)bits, (unsigned long long)loaded);
    u64 ndead = 0, ncert = 0, nunres = 0;
    double t0 = now_sec();
    for (u64 k = 0; k < c; k++) {
        u64 D = 0, steps = 0, lt = 0, cN = 0, cv = 0, Nf = 0, vf = 0;
        int rc = deep_walk(ns[k], cap, bits, 1 /*probe*/, 1 /*emit*/,
                           emitmin, &D, &steps, &lt, &cN, &cv, &Nf, &vf, 1);
        if (rc == 1) {
            ndead++;
            fprintf(of, "%llu %llu %llu direct %llu\n",
                    (unsigned long long)ns[k], (unsigned long long)D,
                    (unsigned long long)steps, (unsigned long long)lt);
            printf("WALK n=%llu DEAD D=%llu steps=%llu "
                   "(%.2fs, %llu/%llu done)\n",
                   (unsigned long long)ns[k], (unsigned long long)D,
                   (unsigned long long)steps, now_sec() - t0,
                   (unsigned long long)(k + 1), (unsigned long long)c);
        } else if (rc == 2) {
            ncert++;
            fprintf(of, "%llu %llu %llu cert %llu\n",
                    (unsigned long long)ns[k], (unsigned long long)D,
                    (unsigned long long)steps,
                    (unsigned long long)cN);
            printf("WALK n=%llu CERTIFIED D=%llu via N=%llu steps=%llu "
                   "(%.2fs, %llu/%llu done)\n",
                   (unsigned long long)ns[k], (unsigned long long)D,
                   (unsigned long long)cN, (unsigned long long)steps,
                   now_sec() - t0, (unsigned long long)(k + 1),
                   (unsigned long long)c);
        } else {
            nunres++;
            fprintf(of, "%llu 0 %llu unres %llu %llu\n",
                    (unsigned long long)ns[k], (unsigned long long)steps,
                    (unsigned long long)Nf, (unsigned long long)vf);
            printf("WALK n=%llu UNRESOLVED at cap N=%llu v=%llu "
                   "(%.2fs, %llu/%llu done)\n",
                   (unsigned long long)ns[k], (unsigned long long)Nf,
                   (unsigned long long)vf, now_sec() - t0,
                   (unsigned long long)(k + 1), (unsigned long long)c);
        }
        fflush(of); fflush(stdout);
        if (certf_out) fflush(certf_out);
    }
    printf("[deepmany DONE] dead=%llu cert=%llu unres=%llu elapsed=%.1fs\n",
           (unsigned long long)ndead, (unsigned long long)ncert,
           (unsigned long long)nunres, now_sec() - t0);
    fclose(of);
    if (certf_out) { fflush(certf_out); fclose(certf_out); }
    return nunres ? 1 : 0;
}

/* ===================== mode: sweep (direct baseline) ==================== */
static int cmd_sweep(u64 lo, u64 hi, u64 cap, const char *outfile) {
    FILE *of = outfile ? fopen(outfile, "a") : stdout;
    if (!of) fatal("cannot open sweep outfile");
    if (of != stdout) setvbuf(of, NULL, _IOFBF, 1 << 18);
    u64 total = 0, nunres = 0, worst = 0, worstn = 0;
    double t0 = now_sec();
    for (u64 n = lo; n <= hi; n++) {
        u64 N, v, steps = 0;
        start_state(n, &N, &v);
        int died = (v == 0);
        u64 D = died ? N : 0;
        while (!died && steps < cap) {
            u64 want = cap - steps < (1ULL << 20) ? cap - steps : (1ULL << 20);
            u64 used;
            if (step_block(&N, &v, want, &used)) { died = 1; D = N; }
            steps += used;
            if (died) break;
        }
        fprintf(of, "%llu %llu %llu\n", (unsigned long long)n,
                (unsigned long long)D, (unsigned long long)steps);
        if (!died) { nunres++; if (nunres <= 20)
            printf("UNRESOLVED n=%llu at N=%llu v=%llu\n",
                   (unsigned long long)n, (unsigned long long)N,
                   (unsigned long long)v);
        }
        else { total += steps; if (steps > worst) { worst = steps; worstn = n; } }
        if ((n - lo) % 100000 == 99999 || n == hi) {
            printf("[sweep %llu..%llu] n=%llu done, unres=%llu, "
                   "elapsed=%.1fs rate=%.0f/s\n",
                   (unsigned long long)lo, (unsigned long long)hi,
                   (unsigned long long)n, (unsigned long long)nunres,
                   now_sec() - t0,
                   (now_sec() - t0) > 0 ? total / (now_sec() - t0) : 0.0);
            fflush(stdout);
        }
    }
    printf("[sweep DONE %llu..%llu] unresolved=%llu worst_steps=%llu (n=%llu) "
           "total_steps=%llu elapsed=%.1fs\n",
           (unsigned long long)lo, (unsigned long long)hi,
           (unsigned long long)nunres, (unsigned long long)worst,
           (unsigned long long)worstn, (unsigned long long)total,
           now_sec() - t0);
    if (of != stdout) fclose(of);
    return nunres ? 1 : 0;
}

/* ===================== mode: batch ====================================== */
static u64 g_bits = 20;

/* march walker i until total steps reach stop (or death/merge/cert).
 * returns 0 active, 1 direct death, 2 certified dead (cert or dead class),
 * 3 merged. */
static int march(u32 i, u64 stop) {
    u64 N = wN[i], v = wv[i], st = wsteps[i];
    u64 AM = (1ULL << g_bits) - 1;
    u32 o = 0;

    if (v == 0) {                           /* degenerate start (n = 0) */
        wst[i] = ST_DEAD; wD[i] = N; wmode[i] = 'd';
        log_death_class(i, N);
        return 1;
    }
    /* probe current state (insert only on the first-ever march of i) */
    if (N < MAXN32) {
        u64 key = state_key(N, v), cd;
        if (ctab_find(key, &cd)) {
            wN[i] = N; wv[i] = v; wsteps[i] = st;
            wst[i] = ST_DEAD; wD[i] = cd; wmode[i] = 'c';
            log_death_class(i, cd);
            return 2;
        }
        if (wtab_find(key, &o)) {
            u32 r = uf_find(o);
            if (r == i) fatal("self-hit in walker table (engine bug)");
            if (wst[r] == ST_DEAD) {
                wN[i] = N; wv[i] = v; wsteps[i] = st;
                wst[i] = ST_DEAD; wD[i] = wD[r]; wmode[i] = 'w';
                log_death_class(i, wD[r]);
                return 2;
            }
            goto merge;
        } else if (st == 0) {
            wtab_ins(key, i);
        }
    }
    {
        u64 diedD = 0;
        while (st < stop) {
            u64 nextA = ((N | AM) + 1) & ~AM;      /* next aligned N > N */
            u64 lim = st + (nextA - N);
            if (lim > stop) lim = stop;
            u64 used;
            if (step_block(&N, &v, lim - st, &used)) {
                st += used; diedD = N;
                break;
            }
            st = lim;
            if (st == stop) break;
            /* N == nextA: aligned state — probe cert, then walkers */
            if (N < MAXN32) {
                u64 key = state_key(N, v), cd;
                if (ctab_find(key, &cd)) {
                    wN[i] = N; wv[i] = v; wsteps[i] = st;
                    wst[i] = ST_DEAD; wD[i] = cd; wmode[i] = 'c';
                    log_death_class(i, cd);
                    return 2;
                }
                if (wtab_find(key, &o)) {
                    u32 r = uf_find(o);
                    if (r == i) fatal("self-hit2 in walker table (engine bug)");
                    if (wst[r] == ST_DEAD) {
                        wN[i] = N; wv[i] = v; wsteps[i] = st;
                        wst[i] = ST_DEAD; wD[i] = wD[r]; wmode[i] = 'w';
                        log_death_class(i, wD[r]);
                        return 2;
                    }
                    goto merge;
                }
                wtab_ins(key, i);
            }
        }
        if (diedD == 0) {                    /* budget exhausted: still alive */
            wN[i] = N; wv[i] = v; wsteps[i] = st;
            return 0;
        }
        if ((diedD & 1) == 0) fatal("even death modulus (parity lemma)");
        wN[i] = diedD; wv[i] = 0; wsteps[i] = st;
        wst[i] = ST_DEAD; wD[i] = diedD; wmode[i] = 'd';
        log_death_class(i, diedD);
        return 1;
    }
merge:;
    u32 r = uf_find(o);
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

static const char SNAP_MAGIC2[8] = "WAR261B2";
static void snapshot_save(const char *path, u64 lo, u64 hi, u64 clo, u64 chi,
                          u64 round, u64 budget, u64 cap) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb");
    if (!f) { fprintf(stderr, "WARN: cannot write snapshot %s\n", tmp); return; }
    fwrite(SNAP_MAGIC2, 8, 1, f);
    u64 hdr[8] = { lo, hi, clo, chi, round, budget, cap, WC };
    fwrite(hdr, 8, 8, f);
    fwrite(wst, 1, WC, f);
    fwrite(wlog, 1, WC, f);
    fwrite(wmode, 1, WC, f);
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
static int snapshot_load(const char *path, u64 lo, u64 hi, u64 *clo, u64 *chi,
                         u64 *round, u64 *budget, u64 cap) {
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    char magic[8];
    if (fread(magic, 8, 1, f) != 1 || memcmp(magic, SNAP_MAGIC2, 8) != 0) {
        fprintf(stderr, "WARN: bad snapshot magic, ignoring\n"); fclose(f); return 0;
    }
    u64 hdr[8];
    if (fread(hdr, 8, 8, f) != 8) { fclose(f); return 0; }
    if (hdr[0] != lo || hdr[1] != hi || hdr[7] == 0) {
        fprintf(stderr, "WARN: snapshot range mismatch, ignoring\n"); fclose(f); return 0;
    }
    if (hdr[7] > (u64)2000000) { fclose(f); return 0; }
    walkers_alloc(hdr[7]);
    if (fread(wst, 1, WC, f) != WC || fread(wlog, 1, WC, f) != WC ||
        fread(wmode, 1, WC, f) != WC ||
        fread(wpar, 4, WC, f) != WC || fread(whead, 4, WC, f) != WC ||
        fread(wtail, 4, WC, f) != WC || fread(wnext, 4, WC, f) != WC ||
        fread(wN, 8, WC, f) != WC || fread(wv, 8, WC, f) != WC ||
        fread(wsteps, 8, WC, f) != WC || fread(wD, 8, WC, f) != WC ||
        fread(wn, 8, WC, f) != WC) {
        fprintf(stderr, "WARN: snapshot truncated, ignoring\n");
        fclose(f); return 0;
    }
    *clo = hdr[2]; *chi = hdr[3]; *round = hdr[4];
    *budget = hdr[5] < cap ? hdr[5] : cap;
    fclose(f);
    return 1;
}

static int cmd_batch(u64 lo, u64 hi, u64 cap, u64 round0, u64 mult,
                     u64 bits, u64 tbits, u64 chunk, u64 emitmin,
                     const char *deaths, const char *merges,
                     const char *snap, const char *certin,
                     const char *certout) {
    if (round0 == 0 || mult < 2) { fprintf(stderr, "bad round0/mult\n"); return 2; }
    if (bits == 0 || bits > 40) { fprintf(stderr, "bad bits\n"); return 2; }
    if (hi < lo) { fprintf(stderr, "hi < lo\n"); return 2; }
    if (chunk == 0) chunk = hi - lo + 1;
    if (chunk > 2000000) { fprintf(stderr, "chunk too large\n"); return 2; }
    g_bits = bits;

    wtab_init(tbits);
    ctab_init(21);
    df = fopen(deaths, "a");
    mf = fopen(merges, "a");
    if (!df) fatal("cannot open deaths file");
    if (!mf) mf = fopen("/dev/null", "a");
    setvbuf(df, NULL, _IOFBF, 1 << 20);
    setvbuf(mf, NULL, _IOFBF, 1 << 20);
    int use_certin = strcmp(certin, "-") != 0;
    int use_certout = strcmp(certout, "-") != 0;
    if (use_certout) cert_out_open(certout);

    u64 total_steps = 0, rewalk_steps = 0, rewalk_budget = 20000000000ULL;
    u64 ndead_d = 0, ndead_c = 0, ndead_w = 0, nunres = 0, nalias = 0;
    double t_start = now_sec();

    u64 clo = lo, chi, round = 0, budget = round0;
    int resumed = snapshot_load(snap, lo, hi, &clo, &chi, &round, &budget, cap);
    if (resumed && WC != hi - lo + 1) {
        fprintf(stderr, "WARN: snapshot walker count mismatch, ignoring\n");
        resumed = 0;
    }
    if (!resumed) {
        clo = lo; round = 0; budget = round0;
        walkers_alloc(hi - lo + 1);
        for (u64 i = 0; i < WC; i++) {
            u64 N, v;
            start_state(lo + i, &N, &v);
            wN[i] = N; wv[i] = v; wsteps[i] = 0; wD[i] = 0; wn[i] = lo + i;
            wpar[i] = (u32)i; whead[i] = (u32)i; wtail[i] = (u32)i;
            wnext[i] = NONE32; wst[i] = ST_ACTIVE; wlog[i] = 0; wmode[i] = 0;
        }
    }

    for (; clo <= hi; clo = chi + 1) {
        chi = (hi - clo < chunk) ? hi : clo + chunk - 1;
        u32 i0 = (u32)(clo - lo), i1 = (u32)(chi - lo);
        /* reload certs from disk at every chunk boundary (cross-run growth) */
        if (use_certin && clo != lo) {
            u64 lded = cert_load_file(certin);
            printf("[chunk %llu..%llu] cert reload: +%llu entries "
                   "(table %llu)\n", (unsigned long long)clo,
                   (unsigned long long)chi, (unsigned long long)lded,
                   (unsigned long long)CT.used);
        }
        for (;; round++) {
            u64 stop = budget < cap ? budget : cap;
            u64 rsteps = 0;
            double t0 = now_sec();
            for (u64 i = i0; i <= i1; i++) {
                if (wst[i] != ST_ACTIVE) continue;
                if (wsteps[i] >= stop) continue;
                u64 before = wsteps[i];
                int rc = march((u32)i, stop);
                u64 d = wsteps[i] - before;
                total_steps += d; rsteps += d;
                if (rc == 1) {
                    ndead_d++;
                    /* deep direct death => new trunk: persist its certs */
                    if (use_certout && wsteps[i] >= emitmin &&
                        rewalk_steps < rewalk_budget) {
                        u64 rs = 0;
                        emit_walk_certs(wn[i], wD[i], bits, &rs);
                        rewalk_steps += rs;
                        if (certf_out) fflush(certf_out);
                    }
                }
                else if (rc == 2) {
                    if (wmode[i] == 'c') ndead_c++;
                    else ndead_w++;
                }
                else if (rc == 3) nalias++;
            }
            fflush(df); fflush(mf);
            if (certf_out) fflush(certf_out);
            u64 nact = 0;
            for (u64 i = i0; i <= i1; i++) if (wst[i] == ST_ACTIVE) nact++;
            printf("[n=%llu..%llu round=%llu] budget=%llu active=%llu "
                   "dead(d/c/w)=%llu/%llu/%llu alias=%llu round_steps=%llu "
                   "total=%llu rate=%.0f/s elapsed=%.1fs tab=%llu%s\n",
                   (unsigned long long)clo, (unsigned long long)chi,
                   (unsigned long long)round, (unsigned long long)stop,
                   (unsigned long long)nact,
                   (unsigned long long)ndead_d, (unsigned long long)ndead_c,
                   (unsigned long long)ndead_w, (unsigned long long)nalias,
                   (unsigned long long)rsteps, (unsigned long long)total_steps,
                   rsteps / (now_sec() - t0 + 1e-9), now_sec() - t_start,
                   (unsigned long long)WT.used,
                   WT.full ? " FULL" : "");
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
        for (u64 i = i0; i <= i1; i++)
            if (wst[i] == ST_ACTIVE) wst[i] = ST_UNRES;
        for (u64 i = i0; i <= i1; i++) {
            u32 r = uf_find((u32)i);
            if (wst[r] == ST_DEAD) {
                if (!wlog[i]) log_death_class(r, wD[r]);   /* safety net */
            } else if (wst[r] == ST_UNRES) {
                if (!wlog[i]) {
                    fprintf(df, "%llu 0 %llu %llu %llu\n",
                            (unsigned long long)wn[i],
                            (unsigned long long)wN[r],
                            (unsigned long long)wv[r],
                            (unsigned long long)wsteps[r]);
                    wlog[i] = 1; nunres++;
                }
            }
        }
        fflush(df);
        printf("[chunk %llu..%llu COMPLETE] dead d/c/w=%llu/%llu/%llu "
               "alias=%llu unres=%llu total_steps=%llu elapsed=%.1fs\n",
               (unsigned long long)clo, (unsigned long long)chi,
               (unsigned long long)ndead_d, (unsigned long long)ndead_c,
               (unsigned long long)ndead_w, (unsigned long long)nalias,
               (unsigned long long)nunres, (unsigned long long)total_steps,
               now_sec() - t_start);
        fflush(stdout);
        round = 0; budget = round0;
    }
    /* every walker must be logged exactly once */
    u64 unlogged = 0;
    for (u64 i = 0; i < WC; i++) if (!wlog[i]) unlogged++;
    printf("[ALL DONE %llu..%llu] logged d/c/w=%llu/%llu/%llu (incl. class "
           "members) alias_events=%llu unres=%llu unlogged=%llu "
           "total_steps=%llu rewalk=%llu elapsed=%.1fs tab=%llu cert=%llu\n",
           (unsigned long long)lo, (unsigned long long)hi,
           (unsigned long long)g_cnt_d, (unsigned long long)g_cnt_c,
           (unsigned long long)g_cnt_w, (unsigned long long)nalias,
           (unsigned long long)nunres, (unsigned long long)unlogged,
           (unsigned long long)total_steps, (unsigned long long)rewalk_steps,
           now_sec() - t_start, (unsigned long long)WT.used,
           (unsigned long long)CT.used);
    if (unlogged) fatal("unlogged walkers remain (engine bug)");
    fclose(df); fclose(mf);
    if (certf_out) { fflush(certf_out); fclose(certf_out); }
    return nunres ? 1 : 0;
}

/* ===================== mode: funnels (head enumerator) ================== */
typedef struct { u64 D, cnt, nmin, nmax; } Head;
static int head_cmp(const void *a, const void *b) {
    const Head *x = (const Head *)a, *y = (const Head *)b;
    if (x->cnt != y->cnt) return x->cnt < y->cnt ? 1 : -1;
    return x->D < y->D ? -1 : (x->D > y->D ? 1 : 0);
}
static int cmd_funnels(const char *path, u64 minD, u64 maxD) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", path); return 2; }
    u64 cap = 1 << 20;
    Head *H = (Head *)malloc(cap * sizeof(Head));
    if (!H) fatal("funnels OOM");
    u64 total = 0, outfilt = 0, unres = 0;
    char line[256];
    while (fgets(line, sizeof line, f)) {
        unsigned long long a, b;
        if (sscanf(line, "%llu %llu", &a, &b) != 2) continue;
        u64 nn = a, D = b;
        if (D == 0) { unres++; continue; }
        if (D < minD || D > maxD) { outfilt++; continue; }
        /* linear merge is O(n*heads) — use a tiny hash for speed */
        u64 h = mix64(D) & (cap - 1);
        while (H[h].cnt && H[h].D != D) h = (h + 1) & (cap - 1);
        if (!H[h].cnt) { H[h].D = D; H[h].cnt = 0; H[h].nmin = nn; H[h].nmax = nn; }
        H[h].cnt++;
        if (nn < H[h].nmin) H[h].nmin = nn;
        if (nn > H[h].nmax) H[h].nmax = nn;
        total++;
    }
    fclose(f);
    u64 nh = 0;
    for (u64 i = 0; i < cap; i++) if (H[i].cnt) H[nh++] = H[i];
    qsort(H, nh, sizeof(Head), head_cmp);
    printf("FUNNEL HEAD HIERARCHY: %s (heads with D in [%llu,%llu])\n",
           path, (unsigned long long)minD, (unsigned long long)maxD);
    printf("walks_in_filter=%llu walks_outside_filter=%llu unresolved=%llu "
           "distinct_heads=%llu\n",
           (unsigned long long)total, (unsigned long long)outfilt,
           (unsigned long long)unres, (unsigned long long)nh);
    printf("%-22s %10s %14s %14s\n", "death_modulus_D", "walks", "n_min", "n_max");
    for (u64 i = 0; i < nh; i++)
        printf("%-22llu %10llu %14llu %14llu\n",
               (unsigned long long)H[i].D, (unsigned long long)H[i].cnt,
               (unsigned long long)H[i].nmin, (unsigned long long)H[i].nmax);
    free(H);
    return 0;
}

/* ============================== main ==================================== */
int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr,
            "usage: war261b sweep <lo> <hi> <cap> [outfile]\n"
            "       war261b deep <n> <cap> <bits> <certfile|-> <emitmin>\n"
            "       war261b deepmany <nlist> <cap> <bits> <certin|-> "
            "<certout|-> <outfile> <emitmin>\n"
            "       war261b batch <lo> <hi> <cap> <round0> <mult> <bits> "
            "<tbits> <chunk> <emitmin> <deaths> <merges> <snap> "
            "<certin|-> <certout|->\n"
            "       war261b funnels <deathsfile> [minD [maxD]]\n");
        return 2;
    }
    if (!strcmp(argv[1], "sweep"))
        return cmd_sweep(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10),
                         strtoull(argv[4], 0, 10),
                         argc > 5 ? argv[5] : NULL);
    if (!strcmp(argv[1], "deep")) {
        if (argc < 7) { fprintf(stderr, "deep needs 5 args\n"); return 2; }
        return cmd_deep(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10),
                        strtoull(argv[4], 0, 10), argv[5],
                        strtoull(argv[6], 0, 10));
    }
    if (!strcmp(argv[1], "deepmany")) {
        if (argc < 9) { fprintf(stderr, "deepmany needs 7 args\n"); return 2; }
        return cmd_deepmany(argv[2], strtoull(argv[3], 0, 10),
                            strtoull(argv[4], 0, 10), argv[5], argv[6],
                            argv[7], strtoull(argv[8], 0, 10));
    }
    if (!strcmp(argv[1], "batch")) {
        if (argc < 16) { fprintf(stderr, "batch needs 14 args\n"); return 2; }
        return cmd_batch(strtoull(argv[2], 0, 10), strtoull(argv[3], 0, 10),
                         strtoull(argv[4], 0, 10), strtoull(argv[5], 0, 10),
                         strtoull(argv[6], 0, 10), strtoull(argv[7], 0, 10),
                         strtoull(argv[8], 0, 10), strtoull(argv[9], 0, 10),
                         strtoull(argv[10], 0, 10), argv[11], argv[12],
                         argv[13], argv[14], argv[15]);
    }
    if (!strcmp(argv[1], "funnels")) {
        u64 minD = 1, maxD = ~0ULL;
        if (argc > 3) minD = strtoull(argv[3], 0, 10);
        if (argc > 4) maxD = strtoull(argv[4], 0, 10);
        return cmd_funnels(argv[2], minD, maxD);
    }
    fprintf(stderr, "unknown mode %s\n", argv[1]);
    return 2;
}
