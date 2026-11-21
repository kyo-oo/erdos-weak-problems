/*
 * engine107f9.c — W81-107A — THE f(5)=9 C PORT — Erdos #107 (happy ending).
 *
 * Faithful C port of the W76/W77 python v2 order-type machinery
 * (engine107f5v2.py + engine107f5.py core), for the n=9 grind:
 *
 *   per parent type S (n points, chi, exact-rational realization):
 *     S1 CELLS      all cells of the pair-line arrangement (exact slab
 *                   sampling; per-parent cell count checked against the
 *                   line-arrangement formula
 *                   1 + C(n,2) + n(n-2) + C(C(n,2),2) - n*C(n-1,2)
 *                   e.g. 287 at n=8 parents, 162 at n=7).
 *     S2 WALL SWEEP every concurrency wall (3-matchings of K_n) and every
 *                   parallel wall (disjoint pair-pairs), both sides,
 *                   exact-rational locus intervals, chi-cell filtering,
 *                   4 nudges, centroid / far-column grabs.
 *     S3 CELL WALK  random in-cell single-point moves; cells of every
 *                   visited configuration grabbed.
 *     CANON         canonical form (WL-bucketed relabeling min) — the
 *                   same algorithm as python canonical_key.
 *
 * Every emitted child carries an exact-rational REALIZATION (the
 * realizability filter — no junk can enter) and passes the internal
 * self-check chi_of_points(coords) == chi.  Completeness is certified
 * externally by the classical count anchors (1,2,3,16,135,3315,158817)
 * + mirror closure (the python certification layer; the validation
 * ladder re-enumerates n=4..8 with SET EQUALITY against the bank).
 *
 * All arithmetic exact (GMP mpz/mpq).  Zero floats.
 *
 * Build:  gcc -O2 -lgmp -lm engine107f9.c -o engine107f9
 *
 * I/O (batch on stdin, results on stdout):
 *   in:   "P <parentkey-hex> <n> <chi-hex>" then n lines "x y" (rationals
 *         "a/b" or "a").  Multiple parents per batch.
 *   out:  per parent: one "#P ..." stats line, then per emitted distinct
 *         canonical child one line
 *         "T <ck-hex> <chi-hex> <x0> <y0> ... <x8> <y8>"  (n+1 points),
 *         or "#E <key> GENERIC-FAIL" when no generic realization found.
 *         Assertion failures abort (exit 1) — they must never happen.
 *
 * Sign packing (shared with the python driver): a chirotope of length L
 * (values -1/+1) packs bit i = (sign_i > 0); hex, little-endian nibbles,
 * zero-padded to ceil(L/4) digits.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <gmp.h>

#define MAXN 10          /* parents n<=8, children n+1<=9 */
#define MAXTRI 84        /* C(9,3) */
#define MAXPAIR 28       /* C(8,2) */
#define MAXLINES MAXPAIR

/* ------------------------------------------------------------------ */
/* RNG (splitmix64; deterministic per parent; exploration only — the   */
/* machinery's completeness is certified by the anchors, not by the    */
/* random stream; the validation ladder checks set equality)          */
/* ------------------------------------------------------------------ */
static uint64_t rng_state;
static uint64_t rng_next(void) {
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rng_below(int k) {
    if (k <= 1) return 0;
    uint64_t thresh = UINT64_MAX - (UINT64_MAX % (uint64_t)k);
    uint64_t r;
    do { r = rng_next(); } while (r >= thresh);
    return (int)(r % (uint64_t)k);
}
static int rng_randint(int a, int b) { return a + rng_below(b - a + 1); }

/* ------------------------------------------------------------------ */
/* scratch (single-threaded; allocated once — no per-op allocation)    */
/* ------------------------------------------------------------------ */
static mpz_t zT1, zT2, zT3, zT4, zNbx, zNcy, zNby, zNcx, zA1, zA2, zD;
static mpq_t qT1, qT2, qT3, qT4, qT5;

static void scratch_init(void) {
    mpz_inits(zT1, zT2, zT3, zT4, zNbx, zNcy, zNby, zNcx, zA1, zA2, zD, NULL);
    mpq_inits(qT1, qT2, qT3, qT4, qT5, NULL);
}

/* ------------------------------------------------------------------ */
/* points and lines                                                    */
/* ------------------------------------------------------------------ */
typedef struct { mpq_t x, y; } PT;


/* GMP TRAP: mpq_set_si does NOT reduce common factors, and mpq_equal is a
 * RAW field compare — non-canonical rationals make mpq_equal lie (e.g.
 * 30/16 "!=" 15/8) and no-op arithmetic (+0, *1) does not canonicalize.
 * Every set_si in this engine therefore goes through the canonicalizing
 * wrapper.  (Found by the W81-107A validation ladder: SIGFPE at n=6->7.) */
static void qset_si(mpq_t q, long n, long d) {
    mpq_set_si(q, n, d);
    mpq_canonicalize(q);
}

static void pt_init(PT *p) { mpq_init(p->x); mpq_init(p->y); }
static void pt_set(PT *d, const PT *s) { mpq_set(d->x, s->x); mpq_set(d->y, s->y); }
static void pt_clear(PT *p) { mpq_clear(p->x); mpq_clear(p->y); }

/* sign of orient(a,b,c) = (bx-ax)(cy-ay) - (by-ay)(cx-ax), exact,
 * integer cross-multiplication (no gcds — signs only).               */
static int orient_sign(PT *a, PT *b, PT *c) {
    mpz_ptr axn = mpq_numref(a->x), axd = mpq_denref(a->x);
    mpz_ptr ayn = mpq_numref(a->y), ayd = mpq_denref(a->y);
    mpz_ptr bxn = mpq_numref(b->x), bxd = mpq_denref(b->x);
    mpz_ptr byn = mpq_numref(b->y), byd = mpq_denref(b->y);
    mpz_ptr cxn = mpq_numref(c->x), cxd = mpq_denref(c->x);
    mpz_ptr cyn = mpq_numref(c->y), cyd = mpq_denref(c->y);
    mpz_mul(zT1, bxn, axd); mpz_mul(zT2, axn, bxd); mpz_sub(zNbx, zT1, zT2);
    mpz_mul(zT1, cyn, ayd); mpz_mul(zT2, ayn, cyd); mpz_sub(zNcy, zT1, zT2);
    mpz_mul(zT1, byn, ayd); mpz_mul(zT2, ayn, byd); mpz_sub(zNby, zT1, zT2);
    mpz_mul(zT1, cxn, axd); mpz_mul(zT2, axn, cxd); mpz_sub(zNcx, zT1, zT2);
    /* sign(Nbx*Ncy*byd*cxd - Nby*Ncx*bxdcyd) over common positive den */
    mpz_mul(zT1, zNbx, zNcy); mpz_mul(zT2, byd, cxd); mpz_mul(zA1, zT1, zT2);
    mpz_mul(zT1, zNby, zNcx); mpz_mul(zT2, bxd, cyd); mpz_mul(zA2, zT1, zT2);
    mpz_sub(zD, zA1, zA2);
    return mpz_sgn(zD);
}

/* line A x + B y = C through two points — exactly python pair_lines_of */
typedef struct { mpq_t A, B, C; } LN;

static void ln_from_points(LN *l, const PT *p, const PT *q) {
    mpq_sub(l->A, q->y, p->y);          /* A = yj - yi */
    mpq_sub(l->B, p->x, q->x);          /* B = xi - xj */
    mpq_mul(qT1, l->A, p->x);
    mpq_mul(qT2, l->B, p->y);
    mpq_add(l->C, qT1, qT2);
}

/* sign of A*px + B*py - C for point p, integer cross-multiplication. */
static int line_sign(LN *l, PT *p) {
    mpz_ptr An = mpq_numref(l->A), Ad = mpq_denref(l->A);
    mpz_ptr Bn = mpq_numref(l->B), Bd = mpq_denref(l->B);
    mpz_ptr Cn = mpq_numref(l->C), Cd = mpq_denref(l->C);
    mpz_ptr xn = mpq_numref(p->x), xd = mpq_denref(p->x);
    mpz_ptr yn = mpq_numref(p->y), yd = mpq_denref(p->y);
    /* An*xn*Bd*yd*Cd + Bn*yn*Ad*xd*Cd - Cn*Ad*xd*Bd*yd over common den */
    mpz_mul(zT1, An, xn); mpz_mul(zT2, Bd, yd); mpz_mul(zT3, Cd, zT2);
    mpz_mul(zA1, zT1, zT3);
    mpz_mul(zT1, Bn, yn); mpz_mul(zT2, Ad, xd); mpz_mul(zT3, Cd, zT2);
    mpz_mul(zT4, zT1, zT3); mpz_add(zA1, zA1, zT4);
    mpz_mul(zT1, Ad, xd); mpz_mul(zT2, Bd, yd); mpz_mul(zT3, Cn, zT1);
    mpz_mul(zT4, zT3, zT2); mpz_sub(zD, zA1, zT4);
    return mpz_sgn(zD);
}

/* parallel test: A1*B2 - A2*B1 == 0 ? (integer trick) */
static int lines_parallel(LN *l1, LN *l2) {
    mpz_ptr An1 = mpq_numref(l1->A), Ad1 = mpq_denref(l1->A);
    mpz_ptr Bn1 = mpq_numref(l1->B), Bd1 = mpq_denref(l1->B);
    mpz_ptr An2 = mpq_numref(l2->A), Ad2 = mpq_denref(l2->A);
    mpz_ptr Bn2 = mpq_numref(l2->B), Bd2 = mpq_denref(l2->B);
    mpz_mul(zT1, An1, Bn2); mpz_mul(zT2, Ad2, Bd1); mpz_mul(zT3, zT1, zT2);
    mpz_set(zA1, zT3);
    mpz_mul(zT1, An2, Bn1); mpz_mul(zT2, Ad1, Bd2); mpz_mul(zT3, zT1, zT2);
    mpz_sub(zD, zA1, zT3);
    return mpz_sgn(zD) == 0;
}

/* intersection of two non-parallel lines (mpq values). 0 if parallel.
 * px = (C1*B2 - C2*B1)/den, py = (A1*C2 - A2*C1)/den, den = A1*B2-A2*B1 */
static int line_isect(const LN *l1, const LN *l2, mpq_t px, mpq_t py) {
    mpq_mul(qT1, l1->A, l2->B);
    mpq_mul(qT2, l2->A, l1->B);
    mpq_sub(qT3, qT1, qT2);
    if (mpq_sgn(qT3) == 0) return 0;
    mpq_mul(qT1, l1->C, l2->B);
    mpq_mul(qT2, l2->C, l1->B);
    mpq_sub(qT4, qT1, qT2);
    mpq_div(px, qT4, qT3);
    mpq_mul(qT1, l1->A, l2->C);
    mpq_mul(qT2, l2->A, l1->C);
    mpq_sub(qT4, qT1, qT2);
    mpq_div(py, qT4, qT3);
    return 1;
}

/* ------------------------------------------------------------------ */
/* combinatorial tables per n (3..9)                                   */
/* ------------------------------------------------------------------ */
static int ntri[MAXN + 1];
static int  tri[MAXN + 1][MAXTRI][3];
static int  npair[MAXN + 1];
static int  pairs[MAXN + 1][MAXPAIR][2];
static int16_t RPOS[MAXN + 1][MAXN * MAXN * MAXN];
static uint8_t RFLIP[MAXN + 1][MAXN * MAXN * MAXN];
static int PIDX[MAXN + 1][MAXN][MAXN];
static int table_ready[MAXN + 1];

static void build_tables(int n) {
    if (table_ready[n]) return;
    int t = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            for (int k = j + 1; k < n; k++) {
                tri[n][t][0] = i; tri[n][t][1] = j; tri[n][t][2] = k; t++;
            }
    ntri[n] = t;
    int p = 0;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) { pairs[n][p][0] = i; pairs[n][p][1] = j; p++; }
    npair[n] = p;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) PIDX[n][i][j] = -1;
    for (int p2 = 0; p2 < p; p2++) PIDX[n][pairs[n][p2][0]][pairs[n][p2][1]] = p2;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            for (int k = 0; k < n; k++) {
                int idx = i * MAXN * MAXN + j * MAXN + k;
                RPOS[n][idx] = -1; RFLIP[n][idx] = 0;
            }
    for (int q = 0; q < t; q++) {
        int i = tri[n][q][0], j = tri[n][q][1], k = tri[n][q][2];
        int even[3][3] = { {i, j, k}, {j, k, i}, {k, i, j} };
        int odd[3][3]  = { {j, i, k}, {i, k, j}, {k, j, i} };
        for (int u = 0; u < 3; u++) {
            RPOS[n][even[u][0] * MAXN * MAXN + even[u][1] * MAXN + even[u][2]] = (int16_t)q;
            RFLIP[n][even[u][0] * MAXN * MAXN + even[u][1] * MAXN + even[u][2]] = 0;
            RPOS[n][odd[u][0] * MAXN * MAXN + odd[u][1] * MAXN + odd[u][2]] = (int16_t)q;
            RFLIP[n][odd[u][0] * MAXN * MAXN + odd[u][1] * MAXN + odd[u][2]] = 1;
        }
    }
    table_ready[n] = 1;
}

static inline int osign(const signed char *chi, int n, int i, int j, int k) {
    int idx = i * MAXN * MAXN + j * MAXN + k;
    return RFLIP[n][idx] ? -chi[RPOS[n][idx]] : chi[RPOS[n][idx]];
}

/* ------------------------------------------------------------------ */
/* chi of a point set (over sorted triples)                            */
/* ------------------------------------------------------------------ */
static void chi_of_points(PT *pts, int n, signed char *chi) {
    build_tables(n);
    for (int t = 0; t < ntri[n]; t++) {
        int i = tri[n][t][0], j = tri[n][t][1], k = tri[n][t][2];
        chi[t] = (signed char)orient_sign(&pts[i], &pts[j], &pts[k]);
    }
}
static int is_gp(PT *pts, int n) {
    build_tables(n);
    for (int t = 0; t < ntri[n]; t++) {
        int i = tri[n][t][0], j = tri[n][t][1], k = tri[n][t][2];
        if (orient_sign(&pts[i], &pts[j], &pts[k]) == 0) return 0;
    }
    return 1;
}
static int chi_eq(const signed char *a, const signed char *b, int len) {
    return memcmp(a, b, (size_t)len) == 0;
}

/* ------------------------------------------------------------------ */
/* hashing                                                             */
/* ------------------------------------------------------------------ */
static inline uint64_t hash_bytes(const void *data, size_t len, uint64_t h) {
    const unsigned char *p = (const unsigned char *)data;
    for (size_t i = 0; i < len; i++) h = (h ^ p[i]) * 1099511628211ULL;
    return h;
}
static inline uint64_t mpz_hash(const mpz_t z) {
    int n = z->_mp_size;
    uint64_t h = 1469598103934665603ULL ^ (uint64_t)n;
    if (n < 0) n = -n;
    for (int i = 0; i < n; i++) h = (h ^ (uint64_t)z->_mp_d[i]) * 1099511628211ULL;
    return h;
}
static inline uint64_t mpq_hash(mpq_t q) {
    return mpz_hash(mpq_numref(q)) * 0x9E3779B97F4A7C15ULL
         ^ mpz_hash(mpq_denref(q));
}

/* generic uint64-key set with generations (clear = gen++) */
typedef struct { uint64_t *keys; uint32_t *gens; int cap; uint32_t gen; } U64SET;
static void u64set_init(U64SET *s, int cap) {
    s->cap = cap; s->gen = 1;
    s->keys = calloc((size_t)cap, sizeof(uint64_t));
    s->gens = calloc((size_t)cap, sizeof(uint32_t));
}
static void u64set_clear(U64SET *s) { s->gen++; }
static inline uint64_t u64slot(const U64SET *s, uint64_t k) {
    return (k * 0x9E3779B97F4A7C15ULL) >> 32 & (uint64_t)(s->cap - 1);
}
static inline int u64set_has(const U64SET *s, uint64_t k) {
    for (uint64_t i = u64slot(s, k); ; i = (i + 1) & (uint64_t)(s->cap - 1)) {
        if (s->gens[i] != s->gen) return 0;
        if (s->keys[i] == k) return 1;
    }
}
static inline void u64set_add(U64SET *s, uint64_t k) {
    for (uint64_t i = u64slot(s, k); ; i = (i + 1) & (uint64_t)(s->cap - 1)) {
        if (s->gens[i] != s->gen) { s->gens[i] = s->gen; s->keys[i] = k; return; }
        if (s->keys[i] == k) return;
    }
}

/* exact mpq-point hash set (concurrency dedup) */
typedef struct {
    mpq_t x[1024], y[1024];
    uint32_t g[1024];
    uint32_t gen;
    int inited;
} PTSET;
static PTSET ptset;
static void ptset_use(void) {
    if (!ptset.inited) {
        for (int i = 0; i < 1024; i++) { mpq_init(ptset.x[i]); mpq_init(ptset.y[i]); }
        ptset.inited = 1;
    }
    ptset.gen++;
    if (ptset.gen == 0) { memset(ptset.g, 0, sizeof(ptset.g)); ptset.gen = 1; }
}
/* returns 1 if present; if absent and add, inserts */
static int ptset_lookup(mpq_t x, mpq_t y, int add) {
    uint64_t h = mpq_hash(x) * 0x9E3779B97F4A7C15ULL ^ mpq_hash(y);
    for (int i = (int)(h & 1023); ; i = (i + 1) & 1023) {
        if (ptset.g[i] != ptset.gen) {
            if (!add) return 0;
            ptset.g[i] = ptset.gen;
            mpq_set(ptset.x[i], x); mpq_set(ptset.y[i], y);
            return 0;
        }
        if (mpq_equal(ptset.x[i], x) && mpq_equal(ptset.y[i], y)) return 1;
    }
}

/* ------------------------------------------------------------------ */
/* pair-line arrangement (static, pre-initialized)                     */
/* ------------------------------------------------------------------ */
typedef struct { LN L[MAXLINES]; int nlines; } ARR;
static ARR arr_lines;          /* shared line array (single-threaded) */
static int arr_inited = 0;

static void arr_build(const PT *pts, int n) {
    build_tables(n);
    if (!arr_inited) {
        for (int i = 0; i < MAXLINES; i++) {
            mpq_init(arr_lines.L[i].A); mpq_init(arr_lines.L[i].B); mpq_init(arr_lines.L[i].C);
        }
        arr_inited = 1;
    }
    arr_lines.nlines = 0;
    for (int p = 0; p < npair[n]; p++) {
        int i = pairs[n][p][0], j = pairs[n][p][1];
        ln_from_points(&arr_lines.L[arr_lines.nlines], &pts[i], &pts[j]);
        arr_lines.nlines++;
    }
}

/* ------------------------------------------------------------------ */
/* shear: distinct x (x + t*y, det-1 transform, orientations preserved) */
/* ------------------------------------------------------------------ */
static int shear_distinct_x(const PT *pts, int n, PT *out) {
    for (int t = 0; t <= 4 * n * n + 63; t++) {
        for (int i = 0; i < n; i++) {
            qset_si(qT1, (long)t, 1);
            mpq_mul(qT1, qT1, pts[i].y);
            mpq_add(out[i].x, pts[i].x, qT1);
            mpq_set(out[i].y, pts[i].y);
        }
        int ok = 1;
        for (int i = 0; i < n && ok; i++)
            for (int j = i + 1; j < n && ok; j++)
                if (mpq_equal(out[i].x, out[j].x)) ok = 0;
        if (ok) return t;
    }
    return -1;
}

/* arrangement-generic: no 2 pair-lines parallel, no 3 pairwise-disjoint
 * pair-lines concurrent (shared-endpoint concurrence at config points
 * is not a degeneracy).  Faithful port of python arrangement_generic. */
static int arrangement_generic(const PT *pts, int n) {
    arr_build(pts, n);
    int m = arr_lines.nlines;
    for (int u = 0; u < m; u++)
        for (int v = u + 1; v < m; v++)
            if (lines_parallel(&arr_lines.L[u], &arr_lines.L[v])) return 0;
    ptset_use();
    mpq_t px, py;
    mpq_init(px); mpq_init(py);
    int ok = 1;
    for (int u = 0; u < m && ok; u++) {
        int i1 = pairs[n][u][0], j1 = pairs[n][u][1];
        for (int v = u + 1; v < m && ok; v++) {
            int i2 = pairs[n][v][0], j2 = pairs[n][v][1];
            if (i1 == i2 || i1 == j2 || j1 == i2 || j1 == j2) continue;
            if (!line_isect(&arr_lines.L[u], &arr_lines.L[v], px, py)) { ok = 0; break; }
            if (ptset_lookup(px, py, 1)) ok = 0;      /* >= 3 concurrent */
        }
    }
    mpq_clear(px); mpq_clear(py);
    return ok;
}

/* type-preserving jitter until arrangement-generic (faithful port of
 * make_arrangement_generic; C rng). Returns 0 on failure.             */
static int make_arrangement_generic(const PT *pts, int n, const signed char *chi,
                                    PT *out, int *was_generic) {
    if (arrangement_generic(pts, n)) {
        for (int i = 0; i < n; i++) pt_set(&out[i], &pts[i]);
        *was_generic = 1;
        return 1;
    }
    *was_generic = 0;
    static const int ddens[5] = {8, 16, 32, 5, 7};
    static PT cand[MAXN]; static int cand_inited = 0;
    if (!cand_inited) {
        for (int i = 0; i < MAXN; i++) pt_init(&cand[i]);
        cand_inited = 1;
    }
    static signed char c2[MAXTRI];
    for (int tries = 0; tries < 500; tries++) {
        int m = rng_below(n);
        long dxn = rng_randint(-12, 12), dyn = rng_randint(-12, 12);
        long dxd = ddens[rng_below(5)], dyd = ddens[rng_below(5)];
        for (int i = 0; i < n; i++) pt_set(&cand[i], &pts[i]);
        qset_si(qT1, dxn, dxd); mpq_add(cand[m].x, cand[m].x, qT1);
        qset_si(qT2, dyn, dyd); mpq_add(cand[m].y, cand[m].y, qT2);
        if (is_gp(cand, n)) {
            chi_of_points(cand, n, c2);
            if (chi_eq(c2, chi, ntri[n]) && arrangement_generic(cand, n)) {
                for (int i = 0; i < n; i++) pt_set(&out[i], &cand[i]);
                return 1;
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* S1: exact slab sampling of the pair-line arrangement                */
/* ------------------------------------------------------------------ */
typedef struct {
    PT *pts;            /* cell samples */
    uint32_t *topes;    /* LINE-sign bitpack: bit p = (A x + B y - C > 0) */
    int n;
} CELLS;

typedef struct { int lid; } YENT;
static mpq_t cs_yv[MAXLINES];      /* y-values of lines at current slab x */
static int cmp_yent(const void *a, const void *b) {
    int u = ((const YENT *)a)->lid, v = ((const YENT *)b)->lid;
    int c = mpq_cmp(cs_yv[u], cs_yv[v]);
    if (c) return c;
    return u - v;
}
static int cmp_mpq(const void *a, const void *b) {
    const mpq_t *u = (const mpq_t *)a, *v = (const mpq_t *)b;
    return mpq_cmp(*u, *v);
}

static mpq_t cs_xs[400], cs_slabx[400], cs_ycan[MAXLINES + 2];
static YENT cs_ye[MAXLINES];
static int cs_init = 0;
static U64SET cs_seen;

/* One exact sample per open cell (slab method).  pts must have distinct
 * x.  Returns cell count; the formula count is written to *formula.  */
static int arrangement_cell_samples(const PT *pts, int n, CELLS *out,
                                    int *formula) {
    build_tables(n);
    if (!cs_init) {
        for (int i = 0; i < 400; i++) { mpq_init(cs_xs[i]); mpq_init(cs_slabx[i]); }
        for (int i = 0; i < MAXLINES; i++) mpq_init(cs_yv[i]);
        for (int i = 0; i < MAXLINES + 2; i++) mpq_init(cs_ycan[i]);
        u64set_init(&cs_seen, 4096);
        cs_init = 1;
    }
    arr_build(pts, n);
    int L = arr_lines.nlines;
    long long Lc2 = (long long)L * (L - 1) / 2;
    long long share = (long long)n * ((long long)(n - 1) * (n - 2) / 2);
    *formula = (int)(1 + L + (long long)n * (n - 2) + Lc2 - share);

    /* all pairwise intersection x-coords */
    int nxs = 0;
    for (int u = 0; u < L; u++)
        for (int v = u + 1; v < L; v++) {
            mpq_mul(qT1, arr_lines.L[u].A, arr_lines.L[v].B);
            mpq_mul(qT2, arr_lines.L[v].A, arr_lines.L[u].B);
            mpq_sub(qT3, qT1, qT2);
            if (mpq_sgn(qT3) == 0) continue;
            mpq_mul(qT1, arr_lines.L[u].C, arr_lines.L[v].B);
            mpq_mul(qT2, arr_lines.L[v].C, arr_lines.L[u].B);
            mpq_sub(qT4, qT1, qT2);
            mpq_div(cs_xs[nxs], qT4, qT3);
            nxs++;
        }
    qsort(cs_xs, (size_t)nxs, sizeof(mpq_t), cmp_mpq);
    int nx = 0;
    for (int i = 0; i < nxs; i++)
        if (i == 0 || mpq_cmp(cs_xs[i], cs_xs[nx - 1]) != 0) {
            if (nx != i) mpq_set(cs_xs[nx], cs_xs[i]);
            nx++;
        }

    /* slab x positions: xs[0]-1, midpoints, xs[nx-1]+1 */
    int sx = 0;
    if (nx > 0) {
        qset_si(cs_slabx[sx], -1, 1);
        mpq_add(cs_slabx[sx], cs_xs[0], cs_slabx[sx]); sx++;
        for (int i = 0; i + 1 < nx; i++) {
            mpq_add(cs_slabx[sx], cs_xs[i], cs_xs[i + 1]);
            mpq_div_2exp(cs_slabx[sx], cs_slabx[sx], 1);
            sx++;
        }
        qset_si(cs_slabx[sx], 1, 1);
        mpq_add(cs_slabx[sx], cs_xs[nx - 1], cs_slabx[sx]); sx++;
    } else {
        qset_si(cs_slabx[sx], 0, 1); sx++;
    }

    u64set_clear(&cs_seen);
    int cap = 2048;
    out->pts = malloc((size_t)cap * sizeof(PT));
    out->topes = malloc((size_t)cap * sizeof(uint32_t));
    for (int i = 0; i < cap; i++) pt_init(&out->pts[i]);
    out->n = 0;

    static PT probe;
    static int probe_init = 0;
    if (!probe_init) { pt_init(&probe); probe_init = 1; }

    for (int s = 0; s < sx; s++) {
        for (int l = 0; l < L; l++) {
            /* y = (C - A*x0)/B, B != 0 (distinct x) */
            mpq_mul(qT1, arr_lines.L[l].A, cs_slabx[s]);
            mpq_sub(qT2, arr_lines.L[l].C, qT1);
            mpq_div(cs_yv[l], qT2, arr_lines.L[l].B);
            cs_ye[l].lid = l;
        }
        qsort(cs_ye, (size_t)L, sizeof(YENT), cmp_yent);
        /* tope below all lines at (x0, ye[0].y - 1) */
        mpq_set(probe.x, cs_slabx[s]);
        qset_si(qT1, -1, 1);
        mpq_add(probe.y, cs_yv[cs_ye[0].lid], qT1);
        uint32_t tope_below = 0;
        for (int l = 0; l < L; l++)
            if (line_sign(&arr_lines.L[l], (PT *)&probe) > 0) tope_below |= (1u << l);
        /* candidates: below-all, midpoints (L-1), above-all */
        mpq_set(cs_ycan[0], probe.y);
        for (int k = 0; k + 1 < L; k++) {
            mpq_add(cs_ycan[1 + k], cs_yv[cs_ye[k].lid], cs_yv[cs_ye[k + 1].lid]);
            mpq_div_2exp(cs_ycan[1 + k], cs_ycan[1 + k], 1);
        }
        qset_si(qT1, 1, 1);
        mpq_add(cs_ycan[L], cs_yv[cs_ye[L - 1].lid], qT1);
        int ncand = L + 1;
        /* moving up crosses line ye[k].lid between cand k and k+1 */
        uint32_t cur = tope_below;
        for (int c = 0; c < ncand; c++) {
            if (c > 0) cur ^= (1u << cs_ye[c - 1].lid);
            if (!u64set_has(&cs_seen, cur)) {
                u64set_add(&cs_seen, cur);
                if (out->n >= cap) {
                    int ncap = cap * 2;
                    out->pts = realloc(out->pts, (size_t)ncap * sizeof(PT));
                    out->topes = realloc(out->topes, (size_t)ncap * sizeof(uint32_t));
                    for (int i = cap; i < ncap; i++) pt_init(&out->pts[i]);
                    cap = ncap;
                }
                mpq_set(out->pts[out->n].x, cs_slabx[s]);
                mpq_set(out->pts[out->n].y, cs_ycan[c]);
                out->topes[out->n] = cur;
                out->n++;
            }
        }
    }
    return out->n;
}

/* ------------------------------------------------------------------ */
/* children store: dict chi -> coords (first wins)                     */
/* ------------------------------------------------------------------ */
typedef struct {
    signed char chi[MAXTRI];
    PT pts[MAXN + 1];
} CHILD;

static CHILD *child_pool = NULL;
static int child_pool_cap = 0, child_pool_n = 0;
static struct { uint64_t h[8192]; int slot[8192]; uint32_t g[8192]; uint32_t gen; } chiset;

static void children_reset(void) {
    child_pool_n = 0;
    chiset.gen++;
    if (chiset.gen == 0) { memset(chiset.g, 0, sizeof(chiset.g)); chiset.gen = 1; }
}
static int children_add(const signed char *chi, int len, const PT *pts, int npts) {
    uint64_t h = hash_bytes(chi, (size_t)len, 1469598103934665603ULL);
    int i0 = (int)(h & 8191);
    for (int i = i0; ; i = (i + 1) & 8191) {
        if (chiset.g[i] != chiset.gen) break;
        int j = chiset.slot[i];
        if (memcmp(child_pool[j].chi, chi, (size_t)len) == 0) return 0;
    }
    if (child_pool_n >= child_pool_cap) {
        int ncap = child_pool_cap ? child_pool_cap * 2 : 1024;
        child_pool = realloc(child_pool, (size_t)ncap * sizeof(CHILD));
        for (int i = child_pool_cap; i < ncap; i++)
            for (int p = 0; p <= MAXN; p++) pt_init(&child_pool[i].pts[p]);
        child_pool_cap = ncap;
    }
    CHILD *c = &child_pool[child_pool_n];
    memcpy(c->chi, chi, (size_t)len);
    for (int p = 0; p < npts; p++) pt_set(&c->pts[p], &pts[p]);
    for (int i = i0; ; i = (i + 1) & 8191) {
        if (chiset.g[i] != chiset.gen) {
            chiset.g[i] = chiset.gen; chiset.slot[i] = child_pool_n;
            break;
        }
    }
    child_pool_n++;
    return 1;
}

/* ------------------------------------------------------------------ */
/* sign vectors + insertion                                            */
/* ------------------------------------------------------------------ */
static PT sv_q;
static int sv_q_init = 0;

/* sv[p] = sgn(orient(pts[i], pts[j], q)) over pairs of pts */
static void sv_of_point_bytes(PT *pts, int n, const mpq_t qx, const mpq_t qy,
                              signed char *sv) {
    build_tables(n);
    if (!sv_q_init) { pt_init(&sv_q); sv_q_init = 1; }
    mpq_set(sv_q.x, qx); mpq_set(sv_q.y, qy);
    for (int p = 0; p < npair[n]; p++) {
        int i = pairs[n][p][0], j = pairs[n][p][1];
        sv[p] = (signed char)orient_sign(&pts[i], &pts[j], &sv_q);
    }
}

/* chi_{n+1} from base chi + insertion sign vector (TRIPLES(n+1) order).
 * sv is indexed by the PARENT's pair order (PAIRS(n)) — exactly python's
 * chi_insert (sig = dict(zip(pairs_of_n, sv))).                        */
static void chi_insert(const signed char *base, int n, const signed char *sv,
                       signed char *out) {
    build_tables(n); build_tables(n + 1);
    for (int t = 0; t < ntri[n + 1]; t++) {
        int i = tri[n + 1][t][0], j = tri[n + 1][t][1], k = tri[n + 1][t][2];
        if (k == n) out[t] = sv[PIDX[n][i][j]];
        else out[t] = base[RPOS[n][i * MAXN * MAXN + j * MAXN + k]];
    }
}

/* ------------------------------------------------------------------ */
/* S2: the wall sweep (faithful port of sweep_parent)                  */
/* ------------------------------------------------------------------ */
typedef struct {
    long conc_combos, conc_crossed, par_combos, par_crossed, grabs;
} SWEEPSTAT;

static int rest_pairs[MAXN][MAXPAIR][2];
static int rest_n[MAXN];
static signed char m_sv[MAXN][MAXPAIR];
static LN rlines[MAXN][MAXPAIR];
static int rlines_init = 0;
static U64SET sw_grabbed;
static int sw_grabbed_init = 0;
static signed char sw_sv[MAXPAIR], sw_chi9[MAXTRI], sw_c2[MAXTRI], sw_c9[MAXTRI];
static PT sw_cfg[MAXN], sw_all[MAXN + 1];
static int sw_pts_init = 0;
static mpq_t sw_pmx, sw_pmy, sw_dx, sw_dy, sw_dd, sw_bx, sw_by, sw_tm,
             sw_mx, sw_my, sw_sx, sw_sy, sw_den;
static mpq_t sw_crit[160];
static int sw_mpq_init = 0;
static LN sw_L1;
static mpq_t sw_a1x, sw_a1y, sw_a2x, sw_a2y, sw_a3x, sw_a3y, sw_gx, sw_gy;
static mpq_t sw_Bn, sw_y1, sw_y2;

static void sweep_init_once(void) {
    if (!rlines_init) {
        for (int m = 0; m < MAXN; m++)
            for (int p = 0; p < MAXPAIR; p++) {
                mpq_init(rlines[m][p].A); mpq_init(rlines[m][p].B); mpq_init(rlines[m][p].C);
            }
        rlines_init = 1;
    }
    if (!sw_grabbed_init) { u64set_init(&sw_grabbed, 1024); sw_grabbed_init = 1; }
    if (!sw_pts_init) {
        for (int i = 0; i < MAXN; i++) pt_init(&sw_cfg[i]);
        for (int i = 0; i <= MAXN; i++) pt_init(&sw_all[i]);
        sw_pts_init = 1;
    }
    if (!sw_mpq_init) {
        mpq_inits(sw_pmx, sw_pmy, sw_dx, sw_dy, sw_dd, sw_bx, sw_by, sw_tm,
                  sw_mx, sw_my, sw_sx, sw_sy, sw_den, NULL);
        for (int i = 0; i < 160; i++) mpq_init(sw_crit[i]);
        mpq_inits(sw_a1x, sw_a1y, sw_a2x, sw_a2y, sw_a3x, sw_a3y, sw_gx, sw_gy,
                  sw_Bn, sw_y1, sw_y2, NULL);
        mpq_init(sw_L1.A); mpq_init(sw_L1.B); mpq_init(sw_L1.C);
        sw_mpq_init = 1;
    }
}

/* insertion of a grab: sv (no zeros), cfg, grab point; verifies the
 * chi assert (faithful to python's assert chi_of_points(cfg+g)==chi9). */
static void sweep_grab(PT *cfg, int n, const signed char *base_chi,
                       const signed char *sv, const mpq_t gx, const mpq_t gy,
                       SWEEPSTAT *st) {
    build_tables(n); build_tables(n + 1);
    chi_insert(base_chi, n, sv, sw_chi9);
    for (int i = 0; i < n; i++) pt_set(&sw_all[i], &cfg[i]);
    mpq_set(sw_all[n].x, gx); mpq_set(sw_all[n].y, gy);
    chi_of_points(sw_all, n + 1, sw_c9);
    if (!chi_eq(sw_c9, sw_chi9, ntri[n + 1])) {
        fprintf(stderr, "FATAL: sweep grab chi mismatch\n");
        exit(1);
    }
    if (children_add(sw_chi9, ntri[n + 1], sw_all, n + 1)) st->grabs++;
}

static void sweep_parent(PT *pts, int n, const signed char *base_chi,
                         const U64SET *current_svs, SWEEPSTAT *st) {
    build_tables(n); build_tables(n + 1);
    sweep_init_once();
    int P = npair[n];
    arr_build(pts, n);   /* arr_lines = pair lines of pts */
    for (int m = 0; m < n; m++) {
        rest_n[m] = 0;
        for (int p = 0; p < P; p++) {
            int i = pairs[n][p][0], j = pairs[n][p][1];
            if (i == m || j == m) continue;
            m_sv[m][rest_n[m]] = (signed char)osign(base_chi, n, i, j, m);
            rest_pairs[m][rest_n[m]][0] = i;
            rest_pairs[m][rest_n[m]][1] = j;
            rest_n[m]++;
        }
        for (int p = 0; p < rest_n[m]; p++)
            ln_from_points(&rlines[m][p], &pts[rest_pairs[m][p][0]],
                           &pts[rest_pairs[m][p][1]]);
    }
    static const long snum[4] = {1, -1, 1, -1};
    static const long sden[4] = {4, 4, 64, 64};

    /* ---------- concurrency walls: 3-matchings of K_n ---------- */
    static int matchings[15][3][2];
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
    for (int c = b + 1; c < n; c++) for (int d = c + 1; d < n; d++)
    for (int e = d + 1; e < n; e++) for (int f = e + 1; f < n; f++) {
        int c6[6] = {a, b, c, d, e, f};
        int nm = 0;
        for (int s1 = 1; s1 < 6; s1++) {
            int remv[4]; int rc = 0;
            for (int q = 1; q < 6; q++) if (q != s1) remv[rc++] = q;
            static const int fm[3][4] = { {0,1,2,3}, {0,2,1,3}, {0,3,1,2} };
            for (int u = 0; u < 3; u++) {
                matchings[nm][0][0] = c6[0]; matchings[nm][0][1] = c6[s1];
                matchings[nm][1][0] = c6[remv[fm[u][0]]];
                matchings[nm][1][1] = c6[remv[fm[u][1]]];
                matchings[nm][2][0] = c6[remv[fm[u][2]]];
                matchings[nm][2][1] = c6[remv[fm[u][3]]];
                nm++;
            }
        }
        if (nm != 15) { fprintf(stderr, "FATAL: matching enum %d\n", nm); exit(1); }

        for (int mi = 0; mi < 15; mi++) {
            int (*prs)[2] = matchings[mi];
            int ends[6] = { prs[0][0], prs[0][1], prs[1][0], prs[1][1],
                            prs[2][0], prs[2][1] };
            for (int ei = 0; ei < 6; ei++) {
                int m = ends[ei];
                int partner = -1, o1 = -1, o2 = -1;
                for (int pr = 0; pr < 3; pr++) {
                    if (prs[pr][0] == m || prs[pr][1] == m) {
                        partner = (prs[pr][0] == m) ? prs[pr][1] : prs[pr][0];
                    } else {
                        if (o1 < 0) o1 = pr; else o2 = pr;
                    }
                }
                int p1 = PIDX[n][prs[o1][0] < prs[o1][1] ? prs[o1][0] : prs[o1][1]]
                                  [prs[o1][0] < prs[o1][1] ? prs[o1][1] : prs[o1][0]];
                int p2 = PIDX[n][prs[o2][0] < prs[o2][1] ? prs[o2][0] : prs[o2][1]]
                                  [prs[o2][0] < prs[o2][1] ? prs[o2][1] : prs[o2][0]];
                if (!line_isect(&arr_lines.L[p1], &arr_lines.L[p2], sw_pmx, sw_pmy))
                    continue;
                st->conc_combos++;
                mpq_set(sw_bx, pts[partner].x); mpq_set(sw_by, pts[partner].y);
                mpq_sub(sw_dx, sw_pmx, sw_bx); mpq_sub(sw_dy, sw_pmy, sw_by);
                int nc = 0;
                qset_si(sw_crit[nc], 0, 1); nc++;
                qset_si(sw_crit[nc], 1, 1); nc++;
                for (int p = 0; p < rest_n[m]; p++) {
                    mpq_mul(qT1, rlines[m][p].A, sw_dx);
                    mpq_mul(qT2, rlines[m][p].B, sw_dy);
                    mpq_add(sw_den, qT1, qT2);
                    if (mpq_sgn(sw_den) == 0) continue;
                    mpq_mul(qT1, rlines[m][p].A, sw_bx);
                    mpq_mul(qT2, rlines[m][p].B, sw_by);
                    mpq_add(qT3, qT1, qT2);
                    mpq_sub(qT4, rlines[m][p].C, qT3);
                    mpq_div(sw_crit[nc], qT4, sw_den);
                    nc++;
                }
                for (int i = 1; i < nc; i++) {          /* insertion sort */
                    mpq_set(qT5, sw_crit[i]);
                    int j = i - 1;
                    while (j >= 0 && mpq_cmp(sw_crit[j], qT5) > 0) {
                        mpq_set(sw_crit[j + 1], sw_crit[j]); j--;
                    }
                    mpq_set(sw_crit[j + 1], qT5);
                }
                mpq_mul(sw_dd, sw_dx, sw_dx);
                mpq_mul(qT1, sw_dy, sw_dy);
                mpq_add(sw_dd, sw_dd, qT1);
                if (mpq_sgn(sw_dd) == 0) continue;
                for (int iv = 0; iv + 1 < nc; iv++) {
                    mpq_add(sw_tm, sw_crit[iv], sw_crit[iv + 1]);
                    mpq_div_2exp(sw_tm, sw_tm, 1);
                    mpq_mul(qT1, sw_tm, sw_dx); mpq_add(sw_mx, sw_bx, qT1);
                    mpq_mul(qT1, sw_tm, sw_dy); mpq_add(sw_my, sw_by, qT1);
                    /* chi_ok_with(m, mstar): sv vs m's rest pairs */
                    sv_of_point_bytes(pts, n, sw_mx, sw_my, sw_sv);
                    int ok = 1;
                    for (int rp = 0; rp < rest_n[m]; rp++) {
                        int i = rest_pairs[m][rp][0], j = rest_pairs[m][rp][1];
                        if (sw_sv[PIDX[n][i][j]] != m_sv[m][rp]) { ok = 0; break; }
                    }
                    if (!ok) continue;
                    u64set_clear(&sw_grabbed);
                    int grabbed_any = 0;
                    for (int si = 0; si < 4; si++) {
                        /* mq = mstar + s*nvec/dd, nvec = (-dy, dx) */
                        qset_si(qT1, snum[si], sden[si]);
                        mpq_mul(qT2, qT1, sw_dy); mpq_neg(qT2, qT2);
                        mpq_div(qT3, qT2, sw_dd);
                        mpq_add(sw_sx, sw_mx, qT3);
                        mpq_mul(qT2, qT1, sw_dx);
                        mpq_div(qT3, qT2, sw_dd);
                        mpq_add(sw_sy, sw_my, qT3);
                        for (int i = 0; i < n; i++) pt_set(&sw_cfg[i], &pts[i]);
                        mpq_set(sw_cfg[m].x, sw_sx); mpq_set(sw_cfg[m].y, sw_sy);
                        if (!is_gp(sw_cfg, n)) continue;
                        chi_of_points(sw_cfg, n, sw_c2);
                        if (!chi_eq(sw_c2, base_chi, ntri[n])) continue;
                        int lo = m < partner ? m : partner;
                        int hi = m < partner ? partner : m;
                        ln_from_points(&sw_L1, &sw_cfg[lo], &sw_cfg[hi]);
                        int got = line_isect(&sw_L1, &arr_lines.L[p1], sw_a1x, sw_a1y)
                               && line_isect(&sw_L1, &arr_lines.L[p2], sw_a2x, sw_a2y)
                               && line_isect(&arr_lines.L[p1], &arr_lines.L[p2], sw_a3x, sw_a3y);
                        if (!got) continue;
                        /* g = centroid of the three isects */
                        mpq_add(sw_gx, sw_a1x, sw_a2x);
                        mpq_add(sw_gx, sw_gx, sw_a3x);
                        qset_si(qT1, 1, 3); mpq_mul(sw_gx, sw_gx, qT1);
                        mpq_add(sw_gy, sw_a1y, sw_a2y);
                        mpq_add(sw_gy, sw_gy, sw_a3y);
                        qset_si(qT1, 1, 3); mpq_mul(sw_gy, sw_gy, qT1);
                        sv_of_point_bytes(sw_cfg, n, sw_gx, sw_gy, sw_sv);
                        int zero = 0;
                        for (int p = 0; p < P; p++) if (sw_sv[p] == 0) { zero = 1; break; }
                        if (zero) continue;
                        uint64_t tp = 0;
                        for (int p = 0; p < P; p++)
                            if (sw_sv[p] > 0) tp |= (1ULL << p);
                        if (u64set_has(current_svs, tp) || u64set_has(&sw_grabbed, tp))
                            continue;
                        u64set_add(&sw_grabbed, tp);
                        grabbed_any = 1;
                        sweep_grab(sw_cfg, n, base_chi, sw_sv, sw_gx, sw_gy, st);
                    }
                    if (grabbed_any) st->conc_crossed++;
                }
            }
        }
    }

    /* ---------- parallel walls: disjoint pair-pairs ---------- */
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
    for (int c = b + 1; c < n; c++) for (int d = c + 1; d < n; d++) {
        int quads[3][2][2] = {
            { {a, b}, {c, d} }, { {a, c}, {b, d} }, { {a, d}, {b, c} },
        };
        for (int qi = 0; qi < 3; qi++) {
            int P0 = quads[qi][0][0], P1 = quads[qi][0][1];
            int Q0 = quads[qi][1][0], Q1 = quads[qi][1][1];
            int fours[4] = { P0, P1, Q0, Q1 };
            for (int fi = 0; fi < 4; fi++) {
                int m = fours[fi];
                int inP = (m == P0 || m == P1);
                int partner = inP ? (m == P0 ? P1 : P0) : (m == Q0 ? Q1 : Q0);
                int o0 = inP ? Q0 : P0, o1 = inP ? Q1 : P1;
                mpq_sub(sw_dx, pts[o1].x, pts[o0].x);
                mpq_sub(sw_dy, pts[o1].y, pts[o0].y);
                st->par_combos++;
                mpq_set(sw_bx, pts[partner].x); mpq_set(sw_by, pts[partner].y);
                int nc = 0;
                qset_si(sw_crit[nc], 0, 1); nc++;
                for (int p = 0; p < rest_n[m]; p++) {
                    mpq_mul(qT1, rlines[m][p].A, sw_dx);
                    mpq_mul(qT2, rlines[m][p].B, sw_dy);
                    mpq_add(sw_den, qT1, qT2);
                    if (mpq_sgn(sw_den) == 0) continue;
                    mpq_mul(qT1, rlines[m][p].A, sw_bx);
                    mpq_mul(qT2, rlines[m][p].B, sw_by);
                    mpq_add(qT3, qT1, qT2);
                    mpq_sub(qT4, rlines[m][p].C, qT3);
                    mpq_div(sw_crit[nc], qT4, sw_den);
                    nc++;
                }
                if (mpq_sgn(sw_dy) != 0) {
                    for (int x = 0; x < n; x++) {
                        if (x == m) continue;
                        mpq_sub(qT1, pts[x].y, sw_by);
                        mpq_div(sw_crit[nc], qT1, sw_dy);
                        nc++;
                    }
                }
                for (int i = 1; i < nc; i++) {
                    mpq_set(qT5, sw_crit[i]);
                    int j = i - 1;
                    while (j >= 0 && mpq_cmp(sw_crit[j], qT5) > 0) {
                        mpq_set(sw_crit[j + 1], sw_crit[j]); j--;
                    }
                    mpq_set(sw_crit[j + 1], qT5);
                }
                if (nc > 160) { fprintf(stderr, "FATAL: crit overflow\n"); exit(1); }
                mpq_mul(sw_dd, sw_dx, sw_dx);
                mpq_mul(qT1, sw_dy, sw_dy);
                mpq_add(sw_dd, sw_dd, qT1);
                if (mpq_sgn(sw_dd) == 0) continue;
                for (int iv = 0; iv + 1 < nc; iv++) {
                    mpq_add(sw_tm, sw_crit[iv], sw_crit[iv + 1]);
                    mpq_div_2exp(sw_tm, sw_tm, 1);
                    mpq_mul(qT1, sw_tm, sw_dx); mpq_add(sw_mx, sw_bx, qT1);
                    mpq_mul(qT1, sw_tm, sw_dy); mpq_add(sw_my, sw_by, qT1);
                    sv_of_point_bytes(pts, n, sw_mx, sw_my, sw_sv);
                    int ok = 1;
                    for (int rp = 0; rp < rest_n[m]; rp++) {
                        int i = rest_pairs[m][rp][0], j = rest_pairs[m][rp][1];
                        if (sw_sv[PIDX[n][i][j]] != m_sv[m][rp]) { ok = 0; break; }
                    }
                    if (!ok) continue;
                    u64set_clear(&sw_grabbed);
                    int grabbed_any = 0;
                    for (int si = 0; si < 4; si++) {
                        qset_si(qT1, snum[si], sden[si]);
                        mpq_mul(qT2, qT1, sw_dy); mpq_neg(qT2, qT2);
                        mpq_div(qT3, qT2, sw_dd);
                        mpq_add(sw_sx, sw_mx, qT3);
                        mpq_mul(qT2, qT1, sw_dx);
                        mpq_div(qT3, qT2, sw_dd);
                        mpq_add(sw_sy, sw_my, qT3);
                        for (int i = 0; i < n; i++) pt_set(&sw_cfg[i], &pts[i]);
                        mpq_set(sw_cfg[m].x, sw_sx); mpq_set(sw_cfg[m].y, sw_sy);
                        if (!is_gp(sw_cfg, n)) continue;
                        chi_of_points(sw_cfg, n, sw_c2);
                        if (!chi_eq(sw_c2, base_chi, ntri[n])) continue;
                        /* Bn = max coord abs + 16 */
                        qset_si(sw_Bn, 16, 1);
                        for (int i = 0; i < n; i++) {
                            mpq_abs(qT2, sw_cfg[i].x);
                            if (mpq_cmp(qT2, sw_Bn) > 0) mpq_set(sw_Bn, qT2);
                            mpq_abs(qT2, sw_cfg[i].y);
                            if (mpq_cmp(qT2, sw_Bn) > 0) mpq_set(sw_Bn, qT2);
                        }
                        int lo = m < partner ? m : partner;
                        int hi = m < partner ? partner : m;
                        ln_from_points(&sw_L1, &sw_cfg[lo], &sw_cfg[hi]);
                        int po = PIDX[n][o0 < o1 ? o0 : o1][o0 < o1 ? o1 : o0];
                        LN *Lo = &arr_lines.L[po];
                        if (mpq_sgn(sw_L1.B) == 0 || mpq_sgn(Lo->B) == 0)
                            continue;   /* defensive: vertical far line */
                        static const long Xk[4] = {-1024, -64, 64, 1024};
                        static const long frn[3] = {1, 1, 3};
                        static const long frd[3] = {2, 4, 4};
                        for (int xi = 0; xi < 4; xi++) {
                            qset_si(qT1, Xk[xi], 1);
                            mpq_mul(qT2, qT1, sw_Bn);       /* X = k*Bn */
                            mpq_mul(qT3, sw_L1.A, qT2);
                            mpq_sub(qT4, sw_L1.C, qT3);
                            mpq_div(sw_y1, qT4, sw_L1.B);
                            mpq_mul(qT3, Lo->A, qT2);
                            mpq_sub(qT4, Lo->C, qT3);
                            mpq_div(sw_y2, qT4, Lo->B);
                            for (int fri = 0; fri < 3; fri++) {
                                qset_si(qT1, frn[fri], frd[fri]);
                                mpq_sub(qT3, sw_y2, sw_y1);
                                mpq_mul(qT3, qT3, qT1);
                                mpq_add(qT3, sw_y1, qT3);   /* y = y1 + fr*(y2-y1) */
                                sv_of_point_bytes(sw_cfg, n, qT2, qT3, sw_sv);
                                int zero = 0;
                                for (int p = 0; p < P; p++)
                                    if (sw_sv[p] == 0) { zero = 1; break; }
                                if (zero) continue;
                                uint64_t tp = 0;
                                for (int p = 0; p < P; p++)
                                    if (sw_sv[p] > 0) tp |= (1ULL << p);
                                if (u64set_has(current_svs, tp) ||
                                    u64set_has(&sw_grabbed, tp)) continue;
                                u64set_add(&sw_grabbed, tp);
                                grabbed_any = 1;
                                sweep_grab(sw_cfg, n, base_chi, sw_sv, qT2, qT3, st);
                            }
                        }
                    }
                    if (grabbed_any) st->par_crossed++;
                }
            }
        }
    }
}

/* ------------------------------------------------------------------ */
/* S3: the in-cell walk (faithful port of walk_parent)                 */
/* ------------------------------------------------------------------ */
static PT wk_cur[MAXN], wk_cand[MAXN], wk_sh2[MAXN], wk_q, wk_all[MAXN + 1];
static int wk_pts_init = 0;
static mpq_t wk_lo, wk_hi, wk_W, wk_tmp;
static signed char wk_target[MAXPAIR], wk_sv[MAXPAIR], wk_chi9[MAXTRI];
static int wk_mpq_init = 0;

static int walk_parent(const PT *pts, int n, const signed char *base_chi, int steps) {
    build_tables(n); build_tables(n + 1);
    if (!wk_pts_init) {
        for (int i = 0; i < MAXN; i++) { pt_init(&wk_cur[i]); pt_init(&wk_cand[i]); pt_init(&wk_sh2[i]); }
        for (int i = 0; i <= MAXN; i++) pt_init(&wk_all[i]);
        pt_init(&wk_q);
        wk_pts_init = 1;
    }
    if (!wk_mpq_init) {
        mpq_inits(wk_lo, wk_hi, wk_W, wk_tmp, NULL);
        wk_mpq_init = 1;
    }
    int P = npair[n];
    for (int i = 0; i < n; i++) pt_set(&wk_cur[i], &pts[i]);
    mpq_set(wk_lo, pts[0].x); mpq_set(wk_hi, pts[0].x);
    for (int i = 0; i < n; i++) {
        if (mpq_cmp(pts[i].x, wk_lo) < 0) mpq_set(wk_lo, pts[i].x);
        if (mpq_cmp(pts[i].x, wk_hi) > 0) mpq_set(wk_hi, pts[i].x);
        if (mpq_cmp(pts[i].y, wk_lo) < 0) mpq_set(wk_lo, pts[i].y);
        if (mpq_cmp(pts[i].y, wk_hi) > 0) mpq_set(wk_hi, pts[i].y);
    }
    /* W = (hi - lo) + 4 */
    mpq_sub(wk_W, wk_hi, wk_lo);
    qset_si(qT1, 4, 1);
    mpq_add(wk_W, wk_W, qT1);
    /* randint bounds: int((lo-W)*16), int((hi+W)*16) — python int() truncates
     * toward zero */
    mpq_sub(wk_tmp, wk_lo, wk_W);
    qset_si(qT2, 16, 1);
    mpq_mul(wk_tmp, wk_tmp, qT2);
    mpz_tdiv_q(mpq_numref(qT3), mpq_numref(wk_tmp), mpq_denref(wk_tmp));
    long a_lo = mpz_get_si(mpq_numref(qT3));
    mpq_add(wk_tmp, wk_hi, wk_W);
    mpq_mul(wk_tmp, wk_tmp, qT2);
    mpz_tdiv_q(mpq_numref(qT3), mpq_numref(wk_tmp), mpq_denref(wk_tmp));
    long a_hi = mpz_get_si(mpq_numref(qT3));

    int walked = 0;
    for (int s = 0; s < steps; s++) {
        int m = rng_below(n);
        int rn = 0;
        for (int p = 0; p < P; p++) {
            int i = pairs[n][p][0], j = pairs[n][p][1];
            if (i == m || j == m) continue;
            wk_target[rn++] = (signed char)osign(base_chi, n, i, j, m);
        }
        int placed = 0;
        for (int tr = 0; tr < 300 && !placed; tr++) {
            long vx = rng_randint((int)a_lo, (int)a_hi);
            long vy = rng_randint((int)a_lo, (int)a_hi);
            qset_si(wk_q.x, vx, 16);
            qset_si(wk_q.y, vy, 16);
            int rn2 = 0, ok = 1;
            for (int p = 0; p < P; p++) {
                int i = pairs[n][p][0], j = pairs[n][p][1];
                if (i == m || j == m) continue;
                if (orient_sign(&wk_cur[i], &wk_cur[j], &wk_q) != wk_target[rn2]) {
                    ok = 0; break;
                }
                rn2++;
            }
            if (ok) placed = 1;
        }
        if (!placed) continue;
        for (int i = 0; i < n; i++) pt_set(&wk_cand[i], &wk_cur[i]);
        mpq_set(wk_cand[m].x, wk_q.x); mpq_set(wk_cand[m].y, wk_q.y);
        if (!is_gp(wk_cand, n)) continue;
        static signed char c2[MAXTRI];
        chi_of_points(wk_cand, n, c2);
        if (!chi_eq(c2, base_chi, ntri[n])) continue;
        for (int i = 0; i < n; i++) pt_set(&wk_cur[i], &wk_cand[i]);
        walked++;
        /* grab cells of this configuration */
        int t = shear_distinct_x(wk_cur, n, wk_sh2);
        if (t < 0) continue;
        CELLS cells;
        int fexp;
        arrangement_cell_samples(wk_sh2, n, &cells, &fexp);
        for (int c = 0; c < cells.n; c++) {
            for (int p = 0; p < P; p++) {
                int i = pairs[n][p][0], j = pairs[n][p][1];
                wk_sv[p] = (signed char)orient_sign(&wk_sh2[i], &wk_sh2[j], &cells.pts[c]);
            }
            chi_insert(base_chi, n, wk_sv, wk_chi9);
            for (int i = 0; i < n; i++) pt_set(&wk_all[i], &wk_sh2[i]);
            pt_set(&wk_all[n], &cells.pts[c]);
            children_add(wk_chi9, ntri[n + 1], wk_all, n + 1);
        }
        for (int i = 0; i < cells.n; i++) pt_clear(&cells.pts[i]);
        free(cells.pts); free(cells.topes);
    }
    return walked;
}

/* ------------------------------------------------------------------ */
/* canonical form (WL buckets + relabeling min) — port of              */
/* python canonical_key                                                */
/* ------------------------------------------------------------------ */
typedef struct { int64_t *data; int len; } IVAL;
static IVAL ivals[512];
static int nivals = 0;
static struct { uint64_t h; int slot; uint32_t g; } imap_e[2048];
static uint32_t imap_gen = 0;

static void canon_reset(void) {
    for (int i = 0; i < nivals; i++) { free(ivals[i].data); ivals[i].data = NULL; }
    nivals = 0;
    imap_gen++;
    if (imap_gen == 0) { memset(imap_e, 0, sizeof(imap_e)); imap_gen = 1; }
}
static int intern(const int64_t *data, int len) {
    uint64_t h = hash_bytes(data, (size_t)len * sizeof(int64_t),
                            1469598103934665603ULL);
    for (int i = (int)(h & 2047); ; i = (i + 1) & 2047) {
        if (imap_e[i].g != imap_gen) break;
        int j = imap_e[i].slot;
        if (ivals[j].len == len &&
            memcmp(ivals[j].data, data, (size_t)len * sizeof(int64_t)) == 0)
            return j;
    }
    if (nivals >= 512) { fprintf(stderr, "FATAL: intern overflow\n"); exit(1); }
    ivals[nivals].data = malloc((size_t)(len ? len : 1) * sizeof(int64_t));
    memcpy(ivals[nivals].data, data, (size_t)len * sizeof(int64_t));
    ivals[nivals].len = len;
    for (int i = (int)(h & 2047); ; i = (i + 1) & 2047) {
        if (imap_e[i].g != imap_gen) {
            imap_e[i].g = imap_gen; imap_e[i].slot = nivals; imap_e[i].h = h;
            break;
        }
    }
    return nivals++;
}
static int n_distinct_inv(const int *inv, int n) {
    int cnt = 0;
    for (int i = 0; i < n; i++) {
        int dup = 0;
        for (int j = 0; j < i; j++) if (inv[j] == inv[i]) { dup = 1; break; }
        if (!dup) cnt++;
    }
    return cnt;
}
/* element-wise int64 lexicographic comparison of interned blobs (the
 * python tuple-value ordering, given the blob layout below) */
static int cmp_blob_slots(int a, int b) {
    int la = ivals[a].len, lb = ivals[b].len;
    int l = la < lb ? la : lb;
    for (int q = 0; q < l; q++) {
        if (ivals[a].data[q] < ivals[b].data[q]) return -1;
        if (ivals[a].data[q] > ivals[b].data[q]) return 1;
    }
    return la < lb ? -1 : la > lb ? 1 : 0;
}
/* renumber the invariant ids of the CURRENT round so that id order ==
 * python value order (python: groups = [buckets[v] for v in sorted(...)]) */
static void renumber_inv(int *inv, int n) {
    int present[512], npres = 0;
    for (int i = 0; i < n; i++) {
        int f = 0;
        for (int q = 0; q < npres; q++) if (present[q] == inv[i]) { f = 1; break; }
        if (!f) present[npres++] = inv[i];
    }
    for (int i = 1; i < npres; i++) {          /* insertion sort by blob */
        int v = present[i], j = i - 1;
        while (j >= 0 && cmp_blob_slots(present[j], v) > 0) {
            present[j + 1] = present[j]; j--;
        }
        present[j + 1] = v;
    }
    int newid[512];
    for (int q = 0; q < npres; q++) newid[present[q]] = q;
    for (int i = 0; i < n; i++) inv[i] = newid[inv[i]];
}
static int cmp_i64(const void *a, const void *b) {
    int64_t x = *(const int64_t *)a, y = *(const int64_t *)b;
    return x < y ? -1 : x > y;
}
/* next lexicographic permutation of int array */
static int next_perm(int *a, int len) {
    int i = len - 2;
    while (i >= 0 && a[i] >= a[i + 1]) i--;
    if (i < 0) return 0;
    int j = len - 1;
    while (a[j] <= a[i]) j--;
    int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = len - 1; l < r; l++, r--) {
        t = a[l]; a[l] = a[r]; a[r] = t;
    }
    return 1;
}

static void canonical_key(const signed char *chi, int n, signed char *out) {
    build_tables(n);
    canon_reset();
    int T = ntri[n];
    int inv[MAXN];
    int64_t buf[64];
    /* point invariants: sorted rows of sign-count encodings */
    for (int i = 0; i < n; i++) {
        int r = 0;
        for (int j = 0; j < n; j++) {
            if (j == i) continue;
            int cm = 0, cp = 0;
            for (int k = 0; k < n; k++) {
                if (k == i || k == j) continue;
                int s = osign(chi, n, i, j, k);
                if (s < 0) cm++; else cp++;
            }
            /* python row = (-1)^cm (+1)^cp sorts BEFORE on MORE negatives:
             * encode -cm so int64-ascending == python row order            */
            buf[r++] = -(int64_t)cm;
        }
        qsort(buf, (size_t)r, sizeof(int64_t), cmp_i64);
        if (getenv("F9CANONDBG")) {
            fprintf(stderr, "canondbg V0 i=%d rows=[", i);
            for (int q = 0; q < r; q++) fprintf(stderr, "%d,", (int)buf[q]);
            fprintf(stderr, "]\n");
        }
        inv[i] = intern(buf, r);
    }
    renumber_inv(inv, n);          /* id order == python value order */
    /* refine (<= 3 iterations; keep old on non-growth) */
    if (getenv("F9CANONDBG")) {
        fprintf(stderr, "canondbg V0 inv=[");
        for (int i = 0; i < n; i++) fprintf(stderr, "%d,", inv[i]);
        fprintf(stderr, "] distinct=%d\n", n_distinct_inv(inv, n));
    }
    for (int it = 0; it < 3; it++) {
        int newinv[MAXN];
        for (int i = 0; i < n; i++) {
            int r = 0;
            int64_t ext[64];
            for (int j = 0; j < n; j++) {
                if (j == i) continue;
                int cm = 0, cp = 0;
                for (int k = 0; k < n; k++) {
                    if (k == i || k == j) continue;
                    int s = osign(chi, n, i, j, k);
                    if (s < 0) cm++; else cp++;
                }
                int64_t v1 = cm * 8 + cp, v2 = cp * 8 + cm;
                int64_t pv = v1 < v2 ? v1 : v2;
                ext[r++] = (int64_t)inv[j] * 64 + pv;
            }
            qsort(ext, (size_t)r, sizeof(int64_t), cmp_i64);
            int64_t blob[66];
            blob[0] = inv[i];
            memcpy(blob + 1, ext, (size_t)r * sizeof(int64_t));
            newinv[i] = intern(blob, r + 1);
        }
        renumber_inv(newinv, n);   /* id order == python value order */
        if (getenv("F9CANONDBG")) {
            fprintf(stderr, "canondbg refine %d newinv=[", it);
            for (int i = 0; i < n; i++) fprintf(stderr, "%d,", newinv[i]);
            fprintf(stderr, "] distinct=%d (old %d)\n",
                    n_distinct_inv(newinv, n), n_distinct_inv(inv, n));
        }
        if (n_distinct_inv(newinv, n) <= n_distinct_inv(inv, n)) break;
        memcpy(inv, newinv, sizeof(inv));
    }
    /* buckets by invariant id — AFTER renumber the ids are dense 0..k-1 in
     * python VALUE order, so ascending id == python sorted(buckets) order.
     * (python: groups = [sorted(buckets[v]) for v in sorted(buckets)]) */
    int bhead[MAXN], bnext[MAXN];
    for (int i = 0; i < n; i++) bhead[i] = -1;
    for (int i = 0; i < n; i++) {
        bnext[i] = bhead[inv[i]];
        bhead[inv[i]] = i;
    }
    /* groups (ascending point lists) */
    int *grp[MAXN]; int grpn[MAXN], ngrp = 0;
    unsigned long long total = 1;
    for (int b = 0; b < n; b++) {
        int c = 0;
        for (int i = bhead[b]; i >= 0; i = bnext[i]) c++;
        if (c == 0) continue;
        grp[ngrp] = malloc((size_t)c * sizeof(int));
        grpn[ngrp] = c;
        int q = 0;
        for (int i = bhead[b]; i >= 0; i = bnext[i]) grp[ngrp][q++] = i;
        for (int i = 1; i < c; i++) {           /* insertion sort ascending */
            int v = grp[ngrp][i], j = i - 1;
            while (j >= 0 && grp[ngrp][j] > v) { grp[ngrp][j + 1] = grp[ngrp][j]; j--; }
            grp[ngrp][j + 1] = v;
        }
        for (unsigned long long f = 2; f <= (unsigned long long)c; f++) {
            total *= f;
            if (total > 400000ULL) {
                fprintf(stderr, "FATAL: canonical blow-up %llu (n=%d)\n", total, n);
                exit(1);
            }
        }
        ngrp++;
    }
    /* enumerate mappings (mapping[pos] = original label); take lex-min key */
    int mapping[MAXN];
    {
        int pos = 0;
        for (int g = 0; g < ngrp; g++)
            for (int q = 0; q < grpn[g]; q++) mapping[pos++] = grp[g][q];
    }
    signed char best[MAXTRI], key[MAXTRI];
    int have_best = 0;
    if (getenv("F9CANONDBG")) {
        fprintf(stderr, "canondbg n=%d ngrp=%d total=%llu groups=[", n, ngrp, total);
        for (int g = 0; g < ngrp; g++) {
            fprintf(stderr, "%s%d:", g ? ";" : "", grpn[g]);
            for (int q = 0; q < grpn[g]; q++) fprintf(stderr, "%d,", grp[g][q]);
        }
        fprintf(stderr, "]\n");
    }
    for (unsigned long long it = 0; it < total; it++) {
        /* lexicographic min with early abort: evaluate the key triple by
         * triple and abandon the mapping as soon as it exceeds the current
         * best (identical result, ~10-40x fewer osign evaluations) */
        if (!have_best) {
            for (int t = 0; t < T; t++) {
                int a = tri[n][t][0], b = tri[n][t][1], c = tri[n][t][2];
                best[t] = (signed char)osign(chi, n, mapping[a], mapping[b], mapping[c]);
            }
            have_best = 1;
        } else {
            int t = 0, cmp = 0;
            while (t < T) {
                int a = tri[n][t][0], b = tri[n][t][1], c = tri[n][t][2];
                key[t] = (signed char)osign(chi, n, mapping[a], mapping[b], mapping[c]);
                if (key[t] < best[t]) { cmp = -1; break; }
                if (key[t] > best[t]) { cmp = 1; break; }
                t++;
            }
            if (cmp < 0) {
                /* new best: finish the remaining triples and store */
                for (int t2 = t + 1; t2 < T; t2++) {
                    int a = tri[n][t2][0], b = tri[n][t2][1], c = tri[n][t2][2];
                    key[t2] = (signed char)osign(chi, n, mapping[a], mapping[b], mapping[c]);
                }
                memcpy(best, key, (size_t)T);
            }
            /* cmp == 0: key identical to best on all T — nothing to do   */
            /* cmp > 0: mapping strictly worse — abandoned early          */
        }
        if (it + 1 >= total) break;
        /* odometer advance: last group first; reset wrapped groups */
        int g = ngrp - 1;
        while (g >= 0) {
            if (next_perm(grp[g], grpn[g])) break;
            /* reset group g to ascending, carry */
            for (int i = 0; i < grpn[g]; i++)
                for (int j = i + 1; j < grpn[g]; j++)
                    if (grp[g][i] > grp[g][j]) {
                        int t2 = grp[g][i]; grp[g][i] = grp[g][j]; grp[g][j] = t2;
                    }
            g--;
        }
        {
            int pos = 0;
            for (int gg = 0; gg < ngrp; gg++)
                for (int q = 0; q < grpn[gg]; q++) mapping[pos++] = grp[gg][q];
        }
    }
    memcpy(out, best, (size_t)T);
    for (int g = 0; g < ngrp; g++) free(grp[g]);
}

/* ------------------------------------------------------------------ */
/* hex packing (shared convention with the python driver)              */
/* ------------------------------------------------------------------ */
/* python convention (engine107f5v4.py pack_signs/unpack_signs):
 * hex = format(bits, "0{nib}x") — the string is the BIG-ENDIAN hex of the
 * bits integer, i.e. nibble b (bits 4b..4b+3, b=0 lowest) is the character
 * at position (nbytes-1-b) of the string.                                  */
static void pack_hex(const signed char *s, int len, char *out) {
    static const char hx[] = "0123456789abcdef";
    int nbytes = (len + 3) / 4;
    for (int b = 0; b < nbytes; b++) {
        int v = 0;
        for (int q = 0; q < 4; q++) {
            int idx = b * 4 + q;
            int bit = (idx < len && s[idx] > 0) ? 1 : 0;
            v |= bit << q;
        }
        out[nbytes - 1 - b] = hx[v];
    }
    out[nbytes] = 0;
}
static int unpack_hex(const char *hex, signed char *s, int len) {
    int nbytes = (len + 3) / 4;
    for (int b = 0; b < nbytes; b++) {
        char c = hex[nbytes - 1 - b];
        int v;
        if (c >= '0' && c <= '9') v = c - '0';
        else if (c >= 'a' && c <= 'f') v = c - 'a' + 10;
        else return 0;
        for (int q = 0; q < 4; q++) {
            int idx = b * 4 + q;
            if (idx < len) s[idx] = ((v >> q) & 1) ? 1 : -1;
        }
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* the parent job                                                      */
/* ------------------------------------------------------------------ */
static int walk_steps = 6;
static unsigned long long seed_base = 1070707ULL;

typedef struct {
    int cells, formula_expected, formula_ok, generic;
    long conc_combos, conc_crossed, par_combos, par_crossed, grabs, walk_cfgs;
    int children, selfcheck_ok;
    double ms;
} JOBSTAT;

static signed char rp_ck[MAXTRI];
static signed char rp_ckstore[4096][MAXTRI];
static struct { uint64_t h; int slot; uint32_t g; } rp_e[8192];
static uint32_t rp_gen = 0;

static int run_parent(const char *key, int n, const signed char *chi_in,
                      const PT *pts_in, int parent_idx, JOBSTAT *st) {
    clock_t t0 = clock();
    build_tables(n); build_tables(n + 1);
    memset(st, 0, sizeof(*st));
    int P = npair[n];

    rng_state = seed_base ^ (0x9E3779B97F4A7C15ULL * (uint64_t)(parent_idx + 1));
    for (int i = 0; i < 4; i++) rng_next();

    static PT sh[MAXN], gen[MAXN];
    static int pts_inited = 0;
    if (!pts_inited) {
        for (int i = 0; i < MAXN; i++) { pt_init(&sh[i]); pt_init(&gen[i]); }
        pts_inited = 1;
    }
    int t = shear_distinct_x(pts_in, n, sh);
    if (t < 0) {
        fprintf(stderr, "FATAL: shear failed parent %s\n", key);
        return -1;
    }
    {
        static signed char c2[MAXTRI];
        chi_of_points(sh, n, c2);
        if (!chi_eq(c2, chi_in, ntri[n])) {
            fprintf(stderr, "FATAL: shear chi mismatch parent %s\n", key);
            return -1;
        }
    }
    int was_generic = 0;
    if (!make_arrangement_generic(sh, n, chi_in, gen, &was_generic)) {
        printf("#E %s GENERIC-FAIL\n", key);
        fflush(stdout);
        return 0;
    }
    st->generic = was_generic;

    /* S1: cells */
    CELLS cells;
    arrangement_cell_samples(gen, n, &cells, &st->formula_expected);
    st->cells = cells.n;
    st->formula_ok = (cells.n == st->formula_expected);

    U64SET current_svs; u64set_init(&current_svs, 1024); u64set_clear(&current_svs);
    signed char sv[MAXPAIR], chi9[MAXTRI];
    children_reset();
    for (int c = 0; c < cells.n; c++) {
        /* orient-based sv from line tope: orient sign = -line sign */
        for (int p = 0; p < P; p++)
            sv[p] = ((cells.topes[c] >> p) & 1) ? -1 : 1;
        uint64_t tp = 0;
        for (int p = 0; p < P; p++) if (sv[p] > 0) tp |= (1ULL << p);
        u64set_add(&current_svs, tp);
        chi_insert(chi_in, n, sv, chi9);
        static PT all[MAXN + 1];
        static int all_init = 0;
        if (!all_init) { for (int i = 0; i <= MAXN; i++) pt_init(&all[i]); all_init = 1; }
        for (int i = 0; i < n; i++) pt_set(&all[i], &gen[i]);
        pt_set(&all[n], &cells.pts[c]);
        children_add(chi9, ntri[n + 1], all, n + 1);
    }
    for (int i = 0; i < cells.n; i++) pt_clear(&cells.pts[i]);
    free(cells.pts); free(cells.topes);

    /* S2: sweep */
    SWEEPSTAT sw; memset(&sw, 0, sizeof(sw));
    sweep_parent(gen, n, chi_in, &current_svs, &sw);
    st->conc_combos = sw.conc_combos; st->conc_crossed = sw.conc_crossed;
    st->par_combos = sw.par_combos; st->par_crossed = sw.par_crossed;
    st->grabs = sw.grabs;

    /* S3: walk */
    st->walk_cfgs = walk_parent(gen, n, chi_in, walk_steps);

    /* self-check: every child chi == chi_of_points(coords) */
    st->selfcheck_ok = 1;
    {
        static signed char c9[MAXTRI];
        for (int c = 0; c < child_pool_n && st->selfcheck_ok; c++) {
            chi_of_points(child_pool[c].pts, n + 1, c9);
            if (!chi_eq(c9, child_pool[c].chi, ntri[n + 1])) st->selfcheck_ok = 0;
        }
    }

    /* canonicalize + dedup + emit */
    rp_gen++;
    if (rp_gen == 0) { memset(rp_e, 0, sizeof(rp_e)); rp_gen = 1; }
    char ckhex[64], chihex[64];
    int emitted = 0;
    for (int c = 0; c < child_pool_n; c++) {
        canonical_key(child_pool[c].chi, n + 1, rp_ck);
        uint64_t h = hash_bytes(rp_ck, (size_t)ntri[n + 1], 1469598103934665603ULL);
        int isdup = 0;
        for (int i = (int)(h & 8191); ; i = (i + 1) & 8191) {
            if (rp_e[i].g != rp_gen) break;
            if (memcmp(rp_ckstore[rp_e[i].slot], rp_ck, (size_t)ntri[n + 1]) == 0) {
                isdup = 1; break;
            }
        }
        if (isdup) continue;
        for (int i = (int)(h & 8191); ; i = (i + 1) & 8191) {
            if (rp_e[i].g != rp_gen) {
                rp_e[i].g = rp_gen; rp_e[i].slot = emitted;
                break;
            }
        }
        if (emitted >= 4096) { fprintf(stderr, "FATAL: ck store overflow\n"); exit(1); }
        memcpy(rp_ckstore[emitted], rp_ck, (size_t)ntri[n + 1]);
        pack_hex(rp_ck, ntri[n + 1], ckhex);
        pack_hex(child_pool[c].chi, ntri[n + 1], chihex);
        printf("T %s %s", ckhex, chihex);
        for (int p = 0; p <= n; p++) {
            printf(" ");
            mpq_out_str(stdout, 10, child_pool[c].pts[p].x);
            printf(" ");
            mpq_out_str(stdout, 10, child_pool[c].pts[p].y);
        }
        printf("\n");
        emitted++;
    }
    st->children = emitted;
    free(current_svs.keys); free(current_svs.gens);
    st->ms = (double)(clock() - t0) * 1000.0 / CLOCKS_PER_SEC;
    printf("#P %d %s n=%d cells=%d formula=%d generic=%d conc=%ld/%ld par=%ld/%ld "
           "sweep_grabs=%ld walk=%ld children=%d selfcheck=%d t=%.1fms\n",
           parent_idx, key, n, st->cells, st->formula_ok, st->generic,
           st->conc_crossed, st->conc_combos, st->par_crossed, st->par_combos,
           st->grabs, st->walk_cfgs, st->children, st->selfcheck_ok, st->ms);
    fflush(stdout);
    return 1;
}

/* ------------------------------------------------------------------ */
/* main: batch processing                                              */
/* ------------------------------------------------------------------ */
int main(int argc, char **argv) {
    int canon_only = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--walk-steps") && i + 1 < argc) walk_steps = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--seed") && i + 1 < argc) seed_base = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--canon-only")) canon_only = 1;
    }
    scratch_init();
    for (int n = 3; n <= 9; n++) build_tables(n);
    static char line[65536];
    if (canon_only) {
        /* each input line: "K <n> <chihex>" -> output "CK <chihex> <ckhex>" */
        static signed char chi[MAXTRI], ck[MAXTRI];
        while (fgets(line, sizeof(line), stdin)) {
            if (line[0] == '#' || line[0] == '\n') continue;
            char chex[128];
            int n;
            if (sscanf(line, "K %d %127s", &n, chex) != 2) continue;
            if (!unpack_hex(chex, chi, ntri[n])) continue;
            canonical_key(chi, n, ck);
            char ckhex[64];
            pack_hex(ck, ntri[n], ckhex);
            printf("CK %s %s\n", chex, ckhex);
        }
        fflush(stdout);
        return 0;
    }
    int idx = 0;
    while (fgets(line, sizeof(line), stdin)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (line[0] != 'P') { fprintf(stderr, "FATAL: bad input line: %s", line); return 1; }
        char key[128], chihex[128];
        int n;
        if (sscanf(line, "P %127s %d %127s", key, &n, chihex) != 3) {
            fprintf(stderr, "FATAL: bad P line: %s", line); return 1;
        }
        if (n < 3 || n > 8) { fprintf(stderr, "FATAL: n=%d out of range\n", n); return 1; }
        signed char chi[MAXTRI];
        if (!unpack_hex(chihex, chi, ntri[n])) {
            fprintf(stderr, "FATAL: bad chi hex %s\n", chihex); return 1;
        }
        PT pts[MAXN];
        for (int i = 0; i < MAXN; i++) pt_init(&pts[i]);
        int ok = 1;
        for (int i = 0; i < n && ok; i++) {
            if (!fgets(line, sizeof(line), stdin)) { ok = 0; break; }
            char xs[512], ys[512];
            if (sscanf(line, "%511s %511s", xs, ys) != 2) { ok = 0; break; }
            if (mpq_set_str(pts[i].x, xs, 10) != 0 ||
                mpq_set_str(pts[i].y, ys, 10) != 0) {
                fprintf(stderr, "FATAL: bad rational %s %s\n", xs, ys); return 1;
            }
            mpq_canonicalize(pts[i].x); mpq_canonicalize(pts[i].y);
        }
        if (!ok) { fprintf(stderr, "FATAL: truncated parent %s\n", key); return 1; }
        JOBSTAT st;
        int rc = run_parent(key, n, chi, pts, idx, &st);
        if (rc < 0) return 1;
        idx++;
        for (int i = 0; i < MAXN; i++) pt_clear(&pts[i]);
    }
    return 0;
}
