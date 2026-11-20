/* WRAPSCAN-142 (W76-142E) — model-step NO-WRAP law, brute method (a).
 *
 * THE LAW. For prime p, a cyclic AP P(a,d,L) = {a + i*d mod p : i in [0,L)}
 * with L <= floor(sqrt(p)); every internal 3-AP of P (point triple
 * {x,y,z} subset P, x != z, x + z == 2y mod p) must be GENUINE in rescaled
 * coordinates: phi(x) + phi(z) = 2*phi(y) as INTEGERS, where
 * phi(t) = (t - a) * d^{-1} mod p is the rescaled coordinate.  For points
 * of P, phi(x_i) = i (the construction index), so the law reads: the index
 * triple satisfies 2*j = i + k in Z.
 *
 * THIS SCANNER works purely at the POINT level (never uses the index
 * algebra): for every d in [1,p) and every L in [L_lo,L_hi] it builds the
 * actual point set of P(0,d,L), scans EVERY endpoint pair (i,k), computes
 * the Z_p-midpoint of the actual residues, looks it up in the actual point
 * set, recovers the index, and checks 2*j == i+k as integers.  It also
 * counts original-coordinate wraps (x + z != 2*y as integers — allowed) and
 * rescaled wraps (2*j != i+k — FORBIDDEN by the law; must be 0 while
 * 2*(L-1) < p).  The a-translation invariance (internal 3-AP structure is
 * a-independent) is confirmed empirically on random a-samples.
 *
 * Barrett reduction (mu = floor(2^32/p)) replaces division in the hot loop.
 *
 * Usage: ./wrapscan142 p L_lo L_hi [n_a_sample] [seed] [d_limit_main] > out.jsonl
 * Output: one JSON line per (L) with counts aggregated over all d, plus
 *         sample lines and wrap examples.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static uint64_t P, INV2, MU;

static inline uint64_t barrett(uint64_t x){   /* x < p*p, returns x % p */
    uint64_t q = (uint64_t)(((unsigned __int128)x * MU) >> 32);
    uint64_t r = x - q * P;
    while (r >= P) r -= P;
    return r;
}

typedef struct {
    unsigned long long aps, orig_wraps, rescaled_wraps;
    unsigned long long per_d_min_aps, per_d_max_aps;   /* d-invariance of the count */
} Agg;

/* scan d in [1, d_limit] (d_limit=0 -> all d in [1,p)) for fixed a;
   aggregates per L in aggs[L - L_lo] */
static void sweep(uint64_t a, int L_lo, int L_hi, int L_abs_max,
                  uint64_t d_limit, Agg *aggs, unsigned long long *distinct_total,
                  unsigned long long *param_total,
                  long long *wrap_examples, int *n_wrap_examples, int cap_ex)
{
    uint32_t *stamp = calloc(P, sizeof(uint32_t));
    int32_t  *idxv  = calloc(P, sizeof(int32_t));
    uint32_t gen = 0;
    uint64_t *pts = malloc(L_abs_max * sizeof(uint64_t));
    uint64_t dmax = d_limit ? d_limit : (P - 1);
    for (uint64_t d = 1; d <= dmax; d++) {
        gen++;
        unsigned long long distinct = 0;
        uint64_t x = a % P;
        for (int i = 0; i < L_abs_max; i++) {
            pts[i] = x;
            if (stamp[x] != gen) { stamp[x] = gen; idxv[x] = i; distinct++; }
            else { fprintf(stderr, "DUPLICATE POINT p=%llu a=%llu d=%llu i=%d\n",
                           (unsigned long long)P, (unsigned long long)a,
                           (unsigned long long)d, i); exit(3); }
            x += d; if (x >= P) x -= P;
        }
        *distinct_total += distinct;
        for (int L = L_lo; L <= L_hi; L++) {
            Agg *g = &aggs[L - L_lo];
            unsigned long long aps_this_d = 0;
            for (int i = 0; i < L; i++) {
                for (int k = i + 1; k < L; k++) {
                    uint64_t s = pts[i] + pts[k];
                    if (s >= P) s -= P;
                    uint64_t y = barrett((uint64_t)s * INV2);
                    /* membership in P(0,d,L): marked AND index < L (the table
                       covers the full L_abs_max progression; sub-progression
                       membership requires idx < L) */
                    if (stamp[y] == gen && idxv[y] < L) {
                        int j = idxv[y];
                        aps_this_d++;
                        g->aps++;
                        if (2 * j != i + k) {
                            g->rescaled_wraps++;
                            if (*n_wrap_examples < cap_ex) {
                                long long *e = &wrap_examples[8 * (*n_wrap_examples)];
                                e[0]=(long long)a; e[1]=(long long)d; e[2]=L;
                                e[3]=i; e[4]=j; e[5]=k;
                                e[6]=(long long)pts[i]; e[7]=(long long)y;
                                (*n_wrap_examples)++;
                            }
                        } else if (pts[i] + pts[k] != 2 * (uint64_t)y) {
                            g->orig_wraps++;
                        }
                    }
                }
            }
            if (aps_this_d < g->per_d_min_aps) g->per_d_min_aps = aps_this_d;
            if (aps_this_d > g->per_d_max_aps) g->per_d_max_aps = aps_this_d;
            (*param_total)++;
        }
    }
    free(stamp); free(idxv); free(pts);
}

static uint64_t rnd(uint64_t *s){ *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }

int main(int argc, char **argv){
    if (argc < 4){ fprintf(stderr, "usage: %s p L_lo L_hi [n_a_sample] [seed]\n", argv[0]); return 2; }
    P = strtoull(argv[1], 0, 10);
    int L_lo = atoi(argv[2]), L_hi = atoi(argv[3]);
    int n_a_sample = (argc > 4) ? atoi(argv[4]) : 0;
    uint64_t seed = (argc > 5) ? strtoull(argv[5], 0, 10) : 20261120ULL;
    uint64_t d_limit_main = (argc > 6) ? strtoull(argv[6], 0, 10) : 0;
    INV2 = (P + 1) / 2;
    MU = (((unsigned __int128)1 << 32) / P);   /* Barrett magic */
    int L_abs_max = L_hi;
    Agg *aggs = calloc(L_hi - L_lo + 1, sizeof(Agg));
    for (int i = 0; i <= L_hi - L_lo; i++) aggs[i].per_d_min_aps = ~0ULL;

    unsigned long long distinct_total = 0, param_total = 0;
    long long wrap_examples[8 * 16]; int n_wrap_examples = 0;

    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    sweep(0, L_lo, L_hi, L_abs_max, d_limit_main, aggs, &distinct_total, &param_total,
          wrap_examples, &n_wrap_examples, 16);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double secs = (t1.tv_sec - t0.tv_sec) + 1e-9*(t1.tv_nsec - t0.tv_nsec);

    unsigned long long A = 0, OW = 0, RW = 0;
    for (int L = L_lo; L <= L_hi; L++){
        Agg *g = &aggs[L - L_lo]; A += g->aps; OW += g->orig_wraps; RW += g->rescaled_wraps;
    }
    printf("{\"p\":%llu,\"mode\":\"main-a0\",\"L_lo\":%d,\"L_hi\":%d,\"n_d\":%llu,"
           "\"parametrizations\":%llu,\"distinct_point_checks\":%llu,"
           "\"internal_3aps\":%llu,\"orig_wraps\":%llu,\"rescaled_wraps\":%llu,"
           "\"secs\":%.3f}\n",
           (unsigned long long)P, L_lo, L_hi,
           (unsigned long long)(d_limit_main ? d_limit_main : P - 1),
           param_total, distinct_total, A, OW, RW, secs);
    for (int L = L_lo; L <= L_hi; L++){
        Agg *g = &aggs[L - L_lo];
        printf("{\"p\":%llu,\"mode\":\"perL\",\"L\":%d,\"aps\":%llu,"
               "\"orig_wraps\":%llu,\"rescaled_wraps\":%llu,"
               "\"per_d_min_aps\":%llu,\"per_d_max_aps\":%llu}\n",
               (unsigned long long)P, L, g->aps, g->orig_wraps, g->rescaled_wraps,
               g->per_d_min_aps == ~0ULL ? 0 : g->per_d_min_aps, g->per_d_max_aps);
    }
    for (int e = 0; e < n_wrap_examples; e++){
        long long *w = &wrap_examples[8*e];
        printf("{\"p\":%llu,\"mode\":\"wrap_example\",\"a\":%lld,\"d\":%lld,\"L\":%lld,"
               "\"i\":%lld,\"j\":%lld,\"k\":%lld,\"x\":%lld,\"y\":%lld}\n",
               (unsigned long long)P, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
    }

    /* a-sample sweep: random a values, same L range, sampled d — confirms the
       a-translation invariance of the internal-3AP index structure (valid to
       compare against the a0 totals because the main sweep proves the count
       per (L,d) is d-independent: per_d_min_aps == per_d_max_aps) */
    if (n_a_sample > 0){
        uint64_t s = seed | 1;
        uint64_t dlim = P - 1;
        if (dlim > 200) dlim = 200;
        for (int t = 0; t < n_a_sample; t++){
            uint64_t a = rnd(&s) % P;
            Agg *aggs2 = calloc(L_hi - L_lo + 1, sizeof(Agg));
            for (int i = 0; i <= L_hi - L_lo; i++) aggs2[i].per_d_min_aps = ~0ULL;
            unsigned long long dt = 0, pt2 = 0; long long we[1]; int nwe = 0;
            sweep(a, L_lo, L_hi, L_abs_max, dlim, aggs2, &dt, &pt2, we, &nwe, 0);
            unsigned long long A2 = 0, RW2 = 0;
            int d_inv_ok = 1;
            for (int L = L_lo; L <= L_hi; L++){
                Agg *g = &aggs2[L - L_lo];
                A2 += g->aps;
                RW2 += g->rescaled_wraps;
                /* expected: per-d count (d-invariant) * dlim */
                if (g->aps != aggs[L - L_lo].per_d_max_aps * dlim) d_inv_ok = 0;
            }
            printf("{\"p\":%llu,\"mode\":\"a_sample\",\"a\":%llu,\"d_limit\":%llu,"
                   "\"internal_3aps\":%llu,\"rescaled_wraps\":%llu,"
                   "\"same_per_L_counts_as_a0\":%s}\n",
                   (unsigned long long)P, (unsigned long long)a,
                   (unsigned long long)dlim, A2, RW2,
                   d_inv_ok ? "true" : "false");
            free(aggs2);
        }
    }
    return 0;
}
