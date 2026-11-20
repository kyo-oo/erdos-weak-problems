/* ENGINE-142 TABLE V3 (W77-142E) — general-k branch-and-bound for r_k(N),
 * k in {3,4,5}, N <= 64.  Fresh code, extends the banked bnb142.c (W76,
 * k=3-only) to the 4-AP and 5-AP clauses with the CONSECUTIVE-PREFIX
 * EXCLUSION rule (derived + argued complete/sound this wave):
 *
 *   Recursion over vertices 0..N-1 in increasing order (translation
 *   symmetry: WLOG 0 in A — A - min(A) is k-AP-free, same size, contains 0).
 *   A k-AP (A_0, ..., A_{k-1}) (increasing, step d > 0) can only be violated
 *   when its LARGEST element A_{k-1} is taken; it must therefore be marked
 *   excluded at the moment its second-largest element A_{k-2} is taken — at
 *   which instant every smaller member A_0..A_{k-3} is already decided and
 *   (if the AP is ever completed) taken.  The prefix A_0..A_{k-2} is a
 *   consecutive (k-1)-term arithmetic progression, so the marking rule is:
 *
 *     k=3: taking v, for every p in S with v = 2p'... — v extends the
 *          1-term prefix {p}: mark 2v - p            (the banked rule)
 *     k=4: taking v, for every pair p<q in S with v = 2q - p
 *          (v extends the 2-term prefix (p,q)): mark 3q - 2p
 *     k=5: taking v, for every triple p<q<r in S with r = 2q - p and
 *          v = 3q - 2p (v extends the consecutive 3-term prefix):
 *          mark 4q - 3p
 *
 *   Sound: every marked w completes a genuine integer k-AP with points all
 *   already chosen (the marked quadruple is (A_0..A_{k-2}, w), distinct,
 *   increasing).  Complete: every completed k-AP had its second-largest
 *   element taken while the full prefix sat in S, so its largest was marked.
 *
 *   Bound: count + popcount(available >= i) <= best -> prune.
 *
 * Usage: ./bnb142v3 K N_lo N_hi      (env BNB142V3_NOFORCE=1 -> no 0-break)
 * Prints one JSON line per N.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int N, K;
static uint64_t fullMask;
static uint64_t best_mask; static int best;
static unsigned long long nodes;
static int witness[64], nwit;
static int S[64], nS;

static inline int popcount64(uint64_t x){ return __builtin_popcountll(x); }

static void rec(int i, int count, uint64_t Smask, uint64_t exclMask){
    nodes++;
    uint64_t geMask = (i >= 64) ? 0ULL : (~0ULL << i);   /* N=64 shift guard */
    uint64_t avail = ~exclMask & ~Smask & fullMask & geMask;
    if (count + popcount64(avail) <= best) return;
    if (i >= N){ if (count > best) { best = count; best_mask = Smask; } return; }
    if (!(exclMask >> i & 1ULL)) {
        uint64_t newExcl = exclMask;
        if (K == 3) {
            for (int t = 0; t < nS; t++) {
                long w = 2L * i - S[t];               /* i = A1, S[t] = A0 */
                if (w < N) newExcl |= 1ULL << w;      /* w > i always */
            }
        } else if (K == 4) {
            for (int a = 0; a < nS; a++)
                for (int b = a + 1; b < nS; b++) {
                    if (2 * S[b] - S[a] == i) {       /* (p,q,v)=(A0,A1,A2) */
                        long w = 3L * S[b] - 2L * S[a];
                        if (w >= 0 && w < N) newExcl |= 1ULL << w;
                    }
                }
        } else { /* K == 5 */
            for (int a = 0; a < nS; a++)
                for (int b = a + 1; b < nS; b++) {
                    int r2 = 2 * S[b] - S[a];          /* candidate A2 */
                    if (3 * S[b] - 2 * S[a] != i) continue;
                    for (int c = b + 1; c < nS; c++) {
                        if (S[c] == r2) {              /* (p,q,r) consecutive */
                            long w = 4L * S[b] - 3L * S[a];
                            if (w >= 0 && w < N) newExcl |= 1ULL << w;
                        }
                    }
                }
        }
        S[nS++] = i;
        rec(i + 1, count + 1, Smask | (1ULL << i), newExcl);
        nS--;
    }
    rec(i + 1, count, Smask, exclMask);
}

int main(int argc, char **argv){
    if (argc < 4){ fprintf(stderr, "usage: %s K N_lo N_hi\n", argv[0]); return 2; }
    K = atoi(argv[1]);
    int lo = atoi(argv[2]), hi = atoi(argv[3]);
    int force0 = getenv("BNB142V3_NOFORCE") ? 0 : 1;
    if (K < 3 || K > 5){ fprintf(stderr, "K in {3,4,5}\n"); return 2; }
    for (N = lo; N <= hi; N++){
        best = 0; best_mask = 0; nodes = 0; nS = 0;
        fullMask = (N >= 64) ? ~0ULL : ((1ULL << N) - 1ULL);
        struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
        if (force0 && N >= 1) {
            S[nS++] = 0;
            rec(1, 1, 1ULL, 0ULL);
            nS--;
        } else {
            rec(0, 0, 0ULL, 0ULL);
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double secs = (t1.tv_sec - t0.tv_sec) + 1e-9*(t1.tv_nsec - t0.tv_nsec);
        nwit = 0;
        for (int i = 0; i < N; i++) if (best_mask >> i & 1ULL) witness[nwit++] = i;
        printf("{\"K\":%d,\"N\":%d,\"value\":%d,\"nodes\":%llu,\"secs\":%.4f,"
               "\"forced0\":%s,\"witness_0based\":[",
               K, N, best, nodes, secs, force0 ? "true" : "false");
        for (int i = 0; i < nwit; i++) printf("%s%d", i ? "," : "", witness[i]);
        printf("]}\n");
        fflush(stdout);
    }
    return 0;
}
