/* ENGINE-142 TABLE V2 — independent branch-and-bound for r_3(N).
 * Fresh code (W76-142E), algorithmically distinct from the banked python bnb
 * (experiments/engine_rk.py): bitboard exclusion propagation + translation
 * symmetry (WLOG 0 in A: any AP-free A subset [0,N) translates down to a
 * same-size AP-free set containing 0).
 *
 * Recursion over vertices 0..N-1 in order. State: Smask (chosen), exclMask
 * (vertices that would complete a 3-AP (p,v,w), p<v<w, p,v chosen: marked
 * w = 2v - p at the time v is taken). Taking an excluded vertex is forbidden
 * (sound: it completes an AP; complete: any AP (a,b,w) completing at w has
 * its pair (a,b) chosen before w, so w was marked when b was taken).
 * Bound: count + popcount(available >= i) <= best  -> prune.
 *
 * Usage: ./bnb142 [N_lo N_hi]   (default: 1 48). Prints one JSON line per N:
 * {"N":..,"value":..,"nodes":..,"secs":..,"witness_0based":[..],"forced0":true}
 * Also supports no-force mode via env BNB142_NOFORCE=1 (cross-check).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int N;
static uint64_t fullMask;   /* bits 0..N-1 only (kills phantom vertices >= N) */
static uint64_t best_mask; static int best;
static unsigned long long nodes;
static int witness[64], nwit;

static inline int popcount64(uint64_t x){ return __builtin_popcountll(x); }

static void rec(int i, int count, uint64_t Smask, uint64_t exclMask){
    nodes++;
    /* available = vertices >= i not excluded (vertices < i already decided) */
    uint64_t avail = ~exclMask & ~Smask & fullMask & (~0ULL << i);
    if (count + popcount64(avail) <= best) return;
    if (i >= N){ if (count > best) { best = count; best_mask = Smask; } return; }
    if (!(exclMask >> i & 1ULL)) {
        /* take i: new exclusions w = 2i - p for p in S (w > i since p < i) */
        uint64_t newExcl = exclMask;
        uint64_t S = Smask;
        while (S) {
            int p = __builtin_ctzll(S); S &= S - 1;
            long w = 2L * i - p;
            if (w < N) newExcl |= 1ULL << w;
        }
        rec(i + 1, count + 1, Smask | (1ULL << i), newExcl);
    }
    rec(i + 1, count, Smask, exclMask);
}

int main(int argc, char **argv){
    int lo = 1, hi = 48, force0 = 1;
    if (argc >= 3){ lo = atoi(argv[1]); hi = atoi(argv[2]); }
    if (getenv("BNB142_NOFORCE")) force0 = 0;
    for (N = lo; N <= hi; N++){
        best = 0; best_mask = 0; nodes = 0;
        fullMask = (N >= 64) ? ~0ULL : ((1ULL << N) - 1ULL);
        struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
        if (force0 && N >= 1) {
            rec(1, 1, 1ULL, 0ULL);          /* WLOG 0 in A (translation) */
            /* also run the unforced search if the forced one somehow failed
               to find anything (only possible for N == 0) */
            if (best == 0 && N == 0) {}
        } else {
            rec(0, 0, 0ULL, 0ULL);
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double secs = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
        nwit = 0;
        for (int i = 0; i < N; i++) if (best_mask >> i & 1ULL) witness[nwit++] = i;
        printf("{\"N\":%d,\"value\":%d,\"nodes\":%llu,\"secs\":%.4f,\"forced0\":%s,\"witness_0based\":[",
               N, best, nodes, secs, force0 ? "true" : "false");
        for (int i = 0; i < nwit; i++) printf("%s%d", i ? "," : "", witness[i]);
        printf("]}\n");
        fflush(stdout);
    }
    return 0;
}
