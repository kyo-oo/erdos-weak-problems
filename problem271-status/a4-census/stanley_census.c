/* stanley_census.c — WAR-271 task 2-d: deep census engine for Stanley S(0,t).
 *
 * Convention (Erdos #271, OEIS A005487 for t=4; matches the Lean-proven
 * StanleyA2.lean oracle for t=2):
 *   a_0 = 0, a_1 = t, and for n = t+1, t+2, ... in increasing order, n
 *   joins the sequence iff there is NO 3-term AP (a, b, n) with a < b < n
 *   both earlier members (i.e. no pair with a + n = 2b).
 *
 * Engine (fast path): two bitsets of N bits (member, blocked) plus the
 * sorted member list.  When n joins, mark m = 2n - a for every earlier
 * member a (note m > n), so at inspection time blocked[n] = 1 exactly iff
 * some blocking pair of earlier members exists.  Cost: O(N) scan plus one
 * bit-set per unordered pair of members (m < N only); memory 2*N bits +
 * 4*|A| bytes.
 *
 * Built-in cross-checks (always on where applicable):
 *   - NAIVE recompute by direct per-candidate pair scan up to NAIVE_LIMIT
 *     (default min(N, 3^10); env NAIVE_LIMIT raises it); must agree with
 *     the fast path bit-for-bit.
 *   - For t=2: full-range verification against the Cantor digit predicate
 *     inD of StanleyA2.lean (A(2) = {3m+d : m in Cantor set, d in {0,2}}).
 *
 * Usage: ./stanley_census t N [members_out.txt]
 *   N = exclusive limit; census printed at every 3^k <= N.
 * Env: NOMEMBER=1 drops the `member` bitset (halves memory; disables the
 *      two bitset-based cross-checks) — used for the 3^20 run.
 *      NAIVE_LIMIT=L raises the naive cross-check range to min(N, L).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;
typedef int64_t  i64;
typedef uint32_t u32;

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline int getbit(const u64 *B, u64 i) { return (int)((B[i >> 6] >> (i & 63)) & 1ULL); }
static inline void setbit(u64 *B, u64 i)      { B[i >> 6] |= 1ULL << (i & 63); }

/* ---- Lean oracle inD for t=2 (StanleyA2.lean §1-§2) ---- */
static int noTwo_c(u64 m) {
    while (m) { if (m % 3 == 2) return 0; m /= 3; }
    return 1;
}
static int inD_c(u64 m) {
    if (m % 3 == 0 || m % 3 == 2) return noTwo_c(m / 3);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s t N [members_out.txt]\n", argv[0]);
        return 2;
    }
    const u32 t = (u32)strtoul(argv[1], NULL, 10);
    const u64 N = strtoull(argv[2], NULL, 10);
    const char *outpath = (argc > 3) ? argv[3] : NULL;
    if (t == 0 || N <= t) { fprintf(stderr, "bad args\n"); return 2; }

    const u64 words = (N + 63) / 64;
    /* NOMEMBER=1 drops the `member` bitset (halves memory; the main loop
       only needs `blocked` + the sorted list).  Used for the 3^20 run. */
    const int have_member = (getenv("NOMEMBER") == NULL);
    u64 *member  = have_member ? calloc(words, 8) : NULL;
    u64 *blocked = calloc(words, 8);
    if ((have_member && !member) || !blocked) { fprintf(stderr, "OOM bitsets\n"); return 1; }

    size_t cap = 1 << 20, cnt = 0;
    u32 *mem = malloc(cap * sizeof(u32));
    if (!mem) { fprintf(stderr, "OOM list\n"); return 1; }

    const double t0 = now_sec();
    u64 nmark = 0;

    /* seeds */
    if (member) setbit(member, 0);
    mem[cnt++] = 0;
    if (member) setbit(member, t);
    mem[cnt++] = t;
    { /* pair (0, t) blocks 2t */
        const u64 m = 2 * (u64)t;
        if (m < N) { setbit(blocked, m); nmark++; }
    }

    for (u64 n = t + 1; n < N; n++) {
        if (getbit(blocked, n)) continue;
        if (cnt == cap) { cap *= 2; mem = realloc(mem, cap * sizeof(u32));
                          if (!mem) { fprintf(stderr, "OOM grow\n"); return 1; } }
        mem[cnt++] = (u32)n;
        if (member) setbit(member, n);
        /* mark m = 2n - a for earlier members a; only m < N is useful.
           mem is ascending, so m = 2n - mem[i] descends with i: skip the
           head while m >= N, then set the rest. */
        const u64 base = 2 * n;
        size_t i = 0;
        /* skip members with 2n - a >= N  <=>  a <= 2n - N */
        if (base > N) {
            const u64 amin = base - N;             /* need a > amin */
            size_t lo = 0, hi = cnt - 1;           /* search in mem[0..cnt-2] */
            while (lo < hi) { const size_t mid = (lo + hi) / 2;
                if (mem[mid] > amin) hi = mid; else lo = mid + 1; }
            if (mem[lo] <= amin) i = cnt - 1; else i = lo;
        }
        for (; i < cnt - 1; i++) {
            const u64 m = base - mem[i];
            if (m < N) { setbit(blocked, m); nmark++; }
        }
    }
    const double t1 = now_sec();

    /* ---- census at powers of 3 ---- */
    printf("S(0,%u)  N=%llu  |A|=%zu  marks=%llu  time=%.2fs\n",
           t, (unsigned long long)N, cnt, (unsigned long long)nmark, t1 - t0);
    {
        u64 p = 1; int k = 0;
        printf("counts:");
        while (p <= N) {
            u64 c = 0; for (size_t j = 0; j < cnt && mem[j] < p; j++) c++;
            printf(" %llu", (unsigned long long)c);
            p *= 3; k++;
        }
        printf("   (k=0..%d)\n", k - 1);
    }

    /* ---- cross-check 1: naive pair-scan recompute ---- */
    {
        u64 M = (N < 59049) ? N : 59049;   /* min(N, 3^10); NAIVE_LIMIT overrides */
        { const char *e = getenv("NAIVE_LIMIT");
          if (e) { const u64 L = strtoull(e, NULL, 10); M = (N < L) ? N : L; } }
        if (M > t + 1 && have_member) {
            const u64 mw = (M + 63) / 64;
            u64 *mem2b = calloc(mw, 8);
            u32 *list2 = malloc(M * sizeof(u32));
            size_t c2 = 0;
            setbit(mem2b, 0); list2[c2++] = 0;
            setbit(mem2b, t); list2[c2++] = t;
            for (u64 n = t + 1; n < M; n++) {
                int blockedn = 0;
                for (size_t j = 0; j < c2 && !blockedn; j++) {
                    const u64 b = list2[j];
                    if (2 * b < n) continue;
                    const u64 a = 2 * b - n;
                    if (getbit(mem2b, a)) blockedn = 1;   /* a < b < n holds */
                }
                if (!blockedn) { setbit(mem2b, n); list2[c2++] = (u32)n; }
            }
            size_t bad = 0;
            for (u64 n = 0; n < M; n++)
                if (getbit(member, n) != getbit(mem2b, n)) bad++;
            printf("naive-crosscheck to %llu: %s (%zu mismatches)\n",
                   (unsigned long long)M, bad ? "FAIL" : "PASS", bad);
            free(mem2b); free(list2);
            if (bad) return 1;
        }
    }

    /* ---- cross-check 2: t=2 vs Lean Cantor predicate inD, full range ---- */
    if (t == 2 && have_member) {
        u64 bad = 0, badex = 0;
        for (u64 n = 0; n < N; n++) {
            const int want = inD_c(n), got = getbit(member, n);
            if (want != got) { bad++; if (badex < 10) { badex++; printf("  MISMATCH n=%llu inD=%d engine=%d\n", (unsigned long long)n, want, got); } }
        }
        printf("A(2)-inD full-range check to %llu: %s (%llu mismatches)\n",
               (unsigned long long)N, bad ? "FAIL" : "PASS", (unsigned long long)bad);
        if (bad) return 1;
    }

    /* ---- dump ---- */
    if (outpath) {
        FILE *f = fopen(outpath, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", outpath); return 1; }
        for (size_t j = 0; j < cnt; j++) fprintf(f, "%u\n", mem[j]);
        fclose(f);
        printf("members written: %s (%zu)\n", outpath, cnt);
    }

    free(member); free(blocked); free(mem);
    return 0;
}
