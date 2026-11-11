/* verify_dump_windowed.c — WAR-271 task 1-d: memory-bounded independent
 * verifier for a Stanley dump (built for k=21, where the default two-bitset
 * verify_dump.c would need 2 x 1.31 GB, and its NOMEMBER mode answers
 * membership by binary search PER MARK — O(marks log c), far too slow at
 * ~1.3e11 marks).
 *
 * Identical mathematical content to verify_dump.c, processed in windows of
 * 3^w.  For window [W0, W1):
 *   mwin = bitset of the dump's MEMBERS inside the window (offset by W0);
 *   bwin = bitset of marks m = 2b - a landing in the window (offset by W0);
 *   pair pass over EXACTLY the pairs (a, b), a < b members, with
 *   2b - a in [W0, W1)  <=>  a in [max(0, 2b-W1+1), min(b-1, 2b-W0)]:
 *       AP-freeness: m must not be a member (test mwin), else aps++;
 *       maximality:   set bwin at m; marks++.
 *   maximality scan: every non-member n in [max(W0, t+1), W1) must have
 *   bwin set, else unblocked++.
 * Every mark m = 2b - a satisfies m >= b + 1 >= t + 1, so the windows tiling
 * [0, N) partition the pair set exactly as verify_dump.c's single pass over
 * all pairs with m < N; marks/aps/members must reproduce verify_dump.c
 * EXACTLY (validated on the k=13, 18, 19, 20 dumps before use on k=21).
 * Note: the unblocked counter caps at 5 per window here (vs 5 per run in
 * verify_dump.c) — irrelevant for PASS runs (both require 0).
 *
 * Bonus consistency: windows covering [0, 3^20) must reproduce the k=20
 * verify marks (42,288,440,159), and window 0 alone the k=19 marks
 * (13,762,802,366) — prefix-stability of the greedy sequence.
 *
 * Memory: 2 x 3^w bits + member list (w=19: ~296 MB for N = 3^21).
 * Time: one pair-step per mark, same as verify_dump.c's mark pass.
 *
 * Usage: verify_dump_windowed dump.txt t N [w [wstart wend]]
 *   w = window exponent (window = 3^w), default 19;
 *   wstart..wend = run only these windows (default: all).  Partial runs
 *   print a PARTIAL line (chunked execution under tool-call time caps);
 *   a full-range run prints the exact verify_dump.c receipt lines.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t u64;
typedef uint32_t u32;

static inline int getbit(const u64 *B, u64 i) { return (int)((B[i >> 6] >> (i & 63)) & 1ULL); }
static inline void setbit(u64 *B, u64 i)      { B[i >> 6] |= 1ULL << (i & 63); }

/* first index in mem[0..n) with mem[idx] >= x  (n if none) */
static size_t lower_bound(const u64 *mem, size_t n, u64 x) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        const size_t mid = lo + (hi - lo) / 2;
        if (mem[mid] < x) lo = mid + 1; else hi = mid;
    }
    return lo;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s dump.txt t N [w [wstart wend]]\n", argv[0]); return 2; }
    setvbuf(stdout, NULL, _IOLBF, 0);
    const u32 t = (u32)strtoul(argv[2], NULL, 10);
    const u64 N = strtoull(argv[3], NULL, 10);
    int wexp = 19;
    if (argc > 4) { wexp = atoi(argv[4]); if (wexp < 1 || wexp > 40) { fprintf(stderr, "bad w\n"); return 2; } }
    u64 Delta = 1;
    for (int i = 0; i < wexp; i++) Delta *= 3;
    long wstart = 0, wend = -1;
    if (argc > 5) wstart = atol(argv[5]);
    if (argc > 6) wend = atol(argv[6]);

    /* ---- load list (as verify_dump.c) ---- */
    FILE *f = fopen(argv[1], "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 1; }
    size_t cap = 1 << 20, cnt = 0;
    u64 *mem = malloc(cap * sizeof(u64));
    if (!mem) { return 1; }
    u64 v;
    while (fscanf(f, "%llu", (unsigned long long *)&v) == 1) {
        if (cnt == cap) { cap *= 2; mem = realloc(mem, cap * sizeof(u64)); if (!mem) return 1; }
        mem[cnt++] = v;
    }
    fclose(f);

    /* ---- (1) structural checks (identical to verify_dump.c) ---- */
    int fail = 0;
    if (cnt < 2) { printf("FAIL: too few members\n"); return 1; }
    if (mem[0] != 0) { printf("FAIL: mem[0]=%llu != 0\n", (unsigned long long)mem[0]); fail = 1; }
    if (mem[1] != t) { printf("FAIL: mem[1]=%llu != t=%u\n", (unsigned long long)mem[1], t); fail = 1; }
    for (size_t i = 1; i < cnt; i++)
        if (mem[i] <= mem[i-1]) { printf("FAIL: not ascending at %zu\n", i); fail = 1; }
    for (size_t i = 2; i < cnt && mem[i] < t; i++)
        if (mem[i] < t) { printf("FAIL: member %llu in (0,t)\n", (unsigned long long)mem[i]); fail = 1; }
    if (mem[cnt-1] >= N) { printf("FAIL: max member %llu >= N\n", (unsigned long long)mem[cnt-1]); return 1; }
    if (fail) return 1;

    /* ---- windows ---- */
    const u64 nwin = (N + Delta - 1) / Delta;
    if (wstart < 0) wstart = 0;
    if (wend < 0 || (u64)wend >= nwin) wend = (long)nwin - 1;
    if ((u64)wstart >= nwin || wstart > wend) { fprintf(stderr, "bad window range 0..%llu\n", (unsigned long long)(nwin-1)); return 2; }
    const int full = (wstart == 0 && (u64)wend == nwin - 1);

    u64 marks = 0, aps = 0, unblocked = 0, firstun = 0, wmemsum = 0;
    for (long wi = wstart; wi <= wend; wi++) {
        const u64 W0 = (u64)wi * Delta;
        const u64 W1 = (W0 + Delta < N) ? W0 + Delta : N;
        const u64 len = W1 - W0;
        const u64 words = (len + 63) / 64;
        u64 *mwin = calloc(words, 8), *bwin = calloc(words, 8);
        if (!mwin || !bwin) { fprintf(stderr, "OOM window %ld\n", wi); return 1; }

        /* window member bitset */
        size_t wmem = 0;
        for (size_t j = lower_bound(mem, cnt, W0); j < cnt && mem[j] < W1; j++) {
            setbit(mwin, mem[j] - W0); wmem++;
        }
        wmemsum += wmem;

        /* pair pass: b over members with 2b >= W0 and b < W1 */
        u64 wmarks = 0, waps = 0;
        size_t j = lower_bound(mem, cnt, (W0 + 1) / 2);
        if (j == 0) j = 1;                       /* b = 0 has no earlier a */
        for (; j < cnt && mem[j] < W1; j++) {
            const u64 b = mem[j], base = 2 * b;
            u64 alo = 0, ahi = b - 1;            /* a in [alo, ahi], a < b */
            if (base + 1 > W1) alo = base - W1 + 1;      /* m < W1 */
            if (base - W0 < ahi) ahi = base - W0;        /* m >= W0 */
            if (alo > ahi) continue;
            size_t i = lower_bound(mem, j, alo);
            for (; i < j && mem[i] <= ahi; i++) {
                const u64 a = mem[i], m = base - a;      /* W0 <= m < W1, m > b */
                if (getbit(mwin, m - W0)) {
                    if (aps < 5) printf("FAIL: 3-AP (%llu,%llu,%llu)\n",
                        (unsigned long long)a, (unsigned long long)b, (unsigned long long)m);
                    aps++; waps++;
                }
                if (!getbit(bwin, m - W0)) setbit(bwin, m - W0);
                marks++; wmarks++;
            }
        }

        /* maximality: non-members in [max(W0,t+1), W1) must be blocked */
        u64 wunb = 0, wfirst = 0;
        const u64 nstart = (W0 > (u64)t + 1) ? W0 : (u64)t + 1;
        for (u64 n = nstart; n < W1; n++)
            if (!getbit(mwin, n - W0) && !getbit(bwin, n - W0)) {
                if (!wunb) wfirst = n;
                wunb++;
                if (wunb >= 5) break;
            }
        if (wunb && !unblocked) firstun = wfirst;
        unblocked += wunb;

        printf("window %ld [%llu,%llu): wmem=%zu marks=%llu aps=%llu unblocked=%llu\n",
               wi, (unsigned long long)W0, (unsigned long long)W1, wmem,
               (unsigned long long)wmarks, (unsigned long long)waps,
               (unsigned long long)wunb);
        if (wunb) printf("  first unblocked: %llu\n", (unsigned long long)wfirst);
        free(mwin); free(bwin);
    }

    if (wmemsum != (u64)cnt && full) { printf("FAIL: internal window-member sum %llu != %zu\n", (unsigned long long)wmemsum, cnt); return 1; }

    if (full) {
        printf("verify %s t=%u N=%llu: members=%zu marks=%llu aps=%llu unblocked=%llu",
               argv[1], t, (unsigned long long)N, cnt,
               (unsigned long long)marks, (unsigned long long)aps,
               (unsigned long long)unblocked);
        if (unblocked) printf(" (first unblocked: %llu)", (unsigned long long)firstun);
        printf("\n%s\n", (aps == 0 && unblocked == 0) ? "VERIFY PASS" : "VERIFY FAIL");
    } else {
        printf("PARTIAL %s t=%u N=%llu windows %ld..%ld of 0..%llu: members=%zu marks=%llu aps=%llu unblocked=%llu (%s)\n",
               argv[1], t, (unsigned long long)N, wstart, wend, (unsigned long long)(nwin - 1), cnt,
               (unsigned long long)marks, (unsigned long long)aps, (unsigned long long)unblocked,
               (aps == 0 && unblocked == 0) ? "clean so far" : "FAIL");
    }
    free(mem);
    return (aps == 0 && unblocked == 0) ? 0 : 1;
}
