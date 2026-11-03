/* verify_dump.c — WAR-271 task 2-d: independent verifier for a Stanley dump.
 *
 * Given a member-list file for S(0,t) on [0,N) (ascending, one per line),
 * verify the EXACT greedy characterization:
 *   (1) list strictly ascending, first two entries 0 and t, none in (0,t),
 *       all values < N;
 *   (2) AP-FREENESS: no pair a < b of members has 2b - a a member;
 *   (3) MAXIMALITY: every non-member n in (t, N) is blocked, i.e. 2b - a = n
 *       for some member pair a < b (note a < b < n is automatic).
 * (1)+(2)+(3) imply by induction that the list IS the greedy Stanley
 * sequence S(0,t) ∩ [0,N):  seeds force the base, AP-freeness keeps every
 * listed member admissible, maximality rejects every unlisted candidate.
 *
 * The mark pass recomputes the engine's `marks` count (pairs (a,b) with
 * 2b-a < N) — it must equal the engine's printed nmark.
 *
 * Usage: ./verify_dump dump.txt t N
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef uint64_t u64;
typedef uint32_t u32;

static inline int getbit(const u64 *B, u64 i) { return (int)((B[i >> 6] >> (i & 63)) & 1ULL); }
static inline void setbit(u64 *B, u64 i)      { B[i >> 6] |= 1ULL << (i & 63); }

int main(int argc, char **argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s dump.txt t N\n", argv[0]); return 2; }
    const u32 t = (u32)strtoul(argv[2], NULL, 10);
    const u64 N = strtoull(argv[3], NULL, 10);

    /* load list */
    FILE *f = fopen(argv[1], "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 1; }
    size_t cap = 1 << 20, cnt = 0;
    u32 *mem = malloc(cap * sizeof(u32));
    if (!mem) { return 1; }
    u64 v;
    while (fscanf(f, "%llu", (unsigned long long *)&v) == 1) {
        if (cnt == cap) { cap *= 2; mem = realloc(mem, cap * sizeof(u32)); if (!mem) return 1; }
        mem[cnt++] = (u32)v;
    }
    fclose(f);

    /* (1) structural checks */
    int fail = 0;
    if (cnt < 2) { printf("FAIL: too few members\n"); return 1; }
    if (mem[0] != 0) { printf("FAIL: mem[0]=%u != 0\n", mem[0]); fail = 1; }
    if (mem[1] != t) { printf("FAIL: mem[1]=%u != t=%u\n", mem[1], t); fail = 1; }
    for (size_t i = 1; i < cnt; i++)
        if (mem[i] <= mem[i-1]) { printf("FAIL: not ascending at %zu\n", i); fail = 1; }
    for (size_t i = 2; i < cnt && mem[i] < t; i++)
        if (mem[i] < t) { printf("FAIL: member %u in (0,t)\n", mem[i]); fail = 1; }
    if (mem[cnt-1] >= N) { printf("FAIL: max member %u >= N\n", mem[cnt-1]); fail = 1; }
    if (fail) return 1;

    /* bitset */
    const u64 words = (N + 63) / 64;
    u64 *member  = calloc(words, 8);
    u64 *blocked = calloc(words, 8);
    if (!member || !blocked) { fprintf(stderr, "OOM\n"); return 1; }
    for (size_t i = 0; i < cnt; i++) {
        if (getbit(member, mem[i])) { printf("FAIL: duplicate %u\n", mem[i]); return 1; }
        setbit(member, mem[i]);
    }

    /* (2)+(3) mark pass over all member pairs (a,b), a < b, 2b-a < N */
    u64 marks = 0, aps = 0;
    for (size_t j = 1; j < cnt; j++) {
        const u64 b = mem[j], base = 2 * b;
        if (base >= N + (u64)mem[0]) { /* need a > 2b - N */ }
        size_t lo = 0, hi = j - 1;     /* search a in mem[0..j-1], need a > 2b-N */
        if (base > N) {
            const u64 amin = base - N;
            while (lo < hi) { const size_t mid = (lo + hi) / 2;
                if (mem[mid] > amin) hi = mid; else lo = mid + 1; }
            if (mem[lo] <= amin) lo = j;   /* no admissible a */
        }
        for (size_t i = lo; i < j; i++) {
            const u64 m = base - mem[i];   /* > b, < N */
            if (getbit(member, m)) {
                if (aps < 5) printf("FAIL: 3-AP (%llu,%llu,%llu)\n",
                    (unsigned long long)mem[i], (unsigned long long)b,
                    (unsigned long long)m);
                aps++;
            }
            if (!getbit(blocked, m)) setbit(blocked, m);
            marks++;
        }
    }

    /* maximality: every non-member n in (t,N) must be blocked */
    u64 unblocked = 0, firstun = 0;
    for (u64 n = t + 1; n < N; n++)
        if (!getbit(member, n) && !getbit(blocked, n)) {
            if (!unblocked) firstun = n;
            unblocked++;
            if (unblocked >= 5) break;
        }

    printf("verify %s t=%u N=%llu: members=%zu marks=%llu aps=%llu unblocked=%llu",
           argv[1], t, (unsigned long long)N, cnt,
           (unsigned long long)marks, (unsigned long long)aps,
           (unsigned long long)unblocked);
    if (unblocked) printf(" (first unblocked: %llu)", (unsigned long long)firstun);
    printf("\n%s\n", (aps == 0 && unblocked == 0) ? "VERIFY PASS" : "VERIFY FAIL");
    free(member); free(blocked); free(mem);
    return (aps == 0 && unblocked == 0) ? 0 : 1;
}
