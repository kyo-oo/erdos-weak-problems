/* Erdos Problem #261 — greedy walk engine (64-bit, exact).
 * Walk: (N, v): v' = 2v mod N, N' = N+1, start (n+1, n) [n>=2]; (3,2) for n=1.
 * v = 0 terminates: witness S = taken indices; a_k = last take + ... = N_stop.
 * Invariant theorem: v_N * 2 = n * 2^(N-n) - sum_{a in S_N} a * 2^(N-a).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
    uint64_t lo = strtoull(argv[1], 0, 10);
    uint64_t hi = strtoull(argv[2], 0, 10);
    uint64_t cap = argc > 3 ? strtoull(argv[3], 0, 10) : 400000000ULL;
    uint64_t nonterm = 0, total_steps = 0, worst_steps = 0, worst_n = 0;
    uint64_t ak_max = 0, ak_max_n = 0, k_max = 0;
    /* waterfall census: last-take position histogram for large streams */
    for (uint64_t n = lo; n <= hi; n++) {
        uint64_t N, v, steps = 0, takes = 0, last_take = 0;
        if (n == 1) { N = 3; v = 2; } else { N = n + 1; v = n; }
        while (v > 0 && steps < cap) {
            if (2*v >= N) { v = 2*v - N; takes++; last_take = N; }
            else v = 2*v;
            N++; steps++;
        }
        if (v != 0) {
            printf("NONTERMINATE n=%llu steps>=%llu\n",
                   (unsigned long long)n, (unsigned long long)steps);
            if (++nonterm > 5) break;
            continue;
        }
        total_steps += steps;
        if (steps > worst_steps) { worst_steps = steps; worst_n = n; }
        if (last_take > ak_max) { ak_max = last_take; ak_max_n = n; }
        if (takes > k_max) k_max = takes;
    }
    printf("RANGE %llu..%llu\n", (unsigned long long)lo, (unsigned long long)hi);
    printf("nonterm=%llu total_steps=%llu\n", (unsigned long long)nonterm, (unsigned long long)total_steps);
    printf("worst: n=%llu steps=%llu  a_k_max=%llu (n=%llu)  k_max=%llu\n",
        (unsigned long long)worst_n, (unsigned long long)worst_steps,
        (unsigned long long)ak_max, (unsigned long long)ak_max_n, (unsigned long long)k_max);
    return 0;
}
