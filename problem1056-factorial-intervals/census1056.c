/* THE 1056 CENSUS (independent verification engine, C, exhaustive).
 * For every prime q <= LIMIT: compute the prefix-factorial chain
 * f_j = j! mod q for j = 1..q-1 (cut-point range of the structure law),
 * and M(q) := max over values v of #{j in [1,q-1] : j! = v (mod q)}.
 * Output census1056.txt: one line "q M argmaxvalue" per prime, plus full
 * CHAIN lines for every prime with M >= 12 (the k>=11-class chains).
 * ALERT on stderr for any M >= 13 (a k=12 witness candidate). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LIMIT 200000

static char comp[LIMIT + 1];
static unsigned short cnt[LIMIT];

int main(void) {
    for (long i = 2; i * i <= LIMIT; i++)
        if (!comp[i])
            for (long j = i * i; j <= LIMIT; j += i) comp[j] = 1;

    FILE *out = fopen("census1056.txt", "w");
    if (!out) { fprintf(stderr, "open failed\n"); return 1; }
    long firstEQ[64], firstGE[64];
    for (int m = 0; m < 64; m++) { firstEQ[m] = 0; firstGE[m] = 0; }

    for (long q = 2; q <= LIMIT; q++) {
        if (comp[q]) continue;
        int M; long arg;
        if (q == 2) { M = 1; arg = 1; }          /* j in [1,1]: 1! mod 2 = 1 */
        else {
            memset(cnt, 0, (size_t)q * sizeof(unsigned short));
            long f = 1;
            for (long j = 1; j <= q - 1; j++) { f = (f * j) % q; cnt[f]++; }
            M = 0; arg = 1;
            for (long v = 1; v < q; v++) if (cnt[v] > M) { M = cnt[v]; arg = v; }
        }
        fprintf(out, "%ld %d %ld\n", q, M, arg);
        if (M < 64) {
            for (int m = 2; m <= M; m++) if (!firstGE[m]) firstGE[m] = q;
            if (!firstEQ[M]) firstEQ[M] = q;
        }
        if (M >= 12) {
            fprintf(out, "CHAIN %ld value %ld M=%d:", q, arg, M);
            long f = 1;
            for (long j = 1; j <= q - 1; j++) {
                f = (f * j) % q;
                if (f == arg) fprintf(out, " %ld", j);
            }
            fprintf(out, "\n");
        }
        if (M >= 13) fprintf(stderr, "ALERT k=12 candidate prime %ld M=%d\n", q, M);
    }
    fclose(out);
    printf("m : first prime with M==m : first prime with M>=m\n");
    for (int m = 2; m < 64; m++)
        if (firstEQ[m] || firstGE[m])
            printf("m=%2d  firstEQ=%7ld  firstGE=%7ld\n", m, firstEQ[m], firstGE[m]);
    return 0;
}
