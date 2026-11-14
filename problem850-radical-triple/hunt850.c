/* hunt850.c — Erdős Problem #850: length-3 radical-triple (Erdős–Woods length-3) witness hunt.
 *
 * TARGET: distinct x,y >= 1 with rad(x)=rad(y), rad(x+1)=rad(y+1), rad(x+2)=rad(y+2),
 *         where rad(n) = product of distinct prime factors of n.
 *
 * Design (full-range single-sweep at C speed, exact post-verification):
 *   1. Linear SPF sieve to N = X+2 (uint32 spf[]; every composite marked exactly once).
 *   2. Radical triples via rolling window (rad by SPF walk, optionally cached in
 *      a u32 radtab[] when RAM allows; rad(n) <= n <= 10^8+2 < 2^32 so u32 suffices).
 *   3. Packed 64-bit key: (hash(rad triple) & ~xmask) | x   with bx = bits for X
 *      (hash = splitmix64-style strong mix; any hash collision is re-verified exactly).
 *   4. In-place quicksort of the X packed keys (no auxiliary buffer -> peak RAM ~1.25 GB @ 1e8).
 *   5. Adjacent-equal-hash scan -> candidate pairs -> EXACT rad-triple re-verification.
 *      Sound & complete: equal rad triples => equal hash => adjacent after sort.
 *   6. Same machinery rerun for length-2 pairs (bonus evidence): key = hash(rad(x),rad(x+1)).
 *
 * usage: hunt850 X [-o outdir] [-cache] [-q]        (X >= 16)
 *        hunt850 -selftest                         (sort self-test vs qsort)
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef int64_t  i64;

static const char *outdir = ".";
static u64 X, N;              /* search bound X (pairs need both members <= X); N = X+2 */
static u32 *spf = NULL;       /* smallest prime factor, valid for n in [2..N] */
static u32 *primes = NULL;    /* prime list (for trial-division factorizations) */
static u64 pc = 0;
static u64 *pk = NULL;        /* packed keys, index 1..X */
static u32 *radtab = NULL;    /* optional radical cache, index 0..N */
static int bx = 0;            /* bits reserved for x inside the packed key */
static u64 xmask = 0;

static double nowt(void){
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static double maxrss_mb(void){
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss / 1024.0;
}
static void die(const char *msg){
    fprintf(stderr, "FATAL: %s\n", msg);
    exit(3);
}

/* splitmix64 finalizer */
static inline u64 sm64(u64 z){
    z += 0x9E3779B97F4A7C15ULL;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline u64 hash3(u32 r0, u32 r1, u32 r2){
    u64 h = sm64((u64)r0 * 0x100000001B3ULL + 1ULL);
    h = sm64(h ^ ((u64)r1 * 0xC2B2AE3D27D4EB4FULL));
    h = sm64(h ^ ((u64)r2 * 0x165667B19E3779F9ULL));
    return h;
}
static inline u64 hash2k(u32 r0, u32 r1){
    u64 h = sm64((u64)r0 * 0x9E3779B97F4A7C15ULL + 7ULL);
    h = sm64(h ^ ((u64)r1 * 0xD6E8FEB86659FD93ULL));
    return h;
}

/* ---------------- linear SPF sieve ---------------- */
static void build_spf(void){
    spf = (u32 *)calloc((size_t)N + 1, sizeof(u32));
    if (!spf) die("calloc spf failed");
    u64 cap = N / 12 + 2048;
    primes = (u32 *)malloc((size_t)cap * sizeof(u32));
    if (!primes) die("malloc primes failed");
    fprintf(stderr, "[alloc] spf %.1f MB (N=%llu), primes cap %.1f MB\n",
            (double)((size_t)N + 1) * 4.0 / 1e6, (unsigned long long)N,
            (double)cap * 4.0 / 1e6);
    pc = 0;
    for (u64 i = 2; i <= N; i++){
        u32 si = spf[i];
        if (si == 0){
            si = (u32)i;
            spf[i] = si;
            if (pc >= cap) die("prime capacity overflow");
            primes[pc++] = si;
        }
        for (u64 j = 0; j < pc; j++){
            u64 p = primes[j];
            u64 m = p * i;
            if (m > N) break;
            if (p > (u64)si) break;
            spf[m] = (u32)p;
            if (p == (u64)si) break;
        }
    }
}

/* ---------------- radicals ---------------- */
static inline u32 rad_walk(u32 n){
    u32 r = 1;
    while (n > 1){
        u32 p = spf[n];
        r *= p;
        do { n /= p; } while (n % p == 0);
    }
    return r;
}
static inline u32 rad_get(u32 n){
    return radtab ? radtab[n] : rad_walk(n);
}

/* ---------------- factorization printing ---------------- */
static void print_fact(u32 n){
    if (n <= 1){ printf("1"); return; }
    int first = 1;
    if (spf){
        while (n > 1){
            u32 p = spf[n];
            int e = 0;
            while (n % p == 0){ n /= p; e++; }
            if (!first) printf(" * ");
            first = 0;
            if (e == 1) printf("%u", p); else printf("%u^%d", p, e);
        }
    } else {
        u32 m = n;
        for (u64 j = 0; j < pc; j++){
            u32 p = primes[j];
            if (m <= 1) break;
            if ((u64)p * p > (u64)m) break;
            if (m % p == 0){
                int e = 0;
                while (m % p == 0){ m /= p; e++; }
                if (!first) printf(" * ");
                first = 0;
                if (e == 1) printf("%u", p); else printf("%u^%d", p, e);
            }
        }
        if (m > 1){
            if (!first) printf(" * ");
            printf("%u", m);
        }
    }
}

/* ---------------- in-place quicksort (u64 keys, no aux buffer) ---------------- */
static void insort(u64 *a, size_t n){
    for (size_t i = 1; i < n; i++){
        u64 v = a[i];
        size_t j = i;
        while (j > 0 && a[j-1] > v){ a[j] = a[j-1]; j--; }
        a[j] = v;
    }
}
static void my_qsort(u64 *a, size_t n){
    static size_t SLO[128], SHI[128];
    int sp = 0;
    if (n < 2) return;
    SLO[sp] = 0; SHI[sp] = n; sp++;
    while (sp > 0){
        sp--;
        size_t lo = SLO[sp], hi = SHI[sp];
        while (hi - lo > 32){
            size_t mid = lo + (hi - lo) / 2;
            u64 p1 = a[lo], p2 = a[mid], p3 = a[hi-1];
            if (p2 < p1){ u64 t = p2; p2 = p1; p1 = t; }
            if (p3 < p2){ u64 t = p3; p3 = p2; p2 = t; }
            if (p2 < p1){ u64 t = p2; p2 = p1; p1 = t; }
            u64 piv = p2;                     /* median-of-3 value (present in range) */
            i64 i = (i64)lo, j = (i64)hi - 1; /* Hoare partition */
            for (;;){
                while (a[i] < piv) i++;
                while (a[j] > piv) j--;
                if (i >= j) break;
                u64 t = a[i]; a[i] = a[j]; a[j] = t;
                i++; j--;
            }
            size_t cut = (size_t)(j + 1);
            if (cut <= lo || cut >= hi) die("sort partition degenerate");
            size_t llen = cut - lo, rlen = hi - cut;
            if (llen > rlen){
                if (sp >= 128) die("sort stack overflow");
                SLO[sp] = lo; SHI[sp] = cut; sp++;
                lo = cut;                       /* iterate on smaller right side */
            } else {
                if (sp >= 128) die("sort stack overflow");
                SLO[sp] = cut; SHI[sp] = hi; sp++;
                hi = cut;                       /* iterate on smaller left side */
            }
        }
        insort(a + lo, hi - lo);
    }
}
static int cmp_u64(const void *pa, const void *pb){
    u64 a = *(const u64 *)pa, b = *(const u64 *)pb;
    return (a < b) ? -1 : ((a > b) ? 1 : 0);
}

/* ---------------- self checks ---------------- */
static void self_checks(void){
    u64 lim = (N < 10000) ? N : 10000;
    int bad = 0;
    for (u64 n = 2; n <= lim; n++){
        u32 q = 0;
        for (u64 d = 2; d * d <= n; d++)
            if (n % d == 0){ q = (u32)d; break; }
        if (q == 0) q = (u32)n;
        if (spf[n] != q) bad++;
    }
    static const struct { u32 n, r; } R[] = {
        {2,2},{8,2},{48,6},{75,15},{1215,15},{960,30},{16128,42},{128,2},{720,30},{1024,2},{59049,3}
    };
    int badr = 0;
    for (size_t k = 0; k < sizeof R / sizeof R[0]; k++){
        if (R[k].n > N) continue;
        if (rad_walk(R[k].n) != R[k].r) badr++;
    }
    printf("[self-check] SPF vs trial division (n<=%llu): %s | rad spot values (rad(48)=6, rad(75)=15, rad(960)=30, rad(16128)=42, ...): %s\n",
           (unsigned long long)lim, bad ? "FAIL" : "PASS", badr ? "FAIL" : "PASS");
    if (bad || badr) die("self-check failed");
    fflush(stdout);
}

/* ---------------- length-3 hunt ---------------- */
static u64 l3_cand = 0, l3_true = 0, l3_false = 0;

static void report_l3_witness(u64 x, u64 y, u32 r0, u32 r1, u32 r2){
    printf("\n*** LENGTH-3 RADICAL-TRIPLE WITNESS (ERDOS #850) ***\n");
    printf("x = %llu   y = %llu   (x != y: %s, both >= 1)\n",
           (unsigned long long)x, (unsigned long long)y, (x != y && x >= 1 && y >= 1) ? "yes" : "NO-BUG");
    printf("rad(x)   = rad(y)   = %u\n", r0);
    printf("rad(x+1) = rad(y+1) = %u\n", r1);
    printf("rad(x+2) = rad(y+2) = %u\n", r2);
    printf("factorizations (SPF-sieve method):\n");
    printf("  x   = %10llu = ", (unsigned long long)x);     print_fact((u32)x);   printf("\n");
    printf("  x+1 = %10llu = ", (unsigned long long)(x+1)); print_fact((u32)(x+1)); printf("\n");
    printf("  x+2 = %10llu = ", (unsigned long long)(x+2)); print_fact((u32)(x+2)); printf("\n");
    printf("  y   = %10llu = ", (unsigned long long)y);     print_fact((u32)y);   printf("\n");
    printf("  y+1 = %10llu = ", (unsigned long long)(y+1)); print_fact((u32)(y+1)); printf("\n");
    printf("  y+2 = %10llu = ", (unsigned long long)(y+2)); print_fact((u32)(y+2)); printf("\n");
    char path[4096];
    snprintf(path, sizeof path, "%s/witness_details.txt", outdir);
    FILE *f = fopen(path, "w");
    if (f){
        fprintf(f, "PAIR %llu %llu\n", (unsigned long long)x, (unsigned long long)y);
        fprintf(f, "r0=%u r1=%u r2=%u\n", r0, r1, r2);
        fclose(f);
    }
    fflush(stdout);
}

static void phase_l3(void){
    double t0 = nowt();
    u32 r0 = rad_get(1), r1 = rad_get(2), r2 = rad_get(3);
    for (u64 x = 1; x <= X; x++){
        pk[x] = (hash3(r0, r1, r2) & ~xmask) | x;
        if (x + 3 <= N){
            u32 rn = rad_get((u32)(x + 3));
            r0 = r1; r1 = r2; r2 = rn;
        }
        if ((x & 0x3FFFFFFULL) == 0)
            fprintf(stderr, "[L3 pass] x=%llu\n", (unsigned long long)x);
    }
    double t1 = nowt();
    my_qsort(pk + 1, (size_t)X);
    double t2 = nowt();
    u64 i = 1;
    while (i <= X){
        u64 hh = pk[i] & ~xmask;
        u64 j = i + 1;
        while (j <= X && (pk[j] & ~xmask) == hh) j++;
        if (j - i > 1){
            for (u64 a = i; a < j; a++)
                for (u64 b = a + 1; b < j; b++){
                    u64 x1 = pk[a] & xmask, x2 = pk[b] & xmask;
                    l3_cand++;
                    u32 A0 = rad_get((u32)x1), A1 = rad_get((u32)x1 + 1), A2 = rad_get((u32)x1 + 2);
                    u32 B0 = rad_get((u32)x2), B1 = rad_get((u32)x2 + 1), B2 = rad_get((u32)x2 + 2);
                    if (A0 == B0 && A1 == B1 && A2 == B2){
                        l3_true++;
                        report_l3_witness(x1, x2, A0, A1, A2);
                    } else l3_false++;
                }
        }
        i = j;
    }
    double t3 = nowt();
    printf("[L3] pass %.2f s | sort %.2f s | scan+verify %.2f s | hash-collision candidate pairs: %llu | exact-verified TRUE: %llu | rejected hash collisions: %llu\n",
           t1 - t0, t2 - t1, t3 - t2,
           (unsigned long long)l3_cand, (unsigned long long)l3_true, (unsigned long long)l3_false);
    if (l3_true == 0)
        printf("[L3 VERDICT] NO length-3 radical-triple witness pair with both members in [1, %llu].\n",
               (unsigned long long)X);
    else
        printf("[L3 VERDICT] %llu WITNESS PAIR(S) FOUND — full details above and in witness_details.txt.\n",
               (unsigned long long)l3_true);
    fflush(stdout);
}

/* ---------------- length-2 bonus scan ---------------- */
static u64 l2_cand = 0, l2_count = 0, l2_beyond = 0;

static void phase_l2(void){
    double t0 = nowt();
    u32 r0 = rad_get(1), r1 = rad_get(2);
    for (u64 x = 1; x <= X; x++){
        pk[x] = (hash2k(r0, r1) & ~xmask) | x;
        if (x + 2 <= N){
            u32 rn = rad_get((u32)(x + 2));
            r0 = r1; r1 = rn;
        }
        if ((x & 0x3FFFFFFULL) == 0)
            fprintf(stderr, "[L2 pass] x=%llu\n", (unsigned long long)x);
    }
    double t1 = nowt();
    my_qsort(pk + 1, (size_t)X);
    double t2 = nowt();
    char path[4096];
    snprintf(path, sizeof path, "%s/length2_pairs.txt", outdir);
    FILE *f = fopen(path, "w");
    if (!f) die("cannot open length2_pairs.txt");
    int s_2_8 = 0, s_6_48 = 0, s_75_1215 = 0;
    u64 i = 1;
    while (i <= X){
        u64 hh = pk[i] & ~xmask;
        u64 j = i + 1;
        while (j <= X && (pk[j] & ~xmask) == hh) j++;
        if (j - i > 1){
            for (u64 a = i; a < j; a++)
                for (u64 b = a + 1; b < j; b++){
                    u64 x1 = pk[a] & xmask, x2 = pk[b] & xmask;
                    l2_cand++;
                    u32 A0 = rad_get((u32)x1), A1 = rad_get((u32)x1 + 1);
                    u32 B0 = rad_get((u32)x2), B1 = rad_get((u32)x2 + 1);
                    if (A0 == B0 && A1 == B1){
                        l2_count++;
                        int beyond = (x1 > 20000);
                        if (beyond) l2_beyond++;
                        fprintf(f, "%llu %llu %u %u\n",
                                (unsigned long long)x1, (unsigned long long)x2, A0, A1);
                        if (x1 == 2 && x2 == 8) s_2_8 = 1;
                        if (x1 == 6 && x2 == 48) s_6_48 = 1;
                        if (x1 == 75 && x2 == 1215) s_75_1215 = 1;
                        if (l2_count <= 12 || (beyond && l2_beyond <= 30))
                            printf("[L2 pair] x=%llu y=%llu rad(x)=rad(y)=%u rad(x+1)=rad(y+1)=%u%s\n",
                                   (unsigned long long)x1, (unsigned long long)x2, A0, A1,
                                   beyond ? "   << beyond 2*10^4" : "");
                    }
                }
        }
        i = j;
    }
    fclose(f);
    double t3 = nowt();
    printf("[L2] pass %.2f s | sort %.2f s | scan+verify %.2f s | candidates %llu | verified length-2 pairs: %llu (smaller member > 2*10^4: %llu)\n",
           t1 - t0, t2 - t1, t3 - t2,
           (unsigned long long)l2_cand, (unsigned long long)l2_count, (unsigned long long)l2_beyond);
    printf("[L2 sanity] (2,8):%s (6,48):%s (75,1215):%s   full list: %s/length2_pairs.txt\n",
           s_2_8 ? "FOUND" : "MISSING", s_6_48 ? "FOUND" : "MISSING",
           s_75_1215 ? "FOUND" : "MISSING", outdir);
    fflush(stdout);
}

/* ---------------- rad samples for sympy cross-check ---------------- */
static void emit_samples(void){
    char path[4096];
    snprintf(path, sizeof path, "%s/sample_rads.txt", outdir);
    FILE *f = fopen(path, "w");
    if (!f) return;
    u64 s = 0x9E3779B97F4A7C15ULL ^ X;
    for (int k = 0; k < 64; k++){
        s = sm64(s);
        u32 n = (u32)(1 + s % N);
        fprintf(f, "%u %u\n", n, rad_get(n));
    }
    fclose(f);
}

/* ---------------- sort self-test ---------------- */
static int selftest_main(void){
    srand(20240850);
    size_t cases[] = {0, 1, 2, 3, 7, 31, 32, 33, 100, 1000, 5000, 99999};
    for (int t = 0; t < 400; t++){
        size_t n = cases[t % 12];
        if (t >= 12) n = (size_t)(rand() % 3000);
        u64 *a = malloc((n ? n : 1) * sizeof(u64));
        u64 *b = malloc((n ? n : 1) * sizeof(u64));
        if (!a || !b) die("selftest malloc");
        int mode = t % 4;
        for (size_t k = 0; k < n; k++){
            u64 v;
            switch (mode){
                case 0:  v = ((u64)rand() << 32) | (u64)rand(); break; /* random 64 */
                case 1:  v = (u64)(rand() % 16); break;                /* duplicates */
                case 2:  v = (k % 7 == 0) ? 0xdeadbeefdeadbeefULL : (u64)k; break;
                default: v = (u64)(n - k); break;                      /* reverse sorted */
            }
            a[k] = v; b[k] = v;
        }
        my_qsort(a, n);
        qsort(b, n, sizeof(u64), cmp_u64);
        if (n && memcmp(a, b, n * sizeof(u64))){
            printf("sort selftest: FAIL (case %d, n=%zu)\n", t, n);
            return 1;
        }
        free(a); free(b);
    }
    printf("sort selftest: PASS (400 cases incl. duplicates / sorted / reverse-sorted)\n");
    return 0;
}

static void usage(void){
    fprintf(stderr, "usage: hunt850 X [-o outdir] [-cache] [-q] | hunt850 -selftest\n");
}

int main(int argc, char **argv){
    if (argc < 2){ usage(); return 1; }
    if (!strcmp(argv[1], "-selftest")) return selftest_main();
    X = strtoull(argv[1], NULL, 10);
    int do_l2 = 1, do_cache = 0;
    for (int i = 2; i < argc; i++){
        if (!strcmp(argv[i], "-q")) do_l2 = 0;
        else if (!strcmp(argv[i], "-cache")) do_cache = 1;
        else if (!strcmp(argv[i], "-o") && i + 1 < argc) outdir = argv[++i];
        else { usage(); return 1; }
    }
    if (X < 16) die("X must be >= 16");
    N = X + 2;
    bx = 0;
    while ((1ULL << bx) <= X) bx++;
    xmask = (1ULL << bx) - 1;

    printf("=== HUNT850 — Erdos problem #850: length-3 radical-triple (Erdos-Woods length-3) witness hunt ===\n");
    printf("X=%llu N=%llu bx=%d hash_bits=%d outdir=%s\n",
           (unsigned long long)X, (unsigned long long)N, bx, 64 - bx, outdir);
    double t0 = nowt();
    build_spf();
    double t1 = nowt();
    printf("[sieve] SPF linear sieve: %.2f s, primes: %llu\n", t1 - t0, (unsigned long long)pc);
    self_checks();
    if (do_cache){
        double tc = nowt();
        radtab = (u32 *)calloc((size_t)N + 1, sizeof(u32));
        if (radtab){
            for (u64 n = 1; n <= N; n++) radtab[n] = rad_walk((u32)n);
            free(spf); spf = NULL;
            printf("[radtab] cached radicals: %.2f s (spf freed; factorizations via trial division)\n",
                   nowt() - tc);
        } else {
            printf("[radtab] calloc failed — staying in streaming mode\n");
        }
        fflush(stdout);
    }
    pk = (u64 *)calloc((size_t)X + 1, sizeof(u64));
    if (!pk) die("calloc pk failed");
    fflush(stdout);
    phase_l3();
    if (do_l2) phase_l2();
    emit_samples();
    printf("[done] total %.2f s, peak RSS %.1f MB\n", nowt() - t0, maxrss_mb());
    return 0;
}
