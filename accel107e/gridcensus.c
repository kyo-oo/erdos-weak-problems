
/* gridcensus m n mirror outprefix — W75-107E staged exact census.
   DFS over ALL GP n-subsets of the m*m grid ((y,x) index order) — every GP
   n-subset of the grid is visited (per-grid completeness is EXACT).
   Per leaf: KEY = chirotope bits under the (y,x)-sorted labeling (<=56 bits).
     key-hit  => same labeled chirotope => same order type => skip.
     key-miss => INV layer: canon = (hullsize, sorted multiset of point
        signatures), the lexicographically least of itself and its mirror in
        mirror mode; buckets are hash-chained on canon.  canon unseen =>
        provably a NEW order type (canon is type-determined).
        canon seen => per-rep PAIRINV prefilter (sorted multiset of pair
        left-counts, mirror-min form when mirroring) then the EXACT
        class-consistent relabeling search (mirror mode: sign-flipped too).
   Work-budget overflow inside one exact search is never silently resolved:
   the candidate is DUMPED (grid indices) to outprefix.unresolved for exact
   offline resolution, so the emitted types count is a certified LOWER bound
   on the true grid count (never an overcount); the Python parent resolves
   every dump exactly, restoring exactness.
   Emits one representative grid-index subset per order type (outprefix.reps).
   All arithmetic exact integers; no floats. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int N, DEPTH, *PX, *PY, MIRROR;
static unsigned long long *lmask;
static signed char *sgn;              /* N*N*N in {-1,0,+1} */
static long long leaves = 0, nodes = 0, keyhits = 0, keymiss = 0;
static long long newsame = 0, invnew = 0, permchk = 0, overflows = 0, ndump = 0;

typedef unsigned char u8;
/* ---- key table (open addressing, keys stored +1 so 0 = empty) ---- */
#define KBITS 27
#define KCAP (1ULL<<KBITS)
static unsigned long long *ktab;
static long long kcount = 0; static int ksat = 0;

static int khit_ins(unsigned long long key) {
    unsigned long long h = (key * 0x9E3779B97F4A7C15ULL) & (KCAP - 1);
    for (;;) {
        unsigned long long v = ktab[h];
        if (v == 0) {
            if (kcount >= (long long)(KCAP * 0.7)) { ksat = 1; return 0; }
            ktab[h] = key + 1; kcount++; return 0;
        }
        if (v == key + 1) return 1;
        h = (h + 1) & (KCAP - 1);
    }
}

/* ---- signature machinery ----
   sig string per point: 1 hull byte + (n-1) sorted left-count bytes. */
static int sig_len;
static void point_sig(const int *idx, int p, int flip, u8 *out) {
    int n = DEPTH, cnt[16], c = 0;
    for (int q = 0; q < n; q++) {
        if (q == p) continue;
        int v = 0;
        for (int r = 0; r < n; r++) {
            if (r == p || r == q) continue;
            int s = sgn[((size_t)idx[p] * N + idx[q]) * N + idx[r]] * flip;
            if (s > 0) v++;
        }
        cnt[c++] = (u8)v;
    }
    for (int i = 1; i < c; i++) { int x = cnt[i], j = i - 1;
        while (j >= 0 && cnt[j] > x) { cnt[j+1] = cnt[j]; j--; } cnt[j+1] = x; }
    out[0] = 0; /* hull byte filled by caller */
    for (int i = 0; i < c; i++) out[1 + i] = (u8)cnt[i];
}

/* hull of the chosen subset: monotone chain over indices, sign lookups */
static int hull_of(const int *idx, u8 *ishull) {
    int n = DEPTH, ord[16];
    for (int i = 0; i < n; i++) ord[i] = i;
    for (int i = 1; i < n; i++) { int t = ord[i], j = i - 1;
        while (j >= 0 && (PX[idx[ord[j]]] > PX[idx[t]] ||
               (PX[idx[ord[j]]] == PX[idx[t]] && PY[idx[ord[j]]] > PY[idx[t]])))
            { ord[j+1] = ord[j]; j--; } ord[j+1] = t; }
    int st[32], top = 0;
    for (int i = 0; i < n; i++) {
        while (top >= 2 && sgn[((size_t)idx[st[top-2]]*N+idx[st[top-1]])*N+idx[ord[i]]] <= 0) top--;
        st[top++] = ord[i];
    }
    for (int i = 0; i < n; i++) ishull[i] = 0;
    for (int i = 0; i < top; i++) ishull[st[i]] = 1;
    top = 0;
    for (int i = n - 1; i >= 0; i--) {
        while (top >= 2 && sgn[((size_t)idx[st[top-2]]*N+idx[st[top-1]])*N+idx[ord[i]]] <= 0) top--;
        st[top++] = ord[i];
    }
    for (int i = 0; i < top; i++) ishull[st[i]] = 1;
    int h = 0; for (int i = 0; i < n; i++) h += ishull[i];
    return h;
}

/* ---- buckets: hash-chained on canon bytes ---- */
typedef struct { u8 idx[16]; u8 sig[16][24]; int hull; u8 pairinv[128]; int pairlen; } Rep;
typedef struct Bucket { u8 *canon; int canonlen; unsigned long long h;
                        Rep *reps; int rn, rcap; struct Bucket *next; } Bucket;
static Bucket *htab[1 << 16];

static unsigned long long fnv(const u8 *b, int len) {
    unsigned long long h = 1469598103934665603ULL;
    for (int i = 0; i < len; i++) { h ^= b[i]; h *= 1099511628211ULL; }
    return h;
}

static int memeq(const u8 *a, const u8 *b, int n) { return memcmp(a, b, n) == 0; }

static void sort_bytes(u8 *a, int c) {
    for (int i = 1; i < c; i++) { u8 x = a[i]; int j = i - 1;
        while (j >= 0 && a[j] > x) { a[j+1] = a[j]; j--; } a[j+1] = x; }
}

/* pair invariant: sorted multiset over ordered pairs (p,q), p!=q, of
   leftcount(p,q) = #{r != p,q : orient(p,q,r) > 0}; in mirror mode the
   mirror-invariant min(c, n-2-c) form.  An order-type invariant (under
   relabeling, and under mirroring in mirror mode). */
static int pairinv_of(const int *idx, u8 *out) {
    int n = DEPTH, c = 0;
    for (int p = 0; p < n; p++)
        for (int q = 0; q < n; q++) {
            if (p == q) continue;
            int v = 0;
            for (int r = 0; r < n; r++) {
                if (r == p || r == q) continue;
                if (sgn[((size_t)idx[p]*N+idx[q])*N+idx[r]] > 0) v++;
            }
            if (MIRROR) { int m = (n - 2) - v; if (m < v) v = m; }
            out[c++] = (u8)v;
        }
    sort_bytes(out, c);
    return c;
}

static int inv_of(const int *idx, u8 *invout, int *invlen, u8 sigs[16][24],
                  u8 ishull[16], int *hullout) {
    int n = DEPTH;
    int hull = hull_of(idx, ishull);
    for (int p = 0; p < n; p++) {
        point_sig(idx, p, +1, sigs[p]);
        sigs[p][0] = ishull[p];
    }
    int ord[16];
    for (int i = 0; i < n; i++) ord[i] = i;
    for (int i = 1; i < n; i++) { int t = ord[i], j = i - 1;
        while (j >= 0 && memcmp(sigs[ord[j]], sigs[t], sig_len) > 0) { ord[j+1]=ord[j]; j--; }
        ord[j+1] = t; }
    int L = 0;
    invout[L++] = (u8)hull;
    for (int i = 0; i < n; i++) { memcpy(invout + L, sigs[ord[i]], sig_len); L += sig_len; }
    *invlen = L; *hullout = hull;
    return hull;
}

static FILE *unresf = NULL;
static void dump_unresolved(const int *chosen) {
    ndump++;
    if (!unresf) return;
    for (int i = 0; i < DEPTH; i++) fprintf(unresf, "%d%c", chosen[i], i+1<DEPTH?' ':'\n');
}

/* exact same-type search: class-consistent injective bijections rep->cand,
   chirotope equality under the assignment (flip = -1: mirrored candidate).
   Per-call work budget; returns 0 no, 1 yes, 2 overflow (never guessed). */
static int same_type(const Rep *rep, const int *cidx, const u8 csig[16][24], int flip) {
    int n = DEPTH, i, j, k;
    const long long budget = 30000;
    long long work = 0;
    int used[16], mp[16], ro[16];
    for (i = 0; i < n; i++) { used[i] = 0; mp[i] = -1; ro[i] = i; }
    for (i = 1; i < n; i++) { int t = ro[i], jj = i - 1;
        while (jj >= 0 && memcmp(rep->sig[ro[jj]], rep->sig[t], sig_len) > 0) { ro[jj+1]=ro[jj]; jj--; }
        ro[jj+1] = t; }
    int candTry[16][16], candN[16];
    for (int d = 0; d < n; d++) {
        int p = ro[d];
        candN[d] = 0;
        for (j = 0; j < n; j++)
            if (memeq(rep->sig[p], csig[j], sig_len))
                candTry[d][candN[d]++] = j;
        if (candN[d] == 0) return 0;
    }
    int pos[16], depth = 0;
    for (i = 0; i < n; i++) pos[i] = 0;
    while (depth >= 0) {
        if (depth == n) {
            if (++work > budget) { overflows++; return 2; }
            permchk++;
            int ok = 1;
            for (i = 0; i < n && ok; i++)
                for (j = i + 1; j < n && ok; j++)
                    for (k = j + 1; k < n && ok; k++) {
                        int a = rep->idx[i], b = rep->idx[j], c = rep->idx[k];
                        int A = cidx[mp[i]], B = cidx[mp[j]], C = cidx[mp[k]];
                        int s1 = sgn[((size_t)a*N+b)*N+c];
                        int s2 = sgn[((size_t)A*N+B)*N+C] * flip;
                        if (s1 != s2) ok = 0;
                    }
            if (ok) return 1;
            depth--;
            if (depth < 0) break;
            used[mp[ro[depth]]] = 0;
            pos[depth]++;
            continue;
        }
        int p = ro[depth];
        while (pos[depth] < candN[depth] && used[candTry[depth][pos[depth]]]) pos[depth]++;
        if (pos[depth] >= candN[depth]) {
            depth--;
            if (depth < 0) break;
            used[mp[ro[depth]]] = 0;
            pos[depth]++;
            continue;
        }
        int c = candTry[depth][pos[depth]];
        used[c] = 1; mp[p] = c;
        depth++;
        pos[depth] = 0;
    }
    return 0;
}

static void add_rep(Bucket *B, const int *chosen, u8 sigs[16][24], int hull,
                    const u8 *pairinv, int pairlen) {
    if (B->rn == B->rcap) { B->rcap *= 2; B->reps = realloc(B->reps, B->rcap * sizeof(Rep)); }
    Rep *R = &B->reps[B->rn++];
    R->hull = hull; R->pairlen = pairlen;
    memcpy(R->pairinv, pairinv, pairlen);
    for (int p = 0; p < DEPTH; p++) { R->idx[p] = (u8)chosen[p]; memcpy(R->sig[p], sigs[p], sig_len); }
    invnew++;
}

static void process_candidate(const int *chosen) {
    int n = DEPTH;
    u8 sigs[16][24], msigs[16][24], inv[400], minv[400], ishull[16];
    int invlen, minvlen, hull;
    inv_of(chosen, inv, &invlen, sigs, ishull, &hull);
    int canonlen = invlen; u8 *canon = inv;
    u8 pairinv[128]; int pairlen = pairinv_of(chosen, pairinv);
    if (MIRROR) {
        for (int p = 0; p < n; p++) {
            point_sig(chosen, p, -1, msigs[p]);
            msigs[p][0] = ishull[p];   /* hull membership is mirror-invariant */
        }
        int ord[16];
        for (int i = 0; i < n; i++) ord[i] = i;
        for (int i = 1; i < n; i++) { int t = ord[i], j = i - 1;
            while (j >= 0 && memcmp(msigs[ord[j]], msigs[t], sig_len) > 0) { ord[j+1]=ord[j]; j--; }
            ord[j+1] = t; }
        int L = 0;
        minv[L++] = (u8)hull;
        for (int i = 0; i < n; i++) { memcpy(minv + L, msigs[ord[i]], sig_len); L += sig_len; }
        minvlen = L;
        if (memcmp(minv, inv, invlen) < 0) { canon = minv; canonlen = minvlen; }
    }
    unsigned long long h = fnv(canon, canonlen);
    for (Bucket *B = htab[h & 0xFFFF]; B; B = B->next) {
        if (B->h != h || B->canonlen != canonlen || !memeq(B->canon, canon, canonlen)) continue;
        for (int r = 0; r < B->rn; r++) {
            Rep *R = &B->reps[r];
            if (R->hull == n && hull == n) { newsame++; return; } /* convex n-set: the unique convex type */
            if (R->pairlen != pairlen || !memeq(R->pairinv, pairinv, pairlen)) continue;
            int res = same_type(R, chosen, sigs, +1);
            if (res == 1) { newsame++; return; }
            if (res == 2) { dump_unresolved(chosen); return; }
            if (MIRROR) {
                res = same_type(R, chosen, msigs, -1);
                if (res == 1) { newsame++; return; }
                if (res == 2) { dump_unresolved(chosen); return; }
            }
        }
        add_rep(B, chosen, sigs, hull, pairinv, pairlen);  /* new type, known canon */
        return;
    }
    Bucket *B = malloc(sizeof(Bucket));
    B->canonlen = canonlen; B->canon = malloc(canonlen); memcpy(B->canon, canon, canonlen);
    B->h = h; B->rcap = 4; B->rn = 0; B->reps = malloc(4 * sizeof(Rep));
    B->next = htab[h & 0xFFFF]; htab[h & 0xFFFF] = B;
    add_rep(B, chosen, sigs, hull, pairinv, pairlen);      /* new canon = new type */
}

static void rec(int start, int depth, unsigned long long forbidden, int *chosen,
                unsigned long long key) {
    nodes++;
    if (depth == DEPTH) {
        leaves++;
        if (khit_ins(key)) { keyhits++; return; }
        keymiss++;
        int local[16];
        for (int i = 0; i < DEPTH; i++) local[i] = chosen[i];
        process_candidate(local);
        return;
    }
    for (int c = start; c < N; c++) {
        if (forbidden & (1ULL << c)) continue;
        unsigned long long nk = key;
        for (int i = 0; i < depth; i++)
            for (int j = i + 1; j < depth; j++) {
                int o = sgn[((size_t)chosen[i] * N + chosen[j]) * N + c];
                nk = (nk << 1) | (o > 0 ? 1ULL : 0ULL);
            }
        unsigned long long nf = forbidden;
        for (int i = 0; i < depth; i++) nf |= lmask[chosen[i] * N + c];
        chosen[depth] = c;
        rec(c + 1, depth + 1, nf, chosen, nk);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: %s m n mirror outprefix\n", argv[0]); return 2; }
    int m = atoi(argv[1]); DEPTH = atoi(argv[2]); MIRROR = atoi(argv[3]);
    N = m * m;
    if (N > 64) { fprintf(stderr, "m<=8 only (bitmask)\n"); return 2; }
    sig_len = 1 + (DEPTH - 1);
    PX = malloc(N * sizeof(int)); PY = malloc(N * sizeof(int));
    for (int y = 0; y < m; y++) for (int x = 0; x < m; x++) { int i = y*m+x; PX[i]=x; PY[i]=y; }
    sgn = calloc((size_t)N * N * N, 1);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) for (int c = 0; c < N; c++) {
        long long o = (long long)(PX[b]-PX[a])*(PY[c]-PY[a]) - (long long)(PY[b]-PY[a])*(PX[c]-PX[a]);
        sgn[((size_t)a*N+b)*N+c] = (signed char)((o > 0) - (o < 0));
    }
    lmask = calloc((size_t)N * N, sizeof(unsigned long long));
    for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++) {
        unsigned long long mk = 0;
        for (int c = 0; c < N; c++) {
            long long o = (long long)(PX[b]-PX[a])*(PY[c]-PY[a]) - (long long)(PY[b]-PY[a])*(PX[c]-PX[a]);
            if (o == 0) mk |= 1ULL << c;
        }
        lmask[a*N+b] = lmask[b*N+a] = mk;
    }
    ktab = calloc(KCAP, sizeof(unsigned long long));
    char path[512]; snprintf(path, sizeof path, "%s.unresolved", argv[4]);
    unresf = fopen(path, "w");
    int chosen[16];
    rec(0, 0, 0, chosen, 0);
    if (unresf) fclose(unresf);
    snprintf(path, sizeof path, "%s.reps", argv[4]);
    FILE *f = fopen(path, "w");
    long long types = 0; int nbuckets = 0;
    for (int b = 0; b < (1 << 16); b++)
        for (Bucket *B = htab[b]; B; B = B->next) {
            nbuckets++;
            for (int r = 0; r < B->rn; r++) {
                fprintf(f, "%lld", types++);
                for (int p = 0; p < DEPTH; p++) fprintf(f, " %d", (int)B->reps[r].idx[p]);
                fprintf(f, "\n");
            }
        }
    fclose(f);
    printf("RESULT m=%d n=%d mirror=%d subsets=%lld nodes=%lld keys=%lld ksat=%d "
           "keyhits=%lld keymiss=%lld types=%lld buckets=%d newsame=%lld invnew=%lld "
           "permchk=%lld overflows=%lld unresolved=%lld\n",
           m, DEPTH, MIRROR, leaves, nodes, kcount, ksat, keyhits, keymiss,
           types, nbuckets, newsame, invnew, permchk, overflows, ndump);
    return 0;
}
