
/* noconvexk — decisive witness certification, three modes:
   file k            — one set: GP check (all C(n,3) triples) + NO convex-k
                       subset among ALL C(n,k) subsets (early exit on find).
   batch file k      — file: first line "nsets n"; then nsets blocks of n
                       points; per block GP + no-convex-k; summary.
   pattern wfile k pfile
                     — EXHAUSTIVE INSERTION-CELL CERTIFICATE.  wfile = the
                       n-point GP witness; pfile: one row per insertion CELL:
                       C(n,2) signs (+1/-1) — sign of orient(w_i, w_j, q) for
                       i<j — followed by n+1 integers: the (x,y)-sorted ORDER
                       of the n+1 points (witness positions 0..n-1, new point
                       = n).  Per row: build the (n+1)^3 sign tensor (witness
                       part from coordinates; mixed part from the pattern with
                       the antisymmetric/cyclic extension), then check ALL
                       C(n,k-1) k-subsets containing the new point for convex
                       position (hull via signs + the given order).  Covering
                       every cell covers EVERY GP insertion position (same
                       cell => same order type => same answer), so a green
                       batch says: witness + ANY (n+1)th point in GP contains
                       a convex k — the reduction step, exhaustively.
   __int128 orientation.  No floats anywhere. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef __int128 i128;
typedef long long ll;
typedef struct { ll x, y; } P;
static P p[128];
static signed char *sg; static ll n;
static ll NSG = 128;
static i128 orient3(P a, P b, P c) {
    return (i128)(b.x-a.x)*(c.y-a.y) - (i128)(b.y-a.y)*(c.x-a.x);
}
static int sgn_at(ll a, ll b, ll c) { return sg[(a*NSG+b)*NSG+c]; }
/* hull size of subset given by positions idx[0..k-1], with a global rank[]
   giving the (x,y) order of positions (rank smaller = earlier). */
static ll rank_[160];
static ll hullsize_ord(const ll *idx, ll k) {
    ll ord[64];
    for (ll i = 0; i < k; i++) ord[i] = i;
    for (ll i = 1; i < k; i++) { ll t = ord[i], j = i-1;
        while (j >= 0 && rank_[idx[ord[j]]] > rank_[idx[t]]) { ord[j+1]=ord[j]; j--; }
        ord[j+1]=t; }
    ll st[128], top = 0, hv[64]; for (ll i = 0; i < k; i++) hv[i] = 0;
    for (ll i = 0; i < k; i++) {
        while (top >= 2 && sgn_at(idx[st[top-2]], idx[st[top-1]], idx[ord[i]]) <= 0) top--;
        st[top++] = ord[i];
    }
    for (ll i = 0; i < top; i++) hv[st[i]] = 1;
    top = 0;
    for (ll i = k-1; i >= 0; i--) {
        while (top >= 2 && sgn_at(idx[st[top-2]], idx[st[top-1]], idx[ord[i]]) <= 0) top--;
        st[top++] = ord[i];
    }
    for (ll i = 0; i < top; i++) hv[st[i]] = 1;
    ll h = 0; for (ll i = 0; i < k; i++) h += hv[i];
    return h;
}
static ll hullsize(const ll *idx, ll k) {
    return hullsize_ord(idx, k);
}
/* rank the loaded witness positions by (x,y) of p[] (call once per set) */
static void compute_rank_xy(void) {
    ll ordp[128];
    for (ll i = 0; i < n; i++) ordp[i] = i;
    for (ll i = 1; i < n; i++) { ll t = ordp[i], j = i-1;
        while (j >= 0) { P a = p[ordp[j]], b = p[t];
            if (a.x < b.x || (a.x == b.x && a.y <= b.y)) break;
            ordp[j+1] = ordp[j]; j--; } ordp[j+1] = t; }
    for (ll i = 0; i < n; i++) rank_[ordp[i]] = i;
}
static int gp_check(void) {
    for (ll i = 0; i < n; i++) for (ll j = i+1; j < n; j++) for (ll l = j+1; l < n; l++)
        if (orient3(p[i], p[j], p[l]) == 0) {
            printf("NOT-GP triple %lld %lld %lld\n", i, j, l);
            return 0;
        }
    return 1;
}
static void build_sg(void) {
    for (ll i = 0; i < n; i++) for (ll j = 0; j < n; j++) for (ll l = 0; l < n; l++) {
        i128 o = orient3(p[i], p[j], p[l]);
        sg[(i*NSG+j)*NSG+l] = (signed char)((o > 0) - (o < 0));
    }
}
static long long g_subsets = 0;
/* enumerate k-subsets of 0..n-1; return 1 if any is in convex position */
static int any_convex_k(ll k) {
    ll c[64];
    for (ll i = 0; i < k; i++) c[i] = i;
    for (;;) {
        g_subsets++;
        if (hullsize(c, k) == k) return 1;
        ll i = k - 1;
        while (i >= 0 && c[i] == n - k + i) i--;
        if (i < 0) return 0;
        c[i]++;
        for (ll j = i+1; j < k; j++) c[j] = c[j-1] + 1;
    }
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s file k | batch file k | pattern wfile k pfile\n", argv[0]); return 2; }
    sg = malloc((size_t)NSG*NSG*NSG);
    if (!strcmp(argv[1], "pattern")) {
        if (argc < 5) { fprintf(stderr, "pattern needs wfile k pfile\n"); return 2; }
        FILE *f = fopen(argv[2], "r");
        if (!f) { perror("fopen"); return 3; }
        n = 0; ll x, y;
        while (fscanf(f, "%lld %lld", &x, &y) == 2) { p[n].x = x; p[n].y = y; n++; }
        fclose(f);
        ll k = atoll(argv[3]);
        if (!gp_check()) { printf("PATTERN RESULT gp=0\n"); return 1; }
        build_sg();
        ll N = n + 1, P2 = n*(n-1)/2;
        FILE *g = fopen(argv[4], "r");
        if (!g) { perror("fopen pfile"); return 3; }
        ll rows = 0, foundrows = 0, badpat = 0;
        int v;
        for (;;) {
            int s[128];
            ll i;
            for (i = 0; i < P2; i++) {
                if (fscanf(g, "%d", &v) != 1) { i = -1; break; }
                if (v != 1 && v != -1) { badpat++; i = -2; break; }
                s[i] = v;
            }
            if (i == -1) break;
            if (i == -2) { /* skip rest of line */ int ch; while ((ch = fgetc(g)) != '\n' && ch != EOF); continue; }
            ll order[160];
            for (i = 0; i < N; i++)
                if (fscanf(g, "%lld", &order[i]) != 1) { badpat++; break; }
            if (i < N) break;
            rows++;
            /* rank of each position in the merged (x,y) order */
            for (i = 0; i < N; i++) rank_[order[i]] = i;
            /* build mixed signs: sign(w_i, w_j, q)=pattern[i<j] (positions!) */
            ll pi = 0;
            for (ll a = 0; a < n; a++) for (ll b = a+1; b < n; b++) {
                int sv = s[pi++];
                ll q = n;
                sg[(a*NSG+b)*NSG+q] = (signed char)sv;
                sg[(b*NSG+a)*NSG+q] = (signed char)-sv;
                sg[(a*NSG+q)*NSG+b] = (signed char)-sv;   /* swap of 2nd/3rd */
                sg[(q*NSG+a)*NSG+b] = (signed char)sv;    /* cyclic */
                sg[(a*NSG+q)*NSG+q] = 0; (void)0;
                sg[(q*NSG+b)*NSG+a] = (signed char)-sv;
                sg[(b*NSG+q)*NSG+a] = (signed char)sv;
                sg[(q*NSG+q)*NSG+a] = 0;
            }
            /* check all C(n, k-1) subsets containing q = position n */
            ll cm[64];
            for (i = 0; i < k-1; i++) cm[i] = i;
            int hit = 0;
            for (;;) {
                ll sub[64];
                for (ll t = 0; t < k-1; t++) sub[t] = cm[t];
                sub[k-1] = n;
                if (hullsize_ord(sub, k) == k) { hit = 1; break; }
                ll ii = k - 2;
                while (ii >= 0 && cm[ii] == n - (k-1) + ii) ii--;
                if (ii < 0) break;
                cm[ii]++;
                for (ll j = ii+1; j < k-1; j++) cm[j] = cm[j-1] + 1;
            }
            if (hit) foundrows++;
            else {
                printf("CELL-NOCONVEXK row=%lld signs=(", rows);
                for (ll t = 0; t < P2; t++) printf("%d,", s[t]);
                printf(")\n");
            }
        }
        fclose(g);
        printf("PATTERN RESULT n=%lld k=%lld cells=%lld convexk=%lld nocells=%lld badpat=%lld\n",
               n, k, rows, foundrows, rows - foundrows, badpat);
        return (rows > 0 && foundrows == rows && badpat == 0) ? 0 : 1;
    }
    if (!strcmp(argv[1], "batch")) {
        FILE *f = fopen(argv[2], "r");
        if (!f) { perror("fopen"); return 3; }
        ll nsets = 0, nn = 0;
        if (fscanf(f, "%lld %lld", &nsets, &nn) != 2) { fprintf(stderr, "bad header\n"); return 3; }
        ll k = atoll(argv[3]);
        n = nn;
        ll sets = 0, convex = 0, nogp = 0;
        for (ll s = 0; s < nsets; s++) {
            for (ll i = 0; i < n; i++)
                if (fscanf(f, "%lld %lld", &p[i].x, &p[i].y) != 2) { fprintf(stderr, "bad set\n"); return 3; }
            sets++;
            if (!gp_check()) { nogp++; printf("BATCH SET %lld NOT-GP\n", s); continue; }
            build_sg();
            compute_rank_xy();
            if (any_convex_k(k)) {
                convex++;
                printf("BATCH SET %lld CONVEX-FOUND:", s);
                for (ll i = 0; i < n; i++) printf(" (%lld,%lld)", p[i].x, p[i].y);
                printf("\n");
            }
        }
        fclose(f);
        printf("BATCH RESULT sets=%lld convexk=%lld noconvexk=%lld nogp=%lld\n",
               sets, convex, sets - convex - nogp, nogp);
        return (sets == nsets && convex == 0 && nogp == 0) ? 0 : 1;
    }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("fopen"); return 3; }
    ll x, y; n = 0;
    while (fscanf(f, "%lld %lld", &x, &y) == 2) { p[n].x = x; p[n].y = y; n++; }
    fclose(f);
    ll k = atoll(argv[2]);
    if (!gp_check()) { printf("NOCONVEXK RESULT gp=0\n"); return 1; }
    build_sg();
    compute_rank_xy();
    if (any_convex_k(k)) {
        printf("NOCONVEXK RESULT gp=1 convexk=1\n");
        return 1;
    }
    printf("NOCONVEXK RESULT gp=1 convexk=0 subsets=%lld\n", g_subsets);
    return 0;
}
