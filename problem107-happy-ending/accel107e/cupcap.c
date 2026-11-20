
/* cupcap:
     verify file k l  — GP check; x-distinct check; max cup <= k-1; max cap <=
                        l-1; extract both maximal chains; certify each: x
                        increasing, consecutive slopes strictly monotone
                        (independent recheck), ALL-triples orientation sign,
                        convex position (hull size == chain length).
     chains file      — GP check + certify both maximal chains (no bounds):
                        the CUPCONV receipt for arbitrary point sets.
     sweep N iters seed B [k l] — random x-distinct GP sets of size N; per set:
                        DP maxcup/maxcap, extract both maximal chains, certify
                        both convex (CUPCONV inline); if k l given, additionally
                        require maxcup >= k or maxcap >= l (the CC threshold
                        claim at size N) and certify the witnessing chain. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef __int128 i128;
typedef long long ll;
typedef struct { ll x, y; } P;

static i128 orient3(P a, P b, P c) {
    return (i128)(b.x-a.x)*(c.y-a.y) - (i128)(b.y-a.y)*(c.x-a.x);
}
static int gp(P *p, ll n) {
    for (ll i = 0; i < n; i++) for (ll j = i+1; j < n; j++) for (ll k = j+1; k < n; k++)
        if (orient3(p[i],p[j],p[k]) == 0) return 0;
    return 1;
}
/* slope(a,b) < slope(c,d)  with x-distinct points, exact cross-multiplication */
static int slope_lt(P a, P b, P c, P d) {
    i128 l = (i128)(b.y-a.y)*(d.x-c.x), r = (i128)(d.y-c.y)*(b.x-a.x);
    return l < r;
}
static ll bestcup[128][128], bestcap[128][128];
static ll pcup[128][128], pcap[128][128];   /* predecessor r of edge (pp,q) */
/* p must be sorted by x (x-distinct). bestcup/pp/q use POSITIONS. */
static void dp(P *p, ll n, ll *maxcup, ll *maxcap, ll *cupedge, ll *capedge) {
    for (ll q = 0; q < n; q++) for (ll pp = 0; pp < n; pp++) {
        bestcup[pp][q] = 0; bestcap[pp][q] = 0; pcup[pp][q] = -1; pcap[pp][q] = -1; }
    for (ll q = 0; q < n; q++) for (ll pp = 0; pp < q; pp++) {
        if (p[pp].x == p[q].x) continue;
        ll bc = 2, bk = 2, bcpar = -1, bkpar = -1;
        for (ll r = 0; r < pp; r++) {
            if (p[r].x == p[pp].x) continue;
            if (slope_lt(p[r], p[pp], p[pp], p[q]) && bestcup[r][pp] + 1 > bc && bestcup[r][pp] > 0) {
                bc = bestcup[r][pp] + 1; bcpar = r; }
            if (slope_lt(p[pp], p[q], p[r], p[pp]) && bestcap[r][pp] + 1 > bk && bestcap[r][pp] > 0) {
                bk = bestcap[r][pp] + 1; bkpar = r; }
        }
        bestcup[pp][q] = bc; pcup[pp][q] = bcpar;
        bestcap[pp][q] = bk; pcap[pp][q] = bkpar;
    }
    ll mc = 0, mk = 0;
    *cupedge = *capedge = -1;
    for (ll q = 0; q < n; q++) for (ll pp = 0; pp < q; pp++) {
        if (bestcup[pp][q] > mc) { mc = bestcup[pp][q]; *cupedge = pp * n + q; }
        if (bestcap[pp][q] > mk) { mk = bestcap[pp][q]; *capedge = pp * n + q; }
    }
    if (n >= 2) { if (mc < 2) mc = 2; if (mk < 2) mk = 2; }
    *maxcup = mc; *maxcap = mk;
}
static ll extract(ll (*par)[128], ll edge, ll n, ll *chain) {
    /* walk the predecessor chain of the max edge (pp,q): r = par[pp][q] means
       edge (r,pp) is the recorded predecessor of edge (pp,q). */
    if (edge < 0) return 0;
    ll pp = edge / n, q = edge % n, len = 0;
    ll rev[128];
    rev[len++] = q; rev[len++] = pp;
    while (par[pp][q] >= 0) {
        ll r = par[pp][q];
        rev[len++] = r;
        q = pp; pp = r;
    }
    for (ll i = 0; i < len; i++) chain[i] = rev[len-1-i];
    return len;
}
static int certify_chain(P *p, ll *chain, ll len, int cup) {
    /* (1) x increasing; (2) consecutive slopes strictly monotone; (3) ALL
       triples same-sign (positive for cups, negative for caps, x-ordered);
       (4) convex position: every chain point a hull vertex of the chain. */
    if (len < 2) return 1;
    for (ll i = 1; i < len; i++) if (p[chain[i]].x <= p[chain[i-1]].x) return 0;
    for (ll i = 2; i < len; i++) {
        int up = slope_lt(p[chain[i-2]], p[chain[i-1]], p[chain[i-1]], p[chain[i]]);
        if (cup ? !up : up) return 0;
    }
    for (ll i = 0; i < len; i++) for (ll j = i+1; j < len; j++) for (ll k = j+1; k < len; k++) {
        i128 o = orient3(p[chain[i]], p[chain[j]], p[chain[k]]);
        if (cup ? (o <= 0) : (o >= 0)) return 0;
    }
    {
        ll hv[128], st[256], top = 0;
        for (ll i = 0; i < len; i++) hv[i] = 0;
        for (ll i = 0; i < len; i++) {
            while (top >= 2 && orient3(p[chain[st[top-2]]], p[chain[st[top-1]]], p[chain[i]]) <= 0) top--;
            st[top++] = i;
        }
        for (ll i = 0; i < top; i++) hv[st[i]] = 1;
        top = 0;
        for (ll i = len-1; i >= 0; i--) {
            while (top >= 2 && orient3(p[chain[st[top-2]]], p[chain[st[top-1]]], p[chain[i]]) <= 0) top--;
            st[top++] = i;
        }
        for (ll i = 0; i < top; i++) hv[st[i]] = 1;
        for (ll i = 0; i < len; i++) if (!hv[i]) return 0;
    }
    return 1;
}
static int cmp_xy(const void *a, const void *b) {
    const P *x = (const P*)a, *y = (const P*)b;
    if (x->x != y->x) return x->x < y->x ? -1 : 1;
    return x->y < y->y ? -1 : (x->y > y->y ? 1 : 0);
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr,
        "usage: %s verify file k l | chains file | sweep N iters seed B [k l]\n", argv[0]); return 2; }
    if (!strcmp(argv[1], "verify") || !strcmp(argv[1], "chains")) {
        int bounded = !strcmp(argv[1], "verify");
        FILE *f = fopen(argv[2], "r");
        if (!f) { perror("fopen"); return 3; }
        static P p[4096]; ll n = 0, x, y;
        while (fscanf(f, "%lld %lld", &x, &y) == 2) { p[n].x = x; p[n].y = y; n++; }
        fclose(f);
        qsort(p, n, sizeof(P), cmp_xy);
        ll k = 1 << 30, l = 1 << 30;
        if (bounded) { k = atoll(argv[3]); l = atoll(argv[4]); }
        int g = gp(p, n);
        int xd = 1;
        for (ll i = 1; i < n; i++) if (p[i].x == p[i-1].x) xd = 0;
        ll mc = 0, mk = 0, ce = 0, ke = 0;
        dp(p, n, &mc, &mk, &ce, &ke);
        ll chain[128], clen = 0, kchain[128], klen = 0;
        if (n >= 2) {
            clen = extract(pcup, ce, n, chain);
            klen = extract(pcap, ke, n, kchain);
        }
        int cc = (clen == mc) && certify_chain(p, chain, clen, 1);
        int ck = (klen == mk) && certify_chain(p, kchain, klen, 0);
        printf("VERIFY n=%lld gp=%d xdistinct=%d maxcup=%lld (bound %lld) maxcap=%lld (bound %lld) "
               "cupchain=%lld cupconvex=%d capchain=%lld capconvex=%d\n",
               n, g, xd, mc, k-1, mk, l-1, clen, cc, klen, ck);
        int ok = g && cc && ck;
        if (bounded) ok = ok && (mc <= k-1) && (mk <= l-1);
        printf(ok ? "VERIFY OK\n" : "VERIFY FAIL\n");
        return ok ? 0 : 1;
    } else if (!strcmp(argv[1], "sweep")) {
        ll N = atoll(argv[2]), iters = atoll(argv[3]);
        unsigned long long s = strtoull(argv[4], 0, 10) * 6364136223846793005ULL + 1442695040888963407ULL;
        if (!s) s = 1442695040888963407ULL;
        ll B = atoll(argv[5]);
        ll k = 0, l = 0;
        if (argc > 7) { k = atoll(argv[6]); l = atoll(argv[7]); }
        static P p[4096];
        ll sets = 0, okc = 0, cert = 0, bad = 0;
        for (ll it = 0; it < iters; it++) {
            for (ll t = 0; t < 400; t++) {
                ll d = B / N;
                for (ll i = 0; i < N; i++) {
                    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                    p[i].x = i * d + (ll)(s % (d/4 + 1));
                    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                    p[i].y = (ll)(s % B);
                }
                if (gp(p, N)) break;
            }
            sets++;
            ll mc = 0, mk = 0, ce = 0, ke = 0;
            dp(p, N, &mc, &mk, &ce, &ke);
            ll chain[128], clen = 0, kchain[128], klen = 0;
            int cc = 0, ck = 0;
            if (N >= 2) {
                clen = extract(pcup, ce, N, chain);
                klen = extract(pcap, ke, N, kchain);
                cc = (clen == mc) && certify_chain(p, chain, clen, 1);
                ck = (klen == mk) && certify_chain(p, kchain, klen, 0);
            }
            int thresh_ok = 1;
            if (k > 0) thresh_ok = (mc >= k || mk >= l);
            if (thresh_ok && cc && ck) { okc++; if (cc && ck) cert++; }
            else {
                bad++;
                printf("CUPSWEEP-FAIL N=%lld maxcup=%lld maxcap=%lld cc=%d ck=%d thr=%d:", N, mc, mk, cc, ck, thresh_ok);
                for (ll i = 0; i < N; i++) printf(" (%lld,%lld)", p[i].x, p[i].y);
                printf("\n");
            }
        }
        printf("CUPSWEEP N=%lld k=%lld l=%lld sets=%lld withcuporcap=%lld certified=%lld bad=%lld\n",
               N, k, l, sets, okc, cert, bad);
        return (bad == 0 && okc == sets && cert == okc) ? 0 : 1;
    }
    fprintf(stderr, "bad mode\n"); return 2;
}
