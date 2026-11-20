
/* sweepk k N iters seed mode B [file] — exact convex-k sweep over GP N-point sets.
   modes: 0 uniform box [0,B)^2, 1 x-ladder, 2 grid cells, 3 clustered,
          4 near-circle, 5 near-parabola,
          6 file+1-grid: file has N-1 points; sweep the Nth over a coarse grid
            of the bbox (step = span/B),
          7 file-subsets: random N-subsets of the file's point list,
          8 uniform box + ANCHOR-DP convex-k finder (Chvatal-Klincsek style
            longest convex chain per bottommost anchor, every proposal
            re-certified by an exact hull test) — for N where C(N,k) brute
            force is infeasible (e.g. N=71, k=6).  A finder failure is only
            ever reported as NOCONVEXK (never a silent pass), and every
            reported find is certified.
   All sets verified GP (exact); a set with NO convex-k subset is printed in
   full (a discovery).  __int128 arithmetic throughout.  Floats appear only
   in construction heuristics of modes 4/5, never in any verdict. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef __int128 i128;
typedef long long ll;

static ll K, NN, MODE, B;
static unsigned long long rng_s;
static unsigned long long xrand(void) {
    rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s;
}

typedef struct { ll x, y; } P;
static P *BASEPTS; static ll NF;   /* the file's points (modes 6/7) */

static i128 orient3(P a, P b, P c) {
    return (i128)(b.x-a.x)*(c.y-a.y) - (i128)(b.y-a.y)*(c.x-a.x);
}
static int gp(P *p, ll n) {
    for (ll i = 0; i < n; i++) for (ll j = i+1; j < n; j++) for (ll k = j+1; k < n; k++)
        if (orient3(p[i],p[j],p[k]) == 0) return 0;
    return 1;
}
static signed char *sg = NULL;  /* n^3 sign table of the CURRENT set */
static void build_sg(P *p, ll n) {
    if (!sg) sg = malloc((size_t)128*128*128);
    for (ll i = 0; i < n; i++) for (ll j = 0; j < n; j++) for (ll k = 0; k < n; k++) {
        i128 o = orient3(p[i],p[j],p[k]);
        sg[(i*128+j)*128+k] = (signed char)((o > 0) - (o < 0));
    }
}
/* hull size of the subset {idx[0..k-1]} of the current set (positions),
   monotone chain via the sign table; positions sorted by (x,y) of CURP. */
static P *CURP = NULL;  /* the current set (for hullsize's coordinate sort) */
static ll hullsize(const ll *idx, ll k) {
    ll ord[64];
    for (ll i = 0; i < k; i++) ord[i] = i;
    /* insertion sort ord by (x, y) of CURP[idx[.]] */
    for (ll i = 1; i < k; i++) { ll t = ord[i], j = i-1;
        while (j >= 0) {
            P a = CURP[idx[ord[j]]], b = CURP[idx[t]];
            if (a.x < b.x || (a.x == b.x && a.y <= b.y)) break;
            ord[j+1]=ord[j]; j--;
        }
        ord[j+1]=t; }
    ll st[128], top = 0, hv[64]; for (ll i = 0; i < k; i++) hv[i] = 0;
    for (ll i = 0; i < k; i++) {
        while (top >= 2 && sg[((size_t)(idx[st[top-2]]*128+idx[st[top-1]])*128)+idx[ord[i]]] <= 0) top--;
        st[top++] = ord[i];
    }
    for (ll i = 0; i < top; i++) hv[st[i]] = 1;
    top = 0;
    for (ll i = k-1; i >= 0; i--) {
        while (top >= 2 && sg[((size_t)(idx[st[top-2]]*128+idx[st[top-1]])*128)+idx[ord[i]]] <= 0) top--;
        st[top++] = ord[i];
    }
    for (ll i = 0; i < top; i++) hv[st[i]] = 1;
    ll h = 0; for (ll i = 0; i < k; i++) h += hv[i];
    return h;
}

static int has_convex_k(P *p, ll n, ll k, ll *outidx) {
    build_sg(p, n);
    CURP = p;
    ll c[64];
    for (ll i = 0; i < k; i++) c[i] = i;
    for (;;) {
        if (hullsize(c, k) == k) { for (ll i = 0; i < k; i++) outidx[i] = c[i]; return 1; }
        ll i = k - 1;
        while (i >= 0 && c[i] == n - k + i) i--;
        if (i < 0) return 0;
        c[i]++;
        for (ll j = i+1; j < k; j++) c[j] = c[j-1] + 1;
    }
}

/* ---- mode 8: anchor-DP convex-k finder (certified) ---- */
static ll fdp[96][96], fch[96][96];
static int chain_convex(P *p, ll *ch, ll m) {
    /* exact: all m chain points are hull vertices of the chain subset
       (direct orientation test: sort by (x,y), monotone chain, orient3) */
    ll ord[96];
    for (ll i = 0; i < m; i++) ord[i] = i;
    for (ll i = 1; i < m; i++) { ll t = ord[i], j = i-1;
        while (j >= 0) { P a = p[ch[ord[j]]], b = p[ch[t]];
            if (a.x < b.x || (a.x == b.x && a.y <= b.y)) break;
            ord[j+1]=ord[j]; j--; } ord[j+1]=t; }
    ll st[192], top = 0, hv[96]; for (ll i = 0; i < m; i++) hv[i] = 0;
    for (ll i = 0; i < m; i++) {
        while (top >= 2 && orient3(p[ch[st[top-2]]], p[ch[st[top-1]]], p[ch[ord[i]]]) <= 0) top--;
        st[top++] = ord[i];
    }
    for (ll i = 0; i < top; i++) hv[st[i]] = 1;
    top = 0;
    for (ll i = m-1; i >= 0; i--) {
        while (top >= 2 && orient3(p[ch[st[top-2]]], p[ch[st[top-1]]], p[ch[ord[i]]]) <= 0) top--;
        st[top++] = ord[i];
    }
    for (ll i = 0; i < top; i++) hv[st[i]] = 1;
    for (ll i = 0; i < m; i++) if (!hv[i]) return 0;
    return 1;
}
static int has_convex_k_ck(P *p, ll n, ll k, ll *outidx) {
    /* for each anchor a (candidate bottommost vertex of the polygon),
       candidates = points strictly above a in the (y,x) order, sorted by
       angle around a in (0, pi]; fdp[i][j] = longest left-turn chain
       a -> c_i -> c_j -> ...;  every proposal certified by chain_convex. */
    for (ll a = 0; a < n; a++) {
        ll cand[96], t = 0;
        for (ll q = 0; q < n; q++)
            if (p[q].y > p[a].y || (p[q].y == p[a].y && p[q].x > p[a].x)) cand[t++] = q;
        if (t < k - 1) continue;
        /* angular sort around a, ASCENDING: shift while cand[j] is CCW of ct
           (cross(cand[j]-a, ct-a) < 0 means angle(cand[j]) > angle(ct)) */
        for (ll i = 1; i < t; i++) { ll ct = cand[i], j = i-1;
            while (j >= 0) {
                i128 cr = (i128)(p[cand[j]].x-p[a].x)*(p[ct].y-p[a].y)
                        - (i128)(p[cand[j]].y-p[a].y)*(p[ct].x-p[a].x);
                if (cr < 0) { cand[j+1]=cand[j]; j--; } else break;
            }
            cand[j+1]=ct; }
        for (ll j = t-1; j >= 1; j--)
            for (ll i = j-1; i >= 0; i--) {
                ll best = 3, ch = -1;
                for (ll q = j+1; q < t; q++)
                    if (orient3(p[cand[i]], p[cand[j]], p[cand[q]]) > 0 && fdp[j][q] + 1 > best) {
                        best = fdp[j][q] + 1; ch = q;
                    }
                fdp[i][j] = best; fch[i][j] = ch;
            }
        for (ll j = 1; j < t; j++)
            for (ll i = 0; i < j; i++) {
                if (fdp[i][j] < k) continue;
                /* extract chain a, cand[i], cand[j], ... */
                ll ch[96], m = 0;
                ch[m++] = a; ch[m++] = cand[i]; ch[m++] = cand[j];
                ll ci = i, cj = j;
                while (fch[ci][cj] >= 0 && m < 96) {
                    ll q = fch[ci][cj];
                    ch[m++] = cand[q];
                    ci = cj; cj = q;
                }
                if (m < k) continue;
                /* any k-subset of a certified-convex chain prefix: take first k */
                if (chain_convex(p, ch, m)) {
                    for (ll q = 0; q < k; q++) outidx[q] = ch[q];
                    return 1;
                }
            }
    }
    return 0;
}

static ll sample_one(P *base, ll nbase, P *p, ll *tries) {
    ll n = NN;
    for (ll t = 0; t < 400; t++) {
        (*tries)++;
        if (MODE == 0 || MODE == 8) {
            for (ll i = 0; i < n; i++) { p[i].x = xrand() % B; p[i].y = xrand() % B; }
        } else if (MODE == 1) {
            ll d = B / n;
            for (ll i = 0; i < n; i++) { p[i].x = i * d + (ll)(xrand() % (d/4 + 1)); p[i].y = xrand() % B; }
        } else if (MODE == 2) {
            ll g = n + 4;
            for (ll i = 0; i < n; i++) { p[i].x = xrand() % g; p[i].y = xrand() % g; }
        } else if (MODE == 3) {
            ll cc[3][2] = {{0,0},{B,B},{0,B}};
            for (ll i = 0; i < n; i++) { ll c = i % 3;
                p[i].x = cc[c][0] + (ll)(xrand() % (B/64 + 1));
                p[i].y = cc[c][1] + (ll)(xrand() % (B/64 + 1)); }
        } else if (MODE == 4) {
            ll R = B / 2;
            for (ll i = 0; i < n; i++) {
                double ang = 6.283185307179586 * i / n + ((double)(xrand() % 1000) / 1000.0 - 0.5) * 0.4;
                ll r = R + (ll)(xrand() % (B/64 + 1)) - B/128;
                p[i].x = (ll)(r * __builtin_cos(ang)); p[i].y = (ll)(r * __builtin_sin(ang));
            }
        } else if (MODE == 5) {
            ll d = B / n, S = B;
            for (ll i = 0; i < n; i++) {
                ll x = i * d + (ll)(xrand() % (d/4 + 1));
                p[i].x = x; p[i].y = (ll)((double)x * x / S) + (ll)(xrand() % (B/256 + 1));
            }
        } else if (MODE == 7) {
            for (ll i = 0; i < n; i++) p[i] = base[xrand() % nbase];
        }
        ll ok = 1;
        for (ll i = 0; i < n && ok; i++) for (ll j = i+1; j < n && ok; j++)
            if (p[i].x == p[j].x && p[i].y == p[j].y) ok = 0;
        if (ok && gp(p, n)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: %s k N iters seed mode B [file]\n", argv[0]); return 2; }
    K = atoll(argv[1]); NN = atoll(argv[2]);
    ll iters = atoll(argv[3]);
    rng_s = strtoull(argv[4], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rng_s == 0) rng_s = 88172645463325252ULL;
    MODE = atoll(argv[5]); B = atoll(argv[6]);
    BASEPTS = malloc(8192 * sizeof(P)); NF = 0;
    if (argc > 7) {
        FILE *f = fopen(argv[7], "r");
        if (!f) { perror("fopen"); return 3; }
        ll x, y;
        while (fscanf(f, "%lld %lld", &x, &y) == 2) { BASEPTS[NF].x = x; BASEPTS[NF].y = y; NF++; }
        fclose(f);
    }
    if (MODE == 6) {
        /* file gives N-1 points; sweep the Nth over a B-step grid of the bbox */
        if (NF < NN - 1) { fprintf(stderr, "mode6: file too small\n"); return 4; }
        ll nbase = NN - 1;
        P *p = malloc(NN * sizeof(P));
        ll gx0 = BASEPTS[0].x, gx1 = gx0, gy0 = BASEPTS[0].y, gy1 = gy0;
        for (ll i = 0; i < nbase; i++) {
            if (BASEPTS[i].x < gx0) gx0 = BASEPTS[i].x;
            if (BASEPTS[i].x > gx1) gx1 = BASEPTS[i].x;
            if (BASEPTS[i].y < gy0) gy0 = BASEPTS[i].y;
            if (BASEPTS[i].y > gy1) gy1 = BASEPTS[i].y;
        }
        ll spanx = gx1 - gx0, spany = gy1 - gy0;
        ll stepx = spanx / B + 1, stepy = spany / B + 1;
        ll M = B / 8 + 1;
        ll xs = (spanx + 2*M) / stepx + 1, ys = (spany + 2*M) / stepy + 1;
        ll sets = 0, found = 0, notfound = 0;
        ll out[64];
        for (ll ix = 0; ix <= xs; ix++) for (ll iy = 0; iy <= ys; iy++) {
            ll px = gx0 - M + ix * stepx, py = gy0 - M + iy * stepy;
            for (ll i = 0; i < nbase; i++) p[i] = BASEPTS[i];
            p[nbase].x = px; p[nbase].y = py;
            sets++;
            if (!gp(p, NN)) continue;
            if (has_convex_k(p, NN, K, out)) found++;
            else { notfound++;
                printf("NOCONVEXK %lld:", NN);
                for (ll i = 0; i < NN; i++) printf(" (%lld,%lld)", p[i].x, p[i].y);
                printf("\n"); }
        }
        printf("SWEEP mode=6 sets=%lld found=%lld notfound=%lld\n", sets, found, notfound);
        return 0;
    }
    if (MODE == 7 && NN > NF) { fprintf(stderr, "mode7: N > file size\n"); return 4; }
    ll sets = 0, found = 0, notfound = 0, tries = 0;
    P *p = malloc(NN * sizeof(P));
    ll out[64];
    for (ll it = 0; it < iters; it++) {
        if (!sample_one(BASEPTS, NF, p, &tries)) { printf("SAMPLING-FAILURE mode=%lld\n", MODE); continue; }
        sets++;
        int ok = (MODE == 8) ? has_convex_k_ck(p, NN, K, out) : has_convex_k(p, NN, K, out);
        if (ok) found++;
        else {
            notfound++;
            printf("NOCONVEXK %lld:", NN);
            for (ll i = 0; i < NN; i++) printf(" (%lld,%lld)", p[i].x, p[i].y);
            printf("\n");
        }
    }
    printf("SWEEP mode=%lld sets=%lld found=%lld notfound=%lld tries=%lld\n",
           MODE, sets, found, notfound, tries);
    return 0;
}
