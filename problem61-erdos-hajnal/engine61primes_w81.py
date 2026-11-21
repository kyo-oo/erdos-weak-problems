#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine61primes_w81.py — W81-61A: THE PRIME ASSAULT ENGINE (Erdos #61)

The three remaining five-vertex prime lanes of Erdos-Hajnal (#61):
  BULL (canon 59, self-complementary), C5 (canon 220, self-complementary),
  P5 (canon 58) + house (canon 221, complement pair — one kill covers both).

Batteries (census-guided structure discovery, all in-package, exact arithmetic):
  S0  PATTERNS + CONTROLS   orbit classifiers (Code 1) vs direct bijection scan
                            (Code 2), planted-host rejection, self-rejection.
  S1  BULL BATTERY          exhaustive n<=6: banked laws re-verified on EVERY
                            triangle (BULL-L1, alpha-union, omega-sum, clique
                            decrements); S_empty-heavy stratum hom; the
                            MAXIMUM-INDEPENDENT-SET anchor PURE concentration
                            laws (coverage, W-clique, alpha(P_A) <= |A|,
                            omega(P_A) <= omega-1, |P_A| <= 4(omega-1)^2 at
                            |A|=2) + the T_hi frontier measurement (T_hi =
                            vertices adjacent to >= 3 of the anchor), at n<=6
                            AND on structured large families (C5-blowups, the
                            join chain, the C5 tower X_2); two-disjoint-
                            triangles cross-pattern absence census; exact
                            h-table + witnesses n<=6.
  S2  C5 BATTERY            exhaustive n<=6: cores (connected AND
                            co-connected) and core+ (adds triangle AND
                            independent triple — the named C5-DICH frontier):
                            counts, min-hom, witnesses; TRIANGLE-ANCHOR
                            constraint table (8 cells, 36 pairs, exhaustive
                            n<=6 core+ + sampled n=7 cores); the derived
                            2-ANCHOR LAW verified on every core+ graph at
                            every triangle; the 1-ANCHOR LAW on sampled n=7
                            cores; the I-anchor PURE concentration + T_hi
                            census on core+; exact h-table n<=6.
  S3  P5 BATTERY            exhaustive n<=6 connected P5-free: exact
                            domination-shape cross-tab (K1/K2/K3/P3), the
                            Z-ONLY STRATUM (no dominating K1, no dominating
                            K2) enumerated and disclosed; for every z-only
                            graph and every dominating P3: the 7-cell
                            constraint table + the P5-CROSS LAW (C_x x C_z
                            complete); the BACSO-TUZA INDUCTION CASE EXPLORER
                            (every connected G, non-cut v, dominating D of
                            G-v with v undominated: candidate sets tested);
                            the C5 TOWER cap (X_2 = C5[C5]: P5-free AND
                            bull-free, alpha = omega = 4); the sec.4
                            separation measurement on z-only; exact h-table.
  S4  FLOORS + DUELS        hom >= n^c floors per class (exhaustive n<=6 +
                            sampled n=7 + structured n=8..25); witness duels
                            (Code 2 + 2^n brute); planted-host controls.

Deterministic (SEED). Receipts -> receipts61primes_w81.txt.
English only. The engine never stops; it never lies.
"""

import sys, time, random, itertools
from collections import defaultdict
from math import comb

SEED = 20271121
rng = random.Random(SEED)
T0 = time.time()
def wall(): return round(time.time() - T0, 1)

RECEIPT_LINES = []
PASS_COUNT = 0; FAIL_COUNT = 0

def section(name, ok, detail):
    global PASS_COUNT, FAIL_COUNT
    tag = "PASS" if ok else "FAIL"
    if ok: PASS_COUNT += 1
    else: FAIL_COUNT += 1
    line = f"[{tag}] {name} :: {detail}"
    RECEIPT_LINES.append(line)
    print(line, flush=True)

def note(msg):
    line = f"[NOTE] {msg}"
    RECEIPT_LINES.append(line)
    print(line, flush=True)

# ---------------------------------------------------------------------------
# §0 GRAPH BASICS (bitmask adjacency; adj[v] = bitmask of neighbors of v)
# ---------------------------------------------------------------------------

def pair_index(n):
    prs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    idx = {p: k for k, p in enumerate(prs)}
    return prs, idx

def adj_from_emask(n, emask, prs):
    adj = [0] * n
    for k, (i, j) in enumerate(prs):
        if (emask >> k) & 1:
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    return adj

def complement_adj(n, adj):
    full = (1 << n) - 1
    return [(full ^ adj[v]) & ~(1 << v) for v in range(n)]

def popcount(x): return bin(x).count('1')

def mis(adj, mask, memo):
    if mask == 0: return 0
    r = memo.get(mask)
    if r is not None: return r
    v = (mask & -mask).bit_length() - 1
    without = mis(adj, mask & ~(1 << v), memo)
    withv = 1 + mis(adj, mask & ~((1 << v) | adj[v]), memo)
    r = max(without, withv)
    memo[mask] = r
    return r

def alpha_of(n, adj): return mis(adj, (1 << n) - 1, {})
def omega_of(n, adj): return alpha_of(n, complement_adj(n, adj))

def alpha_witness(n, adj):
    """(alpha, canonical maximum independent set mask)."""
    memo = {}
    full = (1 << n) - 1
    a = mis(adj, full, memo)
    mask = full; wit = 0
    while mask:
        v = (mask & -mask).bit_length() - 1
        rest = mask & ~(1 << v)
        if 1 + mis(adj, rest & ~adj[v], memo) == mis(adj, mask, memo):
            wit |= 1 << v
            mask = rest & ~adj[v]
        else:
            mask = rest
    assert popcount(wit) == a
    return a, wit

def alpha_brute(n, adj):
    best = 0
    for s in range(1 << n):
        ok = True; t = s
        while t:
            v = (t & -t).bit_length() - 1
            if adj[v] & (s & ~(1 << v)): ok = False; break
            t &= t - 1
        if ok: best = max(best, popcount(s))
    return best

def components(n, adj):
    seen = 0; comps = []
    full = (1 << n) - 1
    while seen != full:
        v = ((full ^ seen) & -(full ^ seen)).bit_length() - 1
        comp = 0; stack = [v]; comp |= 1 << v
        while stack:
            u = stack.pop()
            nb = adj[u] & ~comp
            while nb:
                w = (nb & -nb).bit_length() - 1
                comp |= 1 << w; stack.append(w)
                nb &= nb - 1
        seen |= comp; comps.append(comp)
    return comps

def induced_adj(n, adj, vmask):
    verts = [v for v in range(n) if (vmask >> v) & 1]
    sub = [0] * len(verts)
    for i, v in enumerate(verts):
        for j, w in enumerate(verts):
            if i != j and (adj[v] >> w) & 1:
                sub[i] |= 1 << j
    return sub

# ---------------------------------------------------------------------------
# §0b PATTERNS + CLASSIFIERS (two codes)
# ---------------------------------------------------------------------------

PRS5, IDX5 = pair_index(5)
def E5(i, j): return 1 << IDX5[(min(i, j), max(i, j))]

def named_graph5(name):
    if name == 'P5':   return E5(0,1)|E5(1,2)|E5(2,3)|E5(3,4)
    if name == 'C5':   return E5(0,1)|E5(1,2)|E5(2,3)|E5(3,4)|E5(4,0)
    if name == 'bull': return E5(0,1)|E5(1,2)|E5(0,2)|E5(0,3)|E5(1,4)
    if name == 'house':return E5(0,1)|E5(1,2)|E5(2,3)|E5(3,0)|E5(1,4)|E5(2,4)
    raise ValueError(name)

def orbit_of_pattern(p5):
    out = set()
    for perm in itertools.permutations(range(5)):
        m = 0
        for k, (i, j) in enumerate(PRS5):
            if (p5 >> k) & 1:
                m |= 1 << IDX5[(min(perm[i], perm[j]), max(perm[i], perm[j]))]
        out.add(m)
    return frozenset(out)

CLASSES = ['P5', 'house', 'bull', 'C5']
PATT = {h: named_graph5(h) for h in CLASSES}
ORB = {h: orbit_of_pattern(PATT[h]) for h in CLASSES}

def make_hfree_code1(Hname):
    orb = ORB[Hname]
    def hfree(n, adj, subs5):
        if n < 5: return True
        for S in subs5:
            p = 0; si = 0
            for a in range(5):
                for b in range(a+1, 5):
                    if (adj[S[a]] >> S[b]) & 1:
                        p |= 1 << si
                    si += 1
            if p in orb: return False
        return True
    return hfree

CODE1 = {h: make_hfree_code1(h) for h in CLASSES}

def hfree_code2(n, adj, Hpatt, subs5):
    if n < 5: return True
    for S in subs5:
        for perm in itertools.permutations(range(5)):
            ok = True; si = 0
            for a in range(5):
                for b in range(a+1, 5):
                    want = (Hpatt >> si) & 1
                    got = (adj[S[perm[a]]] >> S[perm[b]]) & 1
                    if want != got: ok = False; break
                    si += 1
                if not ok: break
            if ok: return False
    return True

def all_graphs(n):
    prs, idx = pair_index(n)
    total = 1 << len(prs)
    subs5 = list(itertools.combinations(range(n), 5)) if n >= 5 else []
    for m in range(total):
        yield m, adj_from_emask(n, m, prs), prs, subs5

# ---------------------------------------------------------------------------
# §0c ANCHOR MACHINERY
# ---------------------------------------------------------------------------

def attach_mask(adj, T, v):
    s = 0
    for t in range(3):
        if (adj[v] >> T[t]) & 1:
            s |= 1 << t
    return s

ATT_NAME = {}
for _s in range(8):
    _nm = ''.join('abc'[t] for t in range(3) if (_s >> t) & 1)
    ATT_NAME[_s] = _nm if _nm else '0'

def triangles(n, adj):
    out = []
    for i in range(n):
        for j in range(i+1, n):
            if not ((adj[i] >> j) & 1): continue
            for k in range(j+1, n):
                if ((adj[i] >> k) & 1) and ((adj[j] >> k) & 1):
                    out.append((i, j, k))
    return out

def indep_triples(n, adj):
    out = []
    for i in range(n):
        for j in range(i+1, n):
            if (adj[i] >> j) & 1: continue
            for k in range(j+1, n):
                if not ((adj[i] >> k) & 1) and not ((adj[j] >> k) & 1):
                    out.append((i, j, k))
    return out

def shape_of(S, adj):
    s = len(S)
    e = sum(1 for a, b in itertools.combinations(range(s), 2)
            if (adj[S[a]] >> S[b]) & 1)
    if s == 1: return 'K1'
    if s == 2: return 'K2' if e == 1 else '2K1'
    if s == 3:
        return {3: 'K3', 2: 'P3', 0: '3K1', 1: 'K2+K1'}[e]
    return None

def dominating_sets(n, adj, shapes):
    """all subsets S (|S|<=3), in vertex order, dominating G, shape in shapes."""
    full = (1 << n) - 1
    out = []
    for r in (1, 2, 3):
        for S in itertools.combinations(range(n), r):
            dom = 0
            for v in S: dom |= (1 << v) | adj[v]
            if dom != full: continue
            if shape_of(S, adj) in shapes: out.append(S)
    return out

def has_dominating(n, adj, shape):
    full = (1 << n) - 1
    for r in (1, 2, 3):
        for S in itertools.combinations(range(n), r):
            dom = 0
            for v in S: dom |= (1 << v) | adj[v]
            if dom != full: continue
            if shape_of(S, adj) == shape: return True
    return False

# ===========================================================================
# S0 — PATTERNS + CONTROLS
# ===========================================================================

def run_S0():
    def canon5(p): return min(orbit_of_pattern(p))
    ok1 = canon5(((1 << 10) - 1) ^ PATT['P5']) == canon5(PATT['house'])
    ok2 = canon5(((1 << 10) - 1) ^ PATT['bull']) == canon5(PATT['bull'])
    ok3 = canon5(((1 << 10) - 1) ^ PATT['C5']) == canon5(PATT['C5'])
    section("S0-identities", ok1 and ok2 and ok3,
            "complement(P5)=house; bull, C5 self-complementary (canonical forms)")
    okd = True; nduel = 0
    for n in (6, 7):
        prs, _ = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5))
        for _ in range(1200):
            m = rng.randrange(1 << len(prs))
            adj = adj_from_emask(n, m, prs)
            for hname in ('P5', 'bull', 'C5'):
                c1 = CODE1[hname](n, adj, subs5)
                c2 = hfree_code2(n, adj, PATT[hname], subs5)
                nduel += 1
                if c1 != c2: okd = False
    section("S0-classifier-duel", okd, f"{nduel}/{nduel} two-code agreements (n=6,7 random)")
    okn = True
    for hname in ('P5', 'bull', 'C5'):
        adj = adj_from_emask(5, PATT[hname], PRS5)
        if CODE1[hname](5, adj, [tuple(range(5))]): okn = False
    okp = True
    for hname in ('P5', 'bull', 'C5'):
        for _ in range(200):
            n = rng.randint(5, 7)
            prs, _ = pair_index(n)
            adj = [0] * n
            for i in range(n):
                for j in range(i+1, n):
                    if rng.random() < 0.5:
                        adj[i] |= 1 << j; adj[j] |= 1 << i
            S = rng.sample(range(n), 5)
            ph = PATT[hname]; si = 0
            for a in range(5):
                for b in range(a+1, 5):
                    if (ph >> si) & 1:
                        adj[S[a]] |= 1 << S[b]; adj[S[b]] |= 1 << S[a]
                    else:
                        adj[S[a]] &= ~(1 << S[b]); adj[S[b]] &= ~(1 << S[a])
                    si += 1
            subs5 = list(itertools.combinations(range(n), 5))
            if CODE1[hname](n, adj, subs5): okp = False
    section("S0-negative-controls", okn and okp,
            "H self-rejected by own classifier; 600 planted-H hosts all rejected")

# ===========================================================================
# shared: I-anchor pure concentration census + T_hi measurement
# ===========================================================================

def ianchor_census(hfree, n_lo, n_hi, core_only=False):
    """Verify the PURE I-anchor laws and measure T_hi. Returns dict."""
    res = dict(cov=True, wcl=True, acell=True, wdec=True, ppair=True,
               tested=0, thi_max=0, thi_rows=[], conc6=True)
    for n in range(n_lo, n_hi + 1):
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            if core_only:
                if len(components(n, adj)) != 1: continue
                if len(components(n, complement_adj(n, adj))) != 1: continue
                if not (triangles(n, adj) and indep_triples(n, adj)): continue
            res['tested'] += 1
            aG, Imask = alpha_witness(n, adj)
            wG = omega_of(n, adj)
            outside = [v for v in range(n) if not ((Imask >> v) & 1)]
            for v in outside:
                if not (adj[v] & Imask): res['cov'] = False
            cellsA = defaultdict(list)
            for v in outside:
                cellsA[adj[v] & Imask].append(v)
            thi = sum(len(vs) for A, vs in cellsA.items() if popcount(A) >= 3)
            res['thi_max'] = max(res['thi_max'], thi)
            if thi > 0:
                res['thi_rows'].append((thi, max(aG, wG), n))
            # candidate concentration inequality n <= 6*max(a,w)^4
            M = max(aG, wG)
            if n > 6 * (M ** 4): res['conc6'] = False
            for A, vs in cellsA.items():
                k = popcount(A)
                if not vs: continue
                cm = 0
                for v in vs: cm |= 1 << v
                wc = omega_of(len(vs), induced_adj(n, adj, cm))
                if k >= 1 and wG < wc + 1: res['wdec'] = False
                if k == 1:
                    for u, w in itertools.combinations(vs, 2):
                        if not ((adj[u] >> w) & 1): res['wcl'] = False
                if k <= 2:
                    ac = alpha_of(len(vs), induced_adj(n, adj, cm))
                    if ac > k: res['acell'] = False
                    if k == 2 and len(vs) > 4 * wc * wc: res['ppair'] = False
    return res

def thi_of_graph(n, adj):
    """T_hi w.r.t. the canonical maximum independent set."""
    aG, Imask = alpha_witness(n, adj)
    thi = 0
    for v in range(n):
        if (Imask >> v) & 1: continue
        if popcount(adj[v] & Imask) >= 3: thi += 1
    return aG, Imask, thi

# ===========================================================================
# S1 — BULL BATTERY
# ===========================================================================

def run_S1_bull():
    hfree = CODE1['bull']
    counts = {}; hval = {}; hwit = {}
    for n in range(1, 7):
        c = 0; hv = None; hw = None
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            c += 1
            hom = max(alpha_of(n, adj), omega_of(n, adj))
            if hv is None or hom < hv: hv = hom; hw = m
        counts[n] = c; hval[n] = hv; hwit[n] = hw
    section("S1-bull-htable-n6", [hval[n] for n in range(1, 7)] == [1, 2, 2, 2, 2, 3],
            "h_bull(n) n=1..6 recomputed = " + str([hval[n] for n in range(1, 7)]) +
            " (bank [1,2,2,2,2,3]); counts " + str([counts[n] for n in range(1, 7)]))

    # ---- banked laws on EVERY triangle, n=4..6 exhaustive ----
    l1_ok = True; l1_tests = 0
    aun_ok = True; aun_tests = 0
    wsum_ok = True; wsum_tests = 0
    dec_ok = True; dec_tests = 0
    graphs_tri = 0
    sempty_heavy = []
    for n in range(4, 7):
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            tris = triangles(n, adj)
            if not tris: continue
            graphs_tri += 1
            wG = omega_of(n, adj)
            homG = max(alpha_of(n, adj), wG)
            best_sempty = -1
            for T in tris:
                amap = {}
                for v in range(n):
                    if v in T: continue
                    amap[v] = attach_mask(adj, T, v)
                best_sempty = max(best_sempty,
                                  sum(1 for v in amap if amap[v] == 0))
                singles = [v for v in amap if popcount(amap[v]) == 1]
                for u, w in itertools.combinations(singles, 2):
                    if amap[u] != amap[w]:
                        l1_tests += 1
                        if not ((adj[u] >> w) & 1): l1_ok = False
                umask = 0
                for v in singles: umask |= 1 << v
                if umask:
                    aun_tests += 1
                    a_union = alpha_of(popcount(umask), induced_adj(n, adj, umask))
                    a_max = 0
                    for x in range(3):
                        cm = sum(1 << v for v in singles if amap[v] == (1 << x))
                        if cm:
                            a_max = max(a_max, alpha_of(popcount(cm), induced_adj(n, adj, cm)))
                    if a_union != a_max: aun_ok = False
                wsum_tests += 1
                wsum = 0
                for x in range(3):
                    cm = sum(1 << v for v in amap if amap[v] == (1 << x))
                    if cm:
                        wsum += omega_of(popcount(cm), induced_adj(n, adj, cm))
                if wG < wsum: wsum_ok = False
                bymask = defaultdict(int)
                for v in amap: bymask[amap[v]] |= 1 << v
                for s, cm in bymask.items():
                    if s == 0 or not cm: continue
                    wc = omega_of(popcount(cm), induced_adj(n, adj, cm))
                    dec_tests += 1
                    if wG < wc + popcount(s): dec_ok = False
            if n >= 5 and best_sempty >= (n - 3) / 2:
                sempty_heavy.append((best_sempty, homG, n, m))
    section("S1-bull-L1-reverified", l1_ok,
            f"BULL-L1 cross-one complete: {l1_tests}/{l1_tests} pairs adjacent over "
            f"{graphs_tri} with-triangle bull-free graphs n=4..6 (every triangle)")
    section("S1-bull-alpha-union-reverified", aun_ok,
            f"alpha(S_a u S_b u S_c) = max alpha(S_x): {aun_tests}/{aun_tests}")
    section("S1-bull-omega-sum-reverified", wsum_ok,
            f"omega >= omega(S_a)+omega(S_b)+omega(S_c): {wsum_tests}/{wsum_tests}")
    section("S1-bull-decrements-reverified", dec_ok,
            f"omega(S_S) <= omega - |S| for nonempty S: {dec_tests}/{dec_tests}")
    if sempty_heavy:
        note(f"S1 S_empty-heavy stratum (some triangle with |S_empty| >= (n-3)/2, "
             f"n>=5): {len(sempty_heavy)} graphs; min hom = "
             f"{min(t[1] for t in sempty_heavy)}; max |S_empty| = "
             f"{max(t[0] for t in sempty_heavy)} at n<=6")
    else:
        note("S1 S_empty-heavy stratum empty at n<=6")

    # ---- I-anchor pure laws + T_hi census (all bull-free n<=6) ----
    res = ianchor_census(hfree, 2, 6)
    section("S1-bull-Ianchor-pure-laws",
            res['cov'] and res['wcl'] and res['acell'] and res['wdec'] and res['ppair'],
            f"over {res['tested']} bull-free graphs n<=6 (canonical max IS): coverage "
            f"{res['cov']}, W-cells cliques {res['wcl']}, alpha(P_A)<=|A| {res['acell']}, "
            f"omega(P_A)<=omega-1 {res['wdec']}, |P_A|<=4(omega-1)^2 at |A|=2 "
            f"{res['ppair']}, n<=6*max^4 {res['conc6']}")
    if res['thi_rows']:
        note(f"S1 bull T_hi census n<=6: max |T_hi| = {res['thi_max']}; "
             f"{len(res['thi_rows'])} graphs with T_hi nonempty; min hom among them "
             f"= {min(t[1] for t in res['thi_rows'])}")
    else:
        note("S1 bull T_hi census n<=6: EMPTY (no bull-free graph on <=6 vertices has "
             "a vertex adjacent to >=3 vertices of a maximum independent set)")

    # ---- structured large families: T_hi + concentration at scale ----
    def blowup_C5(t):
        n = 5 * t
        adj = [0] * n
        for p1 in range(5):
            for p2 in ((p1 + 1) % 5, (p1 + 4) % 5):
                for i in range(t):
                    for j in range(t):
                        adj[p1 * t + i] |= 1 << (p2 * t + j)
        return n, adj
    def join_chain(k):
        # ((K1 v 3K1) v 3K1) ... k levels; n = 1 + 3k
        n = 1 + 3 * k
        adj = [0] * n
        # vertex 0 = the seed; levels L_i = {1+3(i-1), 2+3(i-1), 3+3(i-1)}
        def lvl(i): return (1 + 3 * (i - 1), 2 + 3 * (i - 1), 3 + 3 * (i - 1))
        # all cross pairs joined (every two vertices in different levels, and
        # level vertices joined to the seed)
        groups = [(0,)] + [lvl(i) for i in range(1, k + 1)]
        for gi in range(len(groups)):
            for gj in range(gi + 1, len(groups)):
                for a in groups[gi]:
                    for b in groups[gj]:
                        adj[a] |= 1 << b; adj[b] |= 1 << a
        return n, adj
    def substitute(n1, adj1, pieces):
        sizes = [p[0] for p in pieces]
        offs = [0]
        for s in sizes: offs.append(offs[-1] + s)
        N = offs[-1]
        A = [0] * N
        for i in range(n1):
            for j in range(n1):
                if i == j: continue
                if (adj1[i] >> j) & 1:
                    for a in range(sizes[i]):
                        for b in range(sizes[j]):
                            A[offs[i] + a] |= 1 << (offs[j] + b)
        for i in range(n1):
            n2, a2 = pieces[i]
            for a in range(n2):
                for b in range(n2):
                    if a != b and (a2[a] >> b) & 1:
                        A[offs[i] + a] |= 1 << (offs[i] + b)
        return N, A
    c5adj = adj_from_emask(5, PATT['C5'], PRS5)
    struct_ok = True; rows = []
    fams = []
    for t in (2, 3, 4):
        fams.append(("C5-blowup x%d" % t,) + blowup_C5(t))
    for k in (2, 4, 6):
        fams.append(("join-chain k=%d" % k,) + join_chain(k))
    X2n, X2 = substitute(5, c5adj, [(5, c5adj)] * 5)
    fams.append(("X_2=C5[C5]", X2n, X2))
    for (nm, N, A) in fams:
        subs5 = list(itertools.combinations(range(N), 5))
        if not hfree(N, A, subs5): struct_ok = False; continue
        aG, Imask, thi = thi_of_graph(N, A)
        wG = omega_of(N, A)
        M = max(aG, wG)
        ok6 = N <= 6 * (M ** 4)
        if not ok6: struct_ok = False
        rows.append(f"{nm}: n={N} alpha={aG} omega={wG} T_hi={thi} n<=6M^4={ok6}")
    section("S1-bull-structured-families", struct_ok,
            "C5-blowups (triangle-free bull-free), join chains, X_2 tower — all "
            "bull-free, all satisfy n <= 6*max(alpha,omega)^4; " + "; ".join(rows))

    # ---- two-disjoint-triangles cross-pattern absence census (n=6) ----
    present = set(); pairs_dt = 0
    for m, adj, prs, subs5 in all_graphs(6):
        if not hfree(6, adj, subs5): continue
        tris = triangles(6, adj)
        for T1, T2 in itertools.combinations(tris, 2):
            if set(T1) & set(T2): continue
            pairs_dt += 1
            pat = 0; b = 0
            for i in range(3):
                for j in range(3):
                    if (adj[T1[i]] >> T2[j]) & 1: pat |= 1 << b
                    b += 1
            present.add(pat)
    absent_dt = sorted(set(range(512)) - present)
    note(f"S1 bull two-disjoint-triangles: {pairs_dt} disjoint pairs at n=6; "
         f"{len(present)}/512 cross-patterns present, {len(absent_dt)} absent")
    return hval, hwit

# ===========================================================================
# S2 — C5 BATTERY
# ===========================================================================

def run_S2_c5():
    hfree = CODE1['C5']
    hval = {}; hwit = {}
    for n in range(1, 7):
        hv = None; hw = None
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            hom = max(alpha_of(n, adj), omega_of(n, adj))
            if hv is None or hom < hv: hv = hom; hw = m
        hval[n] = hv; hwit[n] = hw
    section("S2-c5-htable-n6", [hval[n] for n in range(1, 7)] == [1, 2, 2, 2, 3, 3],
            "h_C5(n) n=1..6 recomputed = " + str([hval[n] for n in range(1, 7)]) +
            " (bank [1,2,2,2,3,3])")
    core_counts = {}; corep_counts = {}; core_minhom = {}; corep_minhom = {}
    for n in (5, 6):
        cc = 0; cp = 0; mhc = None; mhp = None
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            conn = len(components(n, adj)) == 1
            coconn = len(components(n, complement_adj(n, adj))) == 1
            if not (conn and coconn): continue
            cc += 1
            hom = max(alpha_of(n, adj), omega_of(n, adj))
            if mhc is None or hom < mhc: mhc = hom
            if triangles(n, adj) and indep_triples(n, adj):
                cp += 1
                if mhp is None or hom < mhp: mhp = hom
        core_counts[n] = cc; corep_counts[n] = cp
        core_minhom[n] = mhc; corep_minhom[n] = mhp
    section("S2-c5-core-census",
            core_counts[5] == 420 and core_counts[6] == 18840,
            f"C5-free cores (conn AND coconn): n=5: {core_counts[5]} (bank 420), "
            f"n=6: {core_counts[6]} (bank 18840); min hom {core_minhom[5]}, "
            f"{core_minhom[6]}; core+ (also triangle AND indep triple): n=5: "
            f"{corep_counts[5]}, n=6: {corep_counts[6]}, min hom "
            f"{corep_minhom[5] if corep_minhom[5] else '-'}, "
            f"{corep_minhom[6] if corep_minhom[6] else '-'}")

    # ---- triangle-anchor table + 2-anchor law on core+ (n=5,6 exhaustive) ----
    edge_seen = defaultdict(int); ne_seen = defaultdict(int)
    law2_ok = True; law2_tests = 0
    anchor_graphs = 0
    for n in (5, 6):
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            conn = len(components(n, adj)) == 1
            coconn = len(components(n, complement_adj(n, adj))) == 1
            if not (conn and coconn): continue
            if not (triangles(n, adj) and indep_triples(n, adj)): continue
            anchor_graphs += 1
            for T in triangles(n, adj):
                outs = [v for v in range(n) if v not in T]
                amap = {v: attach_mask(adj, T, v) for v in outs}
                for s1 in range(8):
                    for s2 in range(s1, 8):
                        for u in outs:
                            if amap[u] != s1: continue
                            for w in outs:
                                if w == u or amap[w] != s2: continue
                                if (adj[u] >> w) & 1:
                                    edge_seen[(s1, s2)] += 1
                                else:
                                    ne_seen[(s1, s2)] += 1
                for ei in range(3):
                    x = T[ei]; y = T[(ei + 1) % 3]
                    for p, q, r in itertools.permutations(outs, 3):
                        if (adj[p] >> x) & 1 and not (adj[p] >> y) & 1 and \
                           (adj[q] >> y) & 1 and not (adj[q] >> x) & 1 and \
                           not (adj[r] >> x) & 1 and not (adj[r] >> y) & 1:
                            law2_tests += 1
                            if ((adj[p] >> r) & 1) and ((adj[q] >> r) & 1) \
                               and not ((adj[p] >> q) & 1):
                                law2_ok = False
    forced_edge = []; forced_ne = []; free_pairs = []
    keys = set(edge_seen) | set(ne_seen)
    for (s1, s2) in sorted(keys):
        e = edge_seen[(s1, s2)]; ne = ne_seen[(s1, s2)]
        tag = f"{ATT_NAME[s1]}x{ATT_NAME[s2]}"
        if e == 0 and ne > 0: forced_ne.append(f"{tag}({ne})")
        elif ne == 0 and e > 0: forced_edge.append(f"{tag}({e})")
        else: free_pairs.append(f"{tag}({e}/{ne})")
    note(f"S2 C5 core+ triangle-anchor table over {anchor_graphs} graphs "
         f"(n=5,6 exhaustive): FORCED-EDGE: "
         + (", ".join(forced_edge) or "none")
         + "; FORCED-NONEDGE: " + (", ".join(forced_ne) or "none")
         + f"; FREE: {len(free_pairs)} pairs")
    section("S2-c5-2anchor-law", law2_ok,
            f"2-ANCHOR LAW (edge xy of T; p in N(x)\\N(y), q in N(y)\\N(x), r outside "
            f"both: p~r and q~r imply p~q): {law2_tests} role instances over "
            f"{anchor_graphs} core+ graphs (every triangle), 0 violations")

    # ---- n=7 sampled cores: 1-anchor law + enrich the anchor table ----
    law1_ok = True; cores7 = 0
    prs7, _ = pair_index(7)
    subs7 = list(itertools.combinations(range(7), 5))
    for _ in range(30000):
        m = rng.randrange(1 << 21)
        adj = adj_from_emask(7, m, prs7)
        if not hfree(7, adj, subs7): continue
        if len(components(7, adj)) != 1: continue
        if len(components(7, complement_adj(7, adj))) != 1: continue
        if not (triangles(7, adj) and indep_triples(7, adj)): continue
        cores7 += 1
        for T in triangles(7, adj):
            outs = [v for v in range(7) if v not in T]
            amap = {v: attach_mask(adj, T, v) for v in outs}
            for s1 in range(8):
                for s2 in range(s1, 8):
                    for u in outs:
                        if amap[u] != s1: continue
                        for w in outs:
                            if w == u or amap[w] != s2: continue
                            if (adj[u] >> w) & 1: edge_seen[(s1, s2)] += 1
                            else: ne_seen[(s1, s2)] += 1
            for a in T:
                for W in itertools.combinations(outs, 4):
                    for perm in itertools.permutations(W):
                        b1, c1, d1, e1 = perm
                        if not ((adj[a] >> b1) & 1): continue
                        if not ((adj[a] >> e1) & 1): continue
                        if (adj[a] >> c1) & 1: continue
                        if (adj[a] >> d1) & 1: continue
                        if ((adj[b1] >> c1) & 1) and ((adj[c1] >> d1) & 1) and \
                           ((adj[d1] >> e1) & 1) and not ((adj[b1] >> d1) & 1) and \
                           not ((adj[b1] >> e1) & 1) and not ((adj[c1] >> e1) & 1):
                            law1_ok = False
    forced_edge = []; forced_ne = []; free_pairs = []
    keys = set(edge_seen) | set(ne_seen)
    for (s1, s2) in sorted(keys):
        e = edge_seen[(s1, s2)]; ne = ne_seen[(s1, s2)]
        tag = f"{ATT_NAME[s1]}x{ATT_NAME[s2]}"
        if e == 0 and ne > 0: forced_ne.append(f"{tag}({ne})")
        elif ne == 0 and e > 0: forced_edge.append(f"{tag}({e})")
        else: free_pairs.append(f"{tag}({e}/{ne})")
    note(f"S2 C5 triangle-anchor table (n<=6 exhaustive core+ + {cores7} sampled "
         f"n=7 cores): FORCED-EDGE: " + (", ".join(forced_edge) or "none")
         + "; FORCED-NONEDGE: " + (", ".join(forced_ne) or "none")
         + f"; FREE: {len(free_pairs)}")
    section("S2-c5-1anchor-law-n7", law1_ok,
            f"1-ANCHOR LAW (a in T; b,e in N(a), c,d outside: b~c & c~d & d~e & "
            f"b!~d & b!~e & c!~e forbidden): 0 violations over {cores7} sampled "
            f"n=7 cores (every triangle, every anchor vertex)")

    # ---- I-anchor pure laws + T_hi census on core+ (n=5,6) ----
    res = ianchor_census(hfree, 5, 6, core_only=True)
    section("S2-c5-Ianchor-pure-laws",
            res['cov'] and res['wcl'] and res['acell'] and res['wdec'] and res['ppair'],
            f"over {res['tested']} C5 core+ graphs n=5,6 (canonical max IS): "
            f"coverage {res['cov']}, W-cliques {res['wcl']}, alpha(P_A)<=|A| "
            f"{res['acell']}, omega(P_A)<=omega-1 {res['wdec']}, |P_A|<=4(omega-1)^2 "
            f"at |A|=2 {res['ppair']}, n<=6*max^4 {res['conc6']}")
    if res['thi_rows']:
        note(f"S2 C5 core+ T_hi census n=5,6: max |T_hi| = {res['thi_max']}; "
             f"{len(res['thi_rows'])} graphs with T_hi nonempty; min hom among "
             f"them = {min(t[1] for t in res['thi_rows'])}")
    else:
        note("S2 C5 core+ T_hi census n=5,6: EMPTY (no core+ graph on <=6 vertices "
             "has a vertex adjacent to >=3 vertices of a maximum independent set)")
    return hval, hwit

# ===========================================================================
# S3 — P5 BATTERY
# ===========================================================================

def run_S3_p5():
    hfree = CODE1['P5']
    zoo = defaultdict(int)
    zonly = []; zonly_k3 = []
    conn_counts = {}
    hval = {}; hwit = {}
    for n in range(1, 7):
        cc = 0; hv = None; hw = None
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            if len(components(n, adj)) != 1: continue
            cc += 1
            hom = max(alpha_of(n, adj), omega_of(n, adj))
            if hv is None or hom < hv: hv = hom; hw = m
            if n >= 2:
                shapes = tuple(has_dominating(n, adj, sh)
                               for sh in ('K1', 'K2', 'K3', 'P3'))
                zoo[shapes] += 1
                if (not shapes[0]) and (not shapes[1]):
                    if shapes[3]: zonly.append((n, m, adj))
                    elif shapes[2]: zonly_k3.append((n, m, adj))
        conn_counts[n] = cc; hval[n] = hv; hwit[n] = hw
    total_conn = sum(conn_counts.values())
    section("S3-p5-conn-census", total_conn == 19976,
            f"connected P5-free n=1..6: per-n {[conn_counts[n] for n in range(1,7)]} "
            f"(total {total_conn}, bank 19976); shape cross-tab "
            f"(K1,K2,K3,P3 presence) -> count: " +
            "; ".join(f"{k}:{v}" for k, v in sorted(zoo.items(), key=lambda t: str(t[0]))))
    note(f"S3 z-only stratum (no dominating K1, no dominating K2, dominating P3): "
         f"{len(zonly)} graphs n<=6; K3-but-no-P3 z-only: {len(zonly_k3)}")
    zn = defaultdict(int)
    for (n, m, adj) in zonly: zn[n] += 1
    note("S3 z-only per n: " + str(dict(sorted(zn.items()))))

    # ---- z-only anchor tables + P5-CROSS law ----
    cross_ok = True; cross_tests = 0
    edge_seen = defaultdict(int); ne_seen = defaultdict(int)
    MN = {msk: (('e1' if msk & 4 else '') + ('c' if msk & 2 else '')
                + ('e2' if msk & 1 else '')) or '0' for msk in range(8)}
    for (n, m, adj) in zonly:
        for S in dominating_sets(n, adj, {'P3'}):
            # center = vertex adjacent to both others
            if (adj[S[0]] >> S[1]) & 1 and (adj[S[0]] >> S[2]) & 1:
                ctr, e1, e2 = S[0], S[1], S[2]
            elif (adj[S[1]] >> S[0]) & 1 and (adj[S[1]] >> S[2]) & 1:
                ctr, e1, e2 = S[1], S[0], S[2]
            else:
                ctr, e1, e2 = S[2], S[0], S[1]
            cells = defaultdict(list)
            for v in range(n):
                if v in S: continue
                msk = (((1 if (adj[v] >> e1) & 1 else 0) << 2) |
                       ((1 if (adj[v] >> ctr) & 1 else 0) << 1) |
                       ((1 if (adj[v] >> e2) & 1 else 0)))
                cells[msk].append(v)
            for u in cells.get(4, []):
                for w in cells.get(1, []):
                    cross_tests += 1
                    if not ((adj[u] >> w) & 1): cross_ok = False
            for m1 in cells:
                for m2 in cells:
                    if m1 > m2: continue
                    for u in cells[m1]:
                        for w in cells[m2]:
                            if u == w: continue
                            if (adj[u] >> w) & 1: edge_seen[(m1, m2)] += 1
                            else: ne_seen[(m1, m2)] += 1
    section("S3-p5-CROSS-law", cross_ok,
            f"P5-CROSS (dominating P3 e1-ctr-e2: every vertex adjacent only to e1 is "
            f"adjacent to every vertex adjacent only to e2): {cross_tests}/"
            f"{cross_tests} pairs over all z-only graphs x all dominating P3s, "
            f"0 violations")
    forced_edge = []; forced_ne = []; free_pairs = []
    keys = set(edge_seen) | set(ne_seen)
    for (m1, m2) in sorted(keys):
        e = edge_seen[(m1, m2)]; ne = ne_seen[(m1, m2)]
        tag = f"{MN[m1]}x{MN[m2]}"
        if e == 0 and ne > 0: forced_ne.append(f"{tag}({ne})")
        elif ne == 0 and e > 0: forced_edge.append(f"{tag}({e})")
        else: free_pairs.append(f"{tag}({e}/{ne})")
    note("S3 z-only P3-anchor table: FORCED-EDGE: " + (", ".join(forced_edge) or "none")
         + "; FORCED-NONEDGE: " + (", ".join(forced_ne) or "none")
         + f"; FREE: {len(free_pairs)}: " + ", ".join(free_pairs[:16]))
    for (n, m, adj) in zonly[:10]:
        edges = [(i, j) for i in range(n) for j in range(i+1, n) if (adj[i] >> j) & 1]
        note(f"S3 z-only specimen n={n} emask={m}: edges {edges}")

    # ---- BACSO-TUZA induction case explorer ----
    case_stats = defaultdict(lambda: [0, 0])
    inst = 0; worked_all = 0
    expl_ok = True
    for n in range(4, 7):
        graphs_n = []
        for m, adj, prs, subs5 in all_graphs(n):
            if not hfree(n, adj, subs5): continue
            if len(components(n, adj)) == 1:
                graphs_n.append(adj)
        if n == 6:
            rng.shuffle(graphs_n)
            graphs_n = graphs_n[:6000] + [a for (nn, mm, a) in zonly if nn == 6]
        for adj in graphs_n:
            for v in range(n):
                rest = [w for w in range(n) if w != v]
                remap = {w: i for i, w in enumerate(rest)}
                radj = [0] * (n - 1)
                for a in rest:
                    for b in rest:
                        if a < b and (adj[a] >> b) & 1:
                            radj[remap[a]] |= 1 << remap[b]
                            radj[remap[b]] |= 1 << remap[a]
                if len(components(n - 1, radj)) != 1: continue
                for S in dominating_sets(n - 1, radj, {'K1', 'K2', 'K3', 'P3'}):
                    Sg = [rest[i] for i in S]
                    if any((adj[v] >> d) & 1 for d in Sg): continue
                    inst += 1
                    Nv = [u for u in range(n) if (adj[v] >> u) & 1]
                    cands = [(u,) for u in Nv] + [(v, u) for u in Nv]
                    for u in Nv:
                        for d in Sg:
                            if not ((adj[u] >> d) & 1): continue
                            cands.append((u, d))
                            cands.append((v, u, d))
                            for d2 in Sg:
                                if d2 <= d or not ((adj[u] >> d2) & 1): continue
                                if not ((adj[d] >> d2) & 1): continue
                                cands.append((u, d, d2))
                    okc = False
                    for c in cands:
                        dom = 0
                        for q in c: dom |= (1 << q) | adj[q]
                        if dom == (1 << n) - 1: okc = True; break
                    if okc: worked_all += 1
                    else: expl_ok = False
                    shp = shape_of(S, radj)
                    for u in Nv:
                        pat = sum(1 for d in Sg if (adj[u] >> d) & 1)
                        case_stats[(shp, pat)][0] += 1
                        if okc: case_stats[(shp, pat)][1] += 1
    section("S3-p5-BT-explorer", expl_ok,
            f"induction-step census: {inst} (G, v, D) instances with v undominated "
            f"(n=4,5 exhaustive; n=6: 6000 sampled + all z-only); a candidate from "
            f"{{u}},{{{v},u}},{{u,d}},{{{v},u,d}},{{u,d,d'}} dominated in "
            f"{worked_all}/{inst}")
    for key in sorted(case_stats, key=lambda k: (k[0], k[1])):
        t, w = case_stats[key]
        note(f"S3 BT case D={key[0]}, |N(u) cap D|={key[1]}: {w}/{t} instances "
             f"with a working candidate")

    # ---- C5 tower: X_2 = C5[C5] P5-free AND bull-free; alpha=omega=4 ----
    def substitute(n1, adj1, pieces):
        sizes = [p[0] for p in pieces]
        offs = [0]
        for s in sizes: offs.append(offs[-1] + s)
        N = offs[-1]
        A = [0] * N
        for i in range(n1):
            for j in range(n1):
                if i == j: continue
                if (adj1[i] >> j) & 1:
                    for a in range(sizes[i]):
                        for b in range(sizes[j]):
                            A[offs[i] + a] |= 1 << (offs[j] + b)
        for i in range(n1):
            n2, a2 = pieces[i]
            for a in range(n2):
                for b in range(n2):
                    if a != b and (a2[a] >> b) & 1:
                        A[offs[i] + a] |= 1 << (offs[i] + b)
        return N, A
    c5adj = adj_from_emask(5, PATT['C5'], PRS5)
    X2n, X2 = substitute(5, c5adj, [(5, c5adj)] * 5)
    subs_X2 = list(itertools.combinations(range(X2n), 5))
    p5free = CODE1['P5'](X2n, X2, subs_X2)
    bullfree = CODE1['bull'](X2n, X2, subs_X2)
    aX2 = alpha_of(X2n, X2); wX2 = omega_of(X2n, X2)
    c5freeX2 = CODE1['C5'](X2n, X2, subs_X2)
    section("S3-p5-tower-X2", p5free and bullfree and aX2 == 4 and wX2 == 4,
            f"X_2 = C5[C5] (25 vertices): P5-free={p5free}, bull-free={bullfree}, "
            f"alpha={aX2} (=4), omega={wX2} (=4), C5-free={c5freeX2} (contains C5, "
            f"as it must); the C5 tower caps c(P5) and c(bull) asymptotically: "
            f"hom(X_t) = 2^t at n = 5^t => c <= log2/log5 = 0.4306")

    # ---- sec.4 separation measurement on z-only ----
    complete_to = 0; partial_to = 0
    for (n, m, adj) in zonly:
        for v in range(n):
            Nv_mask = adj[v]
            far = (1 << n) - 1 - (1 << v) - Nv_mask
            if not far: continue
            seen = 0
            while seen != far:
                u0 = ((far ^ seen) & -(far ^ seen)).bit_length() - 1
                comp = 0; stack = [u0]; comp |= 1 << u0
                while stack:
                    uu = stack.pop()
                    nb = adj[uu] & far & ~comp
                    while nb:
                        ww = (nb & -nb).bit_length() - 1
                        comp |= 1 << ww; stack.append(ww); nb &= nb - 1
                seen |= comp
                for uu in range(n):
                    if not ((Nv_mask >> uu) & 1): continue
                    inter = adj[uu] & comp
                    if inter == 0: continue
                    if inter == comp: complete_to += 1
                    else: partial_to += 1
    note(f"S3 z-only separation (sec.4 candidates): N(v)-vertices with a neighbor in "
         f"a far component: complete-to-that-component {complete_to}, partial "
         f"{partial_to}")
    return hval, hwit

# ===========================================================================
# S4 — FLOORS + DUELS
# ===========================================================================

def run_S4_floors(hval, hwit):
    floors_ok = True
    for hname in ('P5', 'bull', 'C5'):
        hv = hval[hname]
        for c in (1/3, 0.4, 0.43):
            for n in range(1, 7):
                if hv[n] < n ** c: floors_ok = False
    prs7, _ = pair_index(7)
    subs7 = list(itertools.combinations(range(7), 5))
    ok7 = True; cnt7 = defaultdict(int)
    for _ in range(25000):
        m = rng.randrange(1 << 21)
        adj = adj_from_emask(7, m, prs7)
        for hname in ('P5', 'bull', 'C5'):
            if not CODE1[hname](7, adj, subs7): continue
            cnt7[hname] += 1
            hom = max(alpha_of(7, adj), omega_of(7, adj))
            if hom < 7 ** 0.43: ok7 = False
    section("S4-floors", floors_ok and ok7,
            f"hom >= n^0.43: exhaustive n<=6 + sampled n=7 ({cnt7['P5']} P5-free, "
            f"{cnt7['bull']} bull-free, {cnt7['C5']} C5-free sampled), 0 violations")
    okw = True
    for hname in ('P5', 'bull', 'C5'):
        for n in (5, 6):
            m = hwit[hname][n]
            prs, _ = pair_index(n)
            adj = adj_from_emask(n, m, prs)
            subs5 = list(itertools.combinations(range(n), 5))
            if not hfree_code2(n, adj, PATT[hname], subs5): okw = False
            a = alpha_brute(n, adj); w = alpha_brute(n, complement_adj(n, adj))
            if max(a, w) != hval[hname][n]: okw = False
    section("S4-witness-duel", okw,
            "all n=5,6 h-witnesses (P5/bull/C5): H-free by Code 2, hom by 2^n brute")
    # structured n=8..25 evidence: split graphs are P5-free; bipartite are
    # C5/bull-free; C5-blowups are P5/bull-free
    okb = True; rows = []
    for (m1, m2) in ((4, 4), (6, 6), (10, 10)):
        n = m1 + m2
        adj = [0] * n
        for i in range(m1):
            for j in range(m1, n):
                if rng.random() < 0.5:
                    adj[i] |= 1 << j; adj[j] |= 1 << i
        subs5 = list(itertools.combinations(range(n), 5))
        if not CODE1['C5'](n, adj, subs5): okb = False
        if not CODE1['bull'](n, adj, subs5): okb = False
        hom = max(alpha_of(n, adj), omega_of(n, adj))
        if hom < n ** (1/3): okb = False
        rows.append(f"bipartite n={n}: hom={hom}")
    for t in (2, 4):
        n = 5 * t
        adj = [0] * n
        for p1 in range(5):
            for p2 in ((p1 + 1) % 5, (p1 + 4) % 5):
                for i in range(t):
                    for j in range(t):
                        adj[p1 * t + i] |= 1 << (p2 * t + j)
        subs5 = list(itertools.combinations(range(n), 5))
        for hname in ('P5', 'bull'):
            if not CODE1[hname](n, adj, subs5): okb = False
        hom = max(alpha_of(n, adj), omega_of(n, adj))
        if hom < n ** (1/3): okb = False
        rows.append(f"C5-blowup x{t} n={n}: hom={hom}")
    section("S4-structured-evidence", okb,
            "structured families (bipartite n=8,12,20 C5/bull-free; C5-blowups "
            "n=10,20 P5/bull-free): all hom >= n^(1/3); " + "; ".join(rows))

# ===========================================================================
# main
# ===========================================================================

def main():
    print(f"engine61primes_w81.py — W81-61A PRIME ASSAULT ENGINE (SEED {SEED})", flush=True)
    run_S0()
    note(f"wall after S0: {wall()}s")
    bull_h, bull_w = run_S1_bull()
    note(f"wall after S1 (bull): {wall()}s")
    c5_h, c5_w = run_S2_c5()
    note(f"wall after S2 (C5): {wall()}s")
    p5_h, p5_w = run_S3_p5()
    note(f"wall after S3 (P5): {wall()}s")
    run_S4_floors({'P5': p5_h, 'bull': bull_h, 'C5': c5_h},
                  {'P5': p5_w, 'bull': bull_w, 'C5': c5_w})
    note(f"wall after S4: {wall()}s")
    print("\n=== h-TABLES (recomputed, exhaustive n<=6) ===", flush=True)
    for nm, hv in (('bull', bull_h), ('C5', c5_h), ('P5', p5_h)):
        row = [hv[n] for n in range(1, 7)]
        line = f"h_{nm}(n), n=1..6: {row}"
        print(line, flush=True); RECEIPT_LINES.append(line)
    print(f"\nTOTALS: PASS={PASS_COUNT} FAIL={FAIL_COUNT} wall={wall()}s", flush=True)
    RECEIPT_LINES.append(f"TOTALS: PASS={PASS_COUNT} FAIL={FAIL_COUNT} wall={wall()}s")
    if FAIL_COUNT == 0:
        print("PRIMES_W81_ENGINE_GREEN=1", flush=True)
        RECEIPT_LINES.append("PRIMES_W81_ENGINE_GREEN=1")
    with open("receipts61primes_w81.txt", "w") as f:
        f.write("\n".join(RECEIPT_LINES) + "\n")
    print("receipts -> receipts61primes_w81.txt", flush=True)
    return 0 if FAIL_COUNT == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
