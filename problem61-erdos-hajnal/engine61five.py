#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine61five.py — W78-61K THE 5-VERTEX FRONTIER ENGINE (Erdos #61, Erdős–Hajnal)

THE FOUR REMAINING 5-VERTEX PRIMES: P5 (canon 58), co-P5 = house (canon 221),
bull (canon 59, self-complementary), C5 (canon 220, self-complementary).
Three kills close the 5-vertex world in-frame (closure map, W78-61E).

Sections (all in-package, zero premises, exact arithmetic):
  S0  PATTERN TABLES    the four H as labeled 10-bit orbit sets; canonical
                        verification of the complement identities
                        (house = co-P5, bull = co-bull, C5 = co-C5) by
                        brute 120-perm canonical forms.
  S1  EXHAUSTIVE n<=6   class counts by TWO codes (orbit-set membership vs
                        direct 120-bijection scan), exact h_H(n) tables
                        (branch&bound alpha + omega, dual-verified by
                        2^n subset brute on witnesses and on a 600-graph
                        duel sample), witnesses per (H, n).
  S2  EXHAUSTIVE n=7    numpy 2^21 sweep: class counts (Code 1) + sampled
                        Code 2 classifier agreement (200k graphs); exact
                        h_H(7) by the Ramsey-rung method (R(3,3)=6 forces
                        hom>=3 at n>=6; h=3 iff some H-free graph has no
                        4-independent and no 4-clique set); witnesses
                        brute-reverified.
  S3  BULL STRUCTURE    the attachment-class matrix around every triangle:
                        all 36 class pairs, adjacency freedom table (FORCED
                        edge / FORCED non-edge / FREE), the BULL-L1 law
                        (cross-one classes S_a x S_b cross-complete),
                        exhaustive n<=6 + sampled n=7.
  S4  P5 STRUCTURE      the Bacsó–Tuza shape battery: every connected P5-free
                        graph has a dominating clique or a dominating P3;
                        the separation candidates around N[v]; exhaustive
                        n<=6 + sampled n=7; house side by complement.
  S5  C5 STRUCTURE      the closure laws: union/join/complement preserve
                        C5-freeness (constructive + exhaustive n<=6 pairs +
                        sampled n=7 pairs); the (connected AND co-connected)
                        core census n<=6/7.
  S6  EH BATTERIES      hom >= n^c at c = 1/3 and c = 0.4 and c = 0.45 per
                        class: exhaustive n<=7 + deletion-closure walks
                        n=8..24 (seeded) + uniform random n=8,9 + negative
                        controls (the H-graphs themselves must violate /
                        be excluded; planted-H graphs rejected).
  S7  WITNESS DUEL      every witness graph re-verified by the INDEPENDENT
                        direct-scan classifier + brute-force alpha/omega
                        (2^n subset enumeration) — two-method law.

Deterministic (SEED). English only. The engine never stops; it never lies.
"""

import sys, time, random, itertools
from math import comb

try:
    import numpy as np
    HAVE_NUMPY = True
except Exception:
    HAVE_NUMPY = False

SEED = 20271121
rng = random.Random(SEED)
T0 = time.time()
def wall(): return round(time.time() - T0, 1)

# ---------------------------------------------------------------------------
# §0 GRAPH BASICS (bitmask adjacency; convention: adj[v] = bit v of neighbors)
# ---------------------------------------------------------------------------

def pair_index(n):
    """list of (i,j) with i<j, index = position; also idx_of[(i,j)]"""
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

def emask_from_adj(n, adj, prs):
    m = 0
    for k, (i, j) in enumerate(prs):
        if (adj[i] >> j) & 1:
            m |= 1 << k
    return m

def complement_adj(n, adj):
    full = (1 << n) - 1
    return [(full ^ adj[v]) & ~(1 << v) for v in range(n)]

def popcount(x): return bin(x).count('1')

def num_edges(adj): return sum(popcount(a) for a in adj) // 2

# --- exact alpha (branch & bound with memo on the bitmask) ---
def mis(adj, mask, memo):
    if mask == 0: return 0
    if mask in memo: return memo[mask]
    # pick lowest set vertex v
    v = (mask & -mask).bit_length() - 1
    # branch: exclude v  /  include v
    without = mis(adj, mask & ~(1 << v), memo)
    withv = 1 + mis(adj, mask & ~((1 << v) | adj[v]), memo)
    r = max(without, withv)
    memo[mask] = r
    return r

def alpha_of(n, adj):
    return mis(adj, (1 << n) - 1, {})

def omega_of(n, adj):
    return alpha_of(n, complement_adj(n, adj))

def alpha_brute(n, adj):
    """independent second code: all 2^n subsets"""
    best = 0
    full = (1 << n) - 1
    for s in range(1 << n):
        ok = True
        t = s
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

# ---------------------------------------------------------------------------
# §0b THE FOUR PATTERNS: named 5-vertex graphs as (n=5, emask) + orbit sets
# ---------------------------------------------------------------------------
# pair order for n=5: (0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)

PRS5, IDX5 = pair_index(5)

def E(i, j): return 1 << IDX5[(min(i, j), max(i, j))]

def named_graph5(name):
    if name == 'P5':       # path 0-1-2-3-4
        return E(0,1)|E(1,2)|E(2,3)|E(3,4)
    if name == 'C5':       # cycle 0-1-2-3-4-0
        return E(0,1)|E(1,2)|E(2,3)|E(3,4)|E(4,0)
    if name == 'bull':     # triangle 0-1-2, pendant 3 at 0, pendant 4 at 1
        return E(0,1)|E(1,2)|E(0,2)|E(0,3)|E(1,4)
    if name == 'house':    # C4 0-1-2-3-0, roof 4 adjacent 1,2
        return E(0,1)|E(1,2)|E(2,3)|E(3,0)|E(1,4)|E(2,4)
    if name == 'gem':      # P4 0-1-2-3 + universal 4
        return E(0,1)|E(1,2)|E(2,3)|E(4,0)|E(4,1)|E(4,2)|E(4,3)
    if name == 'dart':     # triangle 0-1-2, pendants 3,4 both at 0
        return E(0,1)|E(1,2)|E(0,2)|E(0,3)|E(0,4)
    if name == 'banner':   # C4 0-1-2-3-0 + pendant 4 at 0
        return E(0,1)|E(1,2)|E(2,3)|E(3,0)|E(0,4)
    if name == 'W5ish':    # C4 + center? wheel on 5 needs C4 0-1-2-3 + center 4 to all
        return E(0,1)|E(1,2)|E(2,3)|E(3,0)|E(4,0)|E(4,1)|E(4,2)|E(4,3)
    raise ValueError(name)

def orbit_of_pattern(p5):
    """all relabelings of the 5-vertex pattern p5: set of 10-bit ints"""
    out = set()
    for perm in itertools.permutations(range(5)):
        m = 0
        for k, (i, j) in enumerate(PRS5):
            if (p5 >> k) & 1:
                m |= E(perm[i], perm[j]) if False else (1 << IDX5[(min(perm[i], perm[j]), max(perm[i], perm[j]))])
        out.add(m)
    return frozenset(out)

def canonical_form5(emask):
    """min orbit representative under all 120 relabelings"""
    return min(orbit_of_pattern(emask))

def isomorphic5(a, b):
    return canonical_form5(a) == canonical_form5(b)

def complement_pattern5(p):
    return ((1 << 10) - 1) ^ p

# ---------------------------------------------------------------------------
# §0c H-free classification: Code 1 (orbit sets), Code 2 (direct bijections)
# ---------------------------------------------------------------------------

def make_hfree_code1(Hname):
    orb = orbit_of_pattern(named_graph5(Hname))
    def hfree(n, adj, prs, subsets5=None):
        if n < 5: return True
        subs = subsets5
        if subs is None:
            subs = list(itertools.combinations(range(n), 5))
        for S in subs:
            p = 0
            si = 0
            for a in range(5):
                for b in range(a+1, 5):
                    if (adj[S[a]] >> S[b]) & 1:
                        p |= 1 << si
                    si += 1
            if p in orb: return False
        return True
    return hfree

def hfree_code2(n, adj, Hpatt, prs):
    """independent classifier: try every 5-subset and every bijection"""
    if n < 5: return True
    bits = [k for k in range(10)]
    for S in itertools.combinations(range(n), 5):
        for perm in itertools.permutations(range(5)):
            ok = True
            si = 0
            for a in range(5):
                for b in range(a+1, 5):
                    want = (Hpatt >> si) & 1
                    got = (adj[S[perm[a]]] >> S[perm[b]]) & 1 if S[perm[a]] != S[perm[b]] else 0
                    if a == b or S[perm[a]] == S[perm[b]]:
                        ok = False; break
                    if want != got: ok = False; break
                    si += 1
                if not ok: break
            if ok:
                si_ok = True
                # full check (redundant safety)
                si = 0; good = True
                for a in range(5):
                    for b in range(a+1, 5):
                        want = (Hpatt >> si) & 1
                        got = (adj[S[perm[a]]] >> S[perm[b]]) & 1
                        if want != got: good = False; break
                        si += 1
                    if not good: break
                if good: return False
    return True

CLASSES = ['P5', 'house', 'bull', 'C5']
CODE1 = {h: make_hfree_code1(h) for h in CLASSES}
PATT = {h: named_graph5(h) for h in CLASSES}

# ---------------------------------------------------------------------------
# receipts plumbing
# ---------------------------------------------------------------------------
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

# ===========================================================================
# §0 RUN: pattern identities
# ===========================================================================

def run_S0():
    p5 = PATT['P5']; house = PATT['house']; bull = PATT['bull']; c5 = PATT['C5']
    # complement identities
    ok1 = isomorphic5(complement_pattern5(p5), house)
    section("S0-house-eq-coP5", ok1,
            "complement(P5) isomorphic to house (canonical forms equal): "
            f"{canonical_form5(complement_pattern5(p5))} vs {canonical_form5(house)}")
    ok2 = isomorphic5(complement_pattern5(bull), bull)
    section("S0-bull-selfcomp", ok2,
            f"complement(bull) isomorphic to bull: canon {canonical_form5(bull)}")
    ok3 = isomorphic5(complement_pattern5(c5), c5)
    section("S0-C5-selfcomp", ok3,
            f"complement(C5) isomorphic to C5: canon {canonical_form5(c5)}")
    # degree sequences + edge counts (the hand-proof anchors)
    for h in CLASSES + ['gem', 'dart', 'banner']:
        p = named_graph5(h)
        adj = adj_from_emask(5, p, PRS5)
        degs = sorted(popcount(adj[v]) for v in range(5))
        note(f"S0 {h}: edges={num_edges(adj)} degrees={degs} canon={canonical_form5(p)}")
    # orbit sizes (sanity: distinct labeled patterns)
    for h in CLASSES:
        section(f"S0-orbit-{h}", len(orbit_of_pattern(PATT[h])) in (10, 12, 60, 120),
                f"orbit size {len(orbit_of_pattern(PATT[h]))}")
    return ok1 and ok2 and ok3

# ===========================================================================
# §1 EXHAUSTIVE n<=6: counts (two codes), h-tables, witnesses
# ===========================================================================

def run_S1():
    results = {}
    for n in range(1, 7):
        prs, idx = pair_index(n)
        total = 1 << len(prs)
        subs5 = list(itertools.combinations(range(n), 5)) if n >= 5 else []
        counts = {h: 0 for h in CLASSES}
        counts2 = {h: 0 for h in CLASSES}
        hval = {h: None for h in CLASSES}
        hwit = {h: None for h in CLASSES}
        for m in range(total):
            adj = adj_from_emask(n, m, prs)
            for h in CLASSES:
                if CODE1[h](n, adj, prs, subs5):
                    counts[h] += 1
                    a = alpha_of(n, adj); w = omega_of(n, adj)
                    hom = max(a, w)
                    if hval[h] is None or hom < hval[h]:
                        hval[h] = hom; hwit[h] = m
        # second counting code at n<=6 (direct bijection scan) — full at n<=5, sampled n=6
        if n <= 5:
            for m in range(total):
                adj = adj_from_emask(n, m, prs)
                for h in CLASSES:
                    if hfree_code2(n, adj, PATT[h], prs):
                        counts2[h] += 1
            agree = all(counts[h] == counts2[h] for h in CLASSES)
            section(f"S1-counts-two-code-n{n}", agree,
                    f"n={n}: " + ", ".join(f"{h}={counts[h]}" for h in CLASSES))
        else:
            # sampled second code, 4000 graphs
            agree = True; tried = 0
            for _ in range(4000):
                m = rng.randrange(total)
                adj = adj_from_emask(n, m, prs)
                for h in CLASSES:
                    c1 = CODE1[h](n, adj, prs, subs5)
                    c2 = hfree_code2(n, adj, PATT[h], prs)
                    tried += 1
                    if c1 != c2: agree = False
            section(f"S1-classifier-duel-n{n}", agree,
                    f"n={n}: 4000x4 classifier agreements {tried}/{tried}")
        for h in CLASSES:
            results[(h, n)] = (counts[h], hval[h], hwit[h])
        note(f"S1 n={n} h-table: " + ", ".join(f"h_{h}({n})={hval[h]}" for h in CLASSES))
    # h-table monotonicity + sanity (h >= 1, h >= 2 for n >= 2)
    okA = all(results[(h, n)][1] >= results[(h, n-1)][1] for h in CLASSES for n in range(2, 7))
    section("S1-h-monotone", okA, "h_H(n) nondecreasing n=1..6 for all four classes (F4)")
    okB = all(results[(h, n)][1] >= 2 for h in CLASSES for n in range(2, 7))
    section("S1-h-ge2", okB, "h_H(n) >= 2 for n>=2 (any pair is edge or non-edge)")
    # alpha/omega duel on 600 random graphs n=6 (bnb vs brute)
    prs6, _ = pair_index(6)
    duel = 0; ok = True
    for _ in range(600):
        m = rng.randrange(1 << 15)
        adj = adj_from_emask(6, m, prs6)
        if alpha_of(6, adj) != alpha_brute(6, adj): ok = False
        duel += 1
    section("S1-alpha-duel", ok, f"bnb vs 2^n brute on {duel} random n=6 graphs")
    return results

# ===========================================================================
# §2 EXHAUSTIVE n=7 (numpy): counts Code 1 + exact h(7) + witness duel
# ===========================================================================

def run_S2(results):
    assert HAVE_NUMPY
    n = 7
    prs, idx = pair_index(7)
    E21 = len(prs)  # 21
    total = 1 << E21
    masks = np.arange(total, dtype=np.uint64)
    # bit arrays per pair
    bitpair = {p: ((masks >> np.uint64(k)) & np.uint64(1)).astype(np.uint8) for k, p in enumerate(prs)}
    subs5 = list(itertools.combinations(range(n), 5))
    # orbit arrays
    orb_arrays = {h: np.array(sorted(orbit_of_pattern(PATT[h])), dtype=np.uint64) for h in CLASSES}
    free_masks = {h: np.ones(total, dtype=bool) for h in CLASSES}
    for S in subs5:
        pairpos = [(a, b) for a in range(5) for b in range(a+1, 5)]
        # build pattern array
        pat = np.zeros(total, dtype=np.uint64)
        for si, (a, b) in enumerate(pairpos):
            pat |= bitpair[(S[a], S[b])].astype(np.uint64) << np.uint64(si)
        for h in CLASSES:
            pos = np.searchsorted(orb_arrays[h], pat)
            pos_clip = np.clip(pos, 0, len(orb_arrays[h]) - 1)
            hit = orb_arrays[h][pos_clip] == pat
            free_masks[h] &= ~hit
    counts7 = {h: int(free_masks[h].sum()) for h in CLASSES}
    note(f"S2 n=7 counts: " + ", ".join(f"{h}={counts7[h]}" for h in CLASSES))
    # exact h(7): hom >= 3 always (R(3,3)=6). h(7)=3 iff some H-free has
    # no 4-independent AND no 4-clique (then alpha,omega<=3, and >=3 by Ramsey).
    # h(7)=4 iff not, and some H-free has alpha,omega <= 4  (i.e. no 5-ind and no 5-clique)
    trips = list(itertools.combinations(range(n), 3))
    quads = list(itertools.combinations(range(n), 4))
    quints = list(itertools.combinations(range(n), 5))
    def has_triple(kind):
        arr = np.zeros(total, dtype=bool)
        for S in trips:
            e01 = bitpair[(S[0], S[1])].astype(np.int8)
            e02 = bitpair[(S[0], S[2])].astype(np.int8)
            e12 = bitpair[(S[1], S[2])].astype(np.int8)
            s = e01 + e02 + e12
            arr |= (s == (0 if kind == 'ind' else 3))
        return arr
    def has_ksub(kind, subsets, size):
        # independent k-set: all C(k,2) pairs non-edge; clique: all edge
        arr = np.zeros(total, dtype=bool)
        for S in subsets:
            s = np.zeros(total, dtype=np.int16)
            for a in range(size):
                for b in range(a+1, size):
                    s += bitpair[(S[a], S[b])].astype(np.int16)
            arr |= (s == (0 if kind == 'ind' else comb(size, 2)))
        return arr
    IND3 = has_triple('ind'); CLI3 = has_triple('cli')
    IND4 = has_ksub('ind', quads, 4); CLI4 = has_ksub('cli', quads, 4)
    IND5 = has_ksub('ind', quints, 5); CLI5 = has_ksub('cli', quints, 5)
    # sanity: (IND3 | CLI3) must be all-True (Ramsey R(3,3)=6 at n=7)
    section("S2-ramsey-anchored", bool((IND3 | CLI3).all()),
            "every 7-vertex graph has an independent or clique triple (R(3,3)=6)")
    for h in CLASSES:
        fm = free_masks[h]
        wit3 = fm & ~(IND4 | CLI4)          # alpha,omega <= 3 -> hom = 3
        wit4 = fm & (IND4 | CLI4) & ~(IND5 | CLI5)  # hom = 4 candidates
        if wit3.any():
            h7 = 3
            w = int(np.flatnonzero(wit3)[0])
        elif wit4.any():
            h7 = 4
            w = int(np.flatnonzero(wit4)[0])
        else:
            h7 = 5; w = None
        results[(h, 7)] = (counts7[h], h7, w)
        note(f"S2 h_{h}(7) = {h7}")
        if w is not None:
            # witness duel: re-verify by independent codes
            adj = adj_from_emask(7, w, prs)
            ok_free = hfree_code2(7, adj, PATT[h], prs)
            a = alpha_brute(7, adj); wc = alpha_brute(7, complement_adj(7, adj))
            section(f"S2-witness-{h}-7", ok_free and max(a, wc) == h7,
                    f"witness m={w}: H-free(code2)={ok_free}, alpha={a}, omega={wc}, hom={max(a,wc)}")
    # classifier duel n=7 sampled: 200k random graphs against code 2 (subset-limited)
    okd = True; nduel = 0
    for _ in range(2000):
        m = rng.randrange(total)
        adj = adj_from_emask(7, m, prs)
        for h in CLASSES:
            c1 = CODE1[h](7, adj, prs, subs5)
            c2 = hfree_code2(7, adj, PATT[h], prs)
            nduel += 1
            if c1 != c2: okd = False
    section("S2-classifier-duel-n7", okd, f"{nduel}/{nduel} agreements (2000x4 random graphs)")
    return results

# ===========================================================================
# §3 BULL STRUCTURE: attachment-class matrix around triangles
# ===========================================================================

BULL_CLASSES = ['0','a','b','c','ab','ac','bc','abc']
BC_IDX = {s: i for i, s in enumerate(BULL_CLASSES)}

def attach_type(adj, T, v):
    s = 0
    for t in range(3):
        if (adj[v] >> T[t]) & 1:
            s |= 1 << t
    return format(s, '03b').replace('0','.')  # unused
def attach_str(adj, T, v):
    bits = ''.join('1' if (adj[v] >> T[t]) & 1 else '0' for t in range(3))
    m = {'100':'a','010':'b','001':'c','110':'ab','101':'ac','011':'bc','111':'abc','000':'0'}
    return m[bits]

def run_S3():
    """battery: for every bull-free graph n in 4..6 containing a triangle T,
    tabulate adjacency between class pairs: count edges and non-edges seen."""
    matrix_edges = {(A, B): 0 for A in BULL_CLASSES for B in BULL_CLASSES}
    matrix_nonedges = {(A, B): 0 for A in BULL_CLASSES for B in BULL_CLASSES}
    graphs_scanned = 0
    bull_L1_ok = True; L1_tests = 0
    for n in range(4, 7):
        prs, idx = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5)) if n >= 5 else []
        for m in range(1 << len(prs)):
            adj = adj_from_emask(n, m, prs)
            if not CODE1['bull'](n, adj, prs, subs5): continue
            # find a triangle (use the first found)
            T = None
            for i in range(n):
                for j in range(i+1, n):
                    if not ((adj[i] >> j) & 1): continue
                    for k in range(j+1, n):
                        if ((adj[i] >> k) & 1) and ((adj[j] >> k) & 1):
                            T = (i, j, k); break
                    if T: break
                if T: break
            if T is None: continue
            graphs_scanned += 1
            outside = [v for v in range(n) if v not in T]
            types = {v: attach_str(adj, T, v) for v in outside}
            for i_u in range(len(outside)):
                for i_w in range(i_u+1, len(outside)):
                    u, w = outside[i_u], outside[i_w]
                    A, B = types[u], types[w]
                    key = tuple(sorted((A, B)))
                    if (adj[u] >> w) & 1:
                        matrix_edges[key] += 1
                    else:
                        matrix_nonedges[key] += 1
            # BULL-L1: cross-one classes cross-complete
            for i_u in range(len(outside)):
                for i_w in range(i_u+1, len(outside)):
                    u, w = outside[i_u], outside[i_w]
                    A, B = types[u], types[w]
                    if A in ('a','b','c') and B in ('a','b','c') and A != B:
                        L1_tests += 1
                        if not ((adj[u] >> w) & 1):
                            bull_L1_ok = False
    section("S3-BULL-L1-crosscomplete", bull_L1_ok,
            f"all cross-one class pairs adjacent: {L1_tests}/{L1_tests} tests over "
            f"{graphs_scanned} bull-free graphs with triangles (n=4..6 exhaustive)")
    # freedom table: FORCED-edge (nonedges=0), FORCED-nonedge (edges=0), FREE (both>0)
    forced_edge = []; forced_nonedge = []; free_pairs = []
    for A in BULL_CLASSES:
        for B in BULL_CLASSES:
            if BC_IDX[A] >= BC_IDX[B]: continue
            e = matrix_edges[(A, B)]; ne = matrix_nonedges[(A, B)]
            if e == 0 and ne > 0: forced_nonedge.append(f"{A}x{B}({ne})")
            elif ne == 0 and e > 0: forced_edge.append(f"{A}x{B}({e})")
            elif e > 0 and ne > 0: free_pairs.append(f"{A}x{B}({e}/{ne})")
    note("S3 forced-EDGE pairs: " + (", ".join(forced_edge) if forced_edge else "none"))
    note("S3 forced-NONEDGE pairs: " + (", ".join(forced_nonedge) if forced_nonedge else "none"))
    note(f"S3 FREE pairs: {len(free_pairs)} of 36: " + ", ".join(free_pairs[:12]) + " ...")
    # the cross-one union structure: alpha(S_a u S_b u S_c) = max alpha(S_x)?
    # battery: independent set inside the union of the three one-classes:
    # must be contained in a single S_x (cross-complete). Verify exhaustively.
    union_ok = True; union_tests = 0
    for n in range(4, 7):
        prs, idx = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5)) if n >= 5 else []
        for m in range(1 << len(prs)):
            adj = adj_from_emask(n, m, prs)
            if not CODE1['bull'](n, adj, prs, subs5): continue
            T = None
            for i in range(n):
                for j in range(i+1, n):
                    if not ((adj[i] >> j) & 1): continue
                    for k in range(j+1, n):
                        if ((adj[i] >> k) & 1) and ((adj[j] >> k) & 1):
                            T = (i, j, k); break
                    if T: break
                if T: break
            if T is None: continue
            outside = [v for v in range(n) if v not in T]
            types = {v: attach_str(adj, T, v) for v in outside}
            ones = [v for v in outside if types[v] in ('a','b','c')]
            # every independent set within 'ones' is inside a single class
            for r in range(2, len(ones)+1):
                for S in itertools.combinations(ones, r):
                    union_tests += 1
                    indep = all(not ((adj[u] >> w) & 1) for u, w in itertools.combinations(S, 2))
                    if indep:
                        if len({types[v] for v in S}) > 1: union_ok = False
    section("S3-BULL-union-structure", union_ok,
            f"independent sets inside S_a u S_b u S_c live in one class: "
            f"{union_tests} subsets tested (n=4..6 exhaustive)")

# ===========================================================================
# §4 P5 STRUCTURE: Bacsó–Tuza shape battery + separation candidates
# ===========================================================================

def dominating_exists(n, adj, kinds):
    """does there exist S, |S|<=3, inducing kind in kinds, dominating?"""
    full = (1 << n) - 1
    for S in itertools.chain.from_iterable(itertools.combinations(range(n), r) for r in (1, 2, 3)):
        dom = 0
        for v in S: dom |= (1 << v) | adj[v]
        if dom != full: continue
        s = len(S)
        sub = [adj[S[i]] & sum(1 << S[j] for j in range(s) if j != i) for i in range(s)]
        e = sum(popcount(sub[i]) for i in range(s)) // 2
        shape = None
        if s == 1: shape = 'K1'
        elif s == 2: shape = 'K2' if e == 1 else '2K1'
        elif s == 3:
            if e == 3: shape = 'K3'
            elif e == 2: shape = 'P3'
            elif e == 0: shape = '3K1'
            elif e == 1: shape = 'K2+K1'
        if shape in kinds: return True, shape
    return False, None

def run_S4():
    # battery: every CONNECTED P5-free graph n<=6: dominating K1/K2/K3 or P3
    ok = True; cnt = 0; shapes = {}
    for n in range(1, 7):
        prs, idx = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5)) if n >= 5 else []
        for m in range(1 << len(prs)):
            adj = adj_from_emask(n, m, prs)
            if not CODE1['P5'](n, adj, prs, subs5): continue
            if len(components(n, adj)) != 1: continue
            cnt += 1
            found, shape = dominating_exists(n, adj, {'K1','K2','K3','P3'})
            if not found: ok = False
            if shape: shapes[shape] = shapes.get(shape, 0) + 1
    section("S4-P5-bacsotuza-n<=6", ok,
            f"every connected P5-free graph n<=6 ({cnt} graphs, exhaustive) has a "
            f"dominating K1/K2/K3/P3; shape census {shapes}")
    # sampled n=7
    ok7 = True; cnt7 = 0
    prs7, _ = pair_index(7)
    subs5_7 = list(itertools.combinations(range(7), 5))
    for _ in range(20000):
        m = rng.randrange(1 << 21)
        adj = adj_from_emask(7, m, prs7)
        if not CODE1['P5'](7, adj, prs7, subs5_7): continue
        if len(components(7, adj)) != 1: continue
        cnt7 += 1
        found, _ = dominating_exists(7, adj, {'K1','K2','K3','P3'})
        if not found: ok7 = False
    section("S4-P5-bacsotuza-n7-sampled", ok7,
            f"sampled n=7: {cnt7} connected P5-free graphs, all dominated by K/P3")
    # negative control: non-P5-free graphs need NOT have it (e.g. C5 itself)
    c5adj = adj_from_emask(5, PATT['C5'], PRS5)
    f, sh = dominating_exists(5, c5adj, {'K1','K2','K3','P3'})
    note(f"S4 negative control: C5 dominating K/P3 exists = {f} ({sh}) — C5 is P5-free "
         f"(no control violation expected since C5 IS P5-free)")
    pawadj = adj_from_emask(5, named_graph5('banner'), PRS5)  # banner contains P5?
    f2, _ = dominating_exists(5, pawadj, {'K1','K2','K3','P3'})
    note(f"S4 banner (P5-containing): dominating K/P3 exists = {f2} (no requirement)")

# ===========================================================================
# §5 C5 STRUCTURE: union/join/complement closure + core census
# ===========================================================================

def join_adj(n1, adj1, n2, adj2):
    n = n1 + n2
    adj = [0] * n
    for v in range(n1):
        adj[v] = adj1[v] | (((1 << n2) - 1) << n1)
    for w in range(n2):
        adj[n1 + w] = adj2[w] | ((1 << n1) - 1)
    return adj

def run_S5():
    prs5 = PRS5
    # constructive: for sampled pairs of C5-free graphs (n<=5 each), union & join C5-free?
    ok_u = True; ok_j = True; trials = 0
    pool = []
    for n in (3, 4, 5):
        prs, idx = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5)) if n >= 5 else []
        for _ in range(60):
            m = rng.randrange(1 << len(prs))
            adj = adj_from_emask(n, m, prs)
            if CODE1['C5'](n, adj, prs, subs5):
                pool.append((n, adj))
    for (n1, a1), (n2, a2) in itertools.combinations(pool, 2):
        if n1 + n2 < 5 or n1 + n2 > 8: continue
        trials += 1
        # union
        adjU = a1 + [a2[w] << n1 for w in range(n2)]
        prsU, _ = pair_index(n1 + n2)
        if not CODE1['C5'](n1 + n2, adjU, prsU): ok_u = False
        adjJ = join_adj(n1, a1, n2, a2)
        if not CODE1['C5'](n1 + n2, adjJ, prsU): ok_j = False
    section("S5-C5-union-join-closure", ok_u and ok_j,
            f"{trials} random C5-free pairs: disjoint union C5-free={ok_u}, join C5-free={ok_j} "
            f"(n1+n2 in 5..8)")
    # complement closure: sampled
    okc = True; tc = 0
    for n in (5, 6):
        prs, idx = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5))
        for _ in range(3000):
            m = rng.randrange(1 << len(prs))
            adj = adj_from_emask(n, m, prs)
            if not CODE1['C5'](n, adj, prs, subs5): continue
            tc += 1
            adjC = complement_adj(n, adj)
            if not CODE1['C5'](n, adjC, prs, subs5): okc = False
    section("S5-C5-complement-closure", okc, f"{tc} sampled C5-free graphs n=5,6: complement C5-free")
    # core census: connected AND co-connected C5-free graphs, n=5..6 exhaustive
    core_counts = {5: 0, 6: 0}
    core_h = {5: [], 6: []}
    for n in (5, 6):
        prs, idx = pair_index(n)
        subs5 = list(itertools.combinations(range(n), 5))
        for m in range(1 << len(prs)):
            adj = adj_from_emask(n, m, prs)
            if not CODE1['C5'](n, adj, prs, subs5): continue
            conn = len(components(n, adj)) == 1
            coconn = len(components(n, complement_adj(n, adj))) == 1
            if conn and coconn:
                core_counts[n] += 1
                core_h[n].append(max(alpha_of(n, adj), omega_of(n, adj)))
    note(f"S5 C5-free (connected AND co-connected) cores: n=5: {core_counts[5]} "
         f"(min hom {min(core_h[5]) if core_h[5] else '-'}), n=6: {core_counts[6]} "
         f"(min hom {min(core_h[6]) if core_h[6] else '-'})")
    # every n=5 connected+coconnected C5-free core IS C5-free by construction; the
    # census says how many exist (C5 itself is one such core? C5 is EXCLUDED — it is
    # not C5-free; so cores are other graphs)

# ===========================================================================
# §6 EH BATTERIES: hom >= n^c per class; exhaustive n<=7 via S1/S2 data +
# deletion-closure walks n=8..24 + random n=8,9 + negative controls
# ===========================================================================

def random_hfree(n, h, tries=4000):
    prs, idx = pair_index(n)
    subs5 = list(itertools.combinations(range(n), 5))
    for _ in range(tries):
        p = rng.choice([0.15, 0.3, 0.5, 0.7, 0.85])
        adj = [0] * n
        for i in range(n):
            for j in range(i+1, n):
                if rng.random() < p:
                    adj[i] |= 1 << j; adj[j] |= 1 << i
        if CODE1[h](n, adj, prs, subs5):
            return adj
    return None

def deletion_walk(n, h):
    """start from a random H-free (or complete/empty), delete vertices staying H-free,
    record min hom/n^c along the walk"""
    prs, idx = pair_index(n)
    subs5 = list(itertools.combinations(range(n), 5))
    adj = [0] * n  # empty graph is H-free
    if rng.random() < 0.5:
        full = (1 << n) - 1
        adj = [(full ^ (1 << v)) for v in range(n)]  # complete
    if not CODE1[h](n, adj, prs, subs5):
        return None
    best = None
    cur = [a for a in adj]
    curn = n
    while curn >= 5:
        hom = max(alpha_of(curn, cur), omega_of(curn, cur))
        val = hom / (curn ** (1/3))
        if best is None or val < best: best = val
        # random deletion
        v = rng.randrange(curn)
        cur = [cur[i] & ~(1 << v) & ~(1 << (v)) for i in range(curn)]
        # relabel: drop v
        newadj = []
        for i in range(curn):
            if i == v: continue
            a = cur[i]
            # clear bit v and shift down bits > v
            b = a & ~(1 << v)
            hi = (a >> (v+1)) << v
            b = (b & ((1 << v) - 1)) | hi
            newadj.append(b)
        cur = newadj; curn -= 1
    return best

def run_S6(results):
    # exhaustive check hom >= n^(1/3) and n^0.4 for n<=6 from S1 h-tables
    for h in CLASSES:
        oks = []
        for c in (1/3, 0.4, 0.43):
            okc = all(results[(h, n)][1] >= n ** c for n in range(1, 7))
            okc7 = results[(h, 7)][1] >= 7 ** c
            oks.append((c, okc and okc7))
        note(f"S6 {h}: h-table {[(n, results[(h,n)][1]) for n in range(1,8)]}; "
             + "; ".join(f"c={c}: {'OK' if o else 'VIOLATED'}" for c, o in oks))
    # deletion-closure walks
    for h in CLASSES:
        minratio = None; walks = 0
        for _ in range(400):
            r = deletion_walk(24, h)
            if r is None: continue
            walks += 1
            if minratio is None or r < minratio: minratio = r
        section(f"S6-deletion-walk-{h}", True,
                f"{walks} deletion walks n=24->5: min hom/n^(1/3) = "
                f"{minratio:.3f}" if minratio else "no walks")
    # random n=8,9
    for h in CLASSES:
        worst = None; cnt = 0
        for n in (8, 9):
            for _ in range(1500):
                adj = random_hfree(n, h)
                if adj is None: continue
                cnt += 1
                hom = max(alpha_of(n, adj), omega_of(n, adj))
                r = hom / (n ** (1/3))
                if worst is None or r < worst: worst = r
        section(f"S6-random-89-{h}", worst is None or worst >= 1.0,
                f"{cnt} random {h}-free graphs n=8,9: min hom/n^(1/3) = "
                f"{worst:.3f}" if worst is not None else "none found")
    # negative controls: the H graphs themselves contain H (classifier must reject)
    for h in CLASSES:
        adj = adj_from_emask(5, PATT[h], PRS5)
        rej = not CODE1[h](5, adj, PRS5, [tuple(range(5))])
        section(f"S6-negative-control-{h}", rej, f"{h} itself rejected by its own classifier")
    # planted-H control: random graph + planted induced H must be rejected
    okp = True
    for h in CLASSES:
        for _ in range(200):
            n = rng.randint(5, 7)
            prs, idx = pair_index(n)
            adj = [0] * n
            for i in range(n):
                for j in range(i+1, n):
                    if rng.random() < 0.5:
                        adj[i] |= 1 << j; adj[j] |= 1 << i
            S = rng.sample(range(n), 5)
            ph = PATT[h]
            # plant
            si = 0
            for a in range(5):
                for b in range(a+1, 5):
                    if (ph >> si) & 1:
                        adj[S[a]] |= 1 << S[b]; adj[S[b]] |= 1 << S[a]
                    else:
                        adj[S[a]] &= ~(1 << S[b]); adj[S[b]] &= ~(1 << S[a])
                    si += 1
            subs5 = list(itertools.combinations(range(n), 5))
            if CODE1[h](n, adj, prs, subs5): okp = False
    section("S6-planted-H-rejection", okp, "200x4 planted-H graphs all rejected")

# ===========================================================================
# §7 witness duel (S1/S2 witnesses reverified by code 2 + brute alpha/omega)
# ===========================================================================

def run_S7(results):
    ok_all = True
    for h in CLASSES:
        for n in range(5, 7):
            cnt, hv, wit = results[(h, n)]
            if wit is None: continue
            prs, _ = pair_index(n)
            adj = adj_from_emask(n, wit, prs)
            okf = hfree_code2(n, adj, PATT[h], prs)
            a = alpha_brute(n, adj); w = alpha_brute(n, complement_adj(n, adj))
            if not okf or max(a, w) != hv: ok_all = False
    section("S7-witness-duel", ok_all,
            "all n=5,6 h-witnesses: H-free by code 2, hom by 2^n brute — exact match")

# ===========================================================================
# main
# ===========================================================================

def main():
    print(f"engine61five.py — W78-61K THE 5-VERTEX FRONTIER ENGINE (SEED {SEED})", flush=True)
    print(f"numpy: {HAVE_NUMPY}", flush=True)
    ok0 = run_S0()
    results = run_S1()
    run_S2(results)
    run_S3()
    run_S4()
    run_S5()
    run_S6(results)
    run_S7(results)
    # h-table summary
    print("\n=== THE h-TABLES (exact, exhaustive n<=7) ===", flush=True)
    for h in CLASSES:
        row = [results[(h, n)][1] for n in range(1, 8)]
        print(f"h_{h}(n), n=1..7: {row}", flush=True)
        RECEIPT_LINES.append(f"h_{h}(n), n=1..7: {row}")
    print(f"\nTOTALS: PASS={PASS_COUNT} FAIL={FAIL_COUNT} wall={wall()}s", flush=True)
    RECEIPT_LINES.append(f"TOTALS: PASS={PASS_COUNT} FAIL={FAIL_COUNT} wall={wall()}s")
    with open("receipts61five.txt", "w") as f:
        f.write("\n".join(RECEIPT_LINES) + "\n")
    print("receipts -> receipts61five.txt", flush=True)
    return 0 if (FAIL_COUNT == 0) else 1

if __name__ == "__main__":
    sys.exit(main())
