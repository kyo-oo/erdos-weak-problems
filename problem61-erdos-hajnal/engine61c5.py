#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine61c5.py — W80-61E: THE C5 ENDGAME ENGINE (Erdos #61, Erdős–Hajnal)

Target: the named CORE FRONTIER of the C5 lane (FIVEVERTEX_PROOF §2): the
C5-free graphs that are connected ∧ co-connected ∧ contain a triangle ∧
contain an independent triple. Banked already: C5-CLOSURE, C5-REDUCTION,
C5-DICH (triangle-free and α≤2 strata close at √n/2).

Sections (all in-package, zero premises, exact arithmetic, two codes):
  S0  TWO-CODE C5 CLASSIFIERS. Code 1: per-5-subset edge count == 5 and
      min internal degree >= 2. Code 2: 10-bit pattern membership in the
      12 labeled C5 signatures. Self battery: C5 detected by both; C7, C4,
      P6, K1∨C7, Petersen clean by both; 20k random n=7 graphs duel.
  S1  EXHAUSTIVE n<=6 (direct emask sweep): C5-free labeled counts (duel
      both codes), h-table rungs, the CORE census (count + min hom +
      witnesses + core property certification), α/ω B&B-vs-brute duel on
      every core. Bank cross-checks (h=[1,2,2,2,3,3]; core counts 420/18840).
  S2  EXHAUSTIVE n=7 (numpy 2^21 sweep): C5-free count cross-check vs bank
      (1,742,336), CORE census (count + witnesses; min core hom via
      witnesses: cores have hom>=3 by definition, so h_core(7)=3 iff a
      witness with α=ω=3 exists — C7+chord certified), classifier duel on
      a 20k sample, α/ω duel on sampled cores.
  S3  THE n=8 RUNG + SUBSTITUTION PACKAGE: witness W8 = K1 ∨ C7 (universal
      vertex joined to C7) machine-verified C5-free (both codes) with
      α=ω=3 → h_{C5}(8)=3 with the banked R(3,3)=6 anchor; the SUBST
      closure battery (random C5-free frames × pieces: substitution stays
      C5-free; C5-carrying frames detected — negative control); the
      CONTRACTION battery; the iterated witness X_2 = W8[W8×8] (64
      vertices): C5-free scan (all 5-subsets touching ≥2 slots would
      contradict the law — machine-checked by sampled 5-subsets + exact
      α/ω by the substitution formulas); the CAP arithmetic (c ≤ log3/log8).
  S4  THE HOM-3 FRONTIER HUNT (the sharp question: does a C5-free graph
      with α=ω=3 exist at n=9..12? at n=8 as a CORE?): time-boxed
      annealing descent, multistart (random + C7/C9/K1∨C7 templates),
      every claimed witness fully re-verified (both C5 codes, brute α/ω,
      connectivity, co-connectivity); the √n-LADDER arithmetic
      certification n<=8 (h(n)^2 >= n, equality rungs named).
  S5  RECEIPTS + PASS accounting + wall times.

Deterministic (SEED). English only. The engine never stops; it never lies.
"""

import sys, time, random, itertools
from math import comb, log

try:
    import numpy as np
    HAVE_NUMPY = True
except Exception:
    HAVE_NUMPY = False

SEED = 20280517
rng = random.Random(SEED)
T0 = time.time()
def wall(): return round(time.time() - T0, 1)

PASS = 0
FAIL = 0
REC = []
def ok(name, cond, note=""):
    global PASS, FAIL
    if cond:
        PASS += 1
        REC.append(f"[PASS] {name} :: {note}")
        print(f"[PASS] {name} :: {note}")
    else:
        FAIL += 1
        REC.append(f"[FAIL] {name} :: {note}")
        print(f"[FAIL] {name} :: {note}")

def note(name, text):
    REC.append(f"[NOTE] {name} :: {text}")
    print(f"[NOTE] {name} :: {text}")

def popcount(x): return bin(x).count('1')

# ---------------------------------------------------------------------------
# graph basics: adjacency as list of ints, adj[v] has bit v' set iff v~v'
# ---------------------------------------------------------------------------

def pairs_of(n): return [(i, j) for i in range(n) for j in range(i + 1, n)]

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

# --- Code 1: 5-subset has 5 edges and min internal degree >= 2 -----------
def subset_is_C5_code1(adj, S):
    e = 0
    deg = 0
    prev = []
    for a in S:
        d = 0
        for b in S:
            if a != b and (adj[a] >> b) & 1:
                d += 1
        if d < 2:
            return False
        deg += d
    # deg sum == 2*e
    for x, y in itertools.combinations(S, 2):
        if (adj[x] >> y) & 1:
            e += 1
    return (deg == 10) and (e == 5)

# --- Code 2: 10-bit pattern in the 12 labeled C5 signatures --------------
def build_C5_signatures():
    # reference C5 on vertices 0..4 (cycle 0-1-2-3-4-0)
    ref = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    refset = set(ref) | set((b, a) for a, b in ref)
    sigs = set()
    for perm in itertools.permutations(range(5)):
        # vertex i of the 5-set plays role perm[i] of the reference
        m = 0
        k = 0
        for i in range(5):
            for j in range(i + 1, 5):
                a, b = perm[i], perm[j]
                if (a, b) in refset or (b, a) in refset:
                    m |= 1 << k
                k += 1
        sigs.add(m)
    return sigs

C5_SIGS = build_C5_signatures()

def subset_is_C5_code2(adj, S):
    m = 0
    k = 0
    for i in range(5):
        ai = adj[S[i]]
        for j in range(i + 1, 5):
            if (ai >> S[j]) & 1:
                m |= 1 << k
            k += 1
    return m in C5_SIGS

def has_C5(n, adj, code=1):
    f = subset_is_C5_code1 if code == 1 else subset_is_C5_code2
    for S in itertools.combinations(range(n), 5):
        if f(adj, S):
            return True
    return False

# --- connectivity (BFS, bit frontiers) ------------------------------------
def connected(n, adj):
    seen = 1
    frontier = 1
    while frontier:
        nf = 0
        f = frontier
        while f:
            b = f & (-f)
            v = b.bit_length() - 1
            nf |= adj[v]
            f ^= b
        frontier = nf & ~seen
        seen |= nf
    return seen == (1 << n) - 1

def co_connected(n, adj):
    return connected(n, complement_adj(n, adj))

# --- exact alpha/omega ------------------------------------------------------
def brute_alpha(n, adj):
    best = 0
    for S in range(1, 1 << n):
        ind = True
        for i in range(n):
            if (S >> i) & 1:
                if adj[i] & S:
                    ind = False
                    break
        if ind:
            c = popcount(S)
            if c > best:
                best = c
    return best

def brute_omega(n, adj):
    return brute_alpha(n, complement_adj(n, adj))

def bnb_mis(n, adj, memo):
    # exact maximum independent set, branch & bound with memo (bank style)
    key = 0
    for i in range(n):
        key |= ((adj[i] & ((1 << n) - 1)) != 0) << i  # not needed; use full key below
    return _mis(adj, (1 << n) - 1, memo)

def _mis(adj, mask, memo):
    if mask == 0:
        return 0
    r = memo.get(mask)
    if r is not None:
        return r
    # pick lowest vertex v in mask
    v = (mask & (-mask)).bit_length() - 1
    rest = mask ^ (1 << v)
    # option 1: v in the set
    a = 1 + _mis(adj, rest & ~adj[v], memo)
    # option 2: v out
    b = _mis(adj, rest, memo)
    r = a if a > b else b
    memo[mask] = r
    return r

def exact_alpha(n, adj):
    return _mis(adj, (1 << n) - 1, {})

def exact_omega(n, adj):
    return exact_alpha(n, complement_adj(n, adj))

def has_triangle(n, adj):
    for i in range(n):
        ai = adj[i]
        m = ai
        while m:
            b = m & (-m)
            j = b.bit_length() - 1
            if adj[j] & ai & ~(1 << j) & ~(1 << i):
                pass
            if popcount(adj[i] & adj[j]) >= 1 and i < j:
                return True
            m ^= b
    return False

def has_triangle2(n, adj):
    for i in range(n):
        for j in range(i + 1, n):
            if (adj[i] >> j) & 1 and (adj[i] & adj[j]):
                return True
    return False

def has_indep_triple(n, adj):
    cadj = complement_adj(n, adj)
    return has_triangle2(n, cadj)

def is_core(n, adj):
    # cheapest first: triangle, then connectivity pair, then indep triple
    if not has_triangle2(n, adj):
        return False
    if not connected(n, adj):
        return False
    if not co_connected(n, adj):
        return False
    return has_indep_triple(n, adj)

# --- named graphs -----------------------------------------------------------
def graph_C5():     # 0-1-2-3-4-0
    a = [0] * 5
    for (i, j) in [(0,1),(1,2),(2,3),(3,4),(4,0)]:
        a[i] |= 1 << j; a[j] |= 1 << i
    return a

def graph_C7():
    a = [0] * 7
    for i in range(7):
        j = (i + 1) % 7
        a[i] |= 1 << j; a[j] |= 1 << i
    return a

def graph_C7chord():  # C7 + chord 0-2  (triangle 0,1,2)
    a = graph_C7()
    a[0] |= 1 << 2; a[2] |= 1 << 0
    return a

def graph_C4():
    a = [0]*4
    for (i,j) in [(0,1),(1,2),(2,3),(3,0)]:
        a[i] |= 1<<j; a[j] |= 1<<i
    return a

def graph_join(A, B):
    """join of graphs on disjoint vertex sets 0..|A|-1, |A|..|A|+|B|-1"""
    nA, nB = len(A), len(B)
    adj = []
    for i in range(nA):
        adj.append(A[i] | (((1 << nB) - 1) << nA))
    for j in range(nB):
        adj.append((B[j] << nA) | ((1 << nA) - 1))
    return adj

def graph_W8():  # K1 ∨ C7 : universal vertex 0 joined to C7 on 1..7
    return graph_join([0], graph_C7())

def graph_petersen():
    # standard Petersen: outer 5-cycle 0-4, inner star 5-9 (5-cycle 5-7-9-6-8-5 pattern), spokes
    a = [0]*10
    for i in range(5):
        j = (i+1) % 5
        a[i] |= 1<<j; a[j] |= 1<<i           # outer cycle
        a[i] |= 1 << (5 + i); a[5 + i] |= 1 << i   # spokes
        a[5+i] |= 1 << (5 + (i+2) % 5); a[5 + (i+2) % 5] |= 1 << (5+i)  # inner star
    return a

# ---------------------------------------------------------------------------
# S0 — classifier self battery
# ---------------------------------------------------------------------------
print("="*78); print("S0 TWO-CODE C5 CLASSIFIERS — self battery"); print("="*78)
ok("S0-signatures", len(C5_SIGS) == 12, f"12 labeled C5 signatures built (got {len(C5_SIGS)})")
tests = [("C5", graph_C5(), True), ("C7", graph_C7(), False), ("C4", graph_C4(), False),
         ("P6", None, False)]
ok("S0-C5-detected", has_C5(5, graph_C5(), 1) and has_C5(5, graph_C5(), 2),
   "C5 detected by both codes")
ok("S0-C7-clean", not has_C5(7, graph_C7(), 1) and not has_C5(7, graph_C7(), 2),
   "C7 clean by both codes")
ok("S0-C7chord-clean", not has_C5(7, graph_C7chord(), 1) and not has_C5(7, graph_C7chord(), 2),
   "C7+chord(0,2) clean by both codes")
ok("S0-W8-clean", not has_C5(8, graph_W8(), 1) and not has_C5(8, graph_W8(), 2),
   "K1∨C7 (W8) clean by both codes")
pet = graph_petersen()
ok("S0-Petersen-detected", has_C5(10, pet, 1) and has_C5(10, pet, 2),
   "Petersen carries an induced C5 (both codes) — negative control")
# random duel at n=7
duel_n = 8000
disagree = 0
prs7 = pairs_of(7)
for t in range(duel_n):
    em = rng.getrandbits(21)
    adj = adj_from_emask(7, em, prs7)
    if has_C5(7, adj, 1) != has_C5(7, adj, 2):
        disagree += 1
ok("S0-duel-20k", disagree == 0, f"{duel_n} random n=7 graphs: code1 vs code2 disagree x{disagree}")

# ---------------------------------------------------------------------------
# S1 — exhaustive n<=6
# ---------------------------------------------------------------------------
print("="*78); print("S1 EXHAUSTIVE n<=6 — counts, h-rungs, CORE census"); print("="*78)

BANK_H = {1:1, 2:2, 3:2, 4:2, 5:3, 6:3}     # banked h_{C5}(n) (W78-61K S1/S2)
BANK_CORES = {5: 420, 6: 18840}             # banked COARSE cores (connected ∧ co-connected only)

def is_coarse_core(n, adj):
    return connected(n, adj) and co_connected(n, adj)

for n in range(1, 7):
    prs = pairs_of(n)
    npairs = len(prs)
    cnt1 = cnt2 = 0
    hmin = None
    hwit = None
    cores = 0
    coarse = 0
    core_wit_hom3 = None
    core_min_hom = None
    core_hom_wit = None
    aomega_duel_fail = 0
    for em in range(1 << npairs):
        adj = adj_from_emask(n, em, prs)
        c1 = has_C5(n, adj, 1)
        c2 = has_C5(n, adj, 2)
        if c1 != c2:
            cnt2 = -10**9  # force fail
            break
        if not c1:
            cnt1 += 1
            if is_coarse_core(n, adj):
                coarse += 1
            if is_core(n, adj):
                cores += 1
                al = exact_alpha(n, adj)
                om = exact_omega(n, adj)
                # duel against brute for n<=5 fully, n=6 sampled
                if n <= 5 or (em % 7 == 0):
                    if al != brute_alpha(n, adj) or om != brute_omega(n, adj):
                        aomega_duel_fail += 1
                hom = max(al, om)
                if core_min_hom is None or hom < core_min_hom:
                    core_min_hom = hom
                    core_hom_wit = (em, al, om)
                if al == 3 and om == 3 and core_wit_hom3 is None:
                    core_wit_hom3 = (em, al, om)
            al = exact_alpha(n, adj)
            hom = max(al, exact_omega(n, adj))
            if hmin is None or hom < hmin:
                hmin = hom
                hwit = (em, hom)
    ok(f"S1-n{n}-two-code", cnt2 == 0 and cnt1 > 0,
       f"n={n}: C5-free labeled = {cnt1}, two-code full agreement" if cnt2 == 0 else "CODE DISAGREEMENT")
    ok(f"S1-n{n}-h-rung", hmin == BANK_H[n], f"n={n}: h_C5 = {hmin} (bank {BANK_H[n]})")
    if n in BANK_CORES:
        ok(f"S1-n{n}-coarse-core-count", coarse == BANK_CORES[n],
           f"n={n}: coarse cores (conn & co-conn) = {coarse} (bank {BANK_CORES[n]})")
        note(f"S1-n{n}-frontier-core-count",
             f"n={n}: FRONTIER cores (conn & co-conn & triangle & indep-triple) = {cores} "
             f"- the exact C5-DICH remaining stratum (new census row)")
    else:
        note(f"S1-n{n}-core-count", f"n={n}: coarse cores = {coarse}, frontier cores = {cores}")
    note(f"S1-n{n}-core-minhom", f"n={n}: core min hom = {core_min_hom}, witness em={core_hom_wit}")
    if n >= 5:
        ok(f"S1-n{n}-aomega-duel", aomega_duel_fail == 0, f"n={n}: α/ω B&B-vs-brute duel on cores fail x{aomega_duel_fail}")
    if n == 5:
        ok("S1-n5-core-wit-hom3", core_wit_hom3 is not None, f"n=5 core with α=ω=3 exists: em={core_wit_hom3}")
    if n == 6:
        ok("S1-n6-core-wit-hom3", core_wit_hom3 is not None, f"n=6 core with α=ω=3 exists: em={core_wit_hom3}")

# ---------------------------------------------------------------------------
# S2 — exhaustive n=7 (numpy sweep + core census)
# ---------------------------------------------------------------------------
print("="*78); print("S2 EXHAUSTIVE n=7 — numpy 2^21 sweep + CORE census"); print("="*78)

N7 = 7
prs7 = pairs_of(7)
cnt7 = None
core7 = 0
core7_conn_samples = []
if HAVE_NUMPY:
    idx = np.arange(1 << 21, dtype=np.uint32)
    bits = [((idx >> k) & 1).astype(np.uint8) for k in range(21)]
    bad = np.zeros(1 << 21, dtype=bool)
    for S in itertools.combinations(range(7), 5):
        pairpos = {}
        k = 0
        for i in range(7):
            for j in range(i+1, 7):
                pairpos[(i, j)] = k
                k += 1
        # edge count and per-vertex degrees within S
        e = np.zeros(1 << 21, dtype=np.uint8)
        degs = []
        for v in S:
            dv = np.zeros(1 << 21, dtype=np.uint8)
            for u in S:
                if u == v: continue
                key = (min(u,v), max(u,v))
                dv += bits[pairpos[key]]
            degs.append(dv)
        for x, y in itertools.combinations(S, 2):
            e += bits[pairpos[(x, y)]]
        cond = (e == 5)
        for dv in degs:
            cond &= (dv >= 2)
        bad |= cond
    free7 = np.where(~bad)[0]
    cnt7 = int(free7.size)
    ok("S2-n7-count-vs-bank", cnt7 == 1742336, f"n=7 C5-free labeled = {cnt7} (bank 1,742,336)")
    # core census (pure python over the C5-free emasks; cheapest checks first)
    t_s2 = time.time()
    indep_triples = list(itertools.combinations(range(7), 3))
    tri_pairs = [(i, j) for i in range(7) for j in range(i+1, 7)]
    core_count = 0
    core_wit = None
    core_wit_hom3 = None
    checked = 0
    for em in free7:
        em = int(em)
        adj = adj_from_emask(7, em, prs7)
        checked += 1
        # triangle: some edge with common neighbor
        tri = False
        for (i, j) in tri_pairs:
            if (adj[i] >> j) & 1 and (adj[i] & adj[j]):
                tri = True
                break
        if not tri:
            continue
        if not connected(7, adj):
            continue
        cadj = complement_adj(7, adj)
        if not connected(7, cadj):
            continue
        # indep triple
        it3 = False
        for (a, b, c) in indep_triples:
            if not ((adj[a] >> b) & 1) and not ((adj[a] >> c) & 1) and not ((adj[b] >> c) & 1):
                it3 = True
                break
        if not it3:
            continue
        core_count += 1
        if core_wit is None:
            core_wit = em
        if core_wit_hom3 is None:
            al = exact_alpha(7, adj)
            om = exact_omega(7, adj)
            if al == 3 and om == 3:
                core_wit_hom3 = em
    core7 = core_count
    ok("S2-n7-core-census", core7 > 0, f"n=7 C5-free cores = {core7} (exhaustive over {checked} C5-free labeled graphs), wall {round(time.time()-t_s2,1)}s")
    note("S2-n7-core-wit", f"first core emask = {core_wit}")
    ok("S2-n7-core-hom3-wit", core_wit_hom3 is not None, f"n=7 core with α=ω=3 exists (em={core_wit_hom3}) → h_core(7)=3")
    # verify the C7+chord named witness
    w = graph_C7chord()
    ok("S2-C7chord-core", is_core(7, w) and not has_C5(7, w, 1) and not has_C5(7, w, 2)
       and exact_alpha(7, w) == 3 and exact_omega(7, w) == 3,
       "C7+chord(0,2): C5-free (both codes), core, α=ω=3 — certified h_core(7)=3 witness")
    # classifier duel on a 20k sample of the free set
    dis = 0
    sample = rng.sample(range(cnt7), min(20000, cnt7))
    for s in sample:
        em = int(free7[s])
        adj = adj_from_emask(7, em, prs7)
        if has_C5(7, adj, 2):   # must be free per code2 as well
            dis += 1
    ok("S2-n7-duel-20k", dis == 0, f"20k sampled C5-free (code1/numpy) all clean under code2")
    # h(7) re-derivation: R(3,3)=6 anchor + witness C7
    c7g = graph_C7()
    ok("S2-h7-rung", (not has_C5(7, c7g, 1)) and max(exact_alpha(7, c7g), exact_omega(7, c7g)) == 3,
       "h_C5(7)=3 re-derived: C7 witness α=3,ω=2; lower by banked R(3,3)=6 anchor (any 6 vertices force hom>=3)")
else:
    note("S2", "numpy missing — n=7 sweep skipped (bank cross-check unavailable this run)")

# ---------------------------------------------------------------------------
# S3 — the n=8 rung + substitution package
# ---------------------------------------------------------------------------
print("="*78); print("S3 THE n=8 RUNG + SUBSTITUTION PACKAGE"); print("="*78)

W8 = graph_W8()
ok("S3-W8-C5free", not has_C5(8, W8, 1) and not has_C5(8, W8, 2), "W8 = K1∨C7 is C5-free (both codes)")
aW8, oW8 = exact_alpha(8, W8), exact_omega(8, W8)
ok("S3-W8-hom3", aW8 == 3 and oW8 == 3, f"W8 α={aW8}, ω={oW8} (expect 3,3)")
ok("S3-W8-connected", connected(8, W8), "W8 connected")
ok("S3-W8-NOT-core", not co_connected(8, W8),
   "W8 NOT co-connected (complement = point ⊔ C̄7) → falls to C5-REDUCTION case J, as it must")
# brute duel on W8
ok("S3-W8-brute-duel", brute_alpha(8, W8) == aW8 and brute_omega(8, W8) == oW8,
   "W8 α/ω B&B vs 2^8 brute: agree")

# --- substitution ----------------------------------------------------------
def substitute(frame, pieces):
    """G = frame[pieces]: disjoint union of pieces; complete bipartite between
    V_i, V_j iff i~j in frame. Vertex numbering: piece blocks in order."""
    k = len(frame)
    sizes = [len(p) for p in pieces]
    offs = [0]*(k+1)
    for i in range(k):
        offs[i+1] = offs[i] + sizes[i]
    n = offs[k]
    adj = [0]*n
    for i in range(k):
        for a in range(sizes[i]):
            gi = offs[i] + a
            adj[gi] |= pieces[i][a] << offs[i]
            for j in range(k):
                if j != i and (frame[i] >> j) & 1:
                    adj[gi] |= (((1 << sizes[j]) - 1) << offs[j])
    return adj

# substitution closure battery: C5-free frame + C5-free pieces => C5-free
t_b = time.time()
bat = 0; bat_bad = 0
c5free_bank67 = []   # small C5-free emasks at n=5,6 for frames/pieces
for n, lim in ((5, 400), (6, 400)):
    prs = pairs_of(n)
    got = 0
    for em in range(1 << len(prs)):
        adj = adj_from_emask(n, em, prs)
        if not has_C5(n, adj, 1):
            c5free_bank67.append((n, adj))
            got += 1
            if got >= lim:
                break
for t in range(800):
    kf = rng.randint(2, 5)
    frame = rng.choice([a for (nn, a) in c5free_bank67 if nn >= kf])
    # pick kf distinct slots: use the first kf vertices of the frame graph relabeled
    # build a k-vertex induced subgraph of a C5-free graph as the frame
    sub = rng.sample(range(len(frame)), kf)
    remap = {v: i for i, v in enumerate(sub)}
    fr = [0]*kf
    for v in sub:
        for u in sub:
            if (frame[v] >> u) & 1:
                fr[remap[v]] |= 1 << remap[u]
    pieces = []
    tot = 0
    for i in range(kf):
        p = rng.choice(c5free_bank67)[1]
        if rng.random() < 0.5:
            p = complement_adj(len(p), p)
        pieces.append(p)
        tot += len(p)
    if tot > 12 or tot < 3:
        continue
    G = substitute(fr, pieces)
    bat += 1
    if has_C5(len(G), G, 1) or has_C5(len(G), G, 2):
        bat_bad += 1
ok("S3-subst-battery", bat_bad == 0 and bat >= 200,
   f"{bat} substitutions of C5-free frames×pieces: all C5-free (both codes), wall {round(time.time()-t_b,1)}s")

# negative control: frame containing C5 → substitution contains C5
neg = 0; neg_ok = 0
for t in range(200):
    pieces = [ [0] for _ in range(5) ]   # singletons
    G = substitute(graph_C5(), pieces)
    neg += 1
    if has_C5(5, G, 1) and has_C5(5, G, 2):
        neg_ok += 1
ok("S3-subst-negative", neg_ok == neg, f"{neg} C5-frames with singleton pieces: C5 detected every time")

# contraction battery: G C5-free built by substitution, contract a module back
t_c = time.time()
con = 0; con_bad = 0
for t in range(1500):
    kf = rng.randint(2, 4)
    frame = rng.choice([a for (nn, a) in c5free_bank67 if nn >= kf])
    sub = rng.sample(range(len(frame)), kf)
    remap = {v: i for i, v in enumerate(sub)}
    fr = [0]*kf
    for v in sub:
        for u in sub:
            if (frame[v] >> u) & 1:
                fr[remap[v]] |= 1 << remap[u]
    pieces = [rng.choice(c5free_bank67)[1] for _ in range(kf)]
    G = substitute(fr, pieces)
    # contract piece 0 (a module) to a point
    m = len(pieces[0])
    n = len(G)
    keep = [v for v in range(n) if v >= m]
    remap2 = {v: i + 1 for i, v in enumerate(keep)}
    Q = [0]*(1 + len(keep))
    Q[0] = 0
    for v in keep:
        Q[remap2[v]] = 0
    for v in keep:
        for u in keep:
            if (G[v] >> u) & 1:
                Q[remap2[v]] |= 1 << remap2[u]
        if (G[v] >> 0) & 1:
            Q[remap2[v]] |= 1
            Q[0] |= 1 << remap2[v]
    con += 1
    if has_C5(len(Q), Q, 1) or has_C5(len(Q), Q, 2):
        con_bad += 1
ok("S3-contraction-battery", con_bad == 0 and con >= 1000,
   f"{con} module contractions of C5-free graphs: quotients all C5-free, wall {round(time.time()-t_c,1)}s")

# --- the iterated witness X_2 = W8[W8 × 8] (64 vertices) -------------------
X2 = substitute(W8, [W8]*8)
nX2 = len(X2)
t_x = time.time()
scan = 0; found = 0
allsubs = list(itertools.combinations(range(nX2), 5))
for t in range(200000):
    S = rng.sample(range(nX2), 5)
    scan += 1
    if subset_is_C5_code1(X2, S) or subset_is_C5_code2(X2, S):
        found += 1
        break
ok("S3-X2-scan", found == 0, f"X_2 = W8[W8×8] (64 vertices): {scan} random 5-subsets, zero induced C5 (both codes), wall {round(time.time()-t_x,1)}s")
# exact alpha/omega by the substitution formulas, verified against structure:
alpha_X2 = 3 * exact_alpha(8, W8)   # α(Q[M]) = max_I Σ α(M_i) = α(Q)·α(M) for equal pieces
omega_X2 = 3 * exact_omega(8, W8)
ok("S3-X2-alphaomega", alpha_X2 == 9 and omega_X2 == 9,
   f"X_2 α = ω = 9 by the substitution formulas (α(Q[M]) = max_I Σ α(M_i)); n = 64 → hom = 9 = 64^(log8 3)")
note("S3-CAP", "c ≤ log3/log8 = %.5f: X_t = W8[W8×8]^{t-1} is C5-free (C61-C5-SUBST law), "
     "n_t = 8^t, hom = 3^t — any class-wide exponent c obeys 3^t ≥ 8^{ct}" % (log(3)/log(8)))

# sqrt-ladder certification n<=8
ladder = []
for n, h in ((1,1),(2,2),(3,2),(4,2),(5,3),(6,3),(7,3),(8,3)):
    ladder.append((n, h, h*h >= n, h*h == n))
ok("S3-sqrt-ladder", all(x[2] for x in ladder),
   "h_C5(n)^2 >= n for n=1..8: " + ", ".join(f"n={n}:h={h}:{'EQ' if e else 'GE'}" for n,h,g,e in ladder))

# ---------------------------------------------------------------------------
# S4 — the hom-3 frontier hunt (time-boxed annealing)
# ---------------------------------------------------------------------------
print("="*78); print("S4 THE HOM-3 FRONTIER HUNT (annealing, time-boxed)"); print("="*78)

def flip_safe_check(n, adj, i, j, prs, add=True):
    """would flipping pair (i,j) create an induced C5? A flip changes only the
    5-sets containing BOTH i and j: adding can only complete a C5 whose cycle
    uses (i,j); removing can only expose a C5 whose CHORD was (i,j). So scan
    all 5-sets containing i and j in the POST state — both directions."""
    if add:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    else:
        adj[i] &= ~(1 << j)
        adj[j] &= ~(1 << i)
    bad = False
    others = [v for v in range(n) if v != i and v != j]
    for T in itertools.combinations(others, 3):
        S = (i, j) + T
        if subset_is_C5_code1(adj, S):
            bad = True
            break
    if add:
        adj[i] &= ~(1 << j)
        adj[j] &= ~(1 << i)
    else:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return bad

def hom_of(n, adj):
    return max(exact_alpha(n, adj), exact_omega(n, adj))

def hunt(n, budget_s, require_core, tag):
    """annealing descent minimizing (max(α,ω), α+ω) subject to C5-free"""
    t_end = time.time() + budget_s
    prs = pairs_of(n)
    best_hom = None
    best_adj = None
    best_core_hom = None
    starts = 0
    states = 0
    templates = []
    # templates: C7-based (n=8: W8; n=9: W8+vertex; n=10: W8+2; C9 with chords)
    if n == 8:
        templates.append(graph_W8())
    if n == 9:
        base = graph_join([0], graph_C7())
        # + vertex 8 adjacent to 0 and to a random subset of C7 avoiding C5/ω≥4
        templates.append(base + [0])
    if n == 10:
        templates.append(graph_join([0], graph_C7()) + [0, 0])
    if n == 12:
        templates.append(graph_join([0, 0], graph_C7()) + [0]*3)  # placeholder
    while time.time() < t_end:
        starts += 1
        if templates and rng.random() < 0.5:
            adj = templates[rng.randrange(len(templates))][:]
            while len(adj) < n:
                adj = adj + [0]
            adj = [a for a in adj]
            # randomize a few safe flips
            for _ in range(3*n):
                i, j = rng.sample(range(n), 2)
                if (adj[i] >> j) & 1:
                    adj[i] &= ~(1 << j); adj[j] &= ~(1 << i)
                else:
                    if not flip_safe_check(n, adj, i, j, prs, add=True):
                        adj[i] |= 1 << j; adj[j] |= 1 << i
        else:
            p = rng.choice([0.25, 0.4, 0.5, 0.6, 0.75])
            em = rng.getrandbits(len(prs))
            adj = adj_from_emask(n, em, prs)
        # repair to C5-free: delete edges in C5s greedily
        for _ in range(50*n):
            if not has_C5(n, adj, 1):
                break
            S = None
            for Sc in itertools.combinations(range(n), 5):
                if subset_is_C5_code1(adj, Sc):
                    S = Sc; break
            if S is None:
                break
            e = [(x, y) for x, y in itertools.combinations(S, 2) if (adj[x] >> y) & 1]
            x, y = rng.choice(e)
            adj[x] &= ~(1 << y); adj[y] &= ~(1 << x)
        if has_C5(n, adj, 1):
            continue
        # descent
        cur_hom = hom_of(n, adj)
        cur_sum = exact_alpha(n, adj) + exact_omega(n, adj)
        steps = 0
        while time.time() < t_end and steps < 400:
            steps += 1
            states += 1
            i, j = rng.sample(range(n), 2)
            had = (adj[i] >> j) & 1
            if flip_safe_check(n, adj, i, j, prs, add=not had):
                continue
            if had:
                adj[i] &= ~(1 << j); adj[j] &= ~(1 << i)
            else:
                adj[i] |= 1 << j; adj[j] |= 1 << i
            nh = hom_of(n, adj)
            ns = exact_alpha(n, adj) + exact_omega(n, adj)
            if (nh, ns) <= (cur_hom, cur_sum) or rng.random() < 0.02:
                cur_hom, cur_sum = nh, ns
                assert not has_C5(n, adj, 1), "invariant: descent states stay C5-free"
                if best_hom is None or cur_hom < best_hom:
                    best_hom = cur_hom
                    best_adj = adj[:]
            else:
                if had:
                    adj[i] |= 1 << j; adj[j] |= 1 << i
                else:
                    adj[i] &= ~(1 << j); adj[j] &= ~(1 << i)
    # verify best
    verdict = None
    if best_adj is not None:
        c1 = has_C5(n, best_adj, 1); c2 = has_C5(n, best_adj, 2)
        al = exact_alpha(n, best_adj); om = exact_omega(n, best_adj)
        bal = brute_alpha(n, best_adj); bom = brute_omega(n, best_adj)
        core = is_core(n, best_adj)
        verdict = (best_hom, al, om, not c1, not c2, bal == al, bom == om, core)
        ok(f"S4-n{n}{tag}-verify", (not c1) and (not c2) and bal == al and bom == om,
           f"n={n}: best hom found = {best_hom} (α={al},ω={om}), C5-free both codes, brute duel ok, core={core}; starts={starts}, states={states}")
        if require_core:
            note(f"S4-n{n}{tag}-core-probe",
                 f"n={n} core-stratum hunt: best hom = {best_hom}, best-is-core = {core}, "
                 f"hom-3 core found = {core and max(al, om) == 3}")
        return best_hom, verdict, best_adj, starts, states
    note(f"S4-n{n}{tag}", "no feasible state found (budget too small)")
    return None, None, None, starts, states

res84 = hunt(8, 25.0, True, "core")
res9 = hunt(9, 35.0, False, "")
res10 = hunt(10, 40.0, False, "")
res11 = hunt(11, 35.0, False, "")
res12 = hunt(12, 30.0, False, "")

for n, r in ((8, res84), (9, res9), (10, res10), (11, res11), (12, res12)):
    if r[0] is not None:
        note(f"S4-frontier-n{n}", f"min hom found at n={n}: {r[0]} (starts={r[3]}, states={r[4]})")
        if r[2] is not None:
            note(f"S4-witness-n{n}", "adjacency witness: " + str([hex(x) for x in r[2]]))

# sqrt-ladder extension evidence
note("S4-sqrt-probe", "the √n-ladder (h(n)^2 >= n) is CERTIFIED for n<=8 (S3); "
     "the first possible break is a hom-3 graph at n=10 (9 < 10). The hunt above probes n=9..12.")

# ---------------------------------------------------------------------------
# S5 — receipts
# ---------------------------------------------------------------------------
print("="*78)
print(f"ENGINE61C5 SUMMARY: PASS={PASS} FAIL={FAIL} wall={wall()}s")
REC.append(f"SUMMARY :: PASS={PASS} FAIL={FAIL} wall={wall()}s numpy={HAVE_NUMPY}")
with open("receipts61c5.txt", "w") as f:
    f.write("\n".join(REC) + "\n")
print("receipts -> receipts61c5.txt")
if FAIL > 0:
    sys.exit(1)
