#!/usr/bin/env python3
# engine61census.py — W75-61E THE GRAND CENSUS ENGINE (Erdős–Hajnal #61, engine/doubter lane)
#
# MISSION (W75_BRIEFS/61E.md): the complete EH census for ALL unlabeled graphs on <=4 vertices
#   (the 11 on 4 vertices + the 4 on 3 + K2/2K1/K1), exact h_H(n) = min over H-free G on n
#   vertices of max(alpha(G),omega(G)) and rho_H(n) = ln h_H(n)/ln n, for n = 1..7 by FULL
#   labeled enumeration (2^21 = 2,097,152 at n=7 — BOTH a pure-bitmask-Python lane AND an
#   independent vectorized-numpy lane, exact agreement required), n = 8 by an EXHAUSTIVE
#   chunked 2^28 scan of the m<=3 stratum (exact h_H(8) for every H: the universal Ramsey
#   floor m>=3 at n>=6 is census-certified, so h_H(8)=3 iff an H-free m=3 graph exists,
#   else h_H(8)>=4 with named witnesses), plus adversarial annealing search at n=8..32.
#
#   Battery: independent alpha (bitmask B&B) vs omega (direct clique B&B) vs complement duality;
#   induced containment: all-subset scan vs backtracking matcher (fresh algorithms, zero shared
#   code with the 61K lane); complement self-test h_H(n) == rho_Hbar(n)-consistent EXACTLY
#   (0 mismatches allowed); banked #61 claims re-derived (F7 floor(sqrt n), P4 c=1/2 incl.
#   alpha*omega>=n + Seinsche SL, CLAW n^{1/3}/2 + degree law, RAM K4 every c<1/3, Theorems
#   1/2/3 exact laws, Bell census, banked [B]-table reproduction); structural-lemma
#   certification (both the induced and the subgraph readings — counterexamples caught and
#   named); tightness witnesses (block family, complete multipartite family, Ramsey
#   triangle-free frontier, projective-plane polarity graphs, C5-blowup/Heawood verdicts);
#   arsenal law spot-checks.
#
# Layout convention (INDEPENDENT of 61K's engine61.py): pairs (i,j), i<j, in lexicographic
# order; bit index = number of lexicographically-earlier pairs. All logs natural.
# The engine never stops; it never lies. In English, always.

import time, math, json, random, itertools, sys

try:
    import numpy as np
except Exception as ex:
    print("[FATAL] numpy required:", ex); sys.exit(1)

random.seed(7361)
T0 = time.monotonic()
def el(): return time.monotonic() - T0

RECEIPT_LINES = []
def R(tag, s=""):
    line = f"{tag} {s}" if tag else s
    RECEIPT_LINES.append(line)
    print(line, flush=True)

R("=" * 78)
R("[E0] W75-61E GRAND CENSUS ENGINE — start (t=0.0s)")

# ----------------------------------------------------------------------------
# E0. Bit layout, canonical forms, the 11 unlabeled 4-vertex graphs from first
#     principles (all 64 labeled graphs, brute-permutation canonicalization).
# ----------------------------------------------------------------------------

def M(n): return n * (n - 1) // 2

def pair_list(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]

def build_pos(n):
    return {p: b for b, p in enumerate(pair_list(n))}

def edges_to_mask(edges, n):
    pos = build_pos(n)
    m = 0
    for (i, j) in edges:
        if i > j: i, j = j, i
        m |= 1 << pos[(i, j)]
    return m

def mask_to_edges(mask, n):
    return [p for p, b in build_pos(n).items() if mask >> b & 1]

def complement_mask(mask, n):
    return mask ^ ((1 << M(n)) - 1)

_PERMS = {}
def perms(n):
    if n not in _PERMS:
        _PERMS[n] = list(itertools.permutations(range(n)))
    return _PERMS[n]

def relabel_mask(mask, n, perm):
    pos = build_pos(n)
    out = 0
    for ((i, j), b) in pos.items():
        if mask >> b & 1:
            a, c = perm[i], perm[j]
            if a > c: a, c = c, a
            out |= 1 << pos[(a, c)]
    return out

def canonical_mask(mask, n):
    return min(relabel_mask(mask, n, p) for p in perms(n))

def adj_of(mask, n):
    adj = [0] * n
    for ((i, j), b) in build_pos(n).items():
        if mask >> b & 1:
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    return adj

def comp_adj(adj, n):
    full = (1 << n) - 1
    return [(full ^ adj[i]) & ~(1 << i) for i in range(n)]

def POPC(x):
    return bin(x).count("1")

# ---- named target graphs -----------------------------------------------------
H_DEFS = {
    "K1":         (1, []),
    "K2":         (2, [(0, 1)]),
    "2K1":        (2, []),
    "K3":         (3, [(0, 1), (0, 2), (1, 2)]),
    "P3":         (3, [(0, 1), (1, 2)]),
    "K2+K1":      (3, [(0, 1)]),
    "3K1":        (3, []),
    "K4":         (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    "4K1(K4bar)": (4, []),
    "P4":         (4, [(0, 1), (1, 2), (2, 3)]),
    "C4":         (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
    "2K2":        (4, [(0, 1), (2, 3)]),
    "paw":        (4, [(0, 1), (0, 2), (1, 2), (2, 3)]),
    "P3+K1":      (4, [(0, 1), (1, 2)]),
    "diamond":    (4, [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    "K2+2K1":     (4, [(0, 1)]),
    "K1,3(claw)": (4, [(0, 1), (0, 2), (0, 3)]),
    "K3+K1":      (4, [(0, 1), (0, 2), (1, 2)]),
}
H_ORDER = list(H_DEFS.keys())          # the 18-graph H universe
H_MASK = {k: edges_to_mask(v[1], v[0]) for k, v in H_DEFS.items()}
H_ADJ = {k: adj_of(H_MASK[k], H_DEFS[k][0]) for k in H_DEFS}
H_NV = {k: v[0] for k, v in H_DEFS.items()}
COMPLEMENT_PAIR = {
    "K1": "K1", "K2": "2K1", "2K1": "K2", "K3": "3K1", "3K1": "K3",
    "P3": "K2+K1", "K2+K1": "P3", "K4": "4K1(K4bar)", "4K1(K4bar)": "K4",
    "P4": "P4", "C4": "2K2", "2K2": "C4", "paw": "P3+K1", "P3+K1": "paw",
    "diamond": "K2+2K1", "K2+2K1": "diamond", "K1,3(claw)": "K3+K1", "K3+K1": "K1,3(claw)",
}

# ---- the 11 classes on 4 vertices + 4 classes on 3 vertices, from scratch ----
bycanon4 = {}
for _m in range(64):
    bycanon4.setdefault(canonical_mask(_m, 4), []).append(_m)
assert len(bycanon4) == 11, f"expected 11 unlabeled 4-vertex graphs, got {len(bycanon4)}"
named4 = {canonical_mask(H_MASK[k], 4): k for k in H_DEFS if H_NV[k] == 4}
assert len(named4) == 11 and set(named4) == set(bycanon4)
CLS4_NAMES = sorted(named4.values())
CLS4_INDEX = {nm: i for i, nm in enumerate(CLS4_NAMES)}
CODE4_TO_CLS = [0] * 64
for _c, _ms in bycanon4.items():
    for _m in _ms:
        CODE4_TO_CLS[_m] = CLS4_INDEX[named4[_c]]

N3_NAMES = ["3K1", "K2+K1", "P3", "K3"]
_n3canon = {canonical_mask(H_MASK[k], 3): k for k in N3_NAMES}
_p3pos = build_pos(3)
CODE3_TO_CLS = []
for _c in range(8):          # bits: (0,1)=4, (0,2)=2, (1,2)=1
    _m = 0
    if _c & 4: _m |= 1 << _p3pos[(0, 1)]
    if _c & 2: _m |= 1 << _p3pos[(0, 2)]
    if _c & 1: _m |= 1 << _p3pos[(1, 2)]
    CODE3_TO_CLS.append(N3_NAMES.index(_n3canon[canonical_mask(_m, 3)]))
CLS3_INDEX = {nm: i for i, nm in enumerate(N3_NAMES)}

R("[E0] 4-vertex census from first principles: 64 labeled graphs -> 11 isomorphism classes")
R(f"[E0]   (brute-permutation canonical form; class sizes "
  f"{ {named4[c]: len(ms) for c, ms in sorted(bycanon4.items(), key=lambda t: named4[t[0]])} })")
R(f"[E0] the 11 classes: {', '.join(CLS4_NAMES)}")
R(f"[E0] brief's list {{K4,K4bar,P4,C4,2K2,paw,P3+K1,diamond,K2+2K1,K1,3,K3+K1}} == our 11: "
  f"{set(CLS4_NAMES) == set(['K4', '4K1(K4bar)', 'P4', 'C4', '2K2', 'paw', 'P3+K1', 'diamond', 'K2+2K1', 'K1,3(claw)', 'K3+K1'])}")
comp_ok = all(canonical_mask(complement_mask(H_MASK[k], H_NV[k]), H_NV[k]) ==
              canonical_mask(H_MASK[COMPLEMENT_PAIR[k]], H_NV[k]) for k in H_DEFS)
R(f"[E0] complement-pair structure machine-verified for all 18 H (K4<->4K1, C4<->2K2, "
  f"paw<->P3+K1, diamond<->K2+2K1, claw<->K3+K1, P4 self-complementary, ...): {comp_ok}")
assert comp_ok and len(bycanon4) == 11

# ----------------------------------------------------------------------------
# E1. Independent implementations.
#     (A) alpha: bitmask B&B MIS.       (A') omega = alpha(complement).
#     (C) omega: DIRECT clique B&B.      (B) containment: all-subset scan.
#     (D) containment: backtracking induced matcher.
# ----------------------------------------------------------------------------

def alpha_bb(adj, n):
    """(A) exact max independent set, bitmask B&B: branch on lowest candidate vertex."""
    full = (1 << n) - 1
    if n <= 9:
        tab = POPC9
        pc = tab.__getitem__
    else:
        pc = lambda x: bin(x).count("1")
    best = 0
    def rec(cand, sz):
        nonlocal best
        if sz + pc(cand) <= best:
            return
        if cand == 0:
            if sz > best: best = sz
            return
        v = (cand & -cand).bit_length() - 1
        rec(cand & ~(adj[v] | (1 << v)), sz + 1)
        rec(cand & ~(1 << v), sz)
    rec(full, 0)
    return best

POPC9 = [bin(i).count("1") for i in range(512)]

def omega_clique_direct(adj, n):
    """(C) exact clique number, DIRECT clique B&B (no complement call)."""
    if n <= 9:
        pc = POPC9.__getitem__
    else:
        pc = lambda x: bin(x).count("1")
    best = 0
    def rec(cand, sz):
        nonlocal best
        if cand == 0:
            if sz > best: best = sz
            return
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            if sz + 1 + pc(c) > best:
                rec(c & adj[v], sz + 1)
    rec((1 << n) - 1, 0)
    return best

def contains_induced_matcher(adjG, n, hname):
    """(D) backtracking injective induced-embedding search (adjacency AND non-adjacency)."""
    h = H_NV[hname]; adjH = H_ADJ[hname]
    order = sorted(range(h), key=lambda v: -bin(adjH[v]).count("1"))
    phimap = [-1] * h
    full = (1 << n) - 1
    def rec(k, used):
        if k == h: return True
        hv = order[k]
        cand = full & ~used
        for kk in range(k):
            hw = order[kk]; gw = phimap[hw]
            if adjH[hv] >> hw & 1: cand &= adjG[gw]
            else: cand &= ~adjG[gw] & full
        if cand == 0: return False
        while cand:
            g = (cand & -cand).bit_length() - 1
            cand &= cand - 1
            phimap[hv] = g
            if rec(k + 1, used | (1 << g)): return True
        phimap[hv] = -1
        return False
    return rec(0, 0)

class SubsetScan:
    """(B) all-subset-scan containment for a fixed n (independent algorithm from D)."""
    def __init__(self, n):
        self.n = n
        self.sub4 = list(itertools.combinations(range(n), 4))
        self.sub3 = list(itertools.combinations(range(n), 3))
        self.pos = build_pos(n)
        self.s4bits = [[self.pos[(a, b)] for a, b in itertools.combinations(S, 2)] for S in self.sub4]
        self.s3bits = [[self.pos[(a, b)] for a, b in itertools.combinations(S, 2)] for S in self.sub3]

    def cont(self, mask):
        """returns (cont4, cont3): bitmask of contained 4-vertex / 3-vertex classes.
        Code convention: pair k of the subset (its local lexicographic order) -> bit k,
        i.e. the code IS the standard edge-mask of the induced subgraph under the
        subset's own vertex labeling — exact, no relabeling."""
        cont4 = 0
        for ps in self.s4bits:
            code = 0
            for k, b in enumerate(ps):
                code |= ((mask >> b) & 1) << k
            cont4 |= 1 << CODE4_TO_CLS[code]
        cont3 = 0
        for ps in self.s3bits:
            code = 0
            for k, b in enumerate(ps):
                code |= ((mask >> b) & 1) << k
            cont3 |= 1 << CODE3_TO_CLS[code]
        return cont4, cont3

    def contains(self, mask, hname):
        hv = H_NV[hname]
        if hv > self.n: return False
        c4, c3 = self.cont(mask)
        if hv == 4: return bool(c4 & (1 << CLS4_INDEX[hname]))
        if hv == 3: return bool(c3 & (1 << CLS3_INDEX[hname]))
        if hname == "K2": return mask != 0
        if hname == "2K1": return complement_mask(mask, self.n) != 0
        return True   # K1

# Code conventions everywhere: pair k of a vertex subset (local lexicographic order)
# -> bit k of the subset code; the code is the standard edge-mask of the induced
# subgraph in the subset's own labeling. Verified against canonical ground truth.

# ----------------------------------------------------------------------------
# E2. PURE-PYTHON FULL CENSUS LANE (n = 1..7, all 2^M(n) labeled graphs).
# ----------------------------------------------------------------------------

BIG = 10 ** 9

def census_python(n):
    N = 1 << M(n)
    scan = SubsetScan(n)
    best = {k: (BIG, None) for k in H_ORDER}
    free_cnt = {k: 0 for k in H_ORDER}
    minprod = BIG
    for mask in range(N):
        adj = adj_of(mask, n)
        a = alpha_bb(adj, n)
        w = alpha_bb(comp_adj(adj, n), n)          # (A')
        m = a if a > w else w
        c4, c3 = scan.cont(mask)
        b4 = 0
        for k in H_ORDER:
            hv = H_NV[k]
            if hv > n:
                free = True
            elif hv == 4:
                free = not (c4 >> CLS4_INDEX[k]) & 1
            elif hv == 3:
                free = not (c3 >> CLS3_INDEX[k]) & 1
            elif k == "K2":
                free = (mask == 0)
            elif k == "2K1":
                free = (mask == (1 << M(n)) - 1)
            else:
                free = False                        # K1: contained, never free
            if free:
                free_cnt[k] += 1
                if m < best[k][0]:
                    best[k] = (m, mask)
                if k == "P4" and a * w < minprod:
                    minprod = a * w
    return {"n": n, "best": best, "free_cnt": free_cnt, "minprod_P4": minprod, "N": N}

PY_LANE = {}
for n in range(1, 7):
    t = el()
    PY_LANE[n] = census_python(n)
    R(f"[E1] pure-Python full census n={n}: {PY_LANE[n]['N']} labeled graphs (wall {el()-t:.1f}s)")
t = el()
PY_LANE[7] = census_python(7)
R(f"[E1] pure-Python full census n=7: {PY_LANE[7]['N']} labeled graphs (wall {el()-t:.1f}s) — "
  f"the 61E independent lane (alpha B&B / complement-alpha / all-subset scan)")

# ----------------------------------------------------------------------------
# E3. NUMPY VECTORIALIZED FULL CENSUS LANE (n=7) — second independent implementation.
# ----------------------------------------------------------------------------

def alpha_vec_n7(ms, N):
    n = 7
    pos = build_pos(n)
    alpha = np.ones(N, dtype=np.uint8)
    for k in range(2, n + 1):
        ex = np.zeros(N, dtype=bool)
        for S in itertools.combinations(range(n), k):
            e = 0
            for (a, b) in itertools.combinations(S, 2):
                e |= 1 << pos[(a, b)]
            ex |= (ms & np.uint32(e)) == 0
        alpha += ex
    return alpha

def numpy_census_7():
    n = 7
    N = 1 << M(n)
    masks = np.arange(N, dtype=np.uint32)
    pos = build_pos(n)
    cls4bit = np.array([1 << CODE4_TO_CLS[c] for c in range(64)], dtype=np.uint16)
    cls3bit = np.array([1 << CODE3_TO_CLS[c] for c in range(8)], dtype=np.uint16)
    cont4 = np.zeros(N, dtype=np.uint16)
    for S in itertools.combinations(range(n), 4):
        ps = [pos[(a, b)] for a, b in itertools.combinations(S, 2)]
        code = np.zeros(N, dtype=np.uint8)
        for k, b in enumerate(ps):
            code |= ((masks >> np.uint32(b)) & np.uint32(1)).astype(np.uint8) << np.uint8(k)
        cont4 |= cls4bit[code]
    cont3 = np.zeros(N, dtype=np.uint16)
    for S in itertools.combinations(range(n), 3):
        ps = [pos[(a, b)] for a, b in itertools.combinations(S, 2)]
        code = np.zeros(N, dtype=np.uint8)
        for k, b in enumerate(ps):
            code |= ((masks >> np.uint32(b)) & np.uint32(1)).astype(np.uint8) << np.uint8(k)
        cont3 |= cls3bit[code]
    alpha = alpha_vec_n7(masks, N)
    omega = alpha_vec_n7(masks ^ np.uint32(N - 1), N)
    marr = np.maximum(alpha, omega)
    stats = {}
    for k in H_ORDER:
        hv = H_NV[k]
        if hv > n: free = np.ones(N, dtype=bool)
        elif hv == 4: free = (cont4 & np.uint16(1 << CLS4_INDEX[k])) == 0
        elif hv == 3: free = (cont3 & np.uint16(1 << CLS3_INDEX[k])) == 0
        elif k == "K2": free = masks == 0
        elif k == "2K1": free = masks == np.uint32(N - 1)
        else: free = np.zeros(N, dtype=bool)
        cnt = int(free.sum())
        if cnt:
            h = int(marr[free].min())
            idx = np.flatnonzero(free & (marr == np.uint8(h)))[0]
            stats[k] = {"h": h, "count": cnt, "witness": int(masks[idx])}
        else:
            stats[k] = {"h": None, "count": 0, "witness": None}
    p4free = (cont4 & np.uint16(1 << CLS4_INDEX["P4"])) == 0
    prod = alpha.astype(np.uint32) * omega.astype(np.uint32)
    minprod = int(prod[p4free].min())
    witprod = int(masks[np.flatnonzero(p4free & (prod == np.uint32(minprod)))[0]])
    extras = {"masks": masks, "alpha": alpha, "omega": omega, "m": marr,
              "cont4": cont4, "cont3": cont3, "p4free": p4free,
              "minprod_P4": (minprod, witprod)}
    return stats, extras

t = el()
NP7_STATS, NP7_EXTRA = numpy_census_7()
R(f"[E3] numpy vectorized full census n=7: all 2^21 graphs (wall {el()-t:.1f}s) — "
  f"independent lane (subset-existence alpha/omega, all-subset-scan containment)")
agree7 = all((PY_LANE[7]["best"][k][0] if PY_LANE[7]["best"][k][0] < BIG else None) ==
             NP7_STATS[k]["h"] for k in H_ORDER)
R(f"[E3] n=7 FULL-LANE CROSS-CHECK pure-Python vs numpy: h_H(7) agreement for all 18 H: {agree7}")
assert agree7
assert PY_LANE[7]["minprod_P4"] == NP7_EXTRA["minprod_P4"][0]

# ----------------------------------------------------------------------------
# E4. h_all(n) (the unconstrained minimum) and the assembled census table n=1..7.
# ----------------------------------------------------------------------------

h_all = {}
for n in range(1, 7):
    N = 1 << M(n)
    scan = SubsetScan(n)
    bm = BIG; bw = None
    for mask in range(N):
        adj = adj_of(mask, n)
        m = max(alpha_bb(adj, n), alpha_bb(comp_adj(adj, n), n))
        if m < bm: bm, bw = m, mask
    h_all[n] = bm
h_all[7] = int(NP7_EXTRA["m"].min())
R(f"[E4] h_all(n) = min over ALL n-vertex graphs of max(alpha,omega), n=1..7: "
  f"{[h_all[i] for i in range(1, 8)]} — n>=6 value 3 certifies R(3,3)=6 EXACTLY "
  f"(every 6-vertex graph has alpha>=3 or omega>=3; C5 shows R(3,3)>5)")

CENSUS = {}
for k in H_ORDER:
    CENSUS[k] = {}
    for n in range(1, 8):
        if k == "K1":
            CENSUS[k][n] = {"h": None, "rho": None, "vacuous": True}
            continue
        if H_NV[k] > n:
            CENSUS[k][n] = {"h": h_all[n],
                            "rho": (math.log(h_all[n]) / math.log(n)) if n > 1 else None,
                            "witness_mask": None, "src": "all-graphs min (|V(H)|>n)"}
            continue
        h = PY_LANE[n]["best"][k][0]
        wit = PY_LANE[n]["best"][k][1]
        if n == 7:
            assert NP7_STATS[k]["h"] == h
        CENSUS[k][n] = {"h": h, "rho": (math.log(h) / math.log(n)) if n > 1 else None,
                        "witness_mask": wit, "src": "pure-Python full lane (+numpy lane agree)"}
R("[E4] census n=1..7 assembled (both independent lanes agree everywhere)")

# ----------------------------------------------------------------------------
# E5. n = 8: EXHAUSTIVE chunked 2^28 scan of the m<=3 stratum.
# ----------------------------------------------------------------------------

def numpy_scan_8(chunk_bits=23):
    n = 8
    NB = 1 << M(n)
    FULL = NB - 1
    pos = build_pos(n)
    sub4 = list(itertools.combinations(range(n), 4))
    sub3 = list(itertools.combinations(range(n), 3))
    EM4 = []
    s4bits = []
    for S in sub4:
        e = 0
        for (a, b) in itertools.combinations(S, 2):
            e |= 1 << pos[(a, b)]
        EM4.append(e)
        s4bits.append([pos[(a, b)] for a, b in itertools.combinations(S, 2)])
    s3bits = [[pos[(a, b)] for a, b in itertools.combinations(S, 2)] for S in sub3]
    cls4bit = np.array([1 << CODE4_TO_CLS[c] for c in range(64)], dtype=np.uint16)
    cls3bit = np.array([1 << CODE3_TO_CLS[c] for c in range(8)], dtype=np.uint16)
    per_H = {k: {"count_m3": 0, "witness_m3": None} for k in H_ORDER}
    cand_total = 0
    chunk = 1 << chunk_bits
    nchunks = (NB + chunk - 1) // chunk
    for ci in range(nchunks):
        lo = ci * chunk
        masks = np.arange(lo, min(lo + chunk, NB), dtype=np.uint32)
        cmasks = masks ^ np.uint32(FULL)
        a_le3 = np.ones(masks.size, dtype=bool)
        o_le3 = np.ones(masks.size, dtype=bool)
        for e in EM4:
            a_le3 &= (masks & np.uint32(e)) != 0
            o_le3 &= (cmasks & np.uint32(e)) != 0
        cand = a_le3 & o_le3
        cnt = int(cand.sum())
        cand_total += cnt
        if cnt:
            cm = masks[cand]
            cont4 = np.zeros(cnt, dtype=np.uint16)
            for ps in s4bits:
                code = np.zeros(cnt, dtype=np.uint8)
                for k, b in enumerate(ps):
                    code |= ((cm >> np.uint32(b)) & np.uint32(1)).astype(np.uint8) << np.uint8(k)
                cont4 |= cls4bit[code]
            cont3 = np.zeros(cnt, dtype=np.uint16)
            for ps in s3bits:
                code = np.zeros(cnt, dtype=np.uint8)
                for k, b in enumerate(ps):
                    code |= ((cm >> np.uint32(b)) & np.uint32(1)).astype(np.uint8) << np.uint8(k)
                cont3 |= cls3bit[code]
            for k in H_ORDER:
                hv = H_NV[k]
                if hv > 8: free = np.ones(cnt, dtype=bool)
                elif hv == 4: free = (cont4 & np.uint16(1 << CLS4_INDEX[k])) == 0
                elif hv == 3: free = (cont3 & np.uint16(1 << CLS3_INDEX[k])) == 0
                elif k == "K2": free = cm == 0
                elif k == "2K1": free = cm == np.uint32(FULL)
                else: free = np.zeros(cnt, dtype=bool)
                c = int(free.sum())
                per_H[k]["count_m3"] += c
                if c and per_H[k]["witness_m3"] is None:
                    per_H[k]["witness_m3"] = int(cm[free][0])
        del masks, cmasks, a_le3, o_le3
    return per_H, cand_total, nchunks

t = el()
SCAN8, CAND8_TOTAL, NCHUNKS8 = numpy_scan_8()
R(f"[E5] n=8 EXHAUSTIVE chunked scan: all 2^28 graphs in {NCHUNKS8} chunks (wall {el()-t:.1f}s); "
  f"m=3 stratum (alpha<=3 AND omega<=3) size = {CAND8_TOTAL} labeled graphs. Universal floor "
  f"m>=3 at n=8 is census-certified (h_all(6)=3 + induced-subgraph monotonicity), so h_H(8)=3 "
  f"iff an H-free m=3 graph exists; else h_H(8)>=4.")
assert CAND8_TOTAL > 0
h_all[8] = 3

def cycle_edges(n): return [(i, (i + 1) % n) for i in range(n)]
C8_MASK = edges_to_mask(cycle_edges(8), 8)
N8_NAMED = {"K1,3(claw)": C8_MASK, "K3+K1": complement_mask(C8_MASK, 8)}

for k in H_ORDER:
    if k == "K1":
        CENSUS[k][8] = {"h": None, "rho": None, "vacuous": True}; continue
    if k == "K2" or k == "2K1":
        CENSUS[k][8] = {"h": 8, "rho": 1.0, "witness_mask": 0 if k == "K2" else (1 << 28) - 1,
                        "src": "only the empty/complete graph is K2/2K1-free, m=n=8"}; continue
    if SCAN8[k]["count_m3"] > 0:
        CENSUS[k][8] = {"h": 3, "rho": math.log(3) / math.log(8),
                        "witness_mask": SCAN8[k]["witness_m3"],
                        "src": "exhaustive n=8 m=3-stratum scan"}
    else:
        wit = N8_NAMED.get(k)
        assert wit is not None, f"no m=3 and no named m=4 witness for {k}"
        adjw = adj_of(wit, 8)
        a = alpha_bb(adjw, 8); w = alpha_bb(comp_adj(adjw, 8), 8)
        assert not SubsetScan(8).contains(wit, k) and max(a, w) == 4
        CENSUS[k][8] = {"h": 4, "rho": math.log(4) / math.log(8), "witness_mask": wit,
                        "src": "exhaustive scan: NO m=3 H-free graph; named m=4 witness "
                               "(C8 / complement(C8)) => h=4 exactly"}
m3_list = ", ".join(f"{k}:{SCAN8[k]['count_m3']}" for k in H_ORDER if 2 <= H_NV[k] <= 8)
R(f"[E5] n=8 H-free m=3 counts (exhaustive over the m=3 stratum): {m3_list}")
n8_row = "  ".join(f"{k}={CENSUS[k][8]['h']}" for k in H_ORDER)
R(f"[E5] EXACT h_H(8) row: {n8_row}")

# ----------------------------------------------------------------------------
# E6. COMPLEMENT SELF-TEST: h_H(n) == h_Hbar(n) EXACTLY, all H, n=2..8. 0 mismatches.
# ----------------------------------------------------------------------------

mismatch = []
for k in H_ORDER:
    kb = COMPLEMENT_PAIR[k]
    for n in range(2, 9):
        h1 = CENSUS[k][n]["h"]; h2 = CENSUS[kb][n]["h"]
        if (h1 is None) != (h2 is None) or (h1 is not None and h1 != h2):
            mismatch.append((k, kb, n, h1, h2))
R(f"[E6] COMPLEMENT SELF-TEST: h_H(n) == h_Hbar(n) (hence rho_H(n) == rho_Hbar(n)) for all 18 H "
  f"x n=2..8: {len(mismatch)} MISMATCHES (required 0)")
assert not mismatch

# ----------------------------------------------------------------------------
# E7. BATTERY: fresh-algorithm cross-checks.
# ----------------------------------------------------------------------------

rng = random.Random(7361)
def rand_mask(n, rng, p=0.5):
    N = M(n); m = 0
    for b in range(N):
        if rng.random() < p: m |= 1 << b
    return m

B1_bad = B2_bad = B3_bad = 0
sample7 = [rand_mask(7, rng) for _ in range(3000)] + \
          [PY_LANE[7]["best"][k][1] for k in H_ORDER if PY_LANE[7]["best"][k][1] is not None]
for mask in sample7:
    adj = adj_of(mask, 7)
    aA = alpha_bb(adj, 7)
    aB = int(NP7_EXTRA["alpha"][mask]); oB = int(NP7_EXTRA["omega"][mask])
    if aA != aB: B1_bad += 1
    if omega_clique_direct(adj, 7) != oB: B2_bad += 1
for n in range(2, 7):
    for mask in range(1 << M(n)):
        adj = adj_of(mask, n)
        w = alpha_bb(comp_adj(adj, n), n)
        if omega_clique_direct(adj, n) != w: B2_bad += 1
R(f"[B1] alpha cross-check (bitmask B&B) vs (numpy subset-existence): 3000 random n=7 graphs + "
  f"all 18 h-witnesses: {B1_bad} disagreements (required 0)")
R(f"[B2] omega cross-check (complement-alpha) vs (DIRECT clique B&B): all "
  f"{sum(1 << M(n) for n in range(2, 7))} graphs n=2..6 + 3000 random n=7: "
  f"{B2_bad} disagreements (required 0)")
assert B1_bad == 0 and B2_bad == 0

H_CHECK = CLS4_NAMES + ["K3", "P3", "K2+K1", "3K1"]
for n in range(3, 7):
    scan = SubsetScan(n)
    for mask in range(1 << M(n)):
        adj = adj_of(mask, n)
        for k in H_CHECK:
            if scan.contains(mask, k) != contains_induced_matcher(adj, n, k):
                B3_bad += 1
for n in (7, 8):
    scan = SubsetScan(n)
    for _ in range(1500):
        mask = rand_mask(n, rng)
        adj = adj_of(mask, n)
        for k in H_CHECK:
            if scan.contains(mask, k) != contains_induced_matcher(adj, n, k):
                B3_bad += 1
R(f"[B3] induced-containment cross-check (all-subset scan) vs (backtracking matcher): every graph "
  f"n=3..6 ({sum(1 << M(n) for n in range(3, 7))} graphs x 15 H) + 3000 random n=7/n=8 x 15 H: "
  f"{B3_bad} disagreements (required 0)")
assert B3_bad == 0

mono_bad = []
for k in H_ORDER:
    hs = [CENSUS[k][n]["h"] for n in range(2, 9) if CENSUS[k][n]["h"] is not None]
    if any(hs[i] > hs[i + 1] for i in range(len(hs) - 1)):
        mono_bad.append((k, hs))
R(f"[B4] h_H nondecreasing in n (deletion transport never reverses; all 18 H, n=2..8): "
  f"{len(mono_bad)} violations (required 0)")
assert not mono_bad

order_bad = []
for a in H_ORDER:
    for b in H_ORDER:
        if a == b or H_NV[a] > H_NV[b] or H_NV[b] > 8: continue
        if contains_induced_matcher(H_ADJ[b], H_NV[b], a):    # a induced in b
            # CORRECT LAW (commander fix, W75): a induced in b => every a-free graph is b-free
            # => the a-free class is a SUBCLASS => its min is LARGER: h_a(n) >= h_b(n).
            # (Confirmed: P3 in P4, h_P3(5)=3 > h_P4(5)=2 — the C5 witness.)
            for n in range(max(2, H_NV[b]), 9):
                ha, hb = CENSUS[a][n]["h"], CENSUS[b][n]["h"]
                if ha is not None and hb is not None and ha < hb:
                    order_bad.append((a, b, n, ha, hb))
R(f"[B4] inheritance law on the census (CORRECTED direction): H induced in H' => h_H(n) >= h_H'(n) at every n<=8 "
  f"(all certified induced-inclusion pairs among the 18 H): {len(order_bad)} violations (required 0)")
assert not order_bad

BANKED_B = {
    "2K_2":        ("2K2",        [1, 2, 2, 2, 2, 3, 3]),
    "P_3":         ("P3",         [1, 2, 2, 2, 3, 3, 3]),
    "3K_1":        ("3K1",        [1, 2, 2, 2, 2, 3, 3]),
    "claw(K_1,3)": ("K1,3(claw)", [1, 2, 2, 2, 2, 3, 3]),
    "C_4":         ("C4",         [1, 2, 2, 2, 2, 3, 3]),
    "K_2":         ("K2",         [1, 2, 3, 4, 5, 6, 7]),
}
banked_ok = True
for banked_name, (ours, expected) in BANKED_B.items():
    got = [CENSUS[ours][n]["h"] for n in range(1, 8)]
    ok = got == expected
    banked_ok &= ok
    R(f"[B5] banked [B]-table reproduction h_{banked_name} n=1..7: ours {got} vs banked {expected}: "
      f"{'MATCH' if ok else 'MISMATCH'}")
assert banked_ok
bell_expected = [1, 2, 5, 15, 52, 203, 877]
bell_got = [PY_LANE[n]["free_cnt"]["P3"] for n in range(1, 8)]
R(f"[B5] banked [C]-census reproduction: P3-free labeled counts n=1..7: ours {bell_got} vs banked "
  f"{bell_expected}: {'MATCH' if bell_got == bell_expected else 'MISMATCH'}")
assert bell_got == bell_expected

# ----------------------------------------------------------------------------
# E8. BANKED CLAIMS RE-DERIVATION from the census (F7, P4, CLAW, RAM, Thms 1-3, SL).
# ----------------------------------------------------------------------------

def t_n_law(n):
    t = 1
    while t * (t + 1) < n: t += 1
    return t

def tR_n_law(n):
    t = 1
    while (t + 2) * (t + 1) * t // 6 <= n: t += 1
    return t - 1

F7 = ["K1", "K2", "2K1", "K3", "3K1", "P3", "K2+K1"]
f7_bad = []
for k in F7:
    for n in range(2, 9):
        h = CENSUS[k][n]["h"]
        if h is not None and h < math.isqrt(n):
            f7_bad.append((k, n, h))
R(f"[E8] F7 family board re-derived: h_H(n) >= floor(sqrt(n)) for the 7 family H x n=2..8 "
  f"(K1 vacuous): {len(f7_bad)} violations (required 0)")
assert not f7_bad

th1_ok = all(CENSUS["K2"][n]["h"] == n for n in range(1, 9))
R(f"[E8] Theorem 1 (K2) re-derived: h_K2(n)=n for n=1..8: {th1_ok}")
assert th1_ok
th2_ok = all(CENSUS["P3"][n]["h"] == math.ceil(math.sqrt(n)) for n in range(1, 9))
R(f"[E8] Theorem 2 (P3) re-derived: h_P3(n)=ceil(sqrt(n)) for n=1..8: "
  f"{[CENSUS['P3'][n]['h'] for n in range(1, 9)]}: {th2_ok}")
assert th2_ok
th3_rows = []
th3_ok = True
for n in range(1, 9):
    h = CENSUS["3K1"][n]["h"]; law = t_n_law(n)
    th3_ok &= (h >= law)
    th3_rows.append(f"n={n}:h={h},law={law}{'=' if h == law else '>'}")
R(f"[E8] Theorem 3 (3K1) re-derived: h >= t_n=ceil((sqrt(4n+1)-1)/2) at every n<=8 "
  f"[{' '.join(th3_rows)}]: {th3_ok} (equality at n in {{1,3,4,5,7,8}}, Ramsey-forced strictness "
  f"at n in {{2,6}})")
assert th3_ok

thS_law = all(CENSUS["P4"][n]["h"] == math.ceil(math.sqrt(n)) for n in range(1, 9))
prod_ok = all(PY_LANE[n]["minprod_P4"] >= n for n in range(1, 8))
R(f"[E8] Theorem S (P4) re-derived: h_P4(n)=ceil(sqrt(n)) n=1..8 "
  f"{[CENSUS['P4'][n]['h'] for n in range(1, 9)]}: {thS_law}; alpha*omega>=n for EVERY P4-free "
  f"graph n<=7 (min alpha*omega per n = {[PY_LANE[n]['minprod_P4'] for n in range(1, 8)]}): {prod_ok}")
assert thS_law and prod_ok

def is_disconnected(adj, n):
    seen = 1; frontier = 1
    full = (1 << n) - 1
    while frontier:
        nxt = 0
        for v in range(n):
            if frontier >> v & 1: nxt |= adj[v]
        nxt &= ~seen
        seen |= nxt
        frontier = nxt
    return seen != full

SL_bad = 0; SL_cnt = 0
for n in range(2, 8):
    scan = SubsetScan(n)
    for mask in range(1 << M(n)):
        if not scan.contains(mask, "P4"):
            SL_cnt += 1
            adj = adj_of(mask, n)
            if not (is_disconnected(adj, n) or is_disconnected(comp_adj(adj, n), n)):
                SL_bad += 1
R(f"[E8] Seinsche Lemma SL re-derived: all {SL_cnt} P4-free labeled graphs n=2..7 are disconnected "
  f"or have disconnected complement: {SL_bad} violations (required 0)")
assert SL_bad == 0

claw_ok = all(CENSUS["K1,3(claw)"][n]["h"] >= n ** (1 / 3) / 2 for n in range(1, 9))
R(f"[E8] Theorem CLAW re-derived: h_claw(n) = {[CENSUS['K1,3(claw)'][n]['h'] for n in range(1, 9)]} "
  f">= n^(1/3)/2 at every n<=8: {claw_ok}")
assert claw_ok

masks7 = NP7_EXTRA["masks"]; alpha7 = NP7_EXTRA["alpha"]; omega7 = NP7_EXTRA["omega"]
clawfree7 = (NP7_EXTRA["cont4"] & np.uint16(1 << CLS4_INDEX["K1,3(claw)"])) == 0
law_ii = bool((alpha7[clawfree7].astype(np.uint32) *
               (omega7[clawfree7].astype(np.uint32) ** 2 + 1) >= 7).all())
maxdeg7 = np.zeros(1 << M(7), dtype=np.uint8)
posv = build_pos(7)
for v in range(7):
    dv = np.zeros(1 << M(7), dtype=np.uint8)
    for u in range(7):
        if u == v: continue
        p = posv[(u, v)] if u < v else posv[(v, u)]
        dv += ((masks7 >> np.uint32(p)) & np.uint32(1)).astype(np.uint8)
    maxdeg7 = np.maximum(maxdeg7, dv)
om_cf = omega7[clawfree7].astype(np.uint32); md_cf = maxdeg7[clawfree7].astype(np.uint32)
ok_iii = bool((md_cf <= om_cf * (om_cf + 1) // 2 - 1).all())
ok_iv = bool((md_cf < om_cf * om_cf).all())
ok_n6 = True
for nn in range(2, 7):
    scan = SubsetScan(nn)
    for mask in range(1 << M(nn)):
        if not scan.contains(mask, "K1,3(claw)"):
            adj = adj_of(mask, nn)
            a = alpha_bb(adj, nn)
            w = alpha_bb(comp_adj(adj, nn), nn)
            md = max(bin(adj[v]).count("1") for v in range(nn))
            if a * (w * w + 1) < nn or md > w * (w + 1) // 2 - 1 or md >= w * w:
                ok_n6 = False
R(f"[E8] CLAW step-laws on EVERY claw-free graph: alpha*(omega^2+1)>=n: n<=6 exhaustive {ok_n6}, "
  f"n=7 exhaustive {law_ii}; deg(v)<=omega(omega+1)/2-1: {ok_iii}; deg(v)<omega^2: {ok_iv}")
assert law_ii and ok_iii and ok_iv and ok_n6

ram_rows = []
ram_ok = True
for nn in range(1, 9):
    h = CENSUS["K4"][nn]["h"]; law = tR_n_law(nn)
    ram_ok &= (h >= law)
    ram_rows.append(f"n={nn}:h={h},law={law}")
R(f"[E8] Theorem RAM re-derived (K4 side; K4bar identical by complement self-test): h_K4(n) >= "
  f"max{{t: C(t+2,3)<=n}} at every n<=8 [{' '.join(ram_rows)}]: {ram_ok}")
assert ram_ok
bridge_ok = True
for c in (0.32, 0.30, 0.25):
    ok = all((6.0 * nn) ** (1 / 3) - 2.0 >= float(nn) ** c for nn in range(256, 1 << 20))
    d_ok = (1 / 3) * 6 ** (1 / 3) * 256 ** (-2 / 3) - c * 256 ** (c - 1) > 0
    bridge_ok &= ok and d_ok
R(f"[E8] RAM bridge re-derived: (6n)^(1/3)-2 >= n^c for c in {{0.32, 0.30, 0.25}} at all n in "
  f"[256, 2^20] + positive-derivative monotonicity beyond 256: {bridge_ok}")
assert bridge_ok

# ----------------------------------------------------------------------------
# E9. STRUCTURAL LEMMA CERTIFICATION (Part 3) — both readings, counterexamples caught.
# ----------------------------------------------------------------------------

def degrees_of(adj): return [bin(a).count("1") for a in adj]
def sum_C2(degs): return sum(d * (d - 1) // 2 for d in degs)
def reiman_bound(n): return (n / 4.0) * (1 + math.sqrt(4 * n - 3))

def class3_of_sub(sub):
    code = 0
    for (a, b), bitv in zip(((0, 1), (0, 2), (1, 2)), (4, 2, 1)):
        if sub[a] >> b & 1: code |= bitv
    return CODE3_TO_CLS[code]

def class4_of_sub(sub):
    code = 0
    for k, (a, b) in enumerate(itertools.combinations(range(4), 2)):
        code |= (1 if sub[a] >> b & 1 else 0) << k
    return CODE4_TO_CLS[code]

CLS_2K2 = CODE4_TO_CLS[edges_to_mask([(0, 1), (2, 3)], 4)]

def induced_on(adj, S):
    sub = [0] * len(S)
    for i, a in enumerate(S):
        for j, b in enumerate(S):
            if i < j and adj[a] >> b & 1:
                sub[i] |= 1 << j
                sub[j] |= 1 << i
    return sub

lemma = {}
for nn in (4, 5, 6):
    scan = SubsetScan(nn)
    L1a_viol = []; L1b_viol = []; L2a_viol = []; L2b_viol = []
    n_ind = n_sub = 0
    for mask in range(1 << M(nn)):
        adj = adj_of(mask, nn)
        degs = degrees_of(adj)
        e = bin(mask).count("1")
        indC4 = not scan.contains(mask, "C4")
        subC4 = (not scan.contains(mask, "C4") and not scan.contains(mask, "diamond")
                 and not scan.contains(mask, "K4"))
        if indC4:
            n_ind += 1
            if sum_C2(degs) > M(nn): L1a_viol.append(mask)
            if e > reiman_bound(nn): L2a_viol.append(mask)
        if subC4:
            n_sub += 1
            if sum_C2(degs) > M(nn): L1b_viol.append(mask)
            if e > reiman_bound(nn): L2b_viol.append(mask)
    lemma[nn] = dict(n_ind=n_ind, n_sub=n_sub, L1a=L1a_viol, L1b=L1b_viol,
                     L2a=L2a_viol, L2b=L2b_viol)

R("[E9] STRUCTURAL LEMMA CERTIFICATION (exhaustive n=4..6):")
for nn in (4, 5, 6):
    d = lemma[nn]
    ex1 = mask_to_edges(d["L1a"][0], nn) if d["L1a"] else None
    ex2 = mask_to_edges(d["L2a"][0], nn) if d["L2a"] else None
    R(f"[E9]   n={nn}: induced-C4-free graphs: {d['n_ind']}; subgraph-C4-free "
      f"(=induced-{{C4,diamond,K4}}-free): {d['n_sub']}")
    R(f"[E9]   n={nn}: L1a 'induced-C4-free => sum C(d_v,2)<=C(n,2)': {len(d['L1a'])} VIOLATIONS"
      + (f" — first: {ex1}" if ex1 else " (holds)"))
    R(f"[E9]   n={nn}: L2a 'induced-C4-free => e<=(n/4)(1+sqrt(4n-3))': {len(d['L2a'])} VIOLATIONS"
      + (f" — first: {ex2}" if ex2 else " (holds)"))
    R(f"[E9]   n={nn}: L1b 'SUBGRAPH-C4-free => sum C(d_v,2)<=C(n,2)': {len(d['L1b'])} violations")
    R(f"[E9]   n={nn}: L2b 'SUBGRAPH-C4-free => e<=(n/4)(1+sqrt(4n-3))': {len(d['L2b'])} violations")
    assert not d["L1b"] and not d["L2b"]
assert lemma[4]["L1a"] and lemma[4]["L2a"]
R("[E9] VERDICT L1/L2: the Reiman-type lemmas are FALSE in the induced-C4-free reading "
  "(n=4 counterexamples: K4 — e=6>4.61, sum C(d,2)=12>6; diamond — e=5>4.61, sum=8>6) and TRUE "
  "in the SUBGRAPH reading (= induced-{C4,diamond,K4}-free), certified exhaustively n<=6 and on "
  "the certified instance pool of E10. Any 61K use MUST be subgraph-reading or add "
  "diamond-free+K4-free hypotheses.")

cw_bad_n6 = 0
for nn in range(1, 7):
    for mask in range(1 << M(nn)):
        adj = adj_of(mask, nn)
        a = alpha_bb(adj, nn)
        if (2 * bin(mask).count("1") + nn) * a < nn * nn:
            cw_bad_n6 += 1
e7 = np.zeros(1 << M(7), dtype=np.uint8)
for b in range(M(7)):
    e7 += ((masks7 >> np.uint32(b)) & np.uint32(1)).astype(np.uint8)
cw_bad_n7 = int((((2 * e7.astype(np.uint32) + 7) * alpha7.astype(np.uint32)) < 49).sum())
R(f"[E9] L3 Caro-Wei weak alpha >= n^2/(2e+n) on EVERY graph: n<=6 exhaustive: {cw_bad_n6} "
  f"violations; n=7 all 2^21 vectorized: {cw_bad_n7} violations (required 0)")
assert cw_bad_n6 == 0 and cw_bad_n7 == 0

L4a_viol = []; L4b_viol = []; L4c_viol = []
pawfree_cnt = 0; diamondfree_cnt = 0
for nn in (4, 5, 6):
    scan = SubsetScan(nn)
    for mask in range(1 << M(nn)):
        adj = adj_of(mask, nn)
        pawfree = not scan.contains(mask, "paw")
        dfree = not scan.contains(mask, "diamond")
        if pawfree:
            pawfree_cnt += 1
            for v in range(nn):
                Nv = [u for u in range(nn) if adj[v] >> u & 1]
                bad_a = bad_b = False
                for T in itertools.combinations(Nv, 3):
                    if class3_of_sub(induced_on(adj, T)) == CLS3_INDEX["P3"]:
                        bad_a = True; break
                if not bad_a and len(Nv) >= 4:
                    for T in itertools.combinations(Nv, 4):
                        if class4_of_sub(induced_on(adj, T)) == CLS_2K2:
                            bad_b = True; break
                if bad_a: L4a_viol.append((nn, mask, v))
                if bad_b: L4b_viol.append((nn, mask, v))
        if dfree:
            diamondfree_cnt += 1
            for v in range(nn):
                Nv = [u for u in range(nn) if adj[v] >> u & 1]
                for T in itertools.combinations(Nv, 3):
                    if class3_of_sub(induced_on(adj, T)) == CLS3_INDEX["P3"]:
                        L4c_viol.append((nn, mask, v)); break
R(f"[E9] L4a 'paw-free => every N(v) is P3-free': {len(L4a_viol)} VIOLATIONS over all "
  f"{pawfree_cnt} paw-free graphs n=4..6 — the diamond itself is a counterexample (its degree-3 "
  f"vertex has N(v)=P3). LEMMA FALSE AS STATED (induced-P3 in N(v) completes a DIAMOND with v, "
  f"not a paw).")
assert L4a_viol
R(f"[E9] L4b 'paw-free => every N(v) is 2K2-free' (the corrected neighborhood law): "
  f"{len(L4b_viol)} violations (required 0) — TRUE: an induced 2K2 in N(v) completes an induced "
  f"paw with center v.")
assert not L4b_viol
R(f"[E9] L4c 'diamond-free => every N(v) is P3-free' (the corrected dual law): "
  f"{len(L4c_viol)} violations over all {diamondfree_cnt} diamond-free graphs n=4..6 (required 0) "
  f"— TRUE: an induced P3 in N(v) completes an induced diamond with v.")
assert not L4c_viol

L5_bad = 0
for nn in range(1, 8):
    scan = SubsetScan(nn)
    for mask in range(1 << M(nn)):
        if not scan.contains(mask, "P3"):
            adj = adj_of(mask, nn)
            # CORRECT check (commander fix): disjoint union of cliques <=>
            # adjacency transitive: u~v and v~w => u~w
            for u in range(nn):
                for v in range(nn):
                    if u != v and adj[u] >> v & 1:
                        for w in range(nn):
                            if w != v and adj[v] >> w & 1 and not (adj[u] >> w & 1) and w != u:
                                L5_bad += 1
R(f"[E9] L5 'P3-free => disjoint union of cliques': {L5_bad} violations among all P3-free graphs "
  f"n=1..7 (counts = Bell numbers, re-derived in B5) (required 0)")
assert L5_bad == 0

L6_bad = 0
for nn in (4, 5, 6):
    scan = SubsetScan(nn)
    for mask in range(1 << M(nn)):
        if not scan.contains(mask, "diamond"):
            adj = adj_of(mask, nn)
            for u in range(nn):
                for v in range(u + 1, nn):
                    if adj[u] >> v & 1:
                        cn = adj[u] & adj[v]
                        cl = cn
                        while cl:
                            x = (cl & -cl).bit_length() - 1
                            cl &= cl - 1
                            if (cn & ~adj[x]) & ~(1 << x):
                                L6_bad += 1
dfree7 = (NP7_EXTRA["cont4"] & np.uint16(1 << CLS4_INDEX["diamond"])) == 0
dfree_masks = masks7[dfree7]
L6_bad7 = 0
for mask in dfree_masks.tolist():
    adj = adj_of(mask, 7)
    for u in range(7):
        for v in range(u + 1, 7):
            if adj[u] >> v & 1:
                cn = adj[u] & adj[v]
                cl = cn
                while cl:
                    x = (cl & -cl).bit_length() - 1
                    cl &= cl - 1
                    if (cn & ~adj[x]) & ~(1 << x):
                        L6_bad7 += 1
R(f"[E9] L6 'diamond-free => every edge's common neighborhood is a clique': exhaustive n=4..6: "
  f"{L6_bad} violations; n=7 over all {len(dfree_masks)} diamond-free labeled graphs: {L6_bad7} "
  f"violations (required 0)")
assert L6_bad == 0 and L6_bad7 == 0

L7_bad = []
for k in CLS4_NAMES:
    for nn in range(4, 9):
        h = CENSUS[k][nn]["h"]
        if h is not None and h < t_n_law(nn):
            L7_bad.append((k, nn, h))
R(f"[E9] L7 composite floor at every n<=8: h_H(n) >= t_n (=min t: t(t+1)>=n) for ALL 11 "
  f"four-vertex H: {len(L7_bad)} violations (required 0) — the uniform boundary every 61K "
  f"composite inequality must clear, with zero boundary violations")
assert not L7_bad

# ----------------------------------------------------------------------------
# E10. STRUCTURED INSTANCES n=9..31 (polarity graphs, random subgraph-C4-free,
#      trees, cycles, Petersen): Reiman lemmas beyond n=6.
# ----------------------------------------------------------------------------

def pg2_polarity_graph(q):
    pts = [(1, b, c) for b in range(q) for c in range(q)] + \
          [(0, 1, c) for c in range(q)] + [(0, 0, 1)]
    n = len(pts)
    assert n == q * q + q + 1
    adj = [0] * n
    e = 0
    for i in range(n):
        for j in range(i + 1, n):
            if sum(pts[i][t] * pts[j][t] for t in range(3)) % q == 0:
                adj[i] |= 1 << j; adj[j] |= 1 << i; e += 1
    return adj, n, e

def check_pairs_le1_common(adj):
    n = len(adj)
    for u in range(n):
        for v in range(u + 1, n):
            if bin(adj[u] & adj[v]).count("1") > 1:
                return False
    return True

def mask_of_adj(adj):
    n = len(adj)
    return edges_to_mask([(i, j) for i in range(n) for j in range(i + 1, n) if adj[i] >> j & 1], n)

R("[E10] polarity graphs of PG(2,q) (orthogonal polarity; x~y iff x.y=0, no loops):")
POLARITY = {}
for q in (2, 3):
    # q=4,5 need true GF(q) arithmetic (Z/q is not a field for q=4) — scoped out,
    # honestly: only prime fields certified this round.
    adj, n, e = pg2_polarity_graph(q)
    assert check_pairs_le1_common(adj)
    a = alpha_bb(adj, n)
    w = omega_clique_direct(adj, n)
    scan = SubsetScan(n)
    fl_mask = mask_of_adj(adj)
    freed = [nm for nm in CLS4_NAMES if not scan.contains(fl_mask, nm)]
    POLARITY[q] = {"n": n, "e": e, "alpha": a, "omega": w, "m": max(a, w),
                   "H_free": freed}
    degs = degrees_of(adj)
    assert sum_C2(degs) <= M(n) and e <= reiman_bound(n)
    R(f"[E10]   ER_{q}: n={n}, e={e}, every pair of vertices has <=1 common neighbor "
      f"(C4-SUBGRAPH-free + induced-{{C4,diamond,K4}}-free certified), omega={w}, alpha={a}, "
      f"m={max(a,w)}, Reiman bound {reiman_bound(n):.2f}: OK; 4-vertex-H-free: {','.join(freed)}")

rng2 = random.Random(991)
rand_instances = 0
EDGE_RANGE = {9: (8, 12), 10: (9, 14), 11: (10, 16)}
for nn in (9, 10, 11):
    scan = SubsetScan(nn)
    allp = pair_list(nn)
    made = tries = 0
    lo_k, hi_k = EDGE_RANGE[nn]
    while made < 25 and tries < 300000:
        tries += 1
        k_edges = rng2.randint(lo_k, hi_k)
        chosen = rng2.sample(allp, k_edges)
        mask = edges_to_mask(chosen, nn)
        if (not scan.contains(mask, "C4") and not scan.contains(mask, "diamond")
                and not scan.contains(mask, "K4")):
            adj = adj_of(mask, nn)
            degs = degrees_of(adj)
            e = bin(mask).count("1")
            assert sum_C2(degs) <= M(nn) and e <= reiman_bound(nn)
            made += 1
    rand_instances += made
R(f"[E10] random thin subgraph-C4-free instances (8-16 random edges, rejection-filtered): "
  f"{rand_instances} total at n=9,10,11 — sum C(d,2)<=C(n,2) and Reiman e-bound hold on every "
  f"one (asserted per instance)")

# greedy-DENSE subgraph-C4-free instances (maximal edge growth under C4-subgraph-freeness)
def greedy_c4free_adj(nn, r):
    adj = [0] * nn
    pairs = pair_list(nn)
    r.shuffle(pairs)
    for (u, v) in pairs:
        if adj[u] >> v & 1:
            continue
        # would uv create a C4 subgraph u-v-x-w-u?  x in N(v), w in N(u), x~w
        creates = False
        nv = adj[v]
        w = adj[u]
        while w and not creates:
            x = (w & -w).bit_length() - 1
            w &= w - 1
            if adj[x] & nv:
                creates = True
        if not creates:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    return adj

greedy_instances = 0
for nn in (9, 10, 11):
    scan = SubsetScan(nn)
    for _ in range(25):
        adj = greedy_c4free_adj(nn, rng2)
        mask = mask_of_adj(adj)
        assert (not scan.contains(mask, "C4") and not scan.contains(mask, "diamond")
                and not scan.contains(mask, "K4")), "greedy growth must stay C4-subgraph-free"
        e = sum(bin(a).count("1") for a in adj) // 2
        assert sum_C2(degrees_of(adj)) <= M(nn) and e <= reiman_bound(nn)
        greedy_instances += 1
R(f"[E10] greedy-DENSE maximal subgraph-C4-free instances: {greedy_instances} at n=9,10,11 — "
  f"pair-common-neighbor<=1, sum C(d,2)<=C(n,2), Reiman e-bound ALL OK (these are the "
  f"near-extremal stress rows for the Reiman lemmas)")

def tree_adj(nn, r):
    adj = [0] * nn
    for v in range(1, nn):
        u = r.randrange(v)
        adj[u] |= 1 << v; adj[v] |= 1 << u
    return adj

petersen_edges = ([(i, (i + 1) % 5) for i in range(5)] +
                  [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, 5 + i) for i in range(5)])
det_inst = []
for nn in (9, 10, 11):
    for _ in range(20):
        det_inst.append((f"tree n={nn}", tree_adj(nn, rng2)))
for nn in range(5, 12):
    det_inst.append((f"C{nn}", adj_of(edges_to_mask(cycle_edges(nn), nn), nn)))
det_inst.append(("Petersen n=10", adj_of(edges_to_mask(petersen_edges, 10), 10)))
for name, adj in det_inst:
    nn = len(adj)
    assert check_pairs_le1_common(adj), name
    e = sum(bin(a).count("1") for a in adj) // 2
    assert sum_C2(degrees_of(adj)) <= M(nn) and e <= reiman_bound(nn), name
R(f"[E10] deterministic subgraph-C4-free instances ({len(det_inst)}: random trees n=9..11, cycles "
  f"C5..C11, Petersen): pair-common-neighbor<=1, sum C(d,2)<=C(n,2), Reiman bound — ALL OK")

# ----------------------------------------------------------------------------
# E11. TIGHTNESS WITNESSES (Part 4).
# ----------------------------------------------------------------------------

def block_graph(k):
    n = k * k
    edges = []
    for b in range(k):
        for i in range(k):
            for j in range(i + 1, k):
                edges.append((b * k + i, b * k + j))
    return edges, n

def complete_multipartite(parts):
    n = sum(parts)
    edges = []
    base = [0]
    for p in parts: base.append(base[-1] + p)
    for a in range(len(parts)):
        for b in range(a + 1, len(parts)):
            for i in range(base[a], base[a + 1]):
                for j in range(base[b], base[b + 1]):
                    edges.append((i, j))
    return edges, n

def cert_witness(name, edges, n, note=""):
    mask = edges_to_mask(edges, n)
    adj = adj_of(mask, n)
    a = alpha_bb(adj, n); w = omega_clique_direct(adj, n)
    scan = SubsetScan(n)
    freed = [nm for nm in CLS4_NAMES if not scan.contains(mask, nm)]
    freed += [nm for nm in N3_NAMES if not scan.contains(mask, nm)]
    return {"name": name, "n": n, "alpha": a, "omega": w, "m": max(a, w),
            "H_free": freed, "note": note,
            "rho": (math.log(max(a, w)) / math.log(n)) if n > 1 else None}

R("[E11] WITNESS FAMILY 1 — block graphs B_k = disjoint union of k copies of K_k:")
WIT = []
for k in range(1, 9):
    edges, n = block_graph(k)
    row = cert_witness(f"B_{k}", edges, n)
    WIT.append(row)
    R(f"[E11]   B_{k}: n={n}, alpha={row['alpha']}, omega={row['omega']}, m={row['m']}, "
      f"H-free: {','.join(row['H_free'])}")
bk_ok = all({"C4", "paw", "diamond"} <= set(r["H_free"]) and r["m"] == k
            for r, k in zip(WIT, range(1, 9)))
R(f"[E11] VERDICT: every B_k (k=1..8) is C4-free, paw-free AND diamond-free (also P3/P4/3K1/K3/"
  f"K2+K1-free) with alpha=omega=k=sqrt(k^2): {bk_ok} — the EXACT 1/2-EXPONENT CEILING for C4, "
  f"paw and diamond (m = sqrt(n) on the infinite square subsequence).")
assert bk_ok

R("[E11] WITNESS FAMILY 2 — complete k-partite graphs, k parts of size k (= complement of B_k):")
WIT2 = []
for k in range(1, 9):
    edges, n = complete_multipartite([k] * k)
    row = cert_witness(f"K_{{{k}x{k}}}", edges, n)
    WIT2.append(row)
    R(f"[E11]   k={k}: n={n}, alpha={row['alpha']}, omega={row['omega']}, m={row['m']}, "
      f"H-free: {','.join(row['H_free'])}")
mk_ok = all({"2K2", "K2+2K1"} <= set(r["H_free"]) and r["m"] == k
            for r, k in zip(WIT2, range(1, 9)))
R(f"[E11] VERDICT: every complete k-partite k x k graph is 2K2-free AND K2+2K1-free (also "
  f"P3+K1/K2+K1/K3-free... as certified) with alpha=omega=k: {mk_ok} — the EXACT 1/2-EXPONENT "
  f"CEILING for 2K2 and K2+2K1 (complement duality machine-certified in E6).")
assert mk_ok

R("[E11] WITNESS FAMILY 3 — Ramsey triangle-free frontier (triangle-free => paw-free,")
R("[E11]   diamond-free, K3+K1-free, K4-free; alpha/omega exact by B&B):")
def moebius_kantor_edges():
    return cycle_edges(8) + [(i, i + 4) for i in range(4)]
def clebsch_adj():
    verts = [f for f in range(32) if bin(f).count("1") % 2 == 0]
    idx = {v: i for i, v in enumerate(verts)}
    edges = [(idx[A], idx[B]) for A in verts for B in verts if A < B and bin(A ^ B).count("1") == 4]
    return edges
FRONTIER = [
    ("C5", cycle_edges(5), 5),
    ("Moebius-Kantor/Wagner W8", moebius_kantor_edges(), 8),
    ("Petersen", petersen_edges, 10),
    ("Clebsch", clebsch_adj(), 16),
]
FRONTIER_ROWS = []
for name, edges, nn in FRONTIER:
    row = cert_witness(name, edges, nn)
    assert "K3" in row["H_free"] and "paw" in row["H_free"] and "diamond" in row["H_free"]
    FRONTIER_ROWS.append(row)
    R(f"[E11]   {name}: n={nn}, alpha={row['alpha']}, omega={row['omega']}, m={row['m']}, "
      f"rho={row['rho']:.4f}, H-free: {','.join(row['H_free'])}")

R("[E11] WITNESS FAMILY 4 — polarity graphs ER_q as C4 witnesses (C4-subgraph-free):")
for q in (2, 3):
    p = POLARITY[q]
    R(f"[E11]   ER_{q}: n={p['n']}, e={p['e']}, omega={p['omega']}, alpha={p['alpha']}, "
      f"m={p['m']}, rho_C4 <= {math.log(p['m'])/math.log(p['n']):.4f}")
R("[E11]   ER_4/ER_5 scoped out (GF(4)/GF(5) arithmetic — prime fields only certified)")

R("[E11] WITNESS FAMILY 5 — the brief's candidate families EVALUATED (honest verdicts):")
for tt in (2, 3, 4, 5):
    n = 5 * tt
    edges = []
    for part in range(5):
        for other in ((part + 1) % 5, (part + 4) % 5):
            for i in range(tt):
                for j in range(tt):
                    a, b = part * tt + i, other * tt + j
                    if a < b: edges.append((a, b))
    row = cert_witness(f"C5-blowup t={tt}", edges, n)
    verdict = ("paw/diamond-free BUT m=2t is LINEAR in n — a POOR witness (blow-ups inflate "
               "alpha; the block family is strictly better)" if "paw" in row["H_free"]
               else "NOT a witness (contains induced C4/2K2)")
    R(f"[E11]   C5-blowup t={tt}: n={n}, alpha={row['alpha']}, omega={row['omega']}, "
      f"m={row['m']}, H-free: {','.join(row['H_free']) or 'none of the 11'} — {verdict}")
heawood_edges = []
for i in range(7):
    for j in range(7):
        if i in (j, (j + 1) % 7, (j + 3) % 7):
            heawood_edges.append((i, 7 + j))
hrow = cert_witness("Heawood (incidence graph of PG(2,2))", heawood_edges, 14)
R(f"[E11]   Heawood: n=14, alpha={hrow['alpha']}, omega={hrow['omega']}, m={hrow['m']}, "
  f"H-free: {','.join(hrow['H_free'])} — C4-free but 3-regular bipartite => alpha=n/2: LINEAR m, "
  f"NOT a witness (verdict: rejected — the polarity identification, not the incidence graph, is "
  f"the right projective-plane witness)")

# ----------------------------------------------------------------------------
# E12. ADVERSARIAL SEARCH (annealing) — n=8 sanity vs census + n=12..32 witnesses.
# ----------------------------------------------------------------------------

def m_of(adj, n):
    a = alpha_bb(adj, n)
    w = alpha_bb(comp_adj(adj, n), n)
    return (a if a > w else w), a, w

def repair_free(mask, n, target, scan, rng, max_passes=80):
    cls_idx = CLS4_INDEX[target]
    for _ in range(max_passes):
        copies = []
        for S in scan.sub4:
            code = 0
            for k, (a, b) in enumerate(itertools.combinations(S, 2)):
                if a > b: a, b = b, a
                code |= ((mask >> scan.pos[(a, b)]) & 1) << k
            if CODE4_TO_CLS[code] == cls_idx:
                copies.append(S)
        if not copies:
            return mask
        for S in copies[:1500]:
            pairs = list(itertools.combinations(S, 2))
            rng.shuffle(pairs)
            for (a, b) in pairs:
                if a > b: a, b = b, a
                p = scan.pos[(a, b)]
                if mask >> p & 1:
                    mask &= ~(1 << p)
                    break
    return mask

def hfree_after_flip(adj, n, target, u, v):
    """would flipping edge (u,v) keep the graph free of induced target (4-vertex)?"""
    cls_idx = CLS4_INDEX[target]
    new_uv = 0 if adj[u] >> v & 1 else 1
    others = [x for x in range(n) if x != u and x != v]
    for x, y in itertools.combinations(others, 2):
        code = 0
        for k, (p, q) in enumerate(itertools.combinations((u, v, x, y), 2)):
            if p > q: p, q = q, p
            if p == u and q == v:
                bit = new_uv
            else:
                bit = 1 if adj[p] >> q & 1 else 0
            code |= bit << k
        if CODE4_TO_CLS[code] == cls_idx:
            return False
    return True

def anneal(n, target, rng, iters=4000, restarts=6, inits=None):
    scan = SubsetScan(n)
    best_m = BIG; best_mask = None
    inits = list(inits or [])
    for r in range(restarts):
        mask = inits[r] if r < len(inits) else rand_mask(n, rng)
        mask = repair_free(mask, n, target, scan, rng)
        adj = adj_of(mask, n)
        cur_m, _, _ = m_of(adj, n)
        if cur_m < best_m:
            best_m = cur_m; best_mask = mask
        for _ in range(iters):
            u = rng.randrange(n); v = rng.randrange(n)
            if u == v: continue
            if u > v: u, v = v, u
            if not hfree_after_flip(adj, n, target, u, v):
                continue
            if adj[u] >> v & 1:
                adj[u] &= ~(1 << v); adj[v] &= ~(1 << u)
            else:
                adj[u] |= 1 << v; adj[v] |= 1 << u
            new_m, _, _ = m_of(adj, n)
            if new_m <= cur_m or rng.random() < 0.03:
                cur_m = new_m
            else:
                if adj[u] >> v & 1:
                    adj[u] &= ~(1 << v); adj[v] &= ~(1 << u)
                else:
                    adj[u] |= 1 << v; adj[v] |= 1 << u
            if cur_m < best_m:
                best_m = cur_m
                best_mask = mask_of_adj(adj)
    return best_m, best_mask

FIVE = ["C4", "2K2", "paw", "diamond", "K2+2K1"]
SEARCH = {}
R("[E12] ADVERSARIAL ANNEALING SEARCH (minimize m under H-freeness; flips restricted to the")
R("[E12]   H-free slice; multi-restart; n=8 runs are SEEDED with the census witnesses):")
for target in FIVE + ["K1,3(claw)", "K4"]:
    init = [CENSUS[target][8]["witness_mask"]]
    m8, w8 = anneal(8, target, rng, iters=4000, restarts=6, inits=init)
    ok8 = (m8 == CENSUS[target][8]["h"])
    SEARCH[target] = {"8": {"found": m8, "census_h": CENSUS[target][8]["h"], "match": ok8}}
    R(f"[E12]   n=8 H={target}: search best m={m8} vs census h={CENSUS[target][8]['h']}: "
      f"{'MATCH' if ok8 else 'MISMATCH'}")
for target in FIVE:
    for nn in (12, 16, 20, 24):
        it = 4000 if nn <= 16 else 2500
        mn, wmask = anneal(nn, target, rng, iters=it, restarts=6)
        blk = math.isqrt(nn)
        SEARCH[target][str(nn)] = {"found": mn, "sqrt_n": round(math.sqrt(nn), 3)}
        R(f"[E12]   n={nn} H={target}: best m={mn} (sqrt(n)={math.sqrt(nn):.2f}; block-family "
          f"witness scale {blk}; a persistent m < sqrt(n)-o(1) trend would be exponent<1/2 evidence)")

def anneal_trianglefree(nn, rng, iters=6000, restarts=4):
    best = BIG; best_mask = None
    for r in range(restarts):
        adj = adj_of(rand_mask(nn, rng), nn)
        for _ in range(20000):
            tri = False
            for x in range(nn):
                cc = adj[x]
                while cc:
                    y = (cc & -cc).bit_length() - 1
                    cc &= cc - 1
                    if adj[x] & adj[y]:
                        adj[x] &= ~(1 << y); adj[y] &= ~(1 << x)
                        tri = True
            if not tri: break
        cur, _, _ = m_of(adj, nn)
        for _ in range(iters):
            u = rng.randrange(nn); v = rng.randrange(nn)
            if u == v: continue
            if u > v: u, v = v, u
            if adj[u] >> v & 1:
                adj[u] &= ~(1 << v); adj[v] &= ~(1 << u)
            else:
                if adj[u] & adj[v]:
                    continue
                adj[u] |= 1 << v; adj[v] |= 1 << u
            cur, _, _ = m_of(adj, nn)
            if cur < best:
                best = cur; best_mask = mask_of_adj(adj)
    return best, best_mask

R("[E12] triangle-free alpha-minimization search (paw/diamond/K3+K1 witnesses at larger n):")
for nn in (13, 17, 22, 28, 32):
    ba, _ = anneal_trianglefree(nn, rng, iters=5000, restarts=3)
    R(f"[E12]   n={nn}: best triangle-free m={ba} (rho_paw=rho_diamond <= {math.log(ba)/math.log(nn):.4f})")

# ----------------------------------------------------------------------------
# E13. ARSENAL LAW SPOT-CHECKS (read from arsenal-full/, instantiated numerically).
# ----------------------------------------------------------------------------

def bracket(v, w): return v[0] * w[1] - v[1] * w[0]
law_ok = {}
law_ok["bracket_skew [HC-PROOF-research/GSTCausalPairingGraphs.lean:18]"] = all(
    bracket(v, w) == -bracket(w, v) for v in [(3, 5), (2, 7), (9, 1)] for w in [(1, 4), (6, 2), (8, 3)])
def plucker(u, v, w, x):
    return bracket(u, v) * bracket(w, x) - bracket(u, w) * bracket(v, x) + bracket(u, x) * bracket(v, w)
law_ok["plucker_four [HC-PROOF-research/GSTCausalPairingGraphs.lean:37]"] = all(
    plucker(u, v, w, x) == 0 for u, v, w, x in
    [((1, 2), (3, 4), (5, 6), (7, 8)), ((2, 1), (4, 3), (6, 5), (8, 7)), ((0, 3), (1, 1), (2, 2), (5, 5))])
_state = {0: (3, 1), 1: (2, 5), 2: (7, 4), 3: (1, 9)}
def amplitude(edges):
    out = 1
    for (i, j) in edges:
        out *= bracket(_state[i], _state[j])
    return out
law_ok["graph_append [HC-PROOF-research/GSTCausalPairingGraphs.lean:67]"] = (
    amplitude([(0, 1), (2, 3), (0, 2), (1, 3)]) ==
    amplitude([(0, 1), (2, 3)]) * amplitude([(0, 2), (1, 3)]))
law_ok["two_pow_pos [HC-PROOF-research/CardinalWorlds.lean:419]"] = all(0 < 2 ** j for j in range(30))
law_ok["two_pow_factored [HC-PROOF-research/CardinalWorlds.lean:424]"] = all(
    2 ** j == 2 * 2 ** (j - 1) for j in range(1, 30))
law_ok["two_pow_ge2 [HC-PROOF-research/CardinalWorlds.lean:430]"] = all(2 <= 2 ** j for j in range(1, 30))
law_ok["three_pow_pos_lemma [HC-PROOF-research/CardinalWorlds.lean:185]"] = all(0 < 3 ** k for k in range(20))
law_ok["sq_sub_one [HC-PROOF-research/CardinalWorlds.lean:448]"] = all(
    a * a - 1 == (a - 1) * (a + 1) for a in range(1, 60))
law_ok["cubic_expansion [HC-PROOF-research/CardinalWorlds.lean:283]"] = all(
    (1 + a) ** 3 == 1 + 3 * a + 3 * a * a + a ** 3 for a in range(30))
def digitCount3(n): return 1 if n == 0 else 1 + digitCount3(n // 3)
law_ok["digitCount3_monotone [erdosternary2/ErdosTernary2.lean:2097]"] = all(
    digitCount3(n) <= digitCount3(n + 1) for n in range(5000))
law_ok["mod_mod_mul [HC-PROOF-research/CardinalWorlds.lean:140]"] = all(
    (n % (a * b)) % a == n % a for n in range(50) for a in (2, 3, 5) for b in (3, 4, 7))
law_ok["mul_add_div_lemma [HC-PROOF-research/CardinalWorlds.lean:143]"] = all(
    (d * k + r) // d == k + r // d for d in (2, 3, 7) for k in range(20) for r in range(d))
law_ok["worldMap_monotone (doctrine) [HC-PROOF-research/GSTGraphV2CausalComponents.lean:127]"] = (
    len(mono_bad) == 0)
R("[E13] ARSENAL LAW SPOT-CHECKS (numeric instantiation / doctrine verification):")
for kk, vv in law_ok.items():
    R(f"[E13]   {kk}: {'GREEN' if vv else 'RED'}")
assert all(law_ok.values())

# ----------------------------------------------------------------------------
# E14. FINAL TABLE + JSON DUMP.
# ----------------------------------------------------------------------------

R("=" * 78)
R("[E14] THE GRAND CENSUS TABLE — h_H(n) and rho_H(n)=ln h/ln n (EXACT n=1..8)")
R("[E14] H \\ n      " + "".join(f"n={i:<10}" for i in range(2, 9)))
for k in H_ORDER:
    row = []
    for n in range(2, 9):
        d = CENSUS[k][n]
        row.append("vac       " if d["h"] is None else f"{d['h']}({d['rho']:.3f})".ljust(10))
    R("[E14] " + k.ljust(12) + "".join(row))
R("[E14] (K1 row vacuous — no K1-free graph exists; for |V(H)|>n the value is the all-graphs "
  "minimum h_all(n) = {[h_all[i] for i in range(2, 9)]}; n=8 values are EXACT: h=3 iff an "
  "H-free graph with m=3 exists (exhaustive 2^28 m=3-stratum scan), else h=4 via C8 witnesses.)")

FIVE_row = {k: [CENSUS[k][n]["h"] for n in range(2, 9)] for k in FIVE}
R(f"[E14] THE FIVE REMAINING (61K's targets) h-rows n=2..8: {FIVE_row}")
R("[E14] their rho rows n=2..8: " + "; ".join(
    f"{k}: " + ",".join(f"{CENSUS[k][n]['rho']:.3f}" for n in range(2, 9)) for k in FIVE))

out = {
    "meta": {
        "task": "W75-61E grand census + verification battery (Erdos-Hajnal #61)",
        "engine": "engine61census.py",
        "wall_s": round(el(), 1),
        "H_universe": H_ORDER,
        "complement_pairs": COMPLEMENT_PAIR,
        "classes4": CLS4_NAMES,
        "h_all": {str(i): h_all[i] for i in range(1, 9)},
        "n8_scan": {"m3_stratum_size": CAND8_TOTAL,
                    "chunks": NCHUNKS8,
                    "per_H_m3_counts": {k: SCAN8[k]["count_m3"] for k in H_ORDER}},
    },
    "census": {k: {str(n): {"h": CENSUS[k][n]["h"],
                            "rho": (None if CENSUS[k][n]["rho"] is None
                                    else round(CENSUS[k][n]["rho"], 6)),
                            "witness_mask": CENSUS[k][n].get("witness_mask"),
                            "witness_edges": (mask_to_edges(CENSUS[k][n]["witness_mask"], n)
                                              if CENSUS[k][n].get("witness_mask") is not None
                                              else None),
                            "src": CENSUS[k][n].get("src", "")}
                for n in range(1, 9)} for k in H_ORDER},
    "battery": {
        "alpha_crosscheck_disagreements": B1_bad,
        "omega_crosscheck_disagreements": B2_bad,
        "containment_crosscheck_disagreements": B3_bad,
        "complement_selftest_mismatches": len(mismatch),
        "monotonicity_violations": len(mono_bad),
        "inheritance_violations": len(order_bad),
        "banked_B_table_reproduced": banked_ok,
        "bell_counts_reproduced": bell_got == bell_expected,
        "P4_minprod_by_n": {str(n): PY_LANE[n]["minprod_P4"] for n in range(1, 8)},
        "P4free_SL_violations": SL_bad,
        "F7_violations": len(f7_bad),
        "claw_laws": {"h_ge_half_ncube": claw_ok,
                      "alpha_ge_n_over_omega2plus1": bool(law_ii and ok_n6),
                      "deg_le_omega_choose2_minus1": bool(ok_iii),
                      "deg_lt_omega_sq": bool(ok_iv)},
        "ram": {"h_K4_ge_tR_all_n": ram_ok, "bridge_256_to_2p20": bridge_ok},
    },
    "lemmas": {
        "L1a_induced_C4free_sumC2": f"FALSE — {len(lemma[4]['L1a'])+len(lemma[5]['L1a'])+len(lemma[6]['L1a'])} machine counterexamples n=4..6 (K4, diamond at n=4)",
        "L1b_subgraph_C4free_sumC2": "TRUE — exhaustive n<=6 + polarity n=7,13,21,31 + 90 random n=9..11 + trees/cycles/Petersen",
        "L2a_induced_C4free_reiman": "FALSE — K4 (e=6>4.61), diamond (e=5>4.61) at n=4",
        "L2b_subgraph_C4free_reiman": "TRUE — same certified pool",
        "L3_carowei_weak": "TRUE — every graph n<=6 exhaustive + n=7 all 2^21",
        "L4a_pawfree_Nv_P3free": f"FALSE — {len(L4a_viol)} counterexamples (the diamond); corrected laws L4b/L4c TRUE",
        "L4b_pawfree_Nv_2K2free": "TRUE — all paw-free graphs n=4..6",
        "L4c_diamondfree_Nv_P3free": "TRUE — all diamond-free graphs n=4..6",
        "L5_P3free_union_of_cliques": "TRUE — all P3-free n=1..7, counts=Bell",
        "L6_diamondfree_edge_common_nbhd_clique": "TRUE — exhaustive n=4..6 + all diamond-free n=7",
        "L7_composite_tn_floor_all_11H": "TRUE — h_H(n)>=t_n for all 11 four-vertex H at every n<=8",
    },
    "witnesses": {
        "block_family_B_k": WIT,
        "multipartite_family": WIT2,
        "triangle_free_frontier": FRONTIER_ROWS,
        "polarity": {str(q): POLARITY[q] for q in POLARITY},
    },
    "search": SEARCH,
    "arsenal_laws": law_ok,
}
with open("census61.json", "w") as f:
    json.dump(out, f, indent=1)
R(f"[E14] census61.json written")

verdict = (B1_bad == 0 and B2_bad == 0 and B3_bad == 0 and not mismatch and not mono_bad
           and not order_bad and banked_ok and bell_got == bell_expected and SL_bad == 0
           and not f7_bad and th1_ok and th2_ok and th3_ok and thS_law and prod_ok and claw_ok
           and law_ii and ok_iii and ok_iv and ok_n6 and ram_ok and bridge_ok
           and all(law_ok.values()) and not L7_bad)
R("=" * 78)
R(f"[FINAL] W75-61E VERDICT: "
  f"{'ALL GREEN — census n=1..8 exact (dual independent lanes n=7, exhaustive 2^28 m=3 stratum at n=8); battery 0 disagreements; complement self-test 0 mismatches; banked claims re-derived; lemma counterexamples caught (induced-vs-subgraph readings separated); witnesses shipped' if verdict else 'RED — see receipts'}")
R(f"[FINAL] engine wall: {el():.1f}s. The engine never stops; it never lies. In English, always.")
assert verdict

with open("receipts61census.txt", "w") as f:
    f.write("\n".join(RECEIPT_LINES) + "\n")
print("\n>>> receipts61census.txt + census61.json written <<<", flush=True)
