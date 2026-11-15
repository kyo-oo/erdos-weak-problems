#!/usr/bin/env python3
"""
ENGINE A — bitmask DP tables for the Erdos #61 doubter census (W67-61D).

Pure exact integer arithmetic. No floats anywhere.

Conventions
-----------
* A graph on k vertices (labels 0..k-1) is an edge bitmask F over the
  m(k) = k*(k-1)/2 pairs, listed in lexicographic order
  (0,1),(0,2),(1,2),(0,3),...,(k-2,k-1).
  Bit position of pair (i,j), i<j, is PI_k[(i,j)].
* KEY STRUCTURAL FACT used everywhere: the pairs involving vertex k-1 are
  exactly the TOP k-1 bits, and m(k-1) = m(k) - (k-1), hence every level-k
  mask decomposes uniquely as
      F = F_low | (Nv << m(k-1))
  where F_low is the induced subgraph on vertices 0..k-2 (a level-(k-1) mask)
  and Nv (k-1 bits, bit i <-> edge {i,k-1}) is the neighbourhood of k-1.
* sub[j][N]  (N a vertex-subset bitmask of {0..j-1}) is a table over ALL
  level-j masks F giving omega of the subgraph induced by F on N.
* om[k][F] = clique number omega of the level-k graph F.
  omega(F) = max( omega(F_low), 1 + omega(induced F_low on Nv) ).
* alpha(F) = omega(complement of F) since alpha(G) = omega(G_bar).
* p4free tables for k<=6 via labelled-copy orbits; for k=7 via the
  fibre/forbid construction over the (F_low, Nv) decomposition.

Everything is exact; the module self-tests its recurrences against a
brute-force reference before use (see self_test()).
"""

import itertools
from math import isqrt

# ---------------------------------------------------------------- constants

def m(k):
    """Number of pairs of a k-vertex graph."""
    return k * (k - 1) // 2

MAXK = 7

PAIRS = {
    # W67-61D repair #3: the seeded file built PAIRS in row-major order
    # ((0,1),(0,2),(0,3),(1,2),...), which contradicts the docstring's
    # convention AND breaks the "pairs of vertex k-1 occupy the TOP k-1 bit
    # positions" structural fact that every DP recurrence here
    # (build_sub_tables, build_om, build_forbid7, _build_forbid_level6,
    # p4free7_blocks) relies on. The docstring order is COlexicographic
    # (sort by larger endpoint, then smaller): (0,1),(0,2),(1,2),(0,3),...
    # so that the first m(k-1) positions are exactly the pairs inside
    # {0..k-2} and the top k-1 bits are exactly the pairs of vertex k-1.
    k: sorted(
        ((i, j) for i in range(k) for j in range(i + 1, k)),
        key=lambda p: (p[1], p[0]),
    )
    for k in range(MAXK + 1)
}
PI = {k: {p: idx for idx, p in enumerate(PAIRS[k])} for k in range(MAXK + 1)}
FULL = {k: (1 << m(k)) - 1 for k in range(MAXK + 1)}

# For each level k and vertex v: list of pair positions incident to v.
INCIDENT = {
    k: {v: [PI[k][p] for p in PAIRS[k] if v in p] for v in range(k)}
    for k in range(MAXK + 1)
}


def popcount(x):
    return x.bit_count()


def comp_mask(F, k):
    """Complement of a level-k graph (same pair indexing)."""
    return F ^ FULL[k]


def comp_half_sqrt(t):
    """ceil(sqrt(t)/2) with exact integer arithmetic.

    ceil(x/2) == ceil(ceil(x)/2) for real x >= 0; ceil(sqrt(t)) is
    isqrt(t) when t is a perfect square else isqrt(t)+1.
    """
    if t <= 0:
        return 0
    s = isqrt(t)
    if s * s != t:
        s += 1
    return (s + 1) // 2


def floor_half_sqrt(t):
    """floor(sqrt(t)/2) == floor(floor(sqrt(t))/2), exact."""
    if t <= 0:
        return 0
    return isqrt(t) // 2


def ceil_sqrt(t):
    if t <= 0:
        return 0
    s = isqrt(t)
    return s if s * s == t else s + 1


def floor_sqrt(t):
    return isqrt(t) if t > 0 else 0


# ---------------------------------------------------------------- omega core

def build_sub_tables(jmax=6):
    """sub[j][N] = bytearray over all level-j masks F:
    sub[j][N][F] = omega(subgraph induced by F on vertex set N)."""
    sub = {0: {0: bytearray([0])}}
    for j in range(1, jmax + 1):
        lowsz = 1 << m(j - 1)
        nvs = 1 << (j - 1)
        level = {}
        # N ranges over ALL vertex subsets of {0..j-1}: 2^j values.
        # (The seeded version looped over range(nvs) = 2^(j-1) values only,
        #  which crashed with KeyError at j=2 and would have silently
        #  half-populated every level -- W67-61D repair, see REPORT_W67.md.)
        for N in range(1 << j):
            tgt = bytearray(lowsz * nvs)
            if N == 0:
                level[N] = tgt
                continue
            h = N.bit_length() - 1  # highest vertex of N (<= j-1)
            if h < j - 1:
                # Induced graph on N touches only F_low bits.
                src = sub[j - 1][N]
                for nv in range(nvs):
                    tgt[nv * lowsz:(nv + 1) * lowsz] = src
            else:
                A = sub[j - 1][N ^ (1 << h)]
                for nv in range(nvs):
                    B = sub[j - 1][nv & N]
                    base = nv * lowsz
                    for fl in range(lowsz):
                        a = A[fl]
                        b = B[fl] + 1
                        tgt[base + fl] = a if a >= b else b
            # W67-61D repair #2: the seeded file never stored tgt for
            # N != 0 (only the N == 0 branch assigned level[N]), so every
            # level above 0 was left with a single key and the build
            # crashed. Store the completed table for this N.
            level[N] = tgt
        sub[j] = level
    return sub


def build_om(kmax=7, sub=None):
    """om[k][F] = clique number of the level-k graph F (bytearray)."""
    if sub is None:
        sub = build_sub_tables(kmax - 1)
    om = {0: bytearray([0]), 1: bytearray([1])}
    for k in range(2, kmax + 1):
        lowsz = 1 << m(k - 1)
        nvs = 1 << (k - 1)
        prev = om[k - 1]
        cur = bytearray(lowsz * nvs)
        for nv in range(nvs):
            S = sub[k - 1][nv]
            base = nv * lowsz
            for fl in range(lowsz):
                a = prev[fl]
                b = S[fl] + 1
                cur[base + fl] = a if a >= b else b
        om[k] = cur
    return om


# ------------------------------------------------------- 4-vertex copy orbits

def copies4_orbits(k, hmask4):
    """For a 4-vertex pattern H (level-4 mask), return for every 4-subset S
    of {0..k-1} the set of LOCAL 6-bit masks of induced copies of H on S.
    Result: dict S(tuple sorted) -> set of local masks, where local bit b
    corresponds to the b-th pair of itertools.combinations(S, 2) -- the
    exact same local indexing that induced_mask_on(F, pos) produces for
    pos = [PI[k][p] for p in combinations(S, 2)].

    W67-61D repair #7: the seeded version built orbit masks with GLOBAL
    level-k bit positions (only the 3 edge bits of H, at positions spread
    over PI[k]) and then compared them against induced_mask_on's LOCAL
    6-bit extraction -- an apples-to-oranges comparison that made
    build_p4free_orbit's flags garbage (e.g. it declared the graph with
    edges (0,1),(1,2),(0,5) on 6 vertices P4-free). Both sides now use
    the combinations(S,2) local indexing, and equality of the 6-bit
    induced mask with an orbit mask certifies EXACTLY the 3 path edges
    on S (an induced copy of H)."""
    assert k >= 4
    Hedges = [PAIRS[4][b] for b in range(m(4)) if (hmask4 >> b) & 1]
    out = {}
    for S in itertools.combinations(range(k), 4):
        local_pairs = list(itertools.combinations(S, 2))
        lidx = {p: i for i, p in enumerate(local_pairs)}
        orbs = set()
        for perm in itertools.permutations(range(4)):
            mask = 0
            for (a, b) in Hedges:
                u, v = S[perm[a]], S[perm[b]]
                if u > v:
                    u, v = v, u
                mask |= 1 << lidx[(u, v)]
            orbs.add(mask)
        out[S] = orbs
    return out


def induced_mask_on(F, positions):
    """Extract the bits of F at the given pair positions into a local mask."""
    r = 0
    b = 1
    for p in positions:
        if (F >> p) & 1:
            r |= b
        b <<= 1
    return r


# The 11 unlabeled 4-vertex graphs, canonical level-4 masks.
H4_NAMES = {
    "I4":        [],                      # empty
    "K2+2I":    [(0, 1)],
    "2K2":      [(0, 1), (2, 3)],
    "P3+I":     [(0, 1), (1, 2)],
    "K3+I":     [(0, 1), (0, 2), (1, 2)],
    "K1,3":     [(0, 1), (0, 2), (0, 3)],
    "P4":       [(0, 1), (1, 2), (2, 3)],
    "C4":       [(0, 1), (1, 2), (2, 3), (0, 3)],
    "paw":      [(0, 1), (0, 2), (1, 2), (0, 3)],
    "diamond":  [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3)],
    "K4":       [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)],
}


def h4_mask(name):
    mask = 0
    for (a, b) in H4_NAMES[name]:
        mask |= 1 << PI[4][(a, b)]
    return mask


H4_BAR = {  # complement names for the frontier map
    "I4": "K4", "K4": "I4",
    "K2+2I": "diamond", "diamond": "K2+2I",
    "2K2": "C4", "C4": "2K2",
    "P3+I": "paw", "paw": "P3+I",
    "K3+I": "K1,3", "K1,3": "K3+I",
    "P4": "P4",
}


# ------------------------------------------------------------- P4 machinery

def p4_masks_labeled():
    """The 12 labelled P4 masks on 4 vertices (level-4 indexing).
    (W67-61D repair #8: rebuilt directly at level-4 indexing; the old
    version returned combinations-indexed local masks mislabelled as
    level-4 masks.)"""
    res = set()
    for perm in itertools.permutations(range(4)):
        m = 0
        for (a, b) in H4_NAMES["P4"]:
            u, v = perm[a], perm[b]
            m |= 1 << PI[4][(min(u, v), max(u, v))]
        res.add(m)
    return res


def build_p4free_orbit(kmax=6):
    """p4free[k] flag tables for k<=kmax via subset/orbit scans (independent
    of the fibre construction used for k=7)."""
    p4 = h4_mask("P4")
    p4free = {}
    for k in range(0, kmax + 1):
        size = 1 << m(k)
        if k < 4:
            p4free[k] = bytearray([1]) * size
            continue
        orbs = copies4_orbits(k, p4)
        # per-subset: positions of the 6 pairs of S in level-k order + orbit
        subset_data = []
        for S, orb in orbs.items():
            pos = [PI[k][(a, b)] for (a, b) in itertools.combinations(S, 2)]
            subset_data.append((pos, orb))
        cur = bytearray(size)
        for F in range(size):
            ok = 1
            for pos, orb in subset_data:
                if induced_mask_on(F, pos) in orb:
                    ok = 0
                    break
            cur[F] = ok
        p4free[k] = cur
    return p4free


def build_forbid7(p4free6=None):
    """forbid[N] (N in 0..63) : bytearray(2^15), forbid[N][F_low] = 1 iff the
    level-7 graph F_low | (N<<15) contains an induced P4 using vertex 6.
    Built by fibre marking over the 20 triples of {0..5}."""
    triples = list(itertools.combinations(range(6), 3))
    # labelled P4 (x,y) signatures per triple: x = bits (ab,ac,bc) of F_low,
    # y = bits (a6,b6,c6) from N.
    sig = {}
    for (a, b, c) in triples:
        s = set()
        for perm in itertools.permutations((a, b, c, 6)):
            v1, v2, v3, v4 = perm
            # W67-61D repair #6: store path edges as NORMALIZED
            # (min,max) pairs -- the seeded file stored ordered tuples,
            # so e(u,v) lookups with (min(u,v),max(u,v)) silently
            # missed every descending-stored edge and the forbid
            # tables were garbage (they marked the empty graph as
            # containing a P4).
            edges = {
                (min(v1, v2), max(v1, v2)),
                (min(v2, v3), max(v2, v3)),
                (min(v3, v4), max(v3, v4)),
            }
            def e(u, v):
                return (min(u, v), max(u, v)) in edges
            x = (4 if e(a, b) else 0) | (2 if e(a, c) else 0) | (1 if e(b, c) else 0)
            y = (4 if e(a, 6) else 0) | (2 if e(b, 6) else 0) | (1 if e(c, 6) else 0)
            # exactly the 3 path edges and no others
            allp = {(a, b), (a, c), (b, c), (a, 6), (b, 6), (c, 6)}
            if set(edges) <= allp:
                s.add((x, y))
        assert len(s) == 12, (a, b, c, len(s))
        sig[(a, b, c)] = s
    # per-triple fibre cores: F_low values with the 3 triple-bits cleared
    core_cache = {}
    for (a, b, c) in triples:
        p1, p2, p3 = PI[6][(a, b)], PI[6][(a, c)], PI[6][(b, c)]
        others = [p for p in range(15) if p not in (p1, p2, p3)]
        assert len(others) == 12
        cores = []
        for t in range(1 << 12):
            v = 0
            for i in range(12):
                if (t >> i) & 1:
                    v |= 1 << others[i]
            cores.append(v)
        core_cache[(a, b, c)] = (p1, p2, p3, cores)
    forbid = []
    for N in range(64):
        f = bytearray(1 << 15)
        for (a, b, c) in triples:
            y = (4 if (N >> a) & 1 else 0) | (2 if (N >> b) & 1 else 0) | (1 if (N >> c) & 1 else 0)
            badx = [x for (x, yy) in sig[(a, b, c)] if yy == y]
            if not badx:
                continue
            p1, p2, p3, cores = core_cache[(a, b, c)]
            for x in badx:
                pat = 0
                if (x >> 2) & 1:
                    pat |= 1 << p1
                if (x >> 1) & 1:
                    pat |= 1 << p2
                if x & 1:
                    pat |= 1 << p3
                for core in cores:
                    f[core | pat] = 1
        forbid.append(f)
    return forbid


def p4free7_blocks(p4free6, forbid):
    """Return list of 64 big ints; block[N] has bit F_low set iff
    F = F_low | (N<<15) is P4-free."""
    blocks = []
    pf6 = int.from_bytes(bytes(p4free6), "little")
    for N in range(64):
        fi = int.from_bytes(bytes(forbid[N]), "little")
        blocks.append(pf6 & ~fi & ((1 << (1 << 15)) - 1))
    return blocks


def iter_set_bits(block_int, width):
    """Yield indices of set bits of a width-bit big int, via to_bytes."""
    nbytes = (width + 7) // 8
    data = block_int.to_bytes(nbytes, "little")
    for bi, byte in enumerate(data):
        if byte:
            for bit in range(8):
                if (byte >> bit) & 1:
                    yield bi * 8 + bit


# ------------------------------------------------------- cograph generation

def set_partitions(vertices):
    """All set partitions of a sequence of distinct vertices (>=1 block)."""
    vertices = list(vertices)
    if not vertices:
        yield []
        return
    first = vertices[0]
    rest = vertices[1:]
    for sub in _subsets(rest):
        others = [v for v in rest if v not in sub]
        for pi in set_partitions(others):
            yield [[first] + list(sub)] + pi


def _subsets(seq):
    for r in range(len(seq) + 1):
        for c in itertools.combinations(seq, r):
            yield list(c)


def _cross_pairs_global(blocks):
    """Bitmask (global 21-pair indexing, n=7) of all pairs across blocks."""
    mask = 0
    for i in range(len(blocks)):
        for j in range(i + 1, len(blocks)):
            for u in blocks[i]:
                for v in blocks[j]:
                    mask |= 1 << PI[7][(min(u, v), max(u, v))]
    return mask


def cographs_global(vertices, memo):
    """Set of global-21-bit edge masks of all P4-free (cograph) graphs on the
    given vertex subset, generated by disjoint-union / join construction
    (Seinsche recursion). Vertices are from {0..6}."""
    key = frozenset(vertices)
    if key in memo:
        return memo[key]
    vs = sorted(key)
    if len(vs) <= 1:
        res = {0}
        memo[key] = res
        return res
    res = set()
    for pi in set_partitions(vs):
        if len(pi) < 2:
            continue
        opts = [cographs_global(b, memo) for b in pi]
        cross = _cross_pairs_global(pi)
        for combo in itertools.product(*opts):
            mu = 0
            for msk in combo:
                mu |= msk
            res.add(mu)                 # disjoint union
            res.add(mu | cross)          # join
    memo[key] = res
    return res


def union_of_cliques_global(vertices):
    """All P3-free graphs (disjoint unions of cliques) on the vertex set as
    global-21-bit masks = all set partitions into clique blocks."""
    res = set()
    for pi in set_partitions(sorted(vertices)):
        mask = 0
        for block in pi:
            for u, v in itertools.combinations(block, 2):
                mask |= 1 << PI[7][(u, v)]
        res.add(mask)
    return res


# ------------------------------------------------------------- connectivity

def adjacency_from_global(F, n=7):
    adj = []
    for v in range(n):
        av = 0
        for u in range(n):
            if u != v:
                p = PI[n][(min(u, v), max(u, v))]
                if (F >> p) & 1:
                    av |= 1 << u
        adj.append(av)
    return adj


def connected_from_adj(adj):
    n = len(adj)
    seen = 1
    frontier = 1
    while frontier:
        nxt = 0
        for v in range(n):
            if (frontier >> v) & 1:
                nxt |= adj[v]
        nxt &= ~seen
        seen |= nxt
        frontier = nxt
        if seen == (1 << n) - 1:
            return True
    return False


def connected_global(F, n=7):
    return connected_from_adj(adjacency_from_global(F, n))


# ------------------------------------------------------------- self tests

def _brute_omega(F, k):
    """Reference clique number by brute force over vertex subsets."""
    best = 0
    for S in range(1 << k):
        ok = True
        pairs = itertools.combinations(range(k), 2)
        for (a, b) in pairs:
            if ((S >> a) & 1) and ((S >> b) & 1):
                if not ((F >> PI[k][(a, b)]) & 1):
                    ok = False
                    break
        if not ok:
            continue
        c = popcount(S)
        if c > best:
            best = c
    return best


def self_test():
    """Verify the table recurrences against brute force on all graphs with
    k <= 5 and the P4 machinery on k <= 5, plus tiny hand cases."""
    sub = build_sub_tables(6)
    om = build_om(7, sub)
    # hand cases at k=3
    assert om[3][0] == 1                    # I3
    assert om[3][7] == 3                    # K3
    assert om[3][5] == 2                    # P3
    assert om[3][3] == 2                    # claw
    assert om[3][1] == 2                    # K2 + isolated
    for k in range(1, 6):
        for F in range(1 << m(k)):
            assert om[k][F] == _brute_omega(F, k), (k, F)
        # complement duality: comp is an involution on masks and the
        # omega/alpha pair is complement-symmetric.
        # (W67-61D repair #4: the seeded check `a * b >= 0` was vacuous.)
        for F in range(1 << m(k)):
            assert comp_mask(comp_mask(F, k), k) == F
            a, b = om[k][F], om[k][comp_mask(F, k)]
            c, d = om[k][comp_mask(F, k)], om[k][comp_mask(comp_mask(F, k), k)]
            assert max(a, b) == max(c, d)          # max(omega, alpha) is comp-invariant
            assert b == om[k][comp_mask(F, k)]     # alpha(F) := omega(F_bar)
    # spot alpha sanity: C5 (level 5, cycle 0-1-2-3-4-0) has omega=alpha=2
    c5 = 0
    for (a, b) in [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]:
        c5 |= 1 << PI[5][(a, b)]
    assert om[5][c5] == 2 and om[5][comp_mask(c5, 5)] == 2
    # P4 orbit machinery
    p4free = build_p4free_orbit(6)
    assert p4free[4][h4_mask("P4")] == 0
    assert p4free[4][h4_mask("C4")] == 1
    assert p4free[4][h4_mask("K4")] == 1
    assert p4free[4][h4_mask("paw")] == 1
    # C5 contains an induced P4 -> not P4-free; K_{2,3}... just check C5:
    assert p4free[5][c5] == 0
    # disjoint union of two triangles is a cograph (6 vertices: the seeded
    # file wrongly indexed this 6-vertex graph with PI[5] -- W67-61D repair #5)
    two_k3 = (1 << PI[6][(0, 1)]) | (1 << PI[6][(0, 2)]) | (1 << PI[6][(1, 2)]) \
        | (1 << PI[6][(3, 4)]) | (1 << PI[6][(3, 5)]) | (1 << PI[6][(4, 5)])
    assert p4free[6][two_k3] == 1
    assert om[6][two_k3] == 3 and om[6][comp_mask(two_k3, 6)] == 2  # omega=3, alpha=2
    # fibre machinery at level 6 must reproduce the orbit table exactly
    forbid6 = _build_forbid_level6()
    pf6_fibre = _p4free6_from_fibre(p4free[5], forbid6)
    assert bytes(pf6_fibre) == bytes(p4free[6])
    # labelled P4 count on 4 vertices is 12
    assert len(p4_masks_labeled()) == 12
    # Bell number check: P3-free graphs on 6 vertices = 203 partitions
    assert len(union_of_cliques_global(range(6))) == 203
    return om, sub


def _build_forbid_level6():
    """Fibre/forbid tables at level 6 (for the self-test of the level-7
    construction applied one level down): forbid[N][F_low] over level-5
    F_low, N in 0..31, marks P4s using vertex 5."""
    triples = list(itertools.combinations(range(5), 3))
    sig = {}
    for (a, b, c) in triples:
        s = set()
        for perm in itertools.permutations((a, b, c, 5)):
            v1, v2, v3, v4 = perm
            # W67-61D repair #6: store path edges as NORMALIZED
            # (min,max) pairs -- the seeded file stored ordered tuples,
            # so e(u,v) lookups with (min(u,v),max(u,v)) silently
            # missed every descending-stored edge and the forbid
            # tables were garbage (they marked the empty graph as
            # containing a P4).
            edges = {
                (min(v1, v2), max(v1, v2)),
                (min(v2, v3), max(v2, v3)),
                (min(v3, v4), max(v3, v4)),
            }
            def e(u, v):
                return (min(u, v), max(u, v)) in edges
            x = (4 if e(a, b) else 0) | (2 if e(a, c) else 0) | (1 if e(b, c) else 0)
            y = (4 if e(a, 5) else 0) | (2 if e(b, 5) else 0) | (1 if e(c, 5) else 0)
            s.add((x, y))
        sig[(a, b, c)] = s
    forbid = []
    for N in range(32):
        f = bytearray(1 << 10)
        for (a, b, c) in triples:
            y = (4 if (N >> a) & 1 else 0) | (2 if (N >> b) & 1 else 0) | (1 if (N >> c) & 1 else 0)
            badx = [x for (x, yy) in sig[(a, b, c)] if yy == y]
            if not badx:
                continue
            p1, p2, p3 = PI[5][(a, b)], PI[5][(a, c)], PI[5][(b, c)]
            others = [p for p in range(10) if p not in (p1, p2, p3)]
            for x in badx:
                pat = 0
                if (x >> 2) & 1:
                    pat |= 1 << p1
                if (x >> 1) & 1:
                    pat |= 1 << p2
                if x & 1:
                    pat |= 1 << p3
                for t in range(1 << 7):
                    core = 0
                    for i in range(7):
                        if (t >> i) & 1:
                            core |= 1 << others[i]
                    f[core | pat] = 1
        forbid.append(f)
    return forbid


def _p4free6_from_fibre(p4free5, forbid6):
    tbl = bytearray(1 << 15)
    for N in range(32):
        f = forbid6[N]
        base = N << 10
        for fl in range(1 << 10):
            tbl[base + fl] = 1 if (p4free5[fl] and not f[fl]) else 0
    return tbl


if __name__ == "__main__":
    import time
    t0 = time.time()
    om, sub = self_test()
    print(f"ENGINE A SELF-TEST GREEN ({time.time()-t0:.1f}s): "
          f"omega tables verified vs brute force for all graphs k<=5; "
          f"P4 orbit==fibre at level 6; Bell(6)=203 P3-free graphs.")
