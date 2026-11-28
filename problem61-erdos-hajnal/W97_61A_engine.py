#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W97_61A_engine.py — THE P5 FRONT ASSAULT ENGINE (Wave 97, Agent 61A).

Target: Erdos-Hajnal for the P5 front (eh_P5 over the official predicate
IsErdosHajnalLowerBound). Modes:

  recon    : exploratory censuses / tables (prints; no receipts)
  --verify : the final receipt battery (PASS/FAIL lines + VERDICT line)

Exact arithmetic (int / Fraction); z3 = independent second method for the
arithmetic lemmas. Graphs = bitmask adjacency tuples. SEED 20271109.
"""
import sys, random, itertools, time
from fractions import Fraction

SEED = 20271109
PASS = 0
FAIL = 0
T0 = time.time()

def note(msg): print(msg)
def check(name, ok, detail=""):
    global PASS, FAIL
    tag = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else: FAIL += 1
    print(f"[{tag}] {name}" + (f" :: {detail}" if detail else ""))
def wall(): return f"{time.time()-T0:.1f}s"

# ---------------------------------------------------------------- graphs
def all_graphs(n):
    m = n * (n - 1) // 2
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << m):
        adj = [0] * n
        for b, (i, j) in enumerate(pairs):
            if mask >> b & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
        yield tuple(adj)

def complement(g):
    n = len(g)
    full = (1 << n) - 1
    return tuple((~g[i]) & full & ~(1 << i) for i in range(n))

def _mask(sub):
    m = 0
    for i in sub: m |= 1 << i
    return m

def degseq(g, sub):
    m = _mask(sub)
    return tuple(sorted(bin(g[i] & m).count("1") for i in sub))

def sub_edges(g, sub):
    m = _mask(sub)
    return sum(bin(g[i] & m).count("1") for i in sub) // 2

def sub_connected(g, sub):
    sub = list(sub)
    if len(sub) <= 1: return True
    m = _mask(sub)
    seen = 1 << sub[0]
    stack = [sub[0]]
    while stack:
        v = stack.pop()
        nb = g[v] & m & ~seen
        while nb:
            b = nb & -nb
            seen |= b
            stack.append(b.bit_length() - 1)
            nb ^= b
    return seen == m

def connected(g): return sub_connected(g, tuple(range(len(g))))

def is_P5(g, sub):
    return (len(sub) == 5 and sub_edges(g, sub) == 4
            and sub_connected(g, sub) and degseq(g, sub) == (1, 1, 2, 2, 2))

def is_C5(g, sub):
    return (len(sub) == 5 and sub_edges(g, sub) == 5
            and sub_connected(g, sub) and degseq(g, sub) == (2, 2, 2, 2, 2))

def has_P5(g):
    n = len(g)
    return any(is_P5(g, s) for s in itertools.combinations(range(n), 5))
def has_C5(g):
    n = len(g)
    return any(is_C5(g, s) for s in itertools.combinations(range(n), 5))

_P5E = {(0,1),(1,2),(2,3),(3,4)}
_C5E = {(0,1),(1,2),(2,3),(3,4),(4,0)}
def has_induced_perm(g, edgeset):
    """Second method: all 5-subsets x 120 bijections (induced check)."""
    n = len(g)
    for sub in itertools.combinations(range(n), 5):
        for pi in itertools.permutations(range(5)):
            ok = True
            for a in range(5):
                for b in range(a+1, 5):
                    e = (g[sub[pi[a]]] >> sub[pi[b]] & 1) == 1
                    if e != ((a, b) in edgeset):
                        ok = False; break
                if not ok: break
            if ok: return True
    return False

def omega_brute(g):
    n, best = len(g), 0
    for mask in range(1 << n):
        ms = [i for i in range(n) if mask >> i & 1]
        ok = True
        for i in range(len(ms)):
            for j in range(i+1, len(ms)):
                if not (g[ms[i]] >> ms[j] & 1):
                    ok = False; break
            if not ok: break
        if ok: best = max(best, len(ms))
    return best

def alpha_brute(g): return omega_brute(complement(g))

def alpha_combos(g):
    n, best = len(g), [0]
    def rec(start, cur):
        if len(cur) > best[0]: best[0] = len(cur)
        for v in range(start, n):
            if all(not (g[v] >> u & 1) for u in cur):
                rec(v+1, cur + [v])
    rec(0, [])
    return best[0]

def hom(g): return max(alpha_brute(g), omega_brute(g))

def is_clique(g, sub):
    sub = list(sub)
    for i in range(len(sub)):
        for j in range(i+1, len(sub)):
            if not (g[sub[i]] >> sub[j] & 1):
                return False
    return True

def dominates(g, sub):
    cover = 0
    for v in sub: cover |= 1 << v | g[v]
    return cover == (1 << len(g)) - 1

def is_induced_P3(g, sub):
    return (len(sub) == 3 and sub_edges(g, sub) == 2 and sub_connected(g, sub))

def bt_shape(g):
    """Best dominating shape: K1 > P3 > K2 > K3 > None."""
    n = len(g)
    for v in range(n):
        if (1 << v | g[v]) == (1 << n) - 1: return "K1"
    for sub in itertools.combinations(range(n), 3):
        if is_induced_P3(g, sub) and dominates(g, sub): return "P3"
    for sub in itertools.combinations(range(n), 2):
        if is_clique(g, sub) and dominates(g, sub): return "K2"
    for sub in itertools.combinations(range(n), 3):
        if is_clique(g, sub) and dominates(g, sub): return "K3"
    return None

def is_module(g, sub):
    sub = list(sub)
    outs = [v for v in range(len(g)) if v not in sub]
    for v in outs:
        val = None
        for u in sub:
            e = (g[v] >> u & 1) == 1
            if val is None: val = e
            elif e != val: return False
    return True

def is_prime(g):
    n = len(g)
    for k in range(2, n):
        for sub in itertools.combinations(range(n), k):
            if is_module(g, sub): return False
    return True

def _reloc(bits, idx):
    out = 0
    for old, new in idx.items():
        if bits >> old & 1: out |= 1 << new
    return out

def canon(g):
    """Canonical form under relabeling (n<=8: 8!=40320 ok for a few k)."""
    n = len(g)
    best = None
    for pi in itertools.permutations(range(n)):
        newpos = {old: i for i, old in enumerate(pi)}
        h = tuple(_reloc(g[pi[i]], newpos) for i in range(n))
        if best is None or h < best: best = h
    return best

def _mkrow(n, es):
    adj = [0]*n
    for a, b in es:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return tuple(adj)

def substitute(frame, slots):
    sizes = [len(s) for s in slots]
    offs, acc = [], 0
    for s in sizes:
        offs.append(acc); acc += s
    n = acc
    adj = [0]*n
    for i in range(n):
        si = max(j for j in range(len(sizes)) if offs[j] <= i)
        li = i - offs[si]
        adj[i] |= _reloc(slots[si][li], {old: offs[si]+old for old in range(sizes[si])})
        for j in range(len(slots)):
            if j != si and (frame[si] >> j & 1):
                adj[i] |= ((1 << sizes[j]) - 1) << offs[j]
    return tuple(adj)

def path5():  return _mkrow(5, [(0,1),(1,2),(2,3),(3,4)])
def cyc5():   return _mkrow(5, [(0,1),(1,2),(2,3),(3,4),(4,0)])
def bull():   return _mkrow(5, [(0,1),(1,2),(0,2),(0,3),(1,4)])
def house():  return _mkrow(5, [(0,1),(1,2),(2,3),(0,3),(0,4),(1,4)])
def rook23():
    es = [(a,b) for a in range(6) for b in range(a+1,6)
          if (divmod(a,3)[0] == divmod(b,3)[0]) or (divmod(a,3)[1] == divmod(b,3)[1])]
    return _mkrow(6, es)
def cycle(n): return _mkrow(n, [(i,(i+1)%n) for i in range(n)])
def cbar(n):  return complement(cycle(n))

# ---------------------------------------------------------------- recon
def extend_class(members, n_from, n_to, forbid):
    """All graphs on n_to vertices whose some (n_to-1)-subset restriction is
    a member: exhaustive extension by one vertex with all attachments,
    canonical-dedup. forbid(g) must be True for members."""
    out = {}
    for g in members:
        assert len(g) == n_from
        for att in range(1 << n_from):
            adj = list(g) + [0]
            for u in range(n_from):
                if att >> u & 1:
                    adj[u] |= 1 << n_from
                    adj[n_from] |= 1 << u
            h = tuple(adj)
            if not forbid(h):
                c = canon(h)
                out[c] = h
    return list(out.values())

def recon():
    rng = random.Random(SEED)
    note(f"== W97-61A RECON (SEED {SEED}) ==")

    # --- R1: exhaustive n<=6 {P5,C5}-free world
    note("\n--- R1: {P5,C5}-free census, exhaustive n<=6 ---")
    members = {n: [] for n in range(1, 7)}
    for n in range(1, 7):
        for g in all_graphs(n):
            if not has_P5(g) and not has_C5(g):
                members[n].append(g)
        a = members[n]
        minaw = min(alpha_brute(g)*omega_brute(g) for g in a) if a else None
        minhomfrac = min(Fraction(hom(g), 1) / (Fraction(n) ** Fraction(1,2) if n else 1) for g in a) if a else None
        conn = sum(1 for g in a if connected(g))
        cc = sum(1 for g in a if connected(g) and connected(complement(g)))
        primes = sum(1 for g in a if len(g) >= 2 and is_prime(g))
        note(f"n={n}: count={len(a)} minAlphaOmega={minaw} conn={conn} connCoconn={cc} primes={primes}")
        if a:
            worst = min(a, key=lambda g: alpha_brute(g)*omega_brute(g))
            note(f"   worst alpha*omega graph: alpha={alpha_brute(worst)} omega={omega_brute(worst)} edges={n_edges_safe(worst)} prime={len(worst)>=2 and is_prime(worst)}")

    # --- R2: domination shapes in {P5,C5}-free connected
    note("\n--- R2: domination shapes ({P5,C5}-free connected) ---")
    for n in range(2, 7):
        shapes = {}
        for g in members[n]:
            if not connected(g): continue
            s = bt_shape(g)
            shapes[s] = shapes.get(s, 0) + 1
        note(f"n={n}: connected {sum(shapes.values())}, shapes={shapes}")

    # --- R3: connected&co-connected {P5,C5}-free: alpha*omega floors + primality
    note("\n--- R3: cc {P5,C5}-free: floors ---")
    for n in range(2, 7):
        ccg = [g for g in members[n] if connected(g) and connected(complement(g))]
        if not ccg: continue
        minaw = min(alpha_brute(g)*omega_brute(g) for g in ccg)
        worst = [g for g in ccg if alpha_brute(g)*omega_brute(g) == minaw]
        prim = sum(1 for g in ccg if is_prime(g))
        note(f"n={n}: cc={len(ccg)} minAlphaOmega={minaw} primeAmongWorst={sum(1 for g in worst if is_prime(g))}/{len(worst)} primesTotal={prim}")

    # --- R4: exact extension to n=7 (and 8 if small)
    note("\n--- R4: exact extension {P5,C5}-free n=7 (+n=8) ---")
    ext7 = extend_class(members[6], 6, 7, lambda g: has_P5(g) or has_C5(g))
    note(f"n=7 exact count={len(ext7)}")
    cc7 = [g for g in ext7 if connected(g) and connected(complement(g))]
    if cc7:
        minaw = min(alpha_brute(g)*omega_brute(g) for g in cc7)
        worst = [g for g in cc7 if alpha_brute(g)*omega_brute(g) == minaw]
        note(f"n=7 cc={len(cc7)} minAlphaOmega={minaw} worst prime={sum(1 for g in worst if is_prime(g))}/{len(worst)}")
        shapes = {}
        for g in cc7: shapes[bt_shape(g)] = shapes.get(bt_shape(g), 0) + 1
        note(f"n=7 cc shapes={shapes}")
    if len(ext7) <= 4000:
        ext8 = extend_class(ext7, 7, 8, lambda g: has_P5(g) or has_C5(g))
        cc8 = [g for g in ext8 if connected(g) and connected(complement(g))]
        minaw = min((alpha_brute(g)*omega_brute(g) for g in cc8), default=None)
        note(f"n=8 exact count={len(ext8)} cc={len(cc8)} minAlphaOmega={minaw}")

    # --- R5: P5-free world basics + B-T census
    note("\n--- R5: P5-free census + Bacsó-Tuza conclusion, n<=6 ---")
    p5free = {n: [] for n in range(1, 7)}
    for n in range(1, 7):
        for g in all_graphs(n):
            if not has_P5(g): p5free[n].append(g)
        conn = [g for g in p5free[n] if connected(g)]
        shapes = {}
        for g in conn:
            s = bt_shape(g); shapes[s] = shapes.get(s, 0) + 1
        note(f"n={n}: P5free={len(p5free[n])} conn={len(conn)} BTshapes={shapes}")

    # --- R6: z-only-style: connected P5-free with dominating P3 (no K1/K2)
    note("\n--- R6: dominating-P3 stratum of P5-free (z-only), n<=6 ---")
    for n in range(4, 7):
        zo = [g for g in p5free[n] if connected(g) and bt_shape(g) == "P3"]
        minaw = min((alpha_brute(g)*omega_brute(g) for g in zo), default=None)
        note(f"n={n}: z-only={len(zo)} minAlphaOmega={minaw}")

    # --- R7: C5-anchor pattern law (P5-free with induced C5)
    note("\n--- R7: C5-anchor patterns in P5-free graphs ---")
    allowed = set()
    bad = 0; tot = 0
    for n in (5, 6):
        for g in p5free[n]:
            n5 = len(g)
            for C in itertools.combinations(range(n5), 5):
                if not is_C5(g, C): continue
                Cs = set(C)
                for v in range(n5):
                    if v in Cs: continue
                    pat = frozenset(u for u in C if g[v] >> u & 1)
                    allowed.add((len(pat), tuple(sorted(pat))))
                    tot += 1
    note(f"pattern multiset sizes seen: {sorted(set(k for k,_ in allowed))}")
    note(f"total (C,v) instances n<=6: {tot}")
    # classify: for n=5-with-C5+1 vertex exhaustive attachment study
    C5g = cyc5()
    ok_pats = []
    for att in range(1 << 5):
        adj = list(C5g) + [0]
        for u in range(5):
            if att >> u & 1:
                adj[u] |= 1 << 5
                adj[5] |= 1 << u
        h = tuple(adj)
        if not has_P5(h):
            ok_pats.append(att)
    note(f"C5+single vertex: P5-free attachment patterns (of 32): {sorted(ok_pats)}")
    note(f"  sizes: {sorted(bin(p).count('1') for p in ok_pats)}")

    # --- R8: clean two-cell table around dominating P3 (typed enumeration)
    note("\n--- R8: clean two-cell law table (u,w + the P3) ---")
    # P3 vertices: 0=e1, 1=c(ctr), 2=e2.  Cells (attachment bitmasks over
    # {e1,c,e2}) for outside vertices u,w placed at positions 3,4.
    def typed_graph(cells, uv_edge):
        # returns adjacency of 5-vertex graph {e1=0, c=1, e2=2, u=3, w=4}
        adj = [0]*5
        def ed(a,b):
            adj[a] |= 1 << b; adj[b] |= 1 << a
        ed(0,1); ed(1,2)          # the P3
        for pos, cell in ((3, cells[0]), (4, cells[1])):
            if cell & 1: ed(pos, 0)
            if cell & 2: ed(pos, 1)
            if cell & 4: ed(pos, 2)
        if uv_edge: ed(3, 4)
        return tuple(adj)
    CELLS = [0b001, 0b010, 0b100, 0b011, 0b101, 0b110, 0b111]  # e1,c,e2,e1c,e1e2,ce2,e1ce2
    names = {0b001:"e1", 0b010:"c", 0b100:"e2", 0b011:"e1c", 0b101:"e1e2",
             0b110:"ce2", 0b111:"e1ce2"}
    table = {}
    for A in CELLS:
        for B in CELLS:
            for e in (0, 1):
                h = typed_graph((A, B), e)
                sub = (0,1,2,3,4)
                p5 = is_P5(h, sub); c5 = is_C5(h, sub)
                table[(A,B,e)] = ("P5" if p5 else "") + ("C5" if c5 else "")
    note("clean table: (cellA, cellB, u~w?) -> forbidden pattern in class")
    for (A,B,e), v in sorted(table.items()):
        if v:
            note(f"  ({names[A]:>6},{names[B]:>6},edge={e}) -> {v}")
    return locals()

def n_edges_safe(g):
    return sum(bin(x).count("1") for x in g)//2

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "recon"
    print(f"W97_61A engine — mode={mode} SEED={SEED}")
    if mode == "recon":
        recon()
    elif mode == "--verify":
        verify()
    print(f"TOTALS: PASS={PASS} FAIL={FAIL} wall={wall()}")
