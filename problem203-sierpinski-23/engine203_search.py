#!/usr/bin/env python3
"""
engine203_search.py — THE COVERING-TREE DFS for Erdős #203 (S043, stage 3).

Region: (b1, b2, c) — lattice basis (b1,b2) of Λ, offset c; index D=|det|.
Prime (q,h,U,V): phi_q(k,l) = (U*k + V*l) % h; Lambda_q = ker phi_q.
On a region: s1=phi(b1), s2=phi(b2); m = h/gcd(h,s1,s2).
  m=1: ABSORB (region inside one Lambda_q-coset; W_q := phi(c)).
  m>1: SPLIT into m cosets of Λ' = Λ ∩ Λ_q; the child with phi = phi(c)
       covered (W_q = phi(c)), siblings join the frontier.
Each prime used at most once GLOBALLY (one W_q); an already-used prime may
absorb a later region iff the region's phi-value == W_q.
Budget prune: Σ_frontier 1/D ≤ Σ_unused 1/h + Σ_used (1/h − spent).
"""
import sys, math, time, os
from collections import deque
HERE = os.path.dirname(os.path.abspath(__file__))
def _palfile():
    return os.path.join(HERE, "palette203.txt")

sys.setrecursionlimit(100000)

def kernel_lattice(u, v, h):
    """basis of {z in Z^2 : u*z1 + v*z2 == 0 mod h}"""
    g0 = math.gcd(math.gcd(u, v), h)
    if g0 > 1:
        u //= g0; v //= g0; h //= g0
    g1 = math.gcd(u, v)
    if g1 == 0:
        return ((1, 0), (0, 1))
    old_r, r = u, v
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        qq = old_r // r
        old_r, r = r, old_r - qq * r
        old_s, s = s, old_s - qq * s
        old_t, t = t, old_t - qq * t
    if old_r < 0:
        old_s, old_t = -old_s, -old_t
    s, t = old_s, old_t
    gg = math.gcd(g1, h)
    m1 = h // gg
    a, bp = s, -(v // g1)
    c, dp = t, (u // g1)
    b1 = (a * m1, c * m1)
    b2 = (bp, dp)
    return b1, b2

def det2(b1, b2):
    return abs(b1[0]*b2[1] - b1[1]*b2[0])

def bfs_reps(s1, s2, h):
    """(α,β) reps of all elements of <s1,s2> <= Z/h; returns list + value map"""
    seen = {0: (0, 0)}
    dq = deque([0])
    while dq:
        s = dq.popleft()
        a, b = seen[s]
        for da, db in ((1,0),(-1,0),(0,1),(0,-1)):
            ns = (s + da*s1 + db*s2) % h
            if ns not in seen:
                seen[ns] = (a+da, b+db)
                dq.append(ns)
    return seen

class Node:
    __slots__ = ("b1","b2","c","D")
    def __init__(self, b1, b2, c):
        self.b1, self.b2, self.c = b1, b2, c
        self.D = det2(b1, b2)

def act_on_region(prime, node):
    """returns (m, s1, s2, sc)"""
    q, h, U, V = prime
    s1 = (U*node.b1[0] + V*node.b1[1]) % h
    s2 = (U*node.b2[0] + V*node.b2[1]) % h
    sc = (U*node.c[0] + V*node.c[1]) % h
    g = math.gcd(h, s1, s2)
    m = h // g
    return m, s1, s2, sc

def split_region(prime, node):
    """split node by prime: returns (covered_child, sibling_children, sc)
    Λ' = B·kernel_lattice(s1,s2,h)"""
    q, h, U, V = prime
    m, s1, s2, sc = act_on_region(prime, node)
    assert m > 1
    k1, k2 = kernel_lattice(s1, s2, h)
    B = ((node.b1, node.b2))
    def Bz(z):
        a1, a2 = z
        return (node.b1[0]*a1 + node.b2[0]*a2,
                node.b1[1]*a1 + node.b2[1]*a2)
    nb1 = Bz(k1); nb2 = Bz(k2)
    reps = bfs_reps(s1, s2, h)
    covered = Node(nb1, nb2, node.c)          # phi value sc (the W_q coset)
    sibs = []
    for s, (a, b) in reps.items():
        if s == 0: continue                   # s=0 IS the covered child
        off = (node.c[0] + a*node.b1[0] + b*node.b2[0],
               node.c[1] + a*node.b1[1] + b*node.b2[1])
        sibs.append(Node(nb1, nb2, off))
    assert len(sibs) == m - 1, f"m={m} sibs={len(sibs)}"
    return covered, sibs, sc

def load_palette(npr):
    rows = [tuple(map(int, l.split())) for l in open("palette203.txt")]
    return [(q, h, U, V) for (q, h, U, V) in rows[:npr]] if len(rows[0]) == 4 else None

def build_palette_dlogs(npr):
    """palette rows (q,h,o2,o3) -> (q,h,U,V) via generator of S_h"""
    import subprocess
    rows = [tuple(map(int, l.split())) for l in open(_palfile())][:npr]
    out = []
    for (q, h, o2, o3) in rows:
        # find generator of the order-h subgroup of F_q^*
        e = q - 1
        # h | q-1 guaranteed? h = lcm(o2,o3) divides q-1 yes
        fac = {}
        x = h
        d = 2
        while d*d <= x:
            while x % d == 0: fac[d] = fac.get(d,0)+1; x //= d
            d += 1 if d == 2 else 2
        if x > 1: fac[x] = fac.get(x,0)+1
        g = None
        for b in (5, 6, 7, 10, 11, 2, 3, 12, 13, 17):
            cand = pow(b, e // h, q)
            o = h
            for p in fac:
                while o % p == 0 and pow(cand, o // p, q) == 1:
                    o //= p
            if o == h and cand != 1:
                g = cand; break
        if g is None: continue
        # dlogs of 2, 3
        U = V = None
        cur = 1
        for i in range(h):
            if cur == 2 % q: U = i
            if cur == 3 % q: V = i
            if U is not None and V is not None: break
            cur = cur * g % q
        if U is None or V is None: continue
        out.append((q, h, U, V))
    return out

def main():
    npr = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    node_limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    print(f"building dlog palette (top {npr})...", flush=True)
    t0 = time.time()
    pal = build_palette_dlogs(npr)
    print(f"palette: {len(pal)} primes with dlogs ({time.time()-t0:.0f}s)", flush=True)
    # DFS state
    root = Node((1,0),(0,1),(0,0))
    frontier = [root]
    used = {}          # prime idx -> (W_q, spent)
    unused = set(range(len(pal)))
    nodes = 0
    best_density = 1.0
    t0 = time.time()
    log = []

    def frontier_density():
        return sum(1.0/n.D for n in frontier)

    def capacity():
        c = sum(1.0/pal[i][1] for i in unused)
        c += sum(1.0/pal[i][1] - spent for (i, (w, spent)) in used.items())
        return c

    import heapq
    # heuristic DFS (greedy with FREE RE-ABSORPTION by used primes)
    while frontier and nodes < node_limit:
        nodes += 1
        frontier.sort(key=lambda n: n.D)
        node = frontier.pop(0)
        # 1) FREE absorption by an already-used prime (coset match)
        done = False
        for i, (w, spent) in used.items():
            m, s1, s2, sc = act_on_region(pal[i], node)
            if m == 1 and sc == w:
                used[i] = (w, spent + 1.0/node.D)
                log.append(("free", pal[i][0], node.D))
                done = True
                break
        if done:
            if nodes % 2000 == 0:
                print(f"node {nodes}: frontier={len(frontier)} density={frontier_density():.5f} "
                      f"used={len(used)} ({time.time()-t0:.0f}s)", flush=True)
            continue
        # 2) unused primes: absorb if m=1, else split with min m
        absorb_i = None
        bestm = None
        for i in sorted(unused):
            m, s1, s2, sc = act_on_region(pal[i], node)
            if m == 1:
                absorb_i = (i, sc)
                break
            if bestm is None or m < bestm[0]:
                bestm = (m, i)
        if absorb_i is not None:
            i, sc = absorb_i
            used[i] = (sc, 1.0/node.D)
            unused.discard(i)
            log.append(("absorb", pal[i][0], node.D))
        elif bestm is not None and unused:
            i = bestm[1]
            covered, sibs, sc = split_region(pal[i], node)
            used[i] = (sc, 1.0/covered.D)
            unused.discard(i)
            frontier.extend(sibs)
            log.append(("split", pal[i][0], node.D, len(sibs)))
        else:
            print(f"STUCK at node {nodes}: no candidate (unused={len(unused)})")
            break
        if nodes % 2000 == 0:
            print(f"node {nodes}: frontier={len(frontier)} density={frontier_density():.5f} "
                  f"used={len(used)} capacity={capacity():.4f} ({time.time()-t0:.0f}s)", flush=True)
        if frontier and frontier_density() > capacity() + 1e-9:
            print(f"DEAD: density {frontier_density():.5f} > capacity {capacity():.5f} at node {nodes}")
            break
    fd = frontier_density() if frontier else 0.0
    print(f"FINAL: nodes={nodes} frontier={len(frontier)} density={fd:.6f} "
          f"used={len(used)} capacity={capacity():.4f}")
    if not frontier:
        print("COVERING FOUND — run with extraction enabled")
    # summary of the split structure
    from collections import Counter
    kinds = Counter(l[0] for l in log)
    print("actions:", dict(kinds))

if __name__ == "__main__":
    main()
