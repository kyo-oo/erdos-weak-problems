#!/usr/bin/env python3
"""
engine203_containment.py — THE CONTAINMENT MATRIX for the #203 chain search
(S043, the round-4 design pre-computed).

For palette primes q, q': Lambda_q ⊆ Lambda_{q'} iff every basis vector of
Lambda_q satisfies 2^k 3^l ≡ 1 mod q' — then any q-split child (a
Lambda_q-coset) is absorbed whole by q' (one coset). The matrix is genuine
geometry (NOT h-divisibility: (k,l)=(0,3) kills Lambda_13 ⊆ Lambda_5).

Output: containment203.txt — the edge list q -> q' (Lambda_q ⊆ Lambda_{q'})
+ per-prime out-degree (how many primes can absorb its children) sorted.
"""
import sys, math, os
HERE = os.path.dirname(os.path.abspath(__file__))

def kernel_lattice(u, v, h):
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
    return (a * m1, c * m1), (bp, dp)

def build_palette_dlogs(npr):
    rows = [tuple(map(int, l.split())) for l in open(os.path.join(HERE, "palette203.txt"))][:npr]
    out = []
    for (q, h, o2, o3) in rows:
        e = q - 1
        fac = {}
        x = h; d = 2
        while d * d <= x:
            while x % d == 0: fac[d] = fac.get(d, 0) + 1; x //= d
            d += 1 if d == 2 else 2
        if x > 1: fac[x] = fac.get(x, 0) + 1
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
    pal = build_palette_dlogs(npr)
    print(f"palette with dlogs: {len(pal)}")
    # Lambda_q bases
    lams = {}
    for (q, h, U, V) in pal:
        lams[q] = kernel_lattice(U, V, h)
    # containment: Lambda_q ⊆ Lambda_{q'}: both basis vectors of Lambda_q
    # satisfy 2^k 3^l ≡ 1 mod q'
    edges = []
    outdeg = {q: 0 for (q, _, _, _) in pal}
    indeg = {q: 0 for (q, _, _, _) in pal}
    for (q, h, U, V) in pal:
        b1, b2 = lams[q]
        for (q2, h2, U2, V2) in pal:
            if q2 == q: continue
            ok = (pow(2, b1[0], q2) * pow(3, b1[1], q2)) % q2 == 1 and \
                 (pow(2, b2[0], q2) * pow(3, b2[1], q2)) % q2 == 1
            if ok:
                edges.append((q, q2))
                outdeg[q] += 1
                indeg[q2] += 1
    print(f"containment edges: {len(edges)}")
    top_out = sorted(pal, key=lambda p: -outdeg[p[0]])[:20]
    print("TOP out-degree (children of a q-split are absorbable by outdeg primes):")
    for (q, h, U, V) in top_out:
        print(f"  q={q} h={h} outdeg={outdeg[q]} indeg={indeg[q]}")
    with open(os.path.join(HERE, "containment203.txt"), "w") as f:
        for (q, q2) in edges:
            f.write(f"{q} {q2}\n")
        f.write("#\n")
        for (q, h, U, V) in pal:
            f.write(f"# deg {q} {h} {outdeg[q]} {indeg[q]}\n")
    print("wrote containment203.txt")

if __name__ == "__main__":
    main()
