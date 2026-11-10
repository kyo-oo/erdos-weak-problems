#!/usr/bin/env python3
"""
engine203_tree.py — THE COVERING-TREE SEARCH for Erdős #203 (S043):
find m, (m,6)=1, with 2^k 3^l m + 1 composite for ALL k,l >= 0.

Reduction (P203 PROOF.md, verified): the problem == cover Z^2 by ONE coset
of Lambda_q per prime q (Lambda_q = {(k,l): 2^k 3^l = 1 mod q}), cosets
chosen freely; CRT then gives m.

Palette: primes q >= 5 with h_q = lcm(ord_q(2), ord_q(3)) <= HMAX.
Stage 1 (this file): compute the palette + the density budget sum 1/h_q.
Stage 2: the tree search (regions, absorption, splits).

Usage: engine203_tree.py palette QMAX HMAX   -> writes palette203.txt
       engine203_tree.py tree PALETTE NPRIMES -> the DFS covering search
"""
import sys, math
from collections import deque

# ---------- number theory basics ----------
def factorint(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def multiplicative_order(a, q, fac_qm1):
    """ord of a mod q given factorization of q-1"""
    n = q - 1
    o = n
    for p, e in fac_qm1.items():
        while o % p == 0 and pow(a, o // p, q) == 1:
            o //= p
    return o

# ---------- stage 1: the palette ----------
def build_palette(qmax, hmax):
    rows = []
    budget = 0.0
    sieve = list(range(qmax + 1))
    for i in range(2, int(qmax**0.5) + 1):
        if sieve[i] == i:
            for j in range(i*i, qmax + 1, i):
                if sieve[j] == j: sieve[j] = i
    for q in range(5, qmax + 1):
        if sieve[q] != q: continue
        if q in (2, 3): continue
        f = factorint(q - 1)
        o2 = multiplicative_order(2, q, f)
        o3 = multiplicative_order(3, q, f)
        h = o3 * o2 // math.gcd(o2, o3)
        if h <= hmax:
            rows.append((q, h, o2, o3))
            budget += 1.0 / h
    return rows, budget

# ---------- stage 2: the tree search ----------
def hnf_basis(v1, v2):
    """Hermite-style reduced basis of the lattice spanned by v1, v2 (2D)."""
    # use integer row reduction: keep det sign
    a, b = v1; c, d = v2
    # ensure nonzero handling: reduce (a,b),(c,d)
    while True:
        if (a, b) == (0, 0):
            a, b, c, d = c, d, 0, 0
            break
        if (c, d) == (0, 0):
            break
        # reduce first vector by second (size reduction on x-coordinate)
        if abs(c) < abs(a) or (abs(c) == abs(a) and abs(d) < abs(b)):
            a, b, c, d = c, d, a, b
        if c != 0 and abs(c) >= 1:
            m = c // a if a != 0 else 0
            a, b, c, d = a, b, c - m * a, d - m * b
        else:
            break
    # now (c,d) should be (0,0) or tiny; final cleanup
    if (c, d) != (0, 0):
        # merge: the lattice is spanned; do a second pass
        pass
    return (a, b)

def lattice_index(b1, b2):
    """|det| of the basis (0 if degenerate)"""
    return abs(b1[0]*b2[1] - b1[1]*b2[0])

def kernel_lattice(u, v, h):
    """basis of {z in Z^2 : u*z1 + v*z2 == 0 mod h} as two 2-vectors"""
    g = math.gcd(math.gcd(u, v), h)
    if g > 1:
        u //= g; v //= g; h //= g
    # Smith-ish: find P in GL2(Z) with (u,v) P = (g1, 0), g1 = gcd(u,v)
    g1 = math.gcd(u, v)
    if g1 == 0:
        # u=v=0: everything
        return ((1,0),(0,1))
    # extended gcd: find (s,t) with u*s + v*t = g1
    # then P = [[s, -v/g1],[t, u/g1]] has (u,v)P = (g1, 0)
    old_r, r = u, v
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        qq = old_r // r
        old_r, r = r, old_r - qq * r
        old_s, s = s, old_s - qq * s
        old_t, t = t, old_t - qq * t
    # old_s*u + old_t*v = old_r = g1 (up to sign)
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    s, t = old_s, old_t
    # w-coords: w = (w1,w2); z = P w ; condition g1*w1 == 0 mod h
    gg = math.gcd(g1, h)
    m1 = h // gg   # w1 must be multiple of m1
    # z = (s*w1 - (v//g1)*w2, t*w1 + (u//g1)*w2)
    a = s; bp = -(v // g1)
    c = t; dp = (u // g1)
    # basis in z-coords: w = (m1, 0) and (0, 1)
    b1 = (a * m1, c * m1)
    b2 = (bp, dp)
    return b1, b2

def gen_of_subgroup(q, h, fac_h):
    """generator of the order-h subgroup of F_q^* (h | q-1)"""
    # try small bases as primitive-root candidates
    e = q - 1
    for x in (5, 6, 7, 10, 11, 12, 13, 14, 15, 17, 2, 3):
        if x % q == 0: continue
        # x primitive root?
        ok = True
        for p in fac_h:
            # need order q-1: check x^((q-1)/p) != 1 for all p | q-1
            pass
        # cheaper: g = x^((q-1)/h) must have order h
        g = pow(x, e // h, q)
        # verify order h
        o = h
        for p, ee in fac_h.items():
            while o % p == 0 and pow(g, o // p, q) == 1:
                o //= p
        if o == h and g != 1:
            return g
    return None

def dlog_in_subgroup(g, target, h, q):
    """U with g^U = target mod q, 0 <= U < h (target must be in <g>)"""
    x = 1
    for i in range(h):
        if x == target: return i
        x = x * g % q
    return None

def build_full_palette_with_dlogs(rows):
    """add U = dlog(2), V = dlog(3) w.r.t. a generator of S_h for each row"""
    out = []
    for (q, h, o2, o3) in rows:
        fac_h = factorint(h)
        g = gen_of_subgroup(q, h, fac_h)
        if g is None: continue
        U = dlog_in_subgroup(g, 2 % q, h, q)
        V = dlog_in_subgroup(g, 3 % q, h, q)
        if U is None or V is None: continue
        out.append((q, h, U, V))
    return out

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "palette"
    if mode == "palette":
        qmax = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
        hmax = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
        rows, budget = build_palette(qmax, hmax)
        rows.sort(key=lambda r: (r[1], r[0]))
        print(f"# palette: {len(rows)} primes q<= {qmax} with h=lcm(ord2,ord3) <= {hmax}")
        print(f"# density budget sum(1/h) = {budget:.4f}")
        for (q, h, o2, o3) in rows[:60]:
            print(f"q={q} h={h} ord2={o2} ord3={o3}")
        with open("palette203.txt", "w") as f:
            for (q, h, o2, o3) in rows:
                f.write(f"{q} {h} {o2} {o3}\n")
        print("wrote palette203.txt")
    elif mode == "tree":
        npr = int(sys.argv[2]) if len(sys.argv) > 2 else 200
        rows = [tuple(map(int, l.split())) for l in open("palette203.txt")]
        rows = [r for r in rows if r[0] not in (2,3)]
        # dlogs
        print(f"computing dlogs for top {npr} palette primes...")
        full = build_full_palette_with_dlogs(rows[:npr])
        print(f"got {len(full)} palette entries with (q,h,U,V)")
        budget = sum(1.0 / r[1] for r in full)
        print(f"budget of used palette: {budget:.4f}")
        # THE TREE (to be driven by the search loop; this round: report the
        # absorption structure of the FULL lattice Z^2 under each prime)
        # region = (b1, b2, c) with basis (b1,b2), offset c
        # prime q splits Z^2: m_q = |phi_q(Z^2)| = h / gcd(h, U, V)
        stats = []
        for (q, h, U, V) in full:
            m = h // math.gcd(h, U, V)
            stats.append((m, h, q))
        stats.sort()
        absorbable = [s for s in stats if s[0] == 1]
        print(f"primes that ABSORB all of Z^2 (m=1): {len(absorbable)} (impossible for the start; m=1 needs U=V=0)")
        print("smallest split factors m (h, q):", stats[:25])
if __name__ == "__main__":
    main()
