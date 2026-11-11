#!/usr/bin/env python3
"""#396 round 2 — the k=2 frontier certificate engine (FIXED: chunks from n=1;
n=1,2 auto-fail via binomP n 3 = 0; x % 0 = x != 0).
Statement (verbatim, formal-conjectures/ErdosProblems/396.lean):
  Is it true that for every k there exists n such that
  prod_{0<=i<=k}(n-i) | C(2n,n)?
Frontier: k=0: n=1 (1 | 2), k=1: n=2 (2 | 6), k=2: n=2480 (NEW).
This engine: (a) exclusion replay n in [1,2480); (b) witness dual-verify;
(c) chunk table for the Lean data module (480-element chunks)."""
from math import comb

def binomP(n, k):
    r = 1
    for i in range(k):
        r *= (n - i)
    return r

def kfact(k):
    r = 1
    for i in range(1, k+1):
        r *= i
    return r

def binom(n, k):
    return binomP(n, k) // kfact(k)

print("=== (a) EXCLUSION REPLAY: n in [1,2480), k=2 ===")
bad = []
for n in range(1, 2480):
    P = binomP(n, 3)          # n(n-1)(n-2); 0 for n <= 2
    C = binom(2*n, n)
    if C % P == 0 if P > 0 else False:
        bad.append(n)
print(f"n in [1,2480) with binomP n 3 | binom (2n) n: {bad}  (expect [])")

print()
print("=== (b) k=2 WITNESS n=2480 dual verification ===")
n = 2480
P = binomP(n, 3)
C = comb(2*n, n)
C2 = binom(2*n, n)
assert C == C2, "binomial def mismatch"
print(f"P = {P} = {n}*{n-1}*{n-2}")
print(f"C(4960,2480) % P = {C % P}  (expect 0)")
print(f"digits of C(4960,2480): {len(str(C))}")

def vp(m, p):
    e = 0
    while m % p == 0:
        m //= p; e += 1
    return e
def vp_fact(m, p):
    s, q = 0, p
    while q <= m:
        s += m // q; q *= p
    return s

fa = {}
for x in (n, n-1, n-2):
    y = x; d = 2
    while d*d <= y:
        while y % d == 0:
            fa[d] = fa.get(d, 0) + 1; y //= d
        d += 1
    if y > 1: fa[y] = fa.get(y, 0) + 1
print("factorization of P:", dict(sorted(fa.items())))
allok = True
for p, e in sorted(fa.items()):
    vC = vp_fact(2*n, p) - 2*vp_fact(n, p)
    print(f"  p={p}: v_P={e}, v_C(Kummer)={vC}, margin={vC-e}")
    allok &= (vC >= e)
print("valuation method agrees:", allok)

print()
print("=== (c) k=0/k=1 frontier checks ===")
print("k=0: n=1: binomP 1 1 =", binomP(1,1), "| binom 2 1 =", binom(2,1), "-> divides:", binom(2,1) % binomP(1,1) == 0)
print("k=1: n=1: binomP 1 2 =", binomP(1,2), "-> 0 divides 2:", binom(2,1) % binomP(1,2) == 0 if binomP(1,2)>0 else False, "(binomP=0, x%0=x!=0 -> excluded)")
print("k=1: n=2: binomP 2 2 =", binomP(2,2), "| binom 4 2 =", binom(4,2), "-> divides:", binom(4,2) % binomP(2,2) == 0)

print()
print("=== (d) k>=3 bounded sweep (n <= 6000, k <= 6) ===")
found = {}
for n in range(4, 6001):
    C = comb(2*n, n)
    Pr = 1
    for k in range(0, 7):
        if n - k < 1:
            break
        Pr *= (n - k)
        if Pr > 0 and C % Pr == 0:
            if k not in found:
                found[k] = (n, Pr)
        else:
            break
print("k -> first n (n <= 6000):", {k: found[k][0] for k in sorted(found) if k >= 3} or "none for k>=3")
