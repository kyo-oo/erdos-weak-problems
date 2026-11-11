#!/usr/bin/env python3
"""battery396.py — the independent dual-method battery for Kernel 31 (#396).
Method 1 (direct): math.comb big-int modulo.
Method 2 (valuation): Legendre-sum Kummer valuations v_p(C(2n,n)) = v_p((2n)!) - 2 v_p(n!).
GREEN requires: witness both methods, exclusion replay empty, frontier k=0/1,
chunk-boundary mirror of the Lean data module."""
from math import comb

def binomP(n, k):
    r = 1
    for i in range(k):
        r *= (n - i)
    return r

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

def factorize(x):
    fa = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            fa[d] = fa.get(d, 0) + 1; x //= d
        d += 1
    if x > 1:
        fa[x] = fa.get(x, 0) + 1
    return fa

ok = True
def check(name, cond):
    global ok
    print(("PASS" if cond else "FAIL"), name)
    ok &= cond

# --- 1. The k=2 witness n=2480, dual method ---
n = 2480
P = binomP(n, 3)
C = comb(2 * n, n)
check("witness direct: C(4960,2480) % (2480*2479*2478) == 0", C % P == 0)
check("witness digits == 1492", len(str(C)) == 1492)
fa = {}
for x in (n, n - 1, n - 2):
    for p, e in factorize(x).items():
        fa[p] = fa.get(p, 0) + e
val_ok = all(vp_fact(2 * n, p) - 2 * vp_fact(n, p) >= e for p, e in fa.items())
check("witness valuation (Kummer): all margins >= 0", val_ok)
margins = {p: vp_fact(2*n, p) - 2*vp_fact(n, p) - e for p, e in sorted(fa.items())}
print("   margins:", margins)

# --- 2. The k=2 exclusion replay [1,2480) ---
bad = []
for m in range(1, 2480):
    Pm = binomP(m, 3)
    Cm = comb(2 * m, m)
    if Pm > 0 and Cm % Pm == 0:
        bad.append(m)
check("exclusion [1,2480): no k=2 solutions", bad == [])

# --- 3. The k=0 / k=1 frontier ---
check("k=0: n=1 works (1 | C(2,1)=2)", comb(2, 1) % binomP(1, 1) == 0)
check("k=1: n=1 fails (binomP=0)", binomP(1, 2) == 0)
check("k=1: n=2 works (2 | C(4,2)=6)", comb(4, 2) % binomP(2, 2) == 0)

# --- 4. Chunk-boundary mirror (the Lean data module edges) ---
edges = [1, 2, 480, 481, 960, 961, 1440, 1441, 1920, 1921, 2400, 2401, 2479]
mir = all(not (binomP(m, 3) > 0 and comb(2*m, m) % binomP(m, 3) == 0) for m in edges)
check("chunk boundaries all fail k=2", mir)

# --- 5. Binomial-def agreement (Lean binom = math.comb) ---
import random
random.seed(396)
agree = all(binomP(2*m, m) // (lambda k: binomP(k, k) if False else __import__('math').factorial(m))(m) == comb(2*m, m)
            for m in [1, 2, 3, 5, 10, 50, 200, 1000, 2479, 2480])
check("binomP/kfact def == math.comb (incl. n=2479, 2480)", agree)

print()
print("BATTERY396:", "GREEN" if ok else "RED")
raise SystemExit(0 if ok else 1)
