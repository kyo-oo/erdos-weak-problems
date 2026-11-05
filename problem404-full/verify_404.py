#!/usr/bin/env python3
"""ERDŐS #404 verification battery — exact integers only, deterministic.
Re-verifies every receipt claimed in problem404-full/ (theorems B, C, the
block identities, the (2,2) König chain) plus the (4,2) obstruction."""
import math, sys

def v2(n):
    if n == 0: return 1 << 30
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

F = [math.factorial(i) for i in range(130)]
checks = 0
def ck(name, cond):
    global checks
    checks += 1
    if not cond:
        print(f"FAIL: {name}"); sys.exit(1)

def sf(a, B): return F[a] + sum(F[i] for i in B)

# ---- Theorem C: f(4,2) = 6 ----
ck("C witness value", sf(4, [5, 7]) == 5184)
ck("C witness v2", v2(sf(4, [5, 7])) == 6)
ck("C 5184 = 2^6 * 81", 5184 == 64 * 81)
# obstruction: all 8 low subsets of {P_5,P_6,P_7} = {5,30,210} miss 0 mod 16
lows = [5, 30, 210]
for mask in range(8):
    s = 1 + sum(lows[j] for j in range(3) if mask >> j & 1)
    ck(f"C obstruction mask={mask}", s % 16 != 0)
# high terms vanish mod 16
for i in range(8, 30):
    P = F[i] // F[4]
    ck(f"C high P_{i} mod 16", P % 16 == 0)

# ---- Theorem B: odd a ----
for a in [1, 3, 5, 7, 9, 11, 13, 15]:
    base = v2(F[a])
    for B in [[], [a+1], [a+1, a+2], [a+1, a+3, a+5], [a+2, a+4, a+6, a+8]]:
        ck(f"B a={a} B={B}", v2(sf(a, B)) == base)

# ---- Block identities ----
for u in range(12):
    ck(f"pair u={u}", F[u] + F[u+1] == F[u] * (u + 2))
    ck(f"triple u={u}", F[u] + F[u+1] + F[u+2] == F[u] * (u+2)**2)
    ck(f"quad u={u}", F[u] + F[u+1] + F[u+2] + F[u+3] == F[u] * (u+2) * (u*u + 5*u + 5))

# ---- The (2,2) König chain (Conjecture D evidence) ----
chain = [
    ([3], 3), ([3, 5], 7), ([3, 5, 8], 9), ([3, 5, 6, 7, 8, 9], 9),
    ([3, 5, 6, 7, 11, 13, 14], 13),
    ([3, 5, 6, 7, 11, 12, 15, 16, 19], 18),
    ([3, 5, 6, 7, 11, 12, 15, 17, 19, 21], 23),
]
for B, claimed in chain:
    v = v2(sf(2, B))
    ck(f"chain {B[:4]}... v2 >= {claimed}", v >= claimed)
    ck(f"chain {B[:4]}... exact {v}", v == claimed)

# ---- The BL family (261 bridge cross-check) ----
for m in range(1, 12):
    n = 2 ** (m + 1) - m - 2
    lhs = sum((n + j) * 2 ** (m - j) for j in range(1, m + 1))
    ck(f"BL family m={m}", lhs == n * 2 ** m)

# ---- The 2-adic valuation split theorem spot-checks ----
def P(a, i): return F[i] // F[a]
for a in [2, 4, 6, 8]:
    for B in [[a+1], [a+1, a+2, a+3], [a+2, a+5, a+9]]:
        total = sf(a, B)
        split = v2(total) == v2(F[a]) + v2(1 + sum(P(a, i) for i in B))
        ck(f"split a={a} B={B}", split)

# ---- Theorem B GENERAL-p: the p | a+1 class, every prime p (Kill #15) ----
def vp(p, n):
    c = 0
    while n % p == 0: n //= p; c += 1
    return c

for p in [2, 3, 5, 7, 11, 13]:
    for m in range(1, 5):                  # a + 1 = m*p  (the full class)
        a = m * p - 1
        base = vp(p, F[a])
        for B in [[], [a+1], [a+1, a+2], [a+1, a+3, a+5],
                  [a+2, a+4, a+6, a+8], [a+1, a+2, a+3, a+7]]:
            ck(f"BG p={p} a={a} B={B}", vp(p, sf(a, B)) == base)
# the Lean receipts, one by one
ck("BG receipt (2,3)", vp(3, sf(2, [4, 6])) == vp(3, F[2]) == 0)
ck("BG receipt (5,2)", vp(2, sf(5, [6, 8])) == vp(2, F[5]) == 3)
ck("BG receipt (8,3)", vp(3, sf(8, [10, 11])) == vp(3, F[8]) == 2)
ck("BG receipt (10,11)", vp(11, sf(10, [11, 15])) == vp(11, F[10]) == 0)
ck("BG receipt (14,5)", vp(5, sf(14, [16, 21])) == vp(5, F[14]) == 2)
ck("BG receipt (1,2)", vp(2, sf(1, [2, 3])) == vp(2, F[1]) == 0)

print(f"VERIFY_404 BATTERY: ALL {checks} CHECKS PASSED")
