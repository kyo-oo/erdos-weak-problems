#!/usr/bin/env python3
"""BATTERY 1073 — dual-method verification of the round-1 census."""
import math

def factorint(n):
    """Pure-Python trial-division factorization (n <= 10^6: trivial)."""
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

X = 10**6
spf = list(range(X + 1))
for i in range(2, int(X**0.5) + 1):
    if spf[i] == i:
        for j in range(i*i, X + 1, i):
            if spf[j] == j: spf[j] = i

# METHOD 1: mod-cascade window scan (the engine)
hits1 = {}
for u in range(4, X):
    if spf[u] == u: continue
    res = 1
    for n in range(1, spf[u]):
        res = (res * n) % u
        if res == u - 1:
            hits1[u] = n
            break

# METHOD 2: direct big-int division u | n!+1 (independent)
fact = 1
facs = {0: 1}
for n in range(1, 1000):
    fact *= n
    facs[n] = fact + 1
ok = True
for u, n in hits1.items():
    if n >= 1000 or facs[n] % u != 0:
        print("DUAL FAIL", u, n); ok = False

# window law L1
for u, n in hits1.items():
    if n >= spf[u]:
        print("L1 FAIL", u, n); ok = False

# Wilson channel
for wp in [5, 13, 563]:
    if wp*wp not in hits1:
        print("WILSON FAIL", wp); ok = False
    elif hits1[wp*wp] != wp - 1:
        print("WILSON WITNESS FAIL", wp); ok = False

# Brocard channel
for u, n in [(25, 4), (121, 5), (5041, 7)]:
    if hits1.get(u) != n:
        print("BROCARD FAIL", u); ok = False

# prefix match A256519
prefix = [25, 121, 169, 437, 551, 667, 721, 1037, 1159, 1273, 1349, 1403, 1541, 1769, 1943, 2209, 2329, 2363, 2419]
us = sorted(hits1)
if us[:len(prefix)] != prefix:
    print("A256519 PREFIX FAIL"); ok = False

# uniqueness rescan (method 3)
multi = 0
for u in us:
    res = 1
    cnt = 0
    for n in range(1, spf[u]):
        res = (res * n) % u
        if res == u - 1: cnt += 1
    if cnt != 1:
        print("UNIQUENESS FAIL", u, cnt); multi += 1

# growth monotonicity + count
print(f"census size: {len(us)} (expect 131)")
print(f"multi-witness: {multi}")
print("A(10^3),A(10^4),A(10^5),A(10^6) =",
      sum(1 for u in us if u < 10**3), sum(1 for u in us if u < 10**4),
      sum(1 for u in us if u < 10**5), sum(1 for u in us if u < 10**6))
print("BATTERY1073:", "GREEN" if ok and multi == 0 and len(us) == 131 else "RED")
