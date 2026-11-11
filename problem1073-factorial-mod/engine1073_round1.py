#!/usr/bin/env python3
"""
ENGINE 1073 ROUND 1 — Erdos #1073 (Hardy-Subbarao): composite u such that
u | n!+1 for some n.  A(x) = count of such u < x.  Is A(x) <= x^{o(1)}?

STRUCTURE LAWS (proved engine-side, to be kernelized):
  L1 (THE GCD LAW): u | n!+1  ==>  gcd(u, n!) = 1  ==>  every prime p | u
      has p > n, i.e. n < P(u) (the least prime factor of u).
      PROOF: u | n!+1 and d = gcd(u, n!) > 1 would give d | 1.
  L2 (THE SATURATION LAW): once n >= P(u), n! is divisible by P(u)
      forever, so n! + 1 is NOT divisible by P(u), hence not by u.
      (Scan window: n in [1, P(u)) -- tiny.)
  L3 (THE PRIME-POWER/WILSON CONNECTION): for u = p^2, solutions n
      correspond to factorial residues -1 mod p^2 below p.
Census: all composite u < 2*10^5, witnesses, decade growth A(x),
factorization structure of the hit set.
"""
import sympy
from sympy import factorint

X = 200000

def least_prime_factor(u):
    return min(factorint(u).keys())

# sieve smallest prime factor
spf = list(range(X + 1))
for i in range(2, int(X**0.5) + 1):
    if spf[i] == i:
        for j in range(i*i, X + 1, i):
            if spf[j] == j:
                spf[j] = i

hits = []          # (u, n) witness pairs
for u in range(4, X):
    if spf[u] == u:
        continue   # prime: Wilson always gives (u-1)! = -1; we want COMPOSITES
    P = spf[u]
    res = 1
    n = 0
    while n + 1 < P:
        n += 1
        res = (res * n) % u
        if res == u - 1:
            hits.append((u, n))
            break
        # res can also become 0 only when n >= P, impossible in-window
    # loop ends: no hit

us = [u for u, n in hits]
print(f"CENSUS: composite u < {X} with u | n!+1: {len(us)}")
print("first 30:", us[:30])
print("matches A256519 prefix (25,121,169,437,...):", us[:4] == [25, 121, 169, 437])

# decade growth
print("\nDECADE GROWTH A(x):")
for x in [100, 1000, 10000, 100000, 200000]:
    c = sum(1 for u in us if u < x)
    import math
    print(f"  A({x:>7}) = {c:>5}   ratio A(x)/x = {c/x:.5f}  log2 A = {math.log2(c) if c else 0:.2f} vs log2 x = {math.log2(x):.2f}")

# structure: factorization shape of hits
from collections import Counter
shape = Counter()
for u, n in hits:
    f = factorint(u)
    if len(f) == 1:
        p, e = list(f.items())[0]
        shape[f"prime power p^{e}"] += 1
    elif all(e == 1 for e in f.values()):
        shape["squarefree"] += 1
    else:
        shape["mixed"] += 1
print("\nFACTORIZATION SHAPES:", dict(shape))

# the witness n vs P(u) relation + prime-power detail
pp = [(u, n, factorint(u)) for u, n in hits if len(factorint(u)) == 1][:20]
print("\nPRIME-POWER HITS (u, n, fact):")
for u, n, f in pp:
    print(f"  u={u:>7} n={n:>4} {f}")

# L1 verification: n < P(u) for all hits
bad = [(u, n) for u, n in hits if n >= spf[u]]
print("\nL1 (n < P(u)) violations:", len(bad))

# squares among hits (p^2 with the Wilson connection)
sq = [(u, n) for u, n in hits if int(u**0.5)**2 == u]
print("square hits (u,n):", sq[:15], "... total", len(sq))

# semiprime structure: u = p*q with p<q: relation between n and p,q
sem = [(u, n, sorted(factorint(u))) for u, n in hits if len(factorint(u)) == 2 and all(e == 1 for e in factorint(u).values())]
print("\nSEMIPRIME HITS (u, n, p*q) first 15:")
for u, n, ps in sem[:15]:
    print(f"  u={u:>7} n={n:>4} = {ps[0]}*{ps[1]}")
print("total semiprime hits:", len(sem))

# THE MINIMAL-WITNESS LAW: for each u, the engine found the SMALLEST n.
# Question: can a u have TWO witness n's in window?  (structure for the kernel)
multi = []
from collections import defaultdict
byu = defaultdict(list)
for u, n in hits:
    byu[u].append(n)
# re-scan collecting ALL witnesses for hits
allw = []
for u in us[:500]:
    P = spf[u]
    res = 1
    ws = []
    for n in range(1, P):
        res = (res * n) % u
        if res == u - 1:
            ws.append(n)
    allw.append((u, ws))
m2 = [(u, ws) for u, ws in allw if len(ws) > 1]
print("\nMULTI-WITNESS u (first 500 hits):", len(m2), m2[:10])
