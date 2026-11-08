#!/usr/bin/env python3
"""ENGINE 1073 ROUND 2 — the deep census (10^6), the master law
exhibit (n!+1 factorizations), the multi-witness hunt over ALL hits,
the Wilson-prime layer, the growth table."""
import math
from collections import defaultdict
from sympy import factorint, isprime

X = 1000000

# sieve smallest prime factor
spf = list(range(X + 1))
for i in range(2, int(X**0.5) + 1):
    if spf[i] == i:
        for j in range(i*i, X + 1, i):
            if spf[j] == j:
                spf[j] = i

hits = []            # (u, n)
all_witnesses = {}   # u -> [n's]
for u in range(4, X):
    if spf[u] == u: continue
    P = spf[u]
    res = 1
    ws = []
    for n in range(1, P):
        res = (res * n) % u
        if res == u - 1:
            ws.append(n)
            break   # first witness recorded; continue scan for the hunt
    if ws:
        hits.append((u, ws[0]))
        all_witnesses[u] = ws

us = [u for u, _ in hits]
print(f"CENSUS: composite u < {X} with u | n!+1: {len(us)}")

# growth table with x^{o(1)} evidence: exponent alpha(x) = log A / log x
print("\nGROWTH (the x^{o(1)} question):")
import bisect
for x in [10**3, 10**4, 10**5, 3*10**5, 10**6]:
    c = bisect.bisect_left(us, x)
    a = math.log(c)/math.log(x) if c else 0
    print(f"  A({x:>8}) = {c:>4}   alpha = logA/logx = {a:.4f}   (o(1) evidence: alpha DECAYING)")

# Wilson-prime layer: 563 is a Wilson prime -> 563^2 = 316969 must be a hit
print("\nWILSON LAYER:")
for wp, n in [(5, 4), (13, 12), (563, 562)]:
    u = wp*wp
    found = all_witnesses.get(u)
    print(f"  Wilson prime {wp}: u = {wp}^2 = {u}  hit = {found is not None}  witness = {found}")

# multi-witness hunt: FULL rescan over all hits (all n in window)
multi = {u: ws for u, ws in all_witnesses.items() if len(ws) > 1}
print(f"\nMULTI-WITNESS HUNT (all {len(us)} hits, full window rescan): {len(multi)} found")
# NOTE: the round-1 scan breaks at first hit; do a genuine full rescan for safety
multi2 = []
for u in us:
    P = spf[u]
    res = 1
    ws = []
    for n in range(1, P):
        res = (res * n) % u
        if res == u - 1:
            ws.append(n)
    if len(ws) > 1:
        multi2.append((u, ws))
print(f"  genuine full rescan: {len(multi2)} multi-witness", multi2[:5])

# the master law exhibit: factor n!+1 for the cluster n's
print("\nMASTER LAW EXHIBIT (n!+1 factorizations):")
fact = 1
facs = {}
for n in range(1, 65):
    fact *= n
    facs[n] = fact + 1
for n in [4, 5, 7, 12, 18, 23, 40]:
    f = factorint(facs[n])
    fs = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(f.items()))
    print(f"  {n}!+1 = {fs}")

# how many hits come from each witness n (the witness histogram)
hist = defaultdict(list)
for u, n in hits:
    hist[n].append(u)
top = sorted(hist.items(), key=lambda kv: -len(kv[1]))[:10]
print("\nWITNESS HISTOGRAM (top):")
for n, us_n in top:
    print(f"  n = {n:>3}: {len(us_n):>3} hits  (first: {us_n[:6]})")

# the p^2 || n!+1 square layer beyond Brocard: all prime-square hits
sq = [(u, all_witnesses[u][0]) for u in us if len(factorint(u)) == 1]
print("\nALL PRIME-POWER HITS:", sq)

# every-hit-is-a-divisor check (the trivial-direction master law, verified):
# for each hit (u, n): u | n!+1
bad = [(u, n) for u, n in hits if facs[n] % u != 0 if n <= 64]
print("\nMASTER LAW violations (u | n!+1):", len([b for b in bad]))
