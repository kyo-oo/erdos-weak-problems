#!/usr/bin/env python3
"""W56-2 sanity hunt v2: subset-sum over prime-pair semiprime windows.
Fast feasibility check (total >= T), flush progress, node caps."""
import sys, time
sys.setrecursionlimit(200000)
from fractions import Fraction
from sympy import primerange

PRIMES = list(primerange(2, 60))

def build(P):
    L = 1
    for p in P: L *= p
    pairs = []
    n = len(P)
    for i in range(n):
        for j in range(i+1, n):
            d = P[i]*P[j]
            pairs.append((d, L//d))
    return L, pairs

def subset_sum(pairs, T, tmo=3.0, node_cap=400000):
    total = sum(v for _, v in pairs)
    if T > total or T < 0:
        return None
    flip = (T * 2 > total)
    if flip:
        T = total - T
    # descending order, include-first (greedy descent on big items)
    ps = sorted(pairs, key=lambda t: -t[1])
    vals = [v for _, v in ps]
    m = len(vals)
    suf = [0]*(m+1)
    for k in range(m-1, -1, -1):
        suf[k] = suf[k+1] + vals[k]
    res = [None]
    nodes = [0]
    t0 = time.time()
    def dfs(k, rem, acc):
        if res[0] is not None or nodes[0] > node_cap: return
        nodes[0] += 1
        if time.time() - t0 > tmo: return
        if rem == 0:
            res[0] = acc[:]; return
        if k >= m or rem > suf[k]: return
        v = vals[k]
        if v <= rem:
            acc.append(ps[k][0])
            dfs(k+1, rem-v, acc)
            if res[0] is not None: return
            acc.pop()
        dfs(k+1, rem, acc)
    dfs(0, T, [])
    if res[0] is None: return None
    if flip:
        chosen = set(res[0])
        return [d for d, _ in pairs if d not in chosen]
    return res[0]

def verify(dens, a, b):
    return (sum(Fraction(1, n) for n in dens) == Fraction(a, b)
            and len(set(dens)) == len(dens) and all(d >= 6 for d in dens))

targets = [
    (1, 1), (1, 2), (2, 3), (1, 3), (1, 5), (2, 5), (3, 5), (4, 5),
    (5, 6), (2, 7), (1, 7), (3, 11), (8, 21),
]
windows = [13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

print("=== hunt v2 ===", flush=True)
found = {}
for (a, b) in targets:
    got = None
    for w in windows:
        P = [p for p in PRIMES if p <= w]
        L, pairs = build(P)
        if L % b != 0:
            continue
        T = a * (L // b)
        total = sum(v for _, v in pairs)
        if T > total:
            print(f"  {a}/{b} w<={w}: total {total:.3f}L < T — skip", flush=True)
            continue
        r = subset_sum(pairs, T)
        if r is not None and verify(sorted(r), a, b):
            got = (w, sorted(r), L)
            break
        print(f"  {a}/{b} w<={w}: no subset (T/Tot={T/total:.3f})", flush=True)
    if got:
        w, dens, L = got
        found[(a, b)] = dens
        print(f"{a}/{b}: window<={w} L={L} terms={len(dens)} dens={dens}", flush=True)
    else:
        print(f"{a}/{b}: NOT FOUND", flush=True)

# Lean-statement helper
print("\n=== Lean statement forms ===", flush=True)
def prime_factors(n):
    f = []
    d = 2
    while d*d <= n:
        while n % d == 0:
            f.append(d); n //= d
        d += 1
    if n > 1: f.append(n)
    return f

for (a, b), dens in sorted(found.items()):
    allp = []
    for n in dens:
        for p in set(prime_factors(n)):
            if p not in allp: allp.append(p)
    L = 1
    for p in allp: L *= p
    lhs = " + ".join(f"{L}//{n}" for n in dens)
    rhs = f"{a}*({L}//{b})" if a > 1 else f"{L}//{b}"
    assert sum(Fraction(L, n) for n in dens) == Fraction(a * L, b)
    print(f"{a}/{b}: D={L}: {lhs} = {rhs}  # {len(dens)} terms", flush=True)
print("\nALL ASSERTS PASSED", flush=True)
