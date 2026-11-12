#!/usr/bin/env python3
"""W56-2 FINAL unit hunt: complement subset-sum over <=47 window (105 pairs).
Target C = total - L; unit = all pairs MINUS the C-subset. Node-capped DFS."""
import sys, time
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
            pairs.append((P[i]*P[j], L//(P[i]*P[j])))
    return L, pairs

def hunt_complement(P, tmo, node_cap=3_000_000):
    L, pairs = build(P)
    total = sum(v for _, v in pairs)
    C = total - L
    if C < 0:
        return None, None, None
    res = [None]; nodes = [0]; t0 = time.time()
    # descending, include-first
    ps = sorted(pairs, key=lambda t: -t[1])
    vals = [v for _, v in ps]
    m = len(vals)
    suf = [0]*(m+1)
    for k in range(m-1, -1, -1): suf[k] = suf[k+1] + vals[k]
    def dfs(k, rem, acc):
        if res[0] is not None or nodes[0] > node_cap: return
        nodes[0] += 1
        if time.time()-t0 > tmo: return
        if rem == 0: res[0] = acc[:]; return
        if k >= m or rem > suf[k] or rem < 0: return
        v = vals[k]
        if v <= rem:
            acc.append(ps[k][0]); dfs(k+1, rem-v, acc)
            if res[0] is not None: return
            acc.pop()
        dfs(k+1, rem, acc)
    dfs(0, C, [])
    if res[0] is None:
        return None, L, pairs
    chosen = set(res[0])
    unit = [d for d, _ in pairs if d not in chosen]
    return sorted(unit), L, pairs

def verify(dens, a, b):
    return (sum(Fraction(1, n) for n in dens) == Fraction(a, b)
            and len(set(dens)) == len(dens))

t_overall = time.time()
for w, tmo in [(47, 12.0), (43, 6.0), (53, 6.0)]:
    P = [p for p in PRIMES if p <= w]
    unit, L, pairs = hunt_complement(P, tmo)
    if unit:
        print(f"UNIT over window<={w}: L={L} terms={len(unit)}", flush=True)
        print(f"dens: {unit}", flush=True)
        print(f"verify == 1: {verify(unit, 1, 1)}", flush=True)
        def prime_factors(n):
            f = []
            d = 2
            while d*d <= n:
                while n % d == 0: f.append(d); n //= d
                d += 1
            if n > 1: f.append(n)
            return f
        allp = []
        for n in unit:
            for p in set(prime_factors(n)):
                if p not in allp: allp.append(p)
        Lc = 1
        for p in allp: Lc *= p
        lhs = " + ".join(f"{Lc} / {n}" for n in unit)
        print(f"LEAN: {lhs} = {Lc}", flush=True)
        assert sum(Fraction(Lc, n) for n in unit) == Lc
        print("ASSERT OK", flush=True)
        break
    else:
        print(f"window<={w}: no complement subset", flush=True)
print(f"[total {time.time()-t_overall:.1f}s]", flush=True)
