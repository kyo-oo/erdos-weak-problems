#!/usr/bin/env python3
"""W56-2 hunt v3: compose the UNIT from certified pieces.
Key idea: 1 = 5/6 + 1/6 over the <=23 window: the 5/6-rep leaves ~8 unused
pairs; enumerate ALL 2^9 subsets for an exact 1/6. Fallbacks: odd-window 1/2,
direct DFS. Also: exhaustive small-window minimal reps (2^15/2^21 scans)."""
import sys, time
from fractions import Fraction
from sympy import primerange
from itertools import combinations

PRIMES = list(primerange(2, 60))
REP56 = [6,10,14,15,21,22,33,34,35,38,39,46,51,55,57,65,69,77,85,91,95,115,119,133,143,221,299,391]
REP12 = [6,10,15,21,26,35,39,65,91]

def prime_factors(n):
    f = []
    d = 2
    while d*d <= n:
        while n % d == 0:
            f.append(d); n //= d
        d += 1
    if n > 1: f.append(n)
    return f

def lcm_of(dens):
    allp = []
    for n in dens:
        for p in set(prime_factors(n)):
            if p not in allp: allp.append(p)
    L = 1
    for p in allp: L *= p
    return L

def verify(dens, a, b):
    return (sum(Fraction(1, n) for n in dens) == Fraction(a, b)
            and len(set(dens)) == len(dens))

def build(P):
    L = 1
    for p in P: L *= p
    pairs = []
    n = len(P)
    for i in range(n):
        for j in range(i+1, n):
            pairs.append(P[i]*P[j])
    return L, sorted(pairs)

print("=== TASK 1: 5/6 + 1/6 unit composition over window <= 23 ===", flush=True)
W23 = [p for p in PRIMES if p <= 23]
L23, PAIRS23 = build(W23)
unused = [d for d in PAIRS23 if d not in REP56]
print(f"window<=23 L={L23}, total pairs {len(PAIRS23)}, unused {len(unused)}: {unused}", flush=True)
print(f"unused reciprocal sum = {sum(Fraction(1,n) for n in unused)} (need >= 1/6={Fraction(1,6)})", flush=True)
# enumerate all subsets of unused (2^9)
hit16 = None
n_un = len(unused)
vals = [L23 // d for d in unused]
for mask in range(1 << n_un):
    s = 0
    m = mask
    idx = 0
    while m:
        if m & 1: s += vals[idx]
        m >>= 1
        idx += 1
    if s == L23 // 6:
        hit16 = [unused[i] for i in range(n_un) if (mask >> i) & 1]
        break
if hit16:
    unit_dens = sorted(REP56 + hit16)
    print(f"1/6 COMPLEMENT FOUND: {hit16}", flush=True)
    print(f"UNIT: 1 = sum over {len(unit_dens)} terms: {unit_dens}", flush=True)
    print(f"verify: {verify(unit_dens, 1, 1)}", flush=True)
else:
    print("no exact 1/6 among unused pairs; try other targets too", flush=True)
    # any target among unused?
    for (a,b) in [(1,6),(1,3),(2,5),(1,2)]:
        for mask in range(1 << n_un):
            s = 0; m = mask; idx = 0
            while m:
                if m & 1: s += vals[idx]
                m >>= 1; idx += 1
            if b * s == a * (L23 // b) * b // b and s * b == a * L23:
                print(f"  {a}/{b} found: {[unused[i] for i in range(n_un) if (mask>>i)&1]}", flush=True)
                break

print("\n=== TASK 2: exhaustive minimal reps over window <= 13 (2^15) ===", flush=True)
W13 = [p for p in PRIMES if p <= 13]
L13, P13 = build(W13)
v13 = [L13 // d for d in P13]
best = {}
for mask in range(1 << len(P13)):
    s = 0; m = mask; idx = 0; cnt = 0
    while m:
        if m & 1: s += v13[idx]; cnt += 1
        m >>= 1; idx += 1
    if s == 0: continue
    # s / L13 in lowest terms
    from math import gcd
    g = gcd(s, L13)
    key = (s // g, L13 // g)
    if key not in best or cnt < best[key][0]:
        best[key] = (cnt, [P13[i] for i in range(len(P13)) if (mask >> i) & 1])
print(f"window<=13: {len(best)} distinct rationals representable", flush=True)
for key in [(1,2),(2,3),(1,3),(2,5),(3,5),(1,5),(3,10),(1,10),(1,6),(5,6),(1,7),(2,7),(1,15),(7,10),(7,15),(11,15),(13,15),(1,30),(1,14),(3,14),(1,21),(2,21)]:
    if key in best:
        cnt, dens = best[key]
        print(f"  {key[0]}/{key[1]}: {cnt} terms: {dens}", flush=True)

print("\n=== TASK 3: 4/5 attempts ===", flush=True)
def subset_sum(items, T, tmo=4.0):
    ps = sorted(items, key=lambda t: -t[1])
    vals = [v for _, v in ps]
    m = len(vals)
    suf = [0]*(m+1)
    for k in range(m-1, -1, -1): suf[k] = suf[k+1] + vals[k]
    res = [None]; t0 = time.time()
    def dfs(k, rem, acc):
        if res[0] is not None: return
        if time.time()-t0 > tmo: return
        if rem == 0: res[0] = acc[:]; return
        if k >= m or rem > suf[k]: return
        v = vals[k]
        if v <= rem:
            acc.append(ps[k][0]); dfs(k+1, rem-v, acc)
            if res[0] is not None: return
            acc.pop()
        dfs(k+1, rem, acc)
    dfs(0, T, [])
    return res[0]

for w in [53, 59]:
    P = [p for p in PRIMES if p <= w]
    L, pairs = build(P)
    if L % 5: continue
    r = subset_sum([(d, L//d) for d in pairs], 4*(L//5))
    if r and verify(sorted(r), 4, 5):
        print(f"4/5 over window<={w}: {sorted(r)}", flush=True)
    else:
        print(f"4/5 window<={w}: no subset", flush=True)

print("\n=== TASK 4: emit Lean forms ===", flush=True)
def emit(a, b, dens, name):
    L = lcm_of(dens)
    assert sum(Fraction(L, n) for n in dens) == Fraction(a*L, b), (name,)
    lhs = " + ".join(f"{L} / {n}" for n in dens)
    rhs = f"{a} * ({L} / {b})" if a > 1 else f"{L} / {b}"
    print(f"{name} [{a}/{b}, D={L}, {len(dens)} terms]:\n  {lhs} = {rhs}", flush=True)
    return dens

if hit16:
    emit(1, 1, sorted(REP56 + hit16), "UNIT")
emit(1, 2, REP12, "HALF")
emit(1, 3, [6,10,15], "THIRD")
emit(1, 5, [10,14,35], "FIFTH")
emit(2, 5, [10,14,21,22,26,33,35,55,77,143], "2/5")
emit(1, 7, [15,21,35], "SEVENTH")
emit(2, 7, [6,14,21], "2/7")
print("DONE", flush=True)
