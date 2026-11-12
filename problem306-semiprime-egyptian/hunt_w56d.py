#!/usr/bin/env python3
"""W56-2 hunt v4: THE UNIT via staged disjoint subset-sums over <=23 window.
1 = 1/2(REP12, fixed) + 1/3(S3) + 1/6(S6) with pairwise-distinct denominators.
Fallbacks: odd-window 1/2; 4/5 via 1/2+3/10; minimal-rep extraction."""
import sys, time
from fractions import Fraction
from sympy import primerange
from math import gcd

PRIMES = list(primerange(2, 70))
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

def subset_sum(dens, L, T, tmo=5.0, excl=()):
    items = [(d, L//d) for d in dens if d not in excl]
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

W23 = [p for p in PRIMES if p <= 23]
L23, P23 = build(W23)
avail = [d for d in P23 if d not in REP12]
print(f"<=23 window: L={L23}, pairs={len(P23)}, available (excl REP12)={len(avail)}", flush=True)
print(f"available sum = {sum(Fraction(1,d) for d in avail)} (need 1/3+1/6=1/2)", flush=True)

# STAGE 1: 1/3 then 1/6
unit = None
s3 = subset_sum(avail, L23, L23//3, tmo=6.0)
if s3:
    print(f"S3 (1/3) found: {sorted(s3)}", flush=True)
    rest = [d for d in avail if d not in s3]
    print(f"remaining sum: {sum(Fraction(1,d) for d in rest)} (need 1/6)", flush=True)
    s6 = subset_sum(rest, L23, L23//6, tmo=6.0)
    if s6:
        print(f"S6 (1/6) found: {sorted(s6)}", flush=True)
        unit = sorted(REP12 + sorted(s3) + sorted(s6))
        print(f"UNIT assembled: {len(unit)} terms", flush=True)
        print(f"UNIT verify == 1: {verify(unit, 1, 1)}", flush=True)
    else:
        print("S6 not found; try 1/6 first, then 1/3", flush=True)
else:
    print("S3 not found over <=23", flush=True)

if unit is None:
    # STAGE 1': 1/6 first then 1/3
    s6 = subset_sum(avail, L23, L23//6, tmo=6.0)
    if s6:
        rest = [d for d in avail if d not in s6]
        s3 = subset_sum(rest, L23, L23//3, tmo=6.0)
        if s3:
            unit = sorted(REP12 + sorted(s3) + sorted(s6))
            print(f"UNIT (1/6-first): {unit}", flush=True)
            print(f"verify: {verify(unit, 1, 1)}", flush=True)

if unit is None:
    # FALLBACK: bigger windows
    for w in [29, 31, 37]:
        P = [p for p in PRIMES if p <= w]
        L, pairs = build(P)
        av = [d for d in pairs if d not in REP12]
        s3 = subset_sum(av, L, L//3, tmo=4.0)
        if s3:
            rest = [d for d in av if d not in s3]
            s6 = subset_sum(rest, L, L//6, tmo=4.0)
            if s6:
                unit = sorted(REP12 + sorted(s3) + sorted(s6))
                print(f"UNIT over <={w}: {unit}", flush=True)
                print(f"verify: {verify(unit, 1, 1)}", flush=True)
                break

# 4/5 = 1/2 + 3/10
print("\n=== 4/5 = REP12 + 3/10 hunt ===", flush=True)
for w in [23, 29, 31]:
    P = [p for p in PRIMES if p <= w]
    L, pairs = build(P)
    av = [d for d in pairs if d not in REP12]
    if L % 10: continue
    s310 = subset_sum(av, L, 3*(L//10), tmo=5.0)
    if s310:
        rep45 = sorted(REP12 + sorted(s310))
        print(f"4/5 over <={w}: {rep45}", flush=True)
        print(f"verify: {verify(rep45, 4, 5)}", flush=True)
        break
    else:
        print(f"3/10 not found over <={w}", flush=True)

# direct 4/5 attempts on mid windows
for w in [23, 29, 31, 37, 41]:
    P = [p for p in PRIMES if p <= w]
    L, pairs = build(P)
    if L % 5: continue
    r = subset_sum(pairs, L, 4*(L//5), tmo=4.0)
    if r and verify(sorted(r), 4, 5):
        print(f"4/5 direct over <={w}: {sorted(r)}", flush=True)
        break

# 3/10 and 7/10 minimal over <=17 window exhaustive (2^21 too big) -> DFS
print("\n=== other targets over <= 17 ===", flush=True)
W17 = [p for p in PRIMES if p <= 17]
L17, P17 = build(W17)
for (a, b) in [(3,10),(7,10),(1,2),(2,5),(3,5),(5,6),(1,9),(1,30),(1,15),(1,14),(3,7),(4,7)]:
    if L17 % b: continue
    r = subset_sum(P17, L17, a*(L17//b), tmo=4.0)
    if r:
        print(f"{a}/{b} over <=17: {sorted(r)}", flush=True)
    else:
        print(f"{a}/{b}: no subset over <=17", flush=True)

print("\n=== Lean emit ===", flush=True)
def emit(a, b, dens, name):
    L = lcm_of(dens)
    assert sum(Fraction(L, n) for n in dens) == Fraction(a*L, b), (name, a, b)
    lhs = " + ".join(f"{L} / {n}" for n in dens)
    rhs = f"{a} * ({L} / {b})" if a > 1 else f"{L} / {b}"
    print(f"{name} [{a}/{b}, D={L}, {len(dens)} terms]:\n  {lhs} = {rhs}", flush=True)

if unit:
    emit(1, 1, unit, "UNIT")
emit(1, 2, REP12, "HALF")
emit(2, 5, [6,15,21,26,35,39,65,91], "2/5")
emit(3, 14, [6,21], "3/14")
emit(2, 21, [15,35], "2/21")
emit(3, 10, [10,21,22,26,33,55,77,143], "3/10")
print("DONE", flush=True)
