#!/usr/bin/env python3
# DEEP SQUARE CENSUS — Gray code over subsets of [1..N], squares only (exact, fast)
from math import isqrt
import sys

def fact(n):
    r = 1
    for i in range(2, n+1): r *= n if False else r*i if False else 1
    return 1
# (placeholder replaced below)

def F_(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r

F = [F_(i) for i in range(0, 28)]

def vp(n, p):
    c = 0
    while n % p == 0: n //= p; c += 1
    return c

def s2(n): return bin(n).count('1')

def pair_law_v2(S):
    Lambda = lambda j: 2*j - s2(j)
    js = sorted(set(b//2 for b in S))
    jstar = js[0]
    V = 0
    for j in js:
        Uj = sum(F[b] for b in S if b//2 == j) >> Lambda(j)
        V += Uj << (Lambda(j) - Lambda(jstar))
    return Lambda(jstar) + vp(V, 2)

N = int(sys.argv[1])
squares = []
total = 0
inset = [False]*(N+2)
for k in range(1, 1 << N):
    t = (k & -k).bit_length() - 1
    elem = t + 1
    gray = k ^ (k >> 1)
    if (gray >> t) & 1:
        inset[elem] = True; total += F[elem]
    else:
        inset[elem] = False; total -= F[elem]
    if total > 1:
        r = isqrt(total)
        if r*r == total:
            S = [i for i in range(1, N+1) if inset[i]]
            lv = vp(total, 2)
            assert lv == pair_law_v2(S), ("LAW FAIL", S)
            assert lv % 2 == 0
            squares.append((S, r))
print(f"DEEP SQUARE CENSUS max(S) <= {N}: {len(squares)} squares — every one re-verified by the pair law (v2 exact + even)")
for S, r in squares:
    print(f"  S={S}  = {r}^2")
