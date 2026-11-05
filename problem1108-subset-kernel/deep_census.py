#!/usr/bin/env python3
# DEEP CENSUS — Gray-code enumeration over subsets of [1..N], strong prefilter
from math import isqrt

def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r

F = [fact(i) for i in range(0, 26)]

def sieve(n):
    sv = bytearray([1])*(n+1); sv[0]=sv[1]=0
    for i in range(2, isqrt(n)+1):
        if sv[i]: sv[i*i::i] = bytearray(len(sv[i*i::i]))
    return [i for i in range(n+1) if sv[i]]

def vp(n, p):
    if n == 0: return 10**9
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

def is_powerful(t):
    n = t; d = 2
    while d*d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0: n //= d; e += 1
            if e == 1: return False
        d += 1
    return n == 1

def gray_census(N):
    P = sieve(N)   # primes <= N divide N!... sums can have prime factors > N though (e.g. 71)
    squares = []; powerful = []
    total = 0
    inset = [False]*(N+2)
    for k in range(1, 1 << N):
        t = (k & -k).bit_length() - 1   # flipped bit = v2(k)
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
                squares.append((S, total, r))
                lv = vp(total,2)
                assert lv == pair_law_v2(S), ("LAW FAIL", S)
                assert lv % 2 == 0, ("ODD v2 SQUARE?!", S)
                continue
            # powerful prefilter: for small primes p (2..23): v_p in {0} or >= 2
            ok = True
            x = total
            for p in (2,3,5,7,11,13,17,19,23):
                if x % p == 0:
                    if x % (p*p) != 0: ok = False; break
            if ok and is_powerful(total):
                S = [i for i in range(1, N+1) if inset[i]]
                powerful.append((S, total))
    return squares, powerful

import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 21
sq, pw = gray_census(N)
print(f"DEEP CENSUS max(S) <= {N}: {len(sq)} SQUARES, {len(pw)} non-square POWERFUL sums")
for S,t,r in sq: print(f"  SQ  S={S}  = {r}^2   [pair-law v2 = {vp(t,2)}, even OK]")
for S,t in pw: print(f"  PW  S={S}  = {t}")
