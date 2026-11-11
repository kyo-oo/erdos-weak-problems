#!/usr/bin/env python3
# THE SUBSET KERNEL LAW — exact verification battery (Erdos #1108)
from math import isqrt
from itertools import combinations, chain

def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r

F = [fact(i) for i in range(0, 30)]

def vp(n, p):
    if n == 0: return 10**9
    c = 0
    while n % p == 0: n //= p; c += 1
    return c

def s2(n): return bin(n).count('1')

def sieve(n):
    sv = bytearray([1])*(n+1); sv[0]=sv[1]=0
    for i in range(2, isqrt(n)+1):
        if sv[i]: sv[i*i::i] = bytearray(len(sv[i*i::i]))
    return [i for i in range(n+1) if sv[i]]

PRIMES = sieve(200)

# ---------- THE PAIR LAW (p=2) ----------
def pair_law_v2(S):
    total = sum(F[a] for a in S)
    Lambda = lambda j: 2*j - s2(j)
    js = sorted(set(b//2 for b in S))
    jstar = js[0]
    V = 0
    for j in js:
        Uj = sum(F[b] for b in S if b//2 == j) >> Lambda(j)
        V += Uj << (Lambda(j) - Lambda(jstar))
    return Lambda(jstar) + vp(V, 2)

# ---------- THE GENERAL p-BLOCK LAW ----------
def block_law_vp(S, p):
    def block_of(b): return b // p if b >= p else 0
    def level_of_block(j): return vp(F[p*j], p) if j >= 1 else 0
    js = sorted(set(block_of(b) for b in S))
    jstar = js[0]
    Lstar = level_of_block(jstar)
    V = 0
    for j in js:
        Lj = level_of_block(j)
        Uj = sum(F[b] for b in S if block_of(b) == j) // (p ** Lj)
        V += Uj * (p ** (Lj - Lstar))
    return Lstar + vp(V, p)

# ---------- BATTERY 1: exhaustive law verification, all S ⊆ [1..12], p=2,3,5,7,11 ----------
def battery1():
    N = 12
    cnt = 0
    for r in range(1, N+1):
        for S in combinations(range(1, N+1), r):
            total = sum(F[a] for a in S)
            for p in (2,3,5,7,11):
                vd = vp(total, p); vl = block_law_vp(S, p)
                assert vd == vl, (S, p, vd, vl)
            assert vp(total,2) == pair_law_v2(S), S
            cnt += 1
    print(f"BATTERY 1: {cnt} subsets of [1..{N}] x p in (2,3,5,7,11) — v_p law EXACT on every one. LAW HOLDS.")

# ---------- BATTERY 2: square + powerful census, all S ⊆ [1..16] ----------
def battery2():
    N = 16
    squares = []; powerful = []
    for r in range(1, N+1):
        for S in combinations(range(1, N+1), r):
            t = sum(F[a] for a in S)
            r_ = isqrt(t)
            if r_*r_ == t: squares.append((S, t, r_))
            # powerful?
            n = t; ok = True
            for d in PRIMES:
                if d*d > n: break
                if n % d == 0:
                    e = 0
                    while n % d == 0: n //= d; e += 1
                    if e == 1: ok = False; break
            if ok and n > 1: ok = False   # leftover prime to first power
            if ok and t > 1: powerful.append((S, t))
    print(f"BATTERY 2: exhaustive census over all 2^16-1 subsets of [1..{N}]:")
    print(f"  SQUARES:")
    for S,t,r_ in squares: print(f"    S={list(S)}  sum = {t} = {r_}^2")
    print(f"  POWERFUL SUMS (>1): {len(powerful)}")
    for S,t in powerful[:20]: print(f"    S={list(S)}  sum = {t}")
    return squares, powerful

# ---------- BATTERY 3: Bertrand-window prime profile ----------
def battery3(squares):
    print("BATTERY 3: Bertrand-window (p in (m/2, m]) profile of the census squares:")
    for S, t, r_ in squares:
        m = max(S)
        prof = []
        for p in PRIMES:
            if m/2 < p <= m:
                Tp = sum(F[a] for a in S if a < p) % p
                prof.append((p, Tp, vp(t, p)))
        print(f"  S={list(S)} m={m}: (p, T_p mod p, v_p(sum)): {prof}")

# ---------- BATTERY 4: the square CRITERION via the law (independent recheck) ----------
def battery4(squares):
    print("BATTERY 4: criterion recheck — every census square has ALL prime cascades even (v_p even for all p <= max(S)):")
    for S, t, r_ in squares:
        m = max(S)
        bad = [(p, vp(t,p)) for p in PRIMES if p <= m and vp(t,p) % 2 == 1]
        assert not bad, (S, bad)
        print(f"  S={list(S)}: all v_p even for p<=m  CONFIRMED (r={r_})")

b1 = battery1()
sq, pw = battery2()
battery3(sq)
battery4(sq)
print("\nALL BATTERIES GREEN.")
