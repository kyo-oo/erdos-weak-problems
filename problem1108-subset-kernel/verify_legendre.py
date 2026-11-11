#!/usr/bin/env python3
# THE LEGENDRE PARITY LAW — exact verification battery (Erdos #1108, Kill #19)
#
# Independent Python check of the Lean 4 §7 theorems of SubsetKernelLaw.lean:
#   legendre_v2_fact      : v2 (fact n) + s2 n = n            (Legendre at p = 2)
#   legendre_v2_fact_sub  : v2 (fact n) = n - s2 n
#   legendre_lam_add      : Lam j + s2 j = 2*j                (the Λ-spine)
#   legendre_lam          : Lam j = 2*j - s2 j
#   v2_fact_even          : v2 (fact (2m)) = m + v2 (fact m)
#   explicit_cascade      : v2 (sumFacts S) = (2*j0 - s2 j0) + v2 (cascadeC S)
#   square_parity_s2      : sumFacts S = r*r  ->  s2 j0 % 2 = v2 (cascadeC S) % 2
#
# Methods: direct loop factorization (no Legendre, no digit sums) vs the
# binary digit sum formula bin(n).count('1'), mirroring verify_subset_kernel.py.
from math import isqrt
from itertools import combinations
import random

def fact(n):
    r = 1
    for i in range(2, n + 1): r *= i
    return r

F = [fact(i) for i in range(0, 301)]

def vp(n, p=2):
    if n == 0: return 10**9
    c = 0
    while n % p == 0: n //= p; c += 1
    return c

def s2(n): return bin(n).count('1')

# v2(n!) by DIRECT loop factorization of 2..n (independent of all formulas):
def v2_fact_direct(n):
    c = 0
    for i in range(2, n + 1):
        m = i
        while m % 2 == 0:
            m //= 2
            c += 1
    return c

# ---------- BATTERY 1: Legendre's formula, n in [0, 300] ----------
def battery1():
    cnt = 0
    for n in range(0, 301):
        vd = v2_fact_direct(n)
        assert vd == n - s2(n), (n, vd, n - s2(n))
        assert vd + s2(n) == n, n
        cnt += 1
    print(f"BATTERY 1: {cnt} factorials (n in [0,300]): v2(n!) by direct loop factorization == n - s2(n). LEGENDRE HOLDS.")

# ---------- BATTERY 2: the Λ-spine + the even-factorial law, j in [0, 150] ----------
def battery2():
    cnt = 0
    for j in range(0, 151):
        Lam_direct = vp(F[2 * j])            # v2((2j)!) by direct factorization
        assert Lam_direct == 2 * j - s2(j), (j, Lam_direct, 2 * j - s2(j))   # legendre_lam
        assert Lam_direct + s2(j) == 2 * j, (j,)                              # legendre_lam_add
        assert Lam_direct == j + vp(F[j]), (j,)                               # v2_fact_even
        cnt += 1
    print(f"BATTERY 2: {cnt} pair levels (j in [0,150]): v2((2j)!) == 2j - s2(j) == j + v2(j!). THE Λ-SPINE IS LEGENDRE.")

# ---------- BATTERY 3: THE EXPLICIT CASCADE, 500 random nonempty lists over [0,25] ----------
def cascade_terms(S):
    total = sum(F[a] for a in S)
    jstar = min(a // 2 for a in S)          # botPair S (mirror of botPairAux)
    LamJS = vp(F[2 * jstar])                # Lam (botPair S), direct factorization
    C = total >> LamJS                      # cascadeC S = total / 2^Lam(j0)
    return total, jstar, LamJS, C

def battery3():
    rng = random.Random(1108)
    cnt = 0
    for _ in range(500):
        k = rng.randint(1, 8)
        S = [rng.randint(0, 25) for _ in range(k)]    # repeats allowed
        total, jstar, LamJS, C = cascade_terms(S)
        # THE EXPLICIT CASCADE: v2(total) = (2*j0 - s2(j0)) + v2(C)
        assert vp(total) == (2 * jstar - s2(jstar)) + vp(C), \
            (S, vp(total), 2 * jstar - s2(jstar), vp(C))
        # the Λ-spine inside the cascade is genuinely Legendre:
        assert LamJS == 2 * jstar - s2(jstar), (S, LamJS)
        cnt += 1
    print(f"BATTERY 3: {cnt} random nonempty lists over [0,25] (repeats allowed): "
          f"v2(sum) == (2*j0 - s2(j0)) + v2(cascadeC). EXPLICIT CASCADE HOLDS.")

# ---------- BATTERY 4: THE SQUARE-PARITY INVARIANT, exhaustive over subsets of [0,12] ----------
def battery4():
    N = 12
    cnt = 0
    squares = []
    for r in range(1, N + 2):
        for S in combinations(range(0, N + 1), r):
            total, jstar, LamJS, C = cascade_terms(S)
            rr = isqrt(total)
            if rr * rr == total:
                # square_parity_s2: s2(j0) % 2 == v2(C) % 2
                assert s2(jstar) % 2 == vp(C) % 2, (S, total, rr, jstar, vp(C))
                # square_cascade_even: (Lam(j0) + v2(C)) % 2 == 0
                assert (LamJS + vp(C)) % 2 == 0, (S, total)
                squares.append((S, total, rr, jstar, s2(jstar) % 2, vp(C) % 2))
            cnt += 1
    print(f"BATTERY 4: {cnt} nonempty subsets of [0,{N}] scanned exhaustively; "
          f"{len(squares)} PERFECT-SQUARE sums, every one satisfies")
    print(f"  s2(j0) % 2 == v2(C) % 2 (square_parity_s2) and (Lam(j0)+v2(C)) % 2 == 0 (square_cascade_even):")
    for S, t, rr, j0, p1, p2 in squares:
        print(f"    S={list(S)}  sum = {t} = {rr}^2  j0={j0}  s2(j0)%2={p1}  v2(C)%2={p2}")

# ---------- RECEIPTS (mirror the Lean §7 #eval receipts exactly) ----------
def receipts():
    assert (s2(0), s2(1), s2(7), s2(255), s2(256)) == (0, 1, 3, 8, 1)
    assert (vp(F[10]), 2 * 5 - s2(5), vp(F[10])) == (8, 8, 8)          # Lam 5 = 8
    assert (vp(F[20]) + s2(20), 20) == (20, 20)
    t, j0, LamJS, C = cascade_terms([4, 5])
    assert (vp(t), 2 * j0 - s2(j0) + vp(C)) == (4, 4)
    assert (s2(j0) % 2, vp(C) % 2) == (1, 1)
    print("RECEIPTS: (0, 1, 3, 8, 1) | (8, 8, 8) | (20, 20) | (4, 4) | (1, 1) — all Lean #eval expectations confirmed.")

battery1()
battery2()
battery3()
battery4()
receipts()
print("\nALL BATTERIES GREEN.")
