#!/usr/bin/env python3
"""Erdős #727 — factorial-square census battery (Session 028).
Census 1: k=2 solutions n < 10000 (expect: 55, n=208 the smallest).
Census 2: k=3 solutions n < 3000 (expect: none).
Witness: n=208 — full prime check (47 primes ≤ 212), tightness profile,
quotient Q = 416!/(210!)² recomputed by two methods.
"""
from math import isqrt

def vpfact(n, p):
    v, q = 0, p
    while q <= n:
        v += n // q; q *= p
    return v

def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, isqrt(p) + 1))]

def solves(n, k):
    for p in PRIMES:
        if p > n + k: break
        if 2 * vpfact(n + k, p) > vpfact(2 * n, p):
            return False
    return True

PRIMES = primes_upto(21000)

if __name__ == "__main__":
    # Witness verification (two methods)
    n = 208
    Q1 = 1
    for i in range(211, 417): Q1 *= i          # method 1: 416!/210!
    F210 = 1
    for i in range(2, 211): F210 *= i
    Q = Q1 // F210                             # Q = 416!/(210!)^2
    Q2 = 1
    for i in range(2, 417): Q2 *= i            # method 2: full 416!
    assert Q * F210 * F210 == Q2
    print(f"[WITNESS] n=208: Q digits={len(str(Q))}, dual-method verified")
    assert str(Q) == "3434625869328791465442615807179469507329299372137898432836386962648328628227617375135477507375828820012927635165314"
    tight = [p for p in primes_upto(212) if vpfact(416, p) - 2 * vpfact(210, p) == 0]
    print(f"[WITNESS] tight primes: {len(tight)} of {len(primes_upto(212))}")
    assert len(tight) == 28 and 5 in tight and 7 in tight
    # Census k=2
    sols2 = [n for n in range(1, 10000) if solves(n, 2)]
    print(f"[CENSUS 1] k=2 solutions n<10000: {len(sols2)}, smallest {sols2[0] if sols2 else None}")
    assert 208 in sols2 and len(sols2) == 55
    # Census k=3
    sols3 = [n for n in range(1, 3000) if solves(n, 3)]
    print(f"[CENSUS 2] k=3 solutions n<3000: {len(sols3)}")
    assert len(sols3) == 0
    print("CENSUS_727_ALL_GREEN")
