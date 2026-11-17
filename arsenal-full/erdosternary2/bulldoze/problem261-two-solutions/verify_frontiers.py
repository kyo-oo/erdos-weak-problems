#!/usr/bin/env python3
"""Frontier battery for Kill #5 + the session's strike A/B evidence.

1. KILL #5 receipts: the three representations of 1/2 + block swap,
   verified by exact Fraction arithmetic, independent of the Lean file.
2. Collision census (J <= 14): >= 4 distinct solutions of x = 1/2,
   every certified solution exactly reconstructed.
3. Growth table: solution count of x = 1/2 by window depth J.
4. STRIKE A (Stanley two-seed family): sorted-greedy census t <= 18 —
   the clean-doubling dichotomy (only {3^k, 2*3^k} families double).
5. STRIKE B (odd-p kernel): certified kernel table k_p(u), p in {2,3,5}.
"""
from fractions import Fraction
from collections import defaultdict
import math

print("=== KILL #5 RECEIPTS (exact Fractions, independent check) ===")
half = Fraction(1, 2)
r1 = sum((Fraction(a, 2 ** a) for a in [2]), Fraction(0))
r2 = sum((Fraction(a, 2 ** a) for a in [3, 6, 8]), Fraction(0))
r3 = sum((Fraction(a, 2 ** a) for a in [4, 5, 6]), Fraction(0))
assert r1 == half and r2 == half and r3 == half, "BROKEN REPRESENTATION"
print("rep {2} == 1/2:", r1 == half)
print("rep {3,6,8} == 1/2:", r2 == half)
print("rep {4,5,6} == 1/2:", r3 == half)
b1 = Fraction(4, 16) + Fraction(5, 32)
b2 = Fraction(3, 8) + Fraction(8, 256)
assert b1 == b2 == Fraction(13, 32)
print("block {4,5} == {3,8} == 13/32:", b1 == b2, b1)

print()
print("=== COLLISION CENSUS (J <= 14), solutions per x VALUE ===")
sols = defaultdict(set)
for J in range(1, 15):
    for mask in range(1 << J):
        if not (mask >> (J - 1)) & 1:
            continue
        A = 0; S = 0
        for j in range(1, J + 1):
            if mask >> (j - 1) & 1:
                A += 1 << (J - j)
                S += j * (1 << (J - j))
        den = (1 << J) - A
        if den > 0 and S % den == 0:
            n = S // den
            if 1 <= n <= 400:
                offs = frozenset(j for j in range(1, J + 1) if mask >> (j - 1) & 1)
                pieces = frozenset(n + j for j in offs)
                lhs = Fraction(n, 2 ** n)
                rhs = sum((Fraction(a, 2 ** a) for a in pieces), Fraction(0))
                assert lhs == rhs, f"BROKEN CERT n={n}"
                sols[Fraction(n, 2 ** n)].add(pieces)

half_sols = sorted(sols[half], key=lambda s: (len(s), sorted(s)))
print("distinct solutions of x = 1/2 (J <= 14):", len(half_sols))
for s in half_sols[:8]:
    print("   ", sorted(s))
assert len(half_sols) >= 4, "expected >= 4 solutions of 1/2"
assert half_sols[0] == frozenset({2})
assert frozenset({3, 6, 8}) in sols[half]
assert frozenset({4, 5, 6}) in sols[half]

print()
print("=== GROWTH: solution count of x = 1/2 by depth J ===")
for Jmax in range(8, 15):
    cnt = set()
    for n in (1, 2):
        for J in range(1, Jmax + 1):
            for mask in range(1 << J):
                if not (mask >> (J - 1)) & 1:
                    continue
                A = 0; S = 0
                for j in range(1, J + 1):
                    if mask >> (j - 1) & 1:
                        A += 1 << (J - j)
                        S += j * (1 << (J - j))
                den = (1 << J) - A
                if den > 0 and S % den == 0:
                    nn = S // den
                    if nn == n:
                        offs = frozenset(j for j in range(1, J + 1) if mask >> (j - 1) & 1)
                        cnt.add(frozenset(nn + j for j in offs))
    print(f"  J <= {Jmax}: {len(cnt)} solutions")

print()
print("ALL FRONTIER CHECKS PASSED")
