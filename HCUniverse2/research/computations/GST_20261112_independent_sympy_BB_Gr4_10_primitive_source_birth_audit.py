#!/usr/bin/env python3
"""Independent exact SymPy audit of algebraic GST Navigation cell birth.

Original X = smooth projective Gr(4,10), dimension 24, middle p=12.
Source cells are actual Schubert varieties born from algebraic G_m fixed
point attracting strata (external Bialynicki-Birula theorem).

This program independently reconstructs integer partitions and the
Pieri ample-divisor matrix (not using Wolfram output).
It checks the two committed primitive Chow cycle coefficient vectors
are annihilated by multiplication with the ample divisor IN CH,
checks the primitive Chow intersection form, and verifies the explicit
12-channel Chow-basis completion and its algebraic duality.

The code validates exact combinatorics: the geometric Schubert-cell
and Pieri theorems are established external results, not proved by code.
It does not imply all arbitrary smooth projective X have a G_m action.
"""
from itertools import product
from sympy import Matrix, eye, zeros

K, WIDTH = 4, 6

def partitions(weight):
    return [
        tup for tup in product(range(WIDTH + 1), repeat=K)
        if tuple(sorted(tup, reverse=True)) == tup and sum(tup) == weight
    ]

mid = partitions(12)
next_degree = partitions(13)
assert len(mid) == 18
assert len(next_degree) == 16

def one_box(source, target):
    delta = tuple(t - s for s, t in zip(source, target))
    return delta.count(1) == 1 and delta.count(0) == K - 1

pieri = Matrix([
    [int(one_box(a, b)) for a in mid]
    for b in next_degree
])
assert pieri.rank() == 16
v1 = Matrix([1, -1, 7, -6, 6, -9, 10, 2, -6, -8, 6, 25,
             -16, 6, 14, 0, -6, 6])
v2 = Matrix([5, -5, -1, 6, -6, 9, -4, -8, 6, 14, -6,
             -25, 16, -12, -14, 6, 0, 0])
assert pieri * v1 == zeros(16, 1)
assert pieri * v2 == zeros(16, 1)

# Opposite Schubert cycles give integral Chow duality.
gram = Matrix([
    [int(a == tuple(WIDTH - x for x in reversed(b))) for b in mid]
    for a in mid
])
prim = Matrix.hstack(v1, v2)
q = prim.T * gram * prim
assert q == Matrix([[1095, -1005], [-1005, 1275]])
assert q.det() == 386100

# The original GST 12-channel source begins with two born primitive
# Chow cycles, plus ten honest Schubert cycles. Complete to full
# 18-dimensional basis using six additional Schubert cycles.
completing = list(range(1, 11)) + [11, 12, 13, 14, 15, 17]
change = Matrix.hstack(
    v1, v2, *(eye(18)[:, i - 1] for i in completing)
)
assert change.rank() == 18
assert change.det() == 36
dual_coefficients = change.inv().T
assert change.T * dual_coefficients == eye(18)

print({
    "original_X": "Gr(4,10)",
    "fixed_points": 210,
    "middle_Chow_rank": len(mid),
    "Pieri_rank": pieri.rank(),
    "primitive_rank": 2,
    "primitive_Chow_intersection": q.tolist(),
    "primitive_Gram_det": q.det(),
    "actual_Chow_basis_change_det": change.det(),
    "allPassed": True
})
