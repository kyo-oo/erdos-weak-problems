#!/usr/bin/env python3
"""Exact symbolic cochain detector for the 48-dimensional obstruction image.

Ring Q[n]; n is an indeterminate, not a sampled orbit length. Hodge forms
are the exterior algebra on u0,u1,u2,w0,w1,w2. Left contraction with ti
is ordinary exterior interior multiplication at wi, including its sign
past the u factors. This is the raw Dolbeault Koszul convention.

This certifies contraction rank, not algebraicity or analytic deformation.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from collections import Counter
import platform


def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Q(0)) + v
        if not out[k]:
            del out[k]
    return out


def mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i+j] = out.get(i+j, Q(0)) + x*y
    return {k: v for k, v in out.items() if v}


ONE = {0: Q(1)}
N = {1: Q(1)}


def scale(a, c):
    return {k: c*v for k, v in a.items() if c*v}


def wedge_sign(a, b):
    return (-1)**sum(1 for i in range(12) if a >> i & 1
                     for j in range(12) if b >> j & 1 and i > j)


def wedge(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            if not i & j:
                v = scale(mul(x, y), wedge_sign(i, j))
                out[i | j] = add(out.get(i | j, {}), v)
    return {k: v for k, v in out.items() if v}


def form_scale(a, p):
    return {k: v for k, x in a.items() if (v := mul(x, p))}


def form_add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = add(out.get(k, {}), v)
        if not out[k]:
            del out[k]
    return out


def act(i, a):
    if i % 6 < 3:
        return wedge({1 << i: ONE}, a)
    out = {}
    for mask, p in a.items():
        if mask >> i & 1:
            sign = (-1)**((mask & ((1 << i)-1)).bit_count())
            out[mask ^ (1 << i)] = scale(p, sign)
    return out


def imbalance(mask):
    return (mask & 7).bit_count() - (mask >> 3).bit_count()


def coefficient(a, mask):
    return a.get(mask, {})


def determinant_diagonal(matrix):
    out = ONE
    for i, row in enumerate(matrix):
        assert all(not v for j, v in enumerate(row) if j != i)
        assert row[i]
        out = mul(out, row[i])
    return out


def fmt(p):
    return ' + '.join(f'{v}*n^{k}' for k, v in sorted(p.items())) or '0'


def main():
    print('Python', platform.python_version())
    theta = {((1 << i) | (1 << (i+3))): ONE for i in range(3)}
    theta2 = wedge(theta, theta)
    theta3 = wedge(theta2, theta)
    f = form_add({0: ONE}, form_add(form_scale(theta2, scale(N, -Q(1, 2))),
                                   form_scale(theta3, scale(N, Q(1, 3)))))
    assert f[0] == ONE
    assert all(imbalance(k) == 0 for k in f)
    c1 = [act(i, f) for i in range(6)]
    ht2 = list(combinations(range(6), 2))
    c2 = [act(i, act(j, f)) for i, j in ht2]
    assert all(all(imbalance(k) == 1 for k in v) for v in c1)
    assert all(all(imbalance(k) == 2 for k in v) for v in c2)

    # c1: rank-term eta coefficients, then one off-diagonal coefficient
    # of -n*j(xi)*theta per xi. The latter have no eta contribution.
    c1rows = [1 << i for i in range(3)]
    c1rows += [(1 << i) | (1 << ((i+1) % 3)) |
               (1 << (((i+1) % 3)+3)) for i in range(3)]
    matrix1 = [[coefficient(col, row) for col in c1] for row in c1rows]
    det1 = determinant_diagonal(matrix1)
    assert abs(det1.get(3, 0)) == 1 and len(det1) == 1

    # c2 target is exactly wedge^2 U plus wedge^3 U tensor W.
    pairs = list(combinations(range(3), 2))
    c2rows = [(1 << i) | (1 << j) for i, j in pairs]
    c2rows += [7 | (1 << (k+3)) for k in range(3)]
    # eta_i*xi_j for i,j complementary to the target w_k.
    c2cols = pairs + [(min({0, 1, 2}-{k}), max({0, 1, 2}-{k})+3)
                     for k in range(3)]
    selected2 = [c2[ht2.index(pair)] for pair in c2cols]
    matrix2 = [[coefficient(col, row) for col in selected2] for row in c2rows]
    det2 = determinant_diagonal(matrix2)
    assert abs(det2.get(3, 0)) == 1 and len(det2) == 1
    assert set(c2rows) == {k for k in range(64) if imbalance(k) == 2}

    # Compute the FULL product directly in the 12-generator exterior
    # algebra, then compare with the independent Kronecker construction.
    # Source operators are ordered left factor before right factor;
    # target basis is external product in that same order.
    fproduct = wedge(f, {k << 6: p for k, p in f.items()})
    product_cols = c2cols + list(product(range(6), range(6, 12))) + [
        (i+6, j+6) for i, j in c2cols]
    product_rows = c2rows + [i | (j << 6) for i, j in product(c1rows, repeat=2)] + [
        k << 6 for k in c2rows]
    direct_cols = [act(i, act(j, fproduct)) for i, j in product_cols]
    direct = [[coefficient(col, row) for col in direct_cols] for row in product_rows]
    blocks = []
    blocks.append(matrix2)
    middle = [[mul(matrix1[i][a], matrix1[j][b])
               for a, b in product(range(6), repeat=2)]
              for i, j in product(range(6), repeat=2)]
    blocks.append(middle)
    blocks.append(matrix2)
    expected = [[{} for _ in range(48)] for _ in range(48)]
    offset = 0
    for block in blocks:
        for i, row in enumerate(block):
            for j, value in enumerate(row):
                expected[offset+i][offset+j] = value
        offset += len(block)
    assert direct == expected
    assert determinant_diagonal(direct) == {42: Q(1)}
    diagonal = [block[i][i] for block in blocks for i in range(len(block))]
    total = ONE
    for block in blocks:
        total = mul(total, determinant_diagonal(block))
    assert total == {42: Q(1)}, total
    # Inspect every entry, not just the diagonal. Opposite blocks cannot
    # overlap: their ordered imbalances are (2,0),(1,1),(0,2).
    sizes = [len(block) for block in blocks]
    assert sizes == [6, 36, 6]
    census = Counter((next(iter(p)), next(iter(p.values()))) for p in diagonal)
    # A right inverse divides each chosen source by its nonzero diagonal
    # monomial. This proves the lower bound for every n != 0 over Q.
    assert all(len(p) == 1 and abs(next(iter(p.values()))) == 1 for p in diagonal)
    print('One-factor c1 detector: 6 x 6, determinant', fmt(det1))
    print('One-factor c2 detector: 6 x 6, determinant', fmt(det2))
    print('Product blocks:', sizes, '; factor imbalances (2,0),(1,1),(0,2)')
    print('All 48 x 48 detector entries checked; determinant', fmt(total))
    print('Diagonal (n-degree, sign) census:', sorted(census.items()))
    print('Rank lower bound 48 for every nonzero n; factorwise upper bound 6+36+6=48.')
    print('Coefficient ring Q[n]; no numerical orbit length or floating-point rank used.')
    print('PASS: full invariant obstruction contraction certificate; geometry is a separate proof.')


if __name__ == '__main__':
    main()
