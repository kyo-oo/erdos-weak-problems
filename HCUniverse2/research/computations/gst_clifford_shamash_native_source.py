#!/usr/bin/env python3
"""Exact equation-defined MF -> syzygy -> native Chern-source audit.

Run: python3 research/computations/gst_clifford_shamash_native_source.py
No source K0 bundle or Hodge-cycle witness is an input. The polynomial input
is F=sum a_i*b_i with p+1 independent linear a_i. The geometric domain is
smooth degree-d hypersurfaces containing their common maximal linear plane.
"""
from fractions import Fraction as Q
from math import comb, factorial
import json
from affine_clifford_k0_source import poly_add, poly_mul, poly_neg, variable, ONE


def basis(p, j):
    return [(mask, (j-mask.bit_count())//2)
            for mask in range(1 << (p+1))
            if mask.bit_count() <= j and (j-mask.bit_count()) % 2 == 0]


def differential(p, j):
    source, target = basis(p, j), basis(p, j-1)
    target_index = {v: i for i, v in enumerate(target)}
    matrix = {}
    for col, (mask, k) in enumerate(source):
        for i in range(p+1):
            sign = (-1)**((mask & ((1 << i)-1)).bit_count())
            if mask & (1 << i):
                destination, name = (mask ^ (1 << i), k), f'a{i}'
            elif k:
                destination, name = (mask | (1 << i), k-1), f'b{i}'
            else:
                continue
            row = target_index[destination]
            value = variable(name)
            matrix[row, col] = value if sign == 1 else poly_neg(value)
    return (len(target), len(source), matrix)


def product(a, b):
    assert a[1] == b[0]
    out = {}
    by_row = {}
    for (k, j), value in b[2].items():
        by_row.setdefault(k, []).append((j, value))
    for (i, k), value in a[2].items():
        for j, other in by_row.get(k, []):
            out[i, j] = poly_add(out.get((i, j), {}), poly_mul(value, other))
    return (a[0], b[1], {ij: v for ij, v in out.items() if v})


def fpoly(p):
    return poly_add(*(poly_mul(variable(f'a{i}'), variable(f'b{i}'))
                      for i in range(p+1)))


def evaluate(poly, values):
    return sum(coefficient * __import__('functools').reduce(
        lambda x, name: x*values[name], monomial, Q(1))
        for monomial, coefficient in poly.items())


def rank(matrix, values):
    a = [[evaluate(matrix[2].get((i, j), {}), values)
          for j in range(matrix[1])] for i in range(matrix[0])]
    k = 0
    for j in range(matrix[1]):
        pivot = next((i for i in range(k, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[k], a[pivot] = a[pivot], a[k]
        c = a[k][j]
        a[k] = [x/c for x in a[k]]
        for i in range(k+1, len(a)):
            c = a[i][j]
            a[i] = [x-c*y for x, y in zip(a[i], a[k])]
        k += 1
        if k == len(a):
            break
    return k


def add_univariate(*polys):
    result = {}
    for poly in polys:
        for degree, coefficient in poly.items():
            result[degree] = result.get(degree, 0)+coefficient
    return {j: c for j, c in result.items() if c}


def shifted(poly, degree, scalar=1):
    return {j+degree: scalar*c for j, c in poly.items()}


def graded_free(p, d, j):
    result = {}
    for mask, k in basis(p, j):
        degree = mask.bit_count()+k*d
        result[degree] = result.get(degree, 0)+1
    return result


def source_case(p, d):
    # Independent enumeration of exterior/Tate basis versus the binomial rule.
    for j in range(p+2):
        via_masks = graded_free(p, d, j)
        via_binomial = {}
        for k in range(j//2+1):
            r = j-2*k
            if r <= p+1:
                degree = r+k*d
                via_binomial[degree] = via_binomial.get(degree, 0)+comb(p+1, r)
        assert via_masks == via_binomial
    # Two independent Hilbert-numerator calculations: periodic MF tail and
    # finite Shamash prefix plus the actual plane module S/(a_0,...,a_p).
    prefix = add_univariate(*(
        {j: (-1)**(p-1-i)*c for j, c in graded_free(p, d, i).items()}
        for i in range(p)))
    from_tail = add_univariate(graded_free(p, d, p),
                              shifted(graded_free(p, d, p+1), 0, -1))
    plane = {j: (-1)**(p+j)*comb(p+1, j) for j in range(p+2)}
    from_prefix = add_univariate(plane, prefix, shifted(prefix, d, -1))
    assert from_tail == from_prefix
    bundle_rank = sum(prefix.values())
    assert bundle_rank == 2**(p-1)
    numerator = sum(c*(-j)**p for j, c in prefix.items())
    plane_coefficient = (-1)**p*factorial(p)
    # Actual normal sequence: c(N_P/X)=(1+h)^(p+1)/(1+d*h).
    self_intersection = sum(comb(p+1, j)*(-d)**(p-j) for j in range(p+1))
    def pair(u, v):
        return d*u[0]*v[0]+u[0]*v[1]+u[1]*v[0]+self_intersection*u[1]*v[1]
    primitive = (-1, d)
    scaled_character = (numerator, plane_coefficient)
    period = pair(primitive, scaled_character)
    assert period == factorial(p)*(d-1)**(p+1) > 0
    correction = (d*numerator-(d*numerator+plane_coefficient),
                  d*plane_coefficient)
    assert correction == tuple(plane_coefficient*x for x in primitive)
    return {'p': p, 'degree': d, 'matrix_size': 2**p,
            'bundle_rank': bundle_rank, 'scaled_ambient_character': numerator,
            'scaled_plane_character': plane_coefficient,
            'exact_scaled_native_period': period,
            'ambient_character': str(Q(numerator, factorial(p)))}


def matrix_case(p):
    ds = {j: differential(p, j) for j in range(1, p+3)}
    F = fpoly(p)
    checked = 0
    for j in range(2, p+3):
        composed = product(ds[j-1], ds[j])
        target_index = {v: i for i, v in enumerate(basis(p, j-2))}
        expected = {(target_index[mask, k-1], col): F
                    for col, (mask, k) in enumerate(basis(p, j)) if k}
        assert composed == (len(target_index), len(basis(p, j)), expected)
        checked += 1
    A, B = ds[p+1], ds[p+2]
    N = 1 << p
    assert product(A, B) == (N, N, {(i, i): F for i in range(N)})
    assert product(B, A) == (N, N, {(i, i): F for i in range(N)})
    for d in (2, 3, 7):
        for j, matrix in ds.items():
            src, dst = basis(p, j), basis(p, j-1)
            for (i, k), entry in matrix[2].items():
                source_shift = src[k][0].bit_count()+src[k][1]*d
                target_shift = dst[i][0].bit_count()+dst[i][1]*d
                for monomial in entry:
                    assert len(monomial) == 1
                    entry_degree = 1 if monomial[0].startswith('a') else d-1
                    assert source_shift-target_shift == entry_degree
    # Two explicit smooth charts on F=0. Rank is derived from the matrices.
    values = {f'{name}{i}': Q(0) for name in ('a', 'b') for i in range(p+1)}
    for chosen in ('a0', 'b0'):
        chart = dict(values); chart[chosen] = Q(1)
        assert evaluate(F, chart) == 0
        assert rank(A, chart) == N//2 and rank(B, chart) == N//2
    return {'p': p, 'matrix_size': N,
            'symbolic_differential_compositions': checked,
            'both_matrix_factorization_products': 'F*identity',
            'graded_homogeneity_degrees': [2, 3, 7],
            'two_smooth_chart_ranks': N//2}


def main():
    matrices = [matrix_case(p) for p in range(1, 6)]
    sources = [source_case(p, d) for p in range(1, 13) for d in range(2, 9)]
    assert len(sources) == 84
    cubic = next(x for x in sources if x['p'] == 2 and x['degree'] == 3)
    assert cubic['bundle_rank'] == 2 and cubic['ambient_character'] == '3/2'
    assert cubic['exact_scaled_native_period'] == 16
    print(json.dumps({'claim': 'Equation-defined graded Clifford MF has a nonambient native syzygy Chern source',
        'matrix_cases': matrices, 'native_source_cases': sources,
        'native_source_case_count': len(sources), 'cubic_fourfold_benchmark': cubic,
        'uniform_unscaled_native_period': '(d-1)^(p+1)',
        'scope': 'Actual equation constructor F=sum a_i*b_i with independent linear a_i and smooth X; no assertion every original X admits a prescribed-residual-adapted factorization'}, indent=2))


if __name__ == '__main__':
    main()
