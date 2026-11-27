#!/usr/bin/env python3
"""Exact bounded cross-checks; the all-n/all-t proofs are in the Lean module.

Run: python3 research/computations/gst_weil_uniform_power_and_shear.py
Only Python's standard library is used. No variety, Chow group, or actual
derived deformation is implemented by this polynomial experiment.
"""
from fractions import Fraction
import json

NAMES = ('a1', 'a2', 'a3', 'b1', 'b2', 'b3', 'd1', 'd2', 'i', 't')
ZERO = (0,) * len(NAMES)


class Poly:
    def __init__(self, terms=0):
        if isinstance(terms, Poly):
            self.terms = terms.terms.copy()
        elif isinstance(terms, dict):
            self.terms = {m: Fraction(c) for m, c in terms.items() if c}
        else:
            self.terms = {} if terms == 0 else {ZERO: Fraction(terms)}

    def __add__(self, other):
        out = self.terms.copy()
        for mon, coeff in Poly(other).terms.items():
            out[mon] = out.get(mon, 0) + coeff
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        out = {}
        for m, c in self.terms.items():
            for n, d in Poly(other).terms.items():
                mon = tuple(a + b for a, b in zip(m, n))
                out[mon] = out.get(mon, 0) + c * d
        return Poly(out)

    __rmul__ = __mul__


def variable(name):
    exponents = list(ZERO)
    exponents[NAMES.index(name)] = 1
    return Poly({tuple(exponents): 1})


def real(a1, a2, a3, b1, b2, b3):
    return -a1*a2*a3 + a1*b2*b3 + b1*a2*b3 + b1*b2*a3


def imag(a1, a2, a3, b1, b2, b3):
    return b1*a2*a3 + a1*b2*a3 + a1*a2*b3 - b1*b2*b3


def gaussian_mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def gaussian_binary_power(n):
    out, base = (1, 0), (2, 1)
    while n:
        if n & 1:
            out = gaussian_mul(out, base)
        base = gaussian_mul(base, base)
        n //= 2
    return out


def exterior_wedge(left, right):
    """Increasing wedge basis with exact inversion sign and Poly scalars."""
    out = {}
    for a, ca in left.items():
        for b, cb in right.items():
            if set(a).intersection(b):
                continue
            sign = (-1)**sum(x > y for x in a for y in b)
            mon = tuple(sorted(a+b))
            out[mon] = out.get(mon, Poly()) + sign*ca*cb
    return {m: c for m, c in out.items() if c.terms}


def direct_line_bundle_variation():
    """Compute c1 of the actual external line-bundle summand under shear."""
    t = variable('t')
    basis = [{(j,): Poly(1)} for j in range(12)]
    moved = [dict(f) for f in basis]
    moved[0][(10,)] = -t  # old u1 = new u1 - t V2
    moved[4][(6,)] = -t   # old v2 = new v2 - t U1

    def line_c1(forms):
        out = {}
        for j in range(3):
            for a, b in ((j, 9+j), (6+j, 3+j)):
                for mon, c in exterior_wedge(forms[a], forms[b]).items():
                    out[mon] = out.get(mon, Poly()) + Fraction(1, 2)*c
        return out

    old, new = line_c1(basis), line_c1(moved)
    difference = {m: new.get(m, Poly())-old.get(m, Poly())
                  for m in set(old).union(new)}
    difference = {m: p for m, p in difference.items() if p.terms}
    tmon = (0,)*(len(NAMES)-1)+(1,)
    assert set(difference) == {(6, 7), (9, 10)}
    assert all(p.terms == {tmon: Fraction(1, 2)}
               for p in difference.values())
    labels = ('u1','u2','u3','v1','v2','v3','U1','U2','U3','V1','V2','V3')
    return {'^'.join(labels[j] for j in mon): str(p.terms[tmon])
            for mon, p in sorted(difference.items())}


def direct_sum_tangent_matrix():
    """Exact Q(i) rank of actual line-summand obstruction coordinates.

    Columns are t11,t12,t13,t21,t22,t23,t31,t32,t33. For each
    external line bundle and a<b, rows read V_a^V_b and U_a^U_b.
    A uses (p,q)=(1,1); B uses (i,-i) in (p*u^V+q*U^v)/2.
    """
    z, one, ii = (Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))
    add = lambda a, b: (a[0]+b[0], a[1]+b[1])
    neg = lambda a: (-a[0], -a[1])
    conj = lambda a: (a[0], -a[1])
    half = lambda a: (a[0]/2, a[1]/2)

    def inverse(a):
        norm = a[0]*a[0]+a[1]*a[1]
        assert norm
        return a[0]/norm, -a[1]/norm

    def rref(matrix):
        m = [row[:] for row in matrix]
        pivot_columns, r = [], 0
        for c in range(9):
            k = next((k for k in range(r, len(m)) if m[k][c] != z), None)
            if k is None:
                continue
            m[r], m[k] = m[k], m[r]
            inv = inverse(m[r][c])
            m[r] = [gaussian_mul(v, inv) for v in m[r]]
            for k in range(len(m)):
                if k != r and m[k][c] != z:
                    factor = m[k][c]
                    m[k] = [add(x, neg(gaussian_mul(factor, y)))
                            for x, y in zip(m[k], m[r])]
            pivot_columns.append(c)
            r += 1
        return m, pivot_columns

    patterns = [(one, one, one), (one, ii, ii),
                (ii, one, ii), (ii, ii, one)]
    matrix, rank_growth = [], []
    for p in patterns:
        q = [conj(x) for x in p]
        for a in range(3):
            for b in range(a+1, 3):
                vr, ur = [z]*9, [z]*9
                vr[3*a+b], vr[3*b+a] = half(p[a]), neg(half(p[b]))
                ur[3*a+b], ur[3*b+a] = half(q[b]), neg(half(q[a]))
                matrix.extend([vr, ur])
        rank_growth.append(len(rref(matrix)[1]))
    reduced, pivots = rref(matrix)
    assert rank_growth == [3, 5, 6, 6]
    assert pivots == [1, 2, 3, 5, 6, 7]
    assert all(row[j] == z for row in matrix for j in (0, 4, 8))
    assert all(all(x == z for x in row) for row in reduced[6:])
    # Orthogonal invariant: the 2x2 block formed by AAA and ABB
    # for pair (1,2) has determinant (1-i)/4, not zero.
    determinant = gaussian_mul(half(one), neg(half(ii)))
    determinant = add(determinant, neg(gaussian_mul(neg(half(one)), half(one))))
    assert determinant == (Fraction(1, 4), Fraction(-1, 4))
    selected_rows, selected_cols = [0, 6, 2, 8, 4, 16], [1, 3, 2, 6, 5, 7]
    minor = [[matrix[r][c] for c in selected_cols] for r in selected_rows]
    block = [[half(one), neg(half(one))], [half(one), neg(half(ii))]]
    assert all(minor[r][c] == (block[r % 2][c % 2] if r//2 == c//2 else z)
               for r in range(6) for c in range(6))
    full_minor = gaussian_mul(gaussian_mul(determinant, determinant), determinant)
    assert full_minor == (Fraction(-1, 32), Fraction(-1, 32))
    return {'coefficient_domain': 'Q(i), pairs of exact Fractions',
            'shape': [24, 9], 'rank_growth_AAA_ABB_BAB_BBA': rank_growth,
            'pivot_columns_zero_based': pivots,
            'kernel_basis_columns_zero_based': [0, 4, 8],
            'kernel': ['t11', 't22', 't33'],
            'mixed_pair_minor': '(1-i)/4',
            'six_direction_minor': '-(1+i)/32',
            'scope': 'Necessary obstruction map of line-bundle direct summands; '
                     'not the full Atiyah map of every representative of the K0 class'}


def main():
    a1, a2, a3, b1, b2, b3, d1, d2, i, t = map(variable, NAMES)
    leak_r = (-(d1*a2*a3+a1*d2*a3)+d1*b2*b3
              + a1*(-i*d2)*b3+(i*d1)*a2*b3+b1*d2*b3
              + (i*d1)*b2*a3+b1*(-i*d2)*a3)
    leak_i = ((i*d1)*a2*a3+b1*d2*a3+d1*b2*a3
              + a1*(-i*d2)*a3+d1*a2*b3+a1*d2*b3
              - (i*d1)*b2*b3-b1*(-i*d2)*b3)
    args = (a1+t*d1, a2+t*d2, a3, b1+i*t*d1, b2-i*t*d2, b3)
    dr = real(*args)-real(a1, a2, a3, b1, b2, b3)
    di = imag(*args)-imag(a1, a2, a3, b1, b2, b3)
    error_r = dr-t*leak_r+(i*i+1)*t*t*d1*d2*a3
    error_i = di-t*leak_i-(i*i+1)*t*t*d1*d2*b3
    assert not error_r.terms and not error_i.terms
    g1, g2 = d1*(a2-i*b2), d2*(a1+i*b1)
    assert not (leak_r-(-a3*(g1+g2)+i*b3*(g1-g2)
                         +(i*i+1)*b3*(b1*d2+b2*d1))).terms
    assert not (leak_i-(i*a3*(g1-g2)+b3*(g1+g2)
                         +(i*i+1)*a3*(b1*d2+b2*d1))).terms
    # Hand-computable sign benchmark: a3=d1=d2=t=1, all other
    # symbols zero (including i) gives delta real=-1, delta imag=0.
    assert real(1, 1, 1, 0, 0, 0) == -1
    a, b = 1, 0
    rows = []
    for n in range(1, 513):
        a, b = 2*a-b, a+2*b
        assert (a, b) == gaussian_binary_power(n)
        assert a*a+b*b == 5**n
        assert (a+2*b) % 5 in (1, 4)
        assert (a-2*b) % 5 == 0
        assert a != 0 and b != 0
        if n <= 12:
            rows.append([n, a, b, (a+2*b) % 5, (a-2*b) % 5])
    # Canonical anti-holomorphic exterior basis U1,U2,U3,V1,V2,V3:
    # d1=-V2 wedge V1/2, d2=-U2 wedge U1/2.
    line_bundle_obstruction = direct_line_bundle_variation()
    print(json.dumps({
        'assertion_tested': 'Exact polynomial finite-shear expansion and '
                            'Gaussian recurrence for every integer n=1..512',
        'coefficient_domain': 'Q[a1,a2,a3,b1,b2,b3,d1,d2,i,t] and Z[i]',
        'polynomial_remainders': [len(error_r.terms), len(error_i.terms)],
        'quadratic_signs': {'real': '-(i*i+1)*t*t*d1*d2*a3',
                            'imag': '+(i*i+1)*t*t*d1*d2*b3'},
        'gaussian_exponents_visited': 512,
        'gaussian_first_twelve': rows,
        'direct_sum_line_bundle_Atiyah_coordinate': line_bundle_obstruction,
        'direct_sum_nine_parameter_obstruction': direct_sum_tangent_matrix(),
        'non_claims': ['No construction of a nonsplit relative perfect complex',
                       'No counterexample to the rational Hodge conjecture',
                       'Finite powers alone do not prove the all-n theorem',
                       'Atiyah interpretation uses the stated geometric comparison'],
    }, indent=2))


if __name__ == '__main__':
    main()
