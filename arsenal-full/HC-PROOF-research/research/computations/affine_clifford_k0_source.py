#!/usr/bin/env python3
"""Exact algebraic Clifford/Bott idempotent source audit, p=1..4.

Coefficient ring: Z[x_1,...,x_p,y_1,...,y_p,z]. No floating point,
sampling, external Python packages or random data.

A_1=[x_1], B_1=[y_1], and recursively:
 A_(n+1)=[[A_n, x_(n+1) I],[y_(n+1) I, -B_n]]
 B_(n+1)=[[B_n, x_(n+1) I],[y_(n+1) I, -A_n]]
so A_n B_n=B_n A_n=q_n I, q_n=sum x_i y_i.
On the affine quadric q_n=z(1-z), define
 E_n=[[zI,A_n],[B_n,(1-z)I]], a 2^n-square idempotent.

Proof (all n): the block products show AB=BA=q I by induction.
Expanding E^2-E gives (q-z(1-z)) I_2^n identically in the
polynomial ring. Passing to the quotient ring sets the scalar
factor zero. The image of E is then a genuine finite projective
module over that quotient ring, hence an algebraic vector bundle.

This is an explicit algebraic K0 source; it does NOT prove every
projective-origin rational Hodge class on any affine variety can
be obtained as its Chern character. That is the open spanning step.
"""
from collections import defaultdict

ZERO = {}
ONE = {(): 1}


def poly_add(*polys):
    result = defaultdict(int)
    for p in polys:
        for monomial, coefficient in p.items():
            result[monomial] += coefficient
    return {m: c for m, c in result.items() if c}


def poly_neg(p):
    return {m: -c for m, c in p.items()}


def poly_mul(a, b):
    out = defaultdict(int)
    for m, x in a.items():
        for n, y in b.items():
            out[tuple(sorted(m + n))] += x * y
    return {m: c for m, c in out.items() if c}


def scalar_poly(n):
    return {(): n} if n else {}


def variable(name):
    return {(name,): 1}


def identity(n, scalar=ONE):
    return [[scalar if i == j else ZERO for j in range(n)] for i in range(n)]


def scalar_matrix(p, n):
    return identity(n, p)


def neg_matrix(a):
    return [[poly_neg(p) for p in row] for row in a]


def block(a, b, c, d):
    n = len(a)
    assert len(b) == len(c) == len(d) == n
    return [a[i] + b[i] for i in range(n)] + [
        c[i] + d[i] for i in range(n)
    ]


def matrix_mul(a, b):
    n = len(a)
    assert len(b) == n and all(len(row) == n for row in a + b)
    return [
        [
            poly_add(*(poly_mul(a[i][k], b[k][j]) for k in range(n)))
            for j in range(n)
        ]
        for i in range(n)
    ]


def matrix_sub(a, b):
    return [
        [poly_add(a[i][j], poly_neg(b[i][j])) for j in range(len(a))]
        for i in range(len(a))
    ]


def is_zero_matrix(a):
    return all(not v for row in a for v in row)


def main():
    a = [[variable("x1")]]
    b = [[variable("y1")]]
    q = ZERO
    z = variable("z")
    one_minus_z = poly_add(ONE, poly_neg(z))
    relation = poly_add(q, poly_neg(poly_mul(z, one_minus_z)))
    for p in range(1, 5):
        if p > 1:
            n = len(a)
            xn, yn = variable(f"x{p}"), variable(f"y{p}")
            old_a, old_b = a, b
            a = block(
                old_a, scalar_matrix(xn, n),
                scalar_matrix(yn, n), neg_matrix(old_b)
            )
            b = block(
                old_b, scalar_matrix(xn, n),
                scalar_matrix(yn, n), neg_matrix(old_a)
            )
        q = poly_add(q, poly_mul(variable(f"x{p}"), variable(f"y{p}")))
        relation = poly_add(q, poly_neg(poly_mul(z, one_minus_z)))
        n = len(a)
        assert is_zero_matrix(matrix_sub(matrix_mul(a, b), scalar_matrix(q, n)))
        assert is_zero_matrix(matrix_sub(matrix_mul(b, a), scalar_matrix(q, n)))
        e = block(
            scalar_matrix(z, n), a,
            b, scalar_matrix(one_minus_z, n)
        )
        defect = matrix_sub(matrix_sub(matrix_mul(e, e), e),
                            scalar_matrix(relation, 2*n))
        assert is_zero_matrix(defect)
        trace = ZERO
        for i in range(2*n):
            trace = poly_add(trace, e[i][i])
        assert trace == scalar_poly(n)
        assert 2*n == (1 << p)
        print(f"p={p}: size={2*n}x{2*n}, AB=BA=q I, "
              f"E²-E=(q-z(1-z))I, trace={n} [PASS]")
    print("PASS: exact integral polynomial identities for p=1..4")
    print("UNIFORM PROOF: Clifford block recursion establishes all p>=1")
    print("SCOPE: explicit algebraic K0 sources, not all-X Hodge-surjectivity")


if __name__ == "__main__":
    main()
