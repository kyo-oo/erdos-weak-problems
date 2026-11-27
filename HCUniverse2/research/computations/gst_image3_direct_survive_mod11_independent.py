#!/usr/bin/env python3
"""Independent standard-library mod-11 Krylov check for original GST U,J,M.

The symbolic rational argument is recorded in the companion Wolfram
certificate/derivation. This script verifies the ENTIRE finite-field
population of eleven direct SURVIVE strengths against independently built
12-cell matrices and the exact committed Q8,Q12 formulas. It does not
by itself prove those integer polynomial coefficient formulas.
"""

P = 11
CELLS = [(i, k) for i in range(4) for k in range(3)]
POS = {cell: i for i, cell in enumerate(CELLS)}
SIGNS = {0, 1, 3, 4, 5, 9}


def zero(n=12):
    return [[0] * n for _ in range(n)]


def matmul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) % P
             for j in range(n)] for i in range(n)]


def matvec(a, v):
    return [sum(x * y for x, y in zip(row, v)) % P for row in a]


def determinant_mod(a):
    a = [[int(x) % P for x in row] for row in a]
    n = len(a)
    ans = 1
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            ans = -ans
        d = a[j][j]
        ans = ans * d % P
        inv = pow(d, -1, P)
        for i in range(j + 1, n):
            factor = a[i][j] * inv % P
            for k in range(j, n):
                a[i][k] = (a[i][k] - factor * a[j][k]) % P
    return ans % P


def p8(a):
    return (-130491-27750*a-25120*a**2-31800*a**3+7068*a**4
            -3304*a**5+1520*a**6-80*a**7+64*a**8)


def p12(a):
    return (-10623+474348*a+710952*a**2+141208*a**3
            +696720*a**4-249912*a**5+418988*a**6
            -196384*a**7+166048*a**8-59264*a**9
            +33664*a**10-6912*a**11+2560*a**12)


def main():
    u, j, m = zero(), zero(), zero()
    for n, (i, k) in enumerate(CELLS):
        digit_shuffle = divmod(i + 4 * k, 3)
        mirror = (3 - i, 2 - k)
        sign = 1 if i + 4 * k in SIGNS else -1
        p = (i // 2 + 2 * k) % 3
        q = (i % 2 + 2 * p) % 3
        survive = int(k == 2 and p == 2) + int(p == 2 and q == 2)
        u[n][POS[digit_shuffle]] = 1
        j[n][POS[mirror]] = sign
        m[n][n] = survive
    jm = matmul(j, m)
    mj = matmul(m, j)
    curvature = [[(jm[i][k] - mj[i][k]) % P for k in range(12)]
                 for i in range(12)]
    seed = [int(cell in ((0, 0), (0, 1))) for cell in CELLS]
    values = []
    for a in range(P):
        f = [[(u[i][k] + j[i][k] + a*m[i][k] + curvature[i][k]) % P
              for k in range(12)] for i in range(12)]
        orbit = []
        v = seed[:]
        for _ in range(12):
            orbit.append(v)
            v = matvec(f, v)
        krylov = [[orbit[k][i] for k in range(12)] for i in range(12)]
        direct = determinant_mod(krylov)
        symbolic = p8(a) * p12(a) % P
        assert direct == symbolic, (a, direct, symbolic)
        assert direct != 0, (a, direct)
        values.append(direct)
    assert (64 * 2560) % P != 0
    print({"prime": P, "complete_residues": list(range(P)),
           "krylov_determinants": values,
           "leading_product_nonzero": True,
           "all_assertions_passed": True})


if __name__ == "__main__":
    main()
