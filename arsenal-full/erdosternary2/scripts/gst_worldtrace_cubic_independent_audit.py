#!/usr/bin/env python3
"""Exact finite independent audit of GST Worldtrace third-band physical formulas.

All calculations are integer arithmetic: modular exponentiation, integer
division and explicit binomial coefficients. No float, random sample or
unverified theorem is used.

Finite assertion only:
- For L=0..7, u in a documented set, M in {0,4,5}, and w in a documented
  set, cubic quotient polynomial matches literal physical 4^exponent
  quotient modulo 3^w.
- Cubic same-position hits for K=355 (row13) and K=35725 (row27);
  quadratic extrapolation alone does not give digit pair (2,2).
- The first common row for a few delayed u=2 perfect-power examples.

Does NOT prove the universal Erdős 406 conjecture or eliminate hGate.
"""
from math import comb

OFFSETS = (0, 4, 5)
MULTIPLIERS = (0, 1, 2, 3, 13, 31, 49)
SCALES = tuple(range(8))


def coefficient(scale: int) -> int:
    return (4 ** (3 ** scale) - 1) // (3 ** (scale + 1))


def quotient_mod(M: int, u: int, L: int, w: int) -> int:
    T = 3 ** (L + 1)
    Q = 3 ** w
    exponent = M + u * (3 ** L)
    return (pow(4, exponent, T * Q) // T) % Q


def polynomial(M: int, u: int, L: int, w: int, degree: int) -> int:
    T = 3 ** (L + 1)
    c = coefficient(L)
    A = 4 ** M
    out = A // T + u * c * A
    if degree >= 2:
        out += comb(u, 2) * T * c ** 2 * A
    if degree >= 3:
        out += comb(u, 3) * T ** 2 * c ** 3 * A
    return out % (3 ** w)


def digit_of_power(exponent: int, row: int) -> int:
    q = 3 ** row
    return (pow(4, exponent, 3 * q) // q) % 3


def first_common_row(K: int, cap: int) -> int | None:
    for p in range(1, cap + 1):
        if digit_of_power(K, p) == digit_of_power(K+1, p) == 2:
            return p
    return None


def audit() -> None:
    count = 0
    for L in SCALES:
        widths = sorted({1, L+1, 2*(L+1), 3*(L+1)})
        for M in OFFSETS:
            for u in MULTIPLIERS:
                for w in widths:
                    expected = quotient_mod(M, u, L, w)
                    actual = polynomial(M, u, L, w, degree=3)
                    assert actual == expected, (L, M, u, w, expected, actual)
                    count += 1
    print(f"CUBIC_THREE_BAND_FINITE_AUDIT_PASS cases={count}")

    for L, u, k in ((3, 13, 9), (6, 49, 20)):
        K = 4 + u * 3 ** L
        w = k + 1
        p = L + 1 + k
        quadratic = tuple((polynomial(M,u,L,w,2)//3**k)%3 for M in (4,5))
        cubic = tuple((polynomial(M,u,L,w,3)//3**k)%3 for M in (4,5))
        physical = (digit_of_power(K,p),digit_of_power(K+1,p))
        assert cubic == physical == (2,2), (L,u,cubic,physical)
        assert quadratic != (2,2), (L,u,quadratic)
        first = first_common_row(K,p)
        assert first == p, (K,p,first)
        print(f"NONLINEAR_PHYSICAL_PASS K={K} row={p} quadratic={quadratic} cubic={cubic} first={first}")

    for L in (6,8,11,15):
        K = 4 + 2 * 3 ** L
        first = first_common_row(K, L+1)
        assert first == L+1, (L,K,first)
        print(f"DELAYED_FIRST_TWO_PASS L={L} K={K} first={first}")

    for K in (0,1,2,3,4,7):
        assert first_common_row(K,50) is None, K
    print("EXCEPTIONAL_SMALL_EXPONENT_BASE_PASS")

    print("AUDIT_STATUS=finite_exact_only_not_universal_proof")


if __name__ == "__main__":
    audit()
