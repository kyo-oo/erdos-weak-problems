#!/usr/bin/env python3
"""Independent exact finite-prefix audit of physical 4-power pair overlap.

For p=0..8 the 3^p distinct exponents k are evaluated by modular pow,
and translated to physical affine coordinates A_k=(4^k-1)/3 mod 3^p.
An independently implemented low-to-high ternary digit scan tests whether
A_k and 4*A_k+1 have a simultaneous 2 below depth p.

The exact 4-state transition count is computed separately and compared.
These finite checks do not assert the universal CommonTwo theorem.
"""

from __future__ import annotations

def count_by_carries(depth: int) -> int:
    states = [1, 1, 1, 1]
    for _ in range(depth):
        a, b, c, d = states
        states = [a+b, a+b+d, a+c+d, b+c]
    return states[1]

def no_shared_two_prefix(a: int, depth: int) -> bool:
    b = 4 * a + 1
    for _ in range(depth):
        if a % 3 == 2 and b % 3 == 2:
            return False
        a //= 3
        b //= 3
    return True

def main() -> None:
    expected = [1, 3, 7, 18, 44, 110, 272, 676, 1676]
    for p in range(9):
        modulus = 3 ** p
        lifted_modulus = 3 * modulus
        coordinates = set()
        survivors = 0
        for k in range(modulus):
            # pow uses integer modular exponentiation; (pow-1) divisible by 3.
            A = (pow(4, k, lifted_modulus) - 1) // 3
            assert 0 <= A < modulus, (p, k, A)
            coordinates.add(A)
            survivors += no_shared_two_prefix(A, p)
        theoretical = count_by_carries(p)
        assert len(coordinates) == modulus, (p, len(coordinates), modulus)
        assert survivors == theoretical == expected[p], (p, survivors, theoretical)
        if p % 2 == 0:
            assert survivors <= 7 ** (p // 2)
        else:
            assert survivors <= 3 * 7 ** (p // 2)
        print(f"depth={p}, original_exponents={modulus}, "
              f"no_common_two_within_depth={survivors}, "
              f"four_state_count={theoretical}, bijection=PASS")
    print("GST_PROBLEM406_FINITE_PREFIX_ENTROPY_AUDIT_PASS=1")
    print("NONCLAIM: this is not a proof of infinite-depth universal CommonTwo")

if __name__ == "__main__":
    main()
