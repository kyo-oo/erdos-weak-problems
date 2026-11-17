"""Independent finite checks of the new GST observation construction.

Run: python3 scripts/check_coherent_cosmology.py
Universal proofs are in GSTCoherentCosmology.lean; these checks diagnose
finite-state/table mistakes and do not replace the Lean proofs.
"""
from itertools import product


def two(d):
    return int(d == 2)


def mid(c, d):
    return (c // 2 + 2 * d) % 3


def out(c, d):
    return (c + 4 * d) % 3


def nxt(c, d):
    return (c + 4 * d) // 3


def kernel(a, d):
    o = (a + 2 * d) % 3
    return 14 * (two(o) - two(d)) + 7 * two(d) * two(o)


def uq(c):
    return 5 if c == 0 else 21 if c == 3 else 15


def mixed(c, d):
    return 8 * (kernel(c // 2, d) + kernel(c % 2, mid(c, d))) + 7 * (
        3 * uq(nxt(c, d)) - uq(c) - 24 * d
    )


def ont(c, d):
    digit_potential = [9, -35, -91]
    carry_potential = [0, 77, 154, 252]
    return (
        digit_potential[out(c, d)] - 7 * digit_potential[d]
        + carry_potential[c] - 3 * carry_potential[nxt(c, d)]
    )


def cell(r, p):
    return 4 * (r % 3**p) // 3**p, r // 3**p % 3


def current(r, p):
    return mixed(*cell(r, p)), ont(*cell(r, p))


def main():
    cells = list(product(range(4), range(3)))
    pairs = {c: (mixed(*c), ont(*c)) for c in cells}
    assert len(set(pairs.values())) == 12
    signatures = 0
    for k in range(1, 7):
        observed = {tuple(current(r, p) for p in range(k)) for r in range(3**k)}
        assert len(observed) == 3**k
        signatures += len(observed)
    checks = 0
    for digits in product(range(3), repeat=6):
        levels = [sum(digits[j] * 3**j for j in range(k)) for k in range(7)]
        for t in range(7):
            for p in range(5):
                c, d = cell(4**t * levels[p + 1], p)
                assert (c, d) == cell(4**t * levels[6], p)
                assert out(c, d) == cell(4**(t + 1) * levels[p + 1], p)[1]
                assert nxt(c, d) == cell(4**t * levels[p + 2], p + 1)[0]
                checks += 1
    print(f"PASS: 12 distinct cell signatures; {signatures} finite signatures; "
          f"{checks} realization and edge checks.")


if __name__ == "__main__":
    main()
