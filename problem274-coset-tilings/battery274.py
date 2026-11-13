#!/usr/bin/env python3
# W57-4 battery: Erdos #274 coset tilings — cyclic census n <= 12 (curiosity to 36).
# Mirrors the Lean search (divisor-subset candidates + shift assignment cover check)
# and cross-checks with an INDEPENDENT set-based disjointness formulation.
# Model: C_n = Z/n. Subgroup of order s (s | n) = multiples of n/s (the unique such
# subgroup); its coset with shift c (0 <= c < n/s) = {x < n : x % (n/s) == c}, size s.
# A distinct-size coset tiling = pick distinct sizes s_i | n, sum s_i = n, k >= 2,
# and shifts c_i so the cosets are pairwise disjoint (then they cover).

import itertools

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def cover_count_ok(n, pairs):
    """Lean mirror: every x < n lies in exactly one coset."""
    for x in range(n):
        cnt = sum(1 for (s, c) in pairs if x % (n // s) == c)
        if cnt != 1:
            return False
    return True

def disjoint_sets_ok(n, pairs):
    """Independent check: residue-class sets pairwise disjoint."""
    sets_ = [frozenset(x for x in range(n) if x % (n // s) == c) for (s, c) in pairs]
    tot = 0
    seen = set()
    for S in sets_:
        tot += len(S)
        seen |= S
    return tot == len(seen) and tot == n

def sum_subsets_matching(n, divs):
    """All sublists (as index subsets) of the ascending divisor list with distinct
    entries, length >= 2, summing to n. (Divisor list entries are already distinct.)"""
    out = []
    for r in range(2, len(divs) + 1):
        for comb in itertools.combinations(divs, r):
            if sum(comb) == n:
                out.append(list(comb))
    return out

def cyclic_tilings(n):
    """All genuine distinct-size coset tilings of C_n (list of pair-lists)."""
    hits = []
    for S in sum_subsets_matching(n, divisors(n)):
        ranges = [range(n // s) for s in S]
        for shifts in itertools.product(*ranges):
            pairs = list(zip(S, shifts))
            if cover_count_ok(n, pairs) and disjoint_sets_ok(n, pairs):
                hits.append(pairs)
    return hits

def two_coset_scan(limit):
    """No two divisors a < b of n with a + b = n (a,b positive, both dividing n)."""
    bad = []
    for n in range(1, limit + 1):
        for a in range(1, n):
            b = n - a
            if a < b and n % a == 0 and n % b == 0:
                bad.append((n, a, b))
    return bad

def main():
    # 1. The two-coset arithmetic impossibility, scanned to 200 (Lean: full theorem).
    bad = two_coset_scan(200)
    print("TWO-COSET: no distinct proper divisor pairs a<b with a+b=n, n<=200:",
          "CONFIRMED" if not bad else f"REFUTED {bad}")

    # 2. The decide-census scope: cyclic groups C_n, n <= 12 — expect ZERO tilings.
    allneg = True
    for n in range(0, 13):
        hits = cyclic_tilings(n)
        if hits:
            allneg = False
            print(f"  C_{n}: TILING FOUND: {hits}")
    print("CYCLIC CENSUS n<=12 (distinct sizes, k>=2):",
          "ALL NEGATIVE" if allneg else "POSITIVE INSTANCE FOUND")

    # 3. Arithmetic feasibility layer: distinct divisor subsets summing to n, n<=12.
    feas = {n: sum_subsets_matching(n, divisors(n)) for n in range(1, 13)}
    for n, Ss in feas.items():
        if Ss:
            print(f"  arithmetic candidates n={n}: {Ss}")

    # 4. Curiosity: cyclic census up to 36 (matches campaign abelian<=36 negative claim).
    hits36 = {n: cyclic_tilings(n) for n in range(13, 37)}
    pos36 = {n: h for n, h in hits36.items() if h}
    print("CYCLIC CENSUS 13<=n<=36:",
          "ALL NEGATIVE" if not pos36 else f"POSITIVE: {pos36}")

    # 5. Cross-check C_6 and C_12 exhaustively by hand-listed candidate sizes.
    assert sum_subsets_matching(6, divisors(6)) == [[1, 2, 3]]
    assert sum_subsets_matching(12, divisors(12)) in ([[1, 2, 3, 6], [2, 4, 6]],
                                                       [[2, 4, 6], [1, 2, 3, 6]])
    print("C_6 candidate sizes = [[1,2,3]]; C_12 = [[1,2,3,6],[2,4,6]]  OK")
    print("BATTERY274_GREEN")

if __name__ == "__main__":
    main()
