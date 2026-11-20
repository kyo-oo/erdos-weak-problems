#!/usr/bin/env python3
"""CHECKER-142 (W76-142E) — the THIRD, independent witness checker.

Deliberately different algorithm from both the Z3 engine (clausal feasibility)
and the C BnB (bitboard exclusion DFS): the PAIR-MIDPOINT SCAN.
A set W (0-based, subset of [0,N)) is 3-AP-free iff for every pair x < z in W
with x + z even, the integer midpoint (x+z)//2 is NOT in W.  This needs no AP
enumeration at all — it scans pairs and looks midpoints up in a hash set.

Also validates: distinctness, size == expected, bounds 0 <= v < N.
Self-test (soundness of the checker itself): planted APs must be flagged.
"""
from itertools import combinations


def check_witness(w, N, expected_size=None):
    """Return (ok, reason). w: iterable of 0-based vertices."""
    W = list(w)
    S = set(W)
    if len(W) != len(S):
        return False, "duplicate elements"
    if any(not (0 <= v < N) for v in W):
        return False, "element out of [0,N)"
    if expected_size is not None and len(W) != expected_size:
        return False, f"size {len(W)} != expected {expected_size}"
    # pair-midpoint scan: any 3-AP x<y<z has y=(x+z)/2 (x+z even).
    for x, z in combinations(sorted(S), 2):
        s = x + z
        if s & 1:
            continue
        y = s >> 1
        if y in S:
            return False, f"3-AP ({x},{y},{z}) present"
    return True, "3-AP-free by pair-midpoint scan"


def self_test():
    """Negative controls: every planted AP must be detected."""
    results = []
    # 1. genuine AP planted in an otherwise free set
    bad = [0, 1, 2, 4, 9]
    ok, why = check_witness(bad, 10, 5)
    results.append(("planted-AP-012", ok is False and "3-AP" in why))
    # 2. long-difference AP: (1, 5, 9) as the ONLY AP in the set
    bad2 = [0, 1, 5, 9]
    ok, why = check_witness(bad2, 10, 4)
    results.append(("planted-AP-159", ok is False and "(1,5,9)" in why))
    # 3. duplicate elements
    ok, why = check_witness([0, 1, 1], 10, 3)
    results.append(("duplicates", ok is False))
    # 4. out of bounds
    ok, why = check_witness([0, 1, 10], 10, 3)
    results.append(("out-of-bounds", ok is False))
    # 5. size mismatch
    ok, why = check_witness([0, 1, 3], 10, 4)
    results.append(("size-mismatch", ok is False))
    # 6. known-good witnesses must pass
    good = [0, 1, 3, 4, 9]           # 3-AP-free in [0,10)
    ok, why = check_witness(good, 10, 5)
    results.append(("good-passes", ok is True))
    good2 = [0, 1, 3, 7, 8]          # r_3(9) witness (Stanley-style)
    ok, why = check_witness(good2, 9, 5)
    results.append(("good2-passes", ok is True))
    return results


if __name__ == "__main__":
    res = self_test()
    for name, ok in res:
        print(("PASS " if ok else "FAIL ") + name)
    print("CHECKER142_SELF_TEST:", "GREEN" if all(ok for _, ok in res) else "RED")
