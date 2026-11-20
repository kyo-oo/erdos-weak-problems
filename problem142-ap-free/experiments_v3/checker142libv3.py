#!/usr/bin/env python3
"""CHECKER-142 V3 (W77-142E) — the THIRD, independent witness checker for
k-AP-free sets, k in {3,4,5}.

k=3: the banked pair-midpoint scan (checker142lib.py, W76) — for every pair
     x < z with x+z even, (x+z)/2 must not be in W.
k=4 (the midpoint-extension / pair-hypothesis scan, derived this wave):
     a 4-AP is (a, a+d, a+2d, a+3d); ANY two of its members determine it via
     a position hypothesis (i,j), 0 <= i < j <= 3: d = (z-x)/(j-i).  The
     checker scans every pair x < z of W and every hypothesis (i,j); whenever
     (z-x) is divisible by (j-i) it reconstructs a = x - i*d and tests the
     FULL quadruple {a, a+d, a+2d, a+3d} for membership.  No AP enumeration;
     complete because every 4-AP is caught through its own (A0,A1) pair under
     the (0,1) hypothesis (the remaining hypotheses are redundant belt and
     braces).
k=5: same with positions 0 <= i < j <= 4 and the full quintuple test.

Also validates distinctness, bounds 0 <= v < N, size == expected.
Self-test: planted k-APs must be flagged; good sets must pass; a set that is
4-AP-free but contains a 3-AP must PASS the k=4 check (specificity control).
"""
from itertools import combinations


def _hypotheses(k):
    return [(i, j) for i in range(k) for j in range(i + 1, k)]


_HYP = {k: _hypotheses(k) for k in (3, 4, 5)}


def check_witness_k(w, N, k, expected_size=None):
    """Return (ok, reason). w: 0-based vertices. k in {3,4,5}."""
    W = list(w)
    S = set(W)
    if len(W) != len(S):
        return False, "duplicate elements"
    if any(not (0 <= v < N) for v in W):
        return False, "element out of [0,N)"
    if expected_size is not None and len(W) != expected_size:
        return False, f"size {len(W)} != expected {expected_size}"
    if k == 3:
        # pair-midpoint scan (the banked independent algorithm)
        for x, z in combinations(sorted(S), 2):
            s = x + z
            if s & 1:
                continue
            if (s >> 1) in S:
                return False, f"3-AP ({x},{s >> 1},{z}) present"
        return True, "3-AP-free by pair-midpoint scan"
    # k in {4,5}: pair-hypothesis scan
    k1 = k - 1
    for x, z in combinations(sorted(S), 2):
        span = z - x
        for (i, j) in _HYP[k]:
            m = j - i
            if span % m:
                continue
            d = span // m
            a = x - i * d
            if a < 0 or a + k1 * d >= N:
                continue
            if all(a + t * d in S for t in range(k)):
                ap = tuple(a + t * d for t in range(k))
                return False, f"{k}-AP {ap} present"
    return True, f"{k}-AP-free by pair-hypothesis scan"


def check_witness(w, N, expected_size=None):
    """Backward-compatible k=3 entry (banked signature)."""
    return check_witness_k(w, N, 3, expected_size)


def self_test():
    """Negative controls: planted APs detected; good sets pass; specificity."""
    res = []
    # --- k=3 (banked battery) ---
    ok, why = check_witness_k([0, 1, 2, 4, 9], 10, 3, 5)
    res.append(("k3-planted-012", ok is False and "3-AP" in why))
    ok, why = check_witness_k([0, 1, 5, 9], 10, 3, 4)
    res.append(("k3-planted-159", ok is False and "(1,5,9)" in why))
    ok, why = check_witness_k([0, 1, 3, 4, 9], 10, 3, 5)
    res.append(("k3-good-passes", ok is True))
    # --- k=4 ---
    ok, why = check_witness_k([0, 1, 2, 3, 9], 10, 4, 5)          # (0,1,2,3)
    res.append(("k4-planted-0123", ok is False and "(0, 1, 2, 3)" in why))
    ok, why = check_witness_k([0, 1, 2, 9, 13], 14, 4, 5)         # (1,5,9,13)? no 5
    # plant a long 4-AP: (0, 4, 8, 12) with decoys
    ok, why = check_witness_k([0, 4, 8, 12, 1], 13, 4, 5)
    res.append(("k4-planted-04812", ok is False and "(0, 4, 8, 12)" in why))
    # non-consecutive-difference plant: (1, 4, 7, 10)
    ok, why = check_witness_k([1, 4, 7, 10, 2], 11, 4, 5)
    res.append(("k4-planted-14710", ok is False and "(1, 4, 7, 10)" in why))
    # 3-AP present but NO 4-AP -> k=4 check must PASS (specificity!)
    ok, why = check_witness_k([0, 1, 2, 9], 10, 4, 4)
    res.append(("k4-3AP-only-passes", ok is True))
    # a 3-AP-free set is automatically 4-AP-free
    ok, why = check_witness_k([0, 1, 3, 7, 8], 9, 4, 5)
    res.append(("k4-stanley-passes", ok is True))
    # 5-AP-free set containing a 4-AP must FAIL k=4 but PASS k=5
    ok4, _ = check_witness_k([0, 1, 2, 3, 9, 11], 12, 4, 6)
    ok5, _ = check_witness_k([0, 1, 2, 3, 9, 11], 12, 5, 6)
    res.append(("k4vs5-disjoint", ok4 is False and ok5 is True))
    # --- k=5 ---
    ok, why = check_witness_k([0, 1, 2, 3, 4, 9], 10, 5, 6)       # (0..4)
    res.append(("k5-planted-01234", ok is False and "(0, 1, 2, 3, 4)" in why))
    ok, why = check_witness_k([0, 2, 4, 6, 8, 1], 9, 5, 6)        # (0,2,4,6,8)
    res.append(("k5-planted-02468", ok is False and "(0, 2, 4, 6, 8)" in why))
    # 4-AP present, no 5-AP -> k=5 PASS (specificity)
    ok, why = check_witness_k([0, 1, 2, 3, 9], 10, 5, 5)
    res.append(("k5-4AP-only-passes", ok is True))
    # duplicates / bounds / size
    res.append(("duplicates", check_witness_k([0, 1, 1], 10, 4, 3)[0] is False))
    res.append(("out-of-bounds", check_witness_k([0, 1, 10], 10, 4, 3)[0] is False))
    res.append(("size-mismatch", check_witness_k([0, 1, 3], 10, 4, 4)[0] is False))
    return res


if __name__ == "__main__":
    r = self_test()
    for name, ok in r:
        print(("PASS " if ok else "FAIL ") + name)
    print("CHECKER142V3_SELF_TEST:", "GREEN" if all(ok for _, ok in r) else "RED")
