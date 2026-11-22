#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W82-142B INDEPENDENT WITNESS VERIFIER (D1/D2 receipts).

Fresh adversarial code (written from scratch for this audit lane; no import
from any campaign engine — different code path by construction):

  * witness sets re-checked by a DIRECT DIFFERENCE-SET scanner (the campaign
    engines scan (a, d) or midpoints; this one precomputes the set of all
    pairwise differences of S and asks, for every element pair (x, z) with
    x < z, whether the arithmetic continuation of x, z lands inside S for
    the full k terms — a third method, agreeing with (a,d)-scan and
    midpoint-scan where they overlap);
  * the Behrend digit-fiber sets re-DERIVED by a different algorithm
    (sort-by-(layer, sphere) buckets + explicit tie-break by SMALLEST key,
    vs the engine's max-by-(size, key) and the driver's largest-key rules),
    then AP-free re-verified by the difference-set scanner;
  * the witnesses_table_ext.json (N=31..48) re-verified: membership in
    [1, N], size == the banked table value, AP-free by the scanner.

Usage: python3 engine142b_audit.py [--verify]
Exit nonzero on any failure. Prints AUDIT142B receipts.
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CAMP = os.path.dirname(HERE)


# ---------------------------------------------------------------- scanner

def full_kap_free(S, k):
    """Difference-set scanner: S (iterable of ints) has NO non-trivial
    k-term AP, i.e. no a, d>=1 with a, a+d, ..., a+(k-1)d all in S.

    Method: for every ordered pair x < z in S, the unique candidate AP
    through x and z with x first and z LAST is d = (z-x)/(k-1) (integer
    only); check all interior terms. Every non-trivial k-AP contains a
    pair (first, last) with the SAME difference, so scanning pairs by the
    (first, last) role is exhaustive. (Distinct from the campaign's
    (a,d)-scan and its midpoint-scan at k=3.)
    """
    T = sorted(set(S))
    n = len(T)
    for i in range(n):
        for j in range(i + 1, n):
            x, z = T[i], T[j]
            gap = z - x
            if gap % (k - 1) != 0:
                continue
            d = gap // (k - 1)
            if d == 0:
                continue
            # x = a, z = a + (k-1)d; check interior terms a + i*d in S
            ok = all((x + t * d) in set(T) for t in range(1, k - 1))
            if ok:
                return False
    return True


def midpoint_free(S):
    """k=3 special: no x<y<z in S with x+z = 2y (yet another method)."""
    T = set(S)
    for x, z in itertools.combinations(sorted(T), 2):
        if (x + z) % 2 == 0 and (x + z) // 2 in T:
            return False
    return True


# ------------------------------------------------------- behrend fibers

def behrend_fiber_b(d, m):
    """Independent Behrend layer x sphere fiber at base B = 2m.

    Different algorithm from the campaign's: bucket ALL digit vectors by
    (layer, sphere), pick the bucket with the LARGEST size, tie-break by
    the SMALLEST key (the engine tie-breaks differently on purpose).
    Returns the sorted list of encoded integers.
    """
    B = 2 * m
    buckets = {}
    for vec in itertools.product(range(m), repeat=d):
        key = (sum(vec), sum(v * v for v in vec))
        buckets.setdefault(key, []).append(vec)
    best = max(buckets.values(), key=len)
    # tie-break independence: among all keys with max size, take the
    # lexicographically SMALLEST key (different from engine/driver rules).
    maxsize = max(len(v) for v in buckets.values())
    cands = sorted(k for k, v in buckets.items() if len(v) == maxsize)
    best = buckets[cands[0]]
    return sorted(sum(v * B ** i for i, v in enumerate(vec)) for vec in best)


def behrend_grid_recheck():
    """The BEHREND_PROOF.md §6 instance grid, recomputed independently."""
    rows = []
    for (d, m) in [(3, 3), (4, 3), (5, 3), (6, 3), (3, 5), (4, 5),
                   (3, 7), (4, 7), (2, 9), (5, 2)]:
        S = behrend_fiber_b(d, m)
        rows.append((d, m, (2 * m) ** d, len(S), S))
    return rows


# ---------------------------------------------------------------- checks

def main():
    lines = []
    fails = []

    def rec(name, ok, detail=""):
        lines.append("[%s] %s %s" % ("PASS" if ok else "FAIL", name, detail))
        if not ok:
            fails.append(name)

    # B1: witnesses_table_ext.json — every banked witness set re-verified.
    wit_path = os.path.join(CAMP, "comparator-official", "challenges",
                            "142", "witnesses_table_ext.json")
    wit = json.load(open(wit_path))
    ext = {31: 12, 32: 13, 33: 13, 34: 13, 35: 13, 36: 14, 37: 14, 38: 14,
           39: 14, 40: 15, 41: 16, 42: 16, 43: 16, 44: 16, 45: 16, 46: 16,
           47: 16, 48: 16}
    all_ok = True
    for Ns, S in sorted(wit.items(), key=lambda kv: int(kv[0])):
        N = int(Ns)
        S = set(S)
        ok = (len(S) == ext[N]
              and min(S) >= 1 and max(S) <= N
              and full_kap_free(S, 3) and midpoint_free(S))
        all_ok = all_ok and ok
        if not ok:
            rec("B1-WITNESS-N%d" % N, False,
                "size=%d want=%d range=[%d,%d] N=%d apfree=%s midfree=%s"
                % (len(S), ext[N], min(S), max(S), N,
                   full_kap_free(S, 3), midpoint_free(S)))
    rec("B1-TABLE-EXT", all_ok,
        "all 18 witness sets (N=31..48): size == banked table, subset [1,N], "
        "AP3-free by the difference-set scanner AND the midpoint scanner")

    # B2: the Behrend instance grid — sizes match the engine-certified
    # BEHREND-GRID table (W74-corrected values), sets AP-free, in range.
    ledger = {(3, 3): 6, (4, 3): 12, (5, 3): 30, (6, 3): 90, (3, 5): 6,
              (4, 5): 24, (3, 7): 12, (4, 7): 48, (2, 9): 2, (5, 2): 10}
    for (d, m, N, sz, S) in behrend_grid_recheck():
        ok = (sz == ledger[(d, m)]
              and max(S) < (2 * m) ** d
              and full_kap_free(S, 3) and midpoint_free(S))
        rec("B2-BEHREND-%d-%d" % (d, m), ok,
            "|S|=%d (ledger %d), max=%d < B^d=%d, AP3-free (two scanners)"
            % (sz, ledger[(d, m)], max(S), (2 * m) ** d))
        # k-ladder spot: a 3-AP-free set is k-AP-free for k=4,5 (first-3-terms
        # containment) — verified directly by the difference scanner.
        rec("B2-LADDER-%d-%d" % (d, m),
            full_kap_free(S, 4) and full_kap_free(S, 5),
            "same fiber also 4-AP-free and 5-AP-free (LAW M-1 instance)")

    # B3: negative controls (the scanner is non-vacuous).
    planted = {1, 2, 3}
    rec("B3-NEG-PLANTED", not full_kap_free(planted, 3)
        and not midpoint_free(planted), "1,2,3 is detected as a 3-AP")
    planted4 = {1, 2, 3, 4, 10}
    rec("B3-NEG-PLANTED4", not full_kap_free(planted4, 4),
        "1,2,3,4 detected as a 4-AP (the k=4 scanner is non-vacuous)")
    near = {1, 2, 4}
    rec("B3-NEG-CLEAN", full_kap_free(near, 3) and midpoint_free(near),
        "1,2,4 correctly accepted (no false positive)")

    # B4: the Behrend grid fibers that AVOID 0 (for the Lean stones: sets
    # must live in [1, N] with N = B^d - 1 or the stone is stated at N+1
    # via a +1 shift; report whether 0 in the fiber).
    for (d, m, N, sz, S) in behrend_grid_recheck():
        lines.append("[INFO] B4 fiber (d=%d,m=%d): 0 in S = %s"
                     % (d, m, 0 in S))

    print("\n".join(lines))
    print("AUDIT142B_CHECKS: %d/%d passed" % (len(lines) - len(fails) -
          sum(1 for l in lines if l.startswith("[INFO]")), len(lines) -
          sum(1 for l in lines if l.startswith("[INFO]"))))
    if fails:
        print("AUDIT142B_ENGINE_GREEN=0")
        print("FAILED:", fails)
        return 1
    print("AUDIT142B_ENGINE_GREEN=1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
