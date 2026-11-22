#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W82-142B STONE PRE-VERIFICATION MIRROR (D2 Lean-kernel support).

Mirrors EXACTLY the Bool checkers of DM142_Proof_B.lean (allT/memL/inRange/
chainLt/midFree3/k4Free/k5Free + the arsenal noTernaryTwoStruct bridge) so
that every `by decide` in the Lean kernel is guaranteed to evaluate to
`true` before the file ever reaches CI. Any FAIL here means the
corresponding Lean stone would fail: fix the data, not the mirror.

Usage: python3 engine142b_stones_mirror.py
Exit nonzero on any failure.
"""
import sys

# ---------------------------------------------------------------- mirrors


def allT(p, L):
    """allT p L = p a0 && p a1 && ... (short-circuit; result-only mirror)."""
    for a in L:
        if not p(a):
            return False
    return True


def memL(x, W):
    return x in W


def inRange(W, N):
    return allT(lambda x: (1 <= x) and (x <= N), W)


def chainLt(W):
    if not W:
        return True
    # ltHead a t = all(a < b for b in t); chainLt (a::t) = ltHead a t && chainLt t
    def ltHead(a, t):
        return allT(lambda b: a < b, t)
    def rec(L):
        if not L:
            return True
        a, t = L[0], L[1:]
        return ltHead(a, t) and rec(t)
    return rec(W)


def midFree3(W):
    # !(decide (x < z) && decide ((x+z)%2 == 0) && memL ((x+z)/2) W)
    return allT(lambda x: allT(
        lambda z: not ((x < z) and ((x + z) % 2 == 0) and memL((x + z) // 2, W)),
        W), W)


def k4Free(W):
    # !(2*x == w+y && 2*y == x+z && w != z)
    return allT(lambda w: allT(lambda x: allT(lambda y: allT(
        lambda z: not ((2 * x == w + y) and (2 * y == x + z) and (w != z)),
        W), W), W), W)


def k5Free(W):
    # !(2*p == u+q && 2*q == p+r && 2*r == q+s && u != s)
    return allT(lambda u: allT(lambda p: allT(lambda q: allT(lambda r: allT(
        lambda s: not ((2 * p == u + q) and (2 * q == p + r)
                       and (2 * r == q + s) and (u != s)),
        W), W), W), W), W)


def noTernaryTwoStruct(n, k):
    """Arsenal/CardinalWorlds.lean:51 (the decide-compatible structural
    twin of the Cantor reader noTernaryTwo, :41): base-3 digits avoid 2."""
    while True:
        if k == 0:
            return True
        if n == 0:
            return True
        if n % 3 == 2:
            return False
        n, k = n // 3, k - 1


# ---------------------------------------------------------------- witnesses
# The banked Behrend-fiber ladder (receipts142b_audit.txt B2, all PASS:
# witnesses 6@216, 12@1296, 30@7776, 90@46656, 6@1000, 24@10000, 12@2744,
# 48@38416, 2@324, 10@1024 — dual scanners + negative controls).

W216 = [8, 13, 38, 48, 73, 78]                    # (d,m)=(3,3), B=6, N=216
W1296 = [8, 13, 38, 48, 73, 78, 218, 228, 288, 433, 438, 468]      # (4,3)
W7776 = [44, 49, 79, 224, 229, 254, 264, 289, 294, 439, 469, 474, 1304,
         1309, 1334, 1344, 1369, 1374, 1514, 1524, 1584, 1729, 1734, 1764,
         2599, 2629, 2634, 2809, 2814, 2844]                        # (5,3)
W46656 = [266, 296, 301, 476, 481, 511, 1346, 1376, 1381, 1526, 1586, 1596,
          1736, 1741, 1766, 1776, 1801, 1806, 2636, 2641, 2671, 2816, 2821,
          2846, 2856, 2881, 2886, 3031, 3061, 3066, 7826, 7856, 7861, 8006,
          8066, 8076, 8216, 8221, 8246, 8256, 8281, 8286, 9086, 9146, 9156,
          9506, 9516, 9576, 10376, 10381, 10406, 10416, 10441, 10446, 10586,
          10596, 10656, 10801, 10806, 10836, 15596, 15601, 15631, 15776,
          15781, 15806, 15816, 15841, 15846, 15991, 16021, 16026, 16856,
          16861, 16886, 16896, 16921, 16926, 17066, 17076, 17136, 17281,
          17286, 17316, 18151, 18181, 18186, 18361, 18366, 18396]   # (6,3)
W1000 = [12, 21, 102, 120, 201, 210]                                 # (3,5)
W10000 = [123, 132, 213, 231, 312, 321, 1023, 1032, 1203, 1230, 1302, 1320,
          2013, 2031, 2103, 2130, 2301, 2310, 3012, 3021, 3102, 3120, 3201,
          3210]                                                     # (4,5)
W2744 = [61, 74, 230, 282, 412, 477, 789, 854, 984, 1036, 1192, 1205]  # (3,7)
W38416 = [649, 662, 831, 857, 1026, 1039, 3184, 3223, 3366, 3418, 3951,
          3964, 5732, 5771, 6096, 6161, 6681, 6707, 8293, 8306, 8462, 8514,
          8644, 8709, 9021, 9086, 9216, 9268, 9424, 9437, 11023, 11049,
          11569, 11634, 11959, 11998, 13766, 13779, 14312, 14364, 14507,
          14546, 16691, 16704, 16873, 16899, 17068, 17081]          # (4,7)
W324 = [1, 18]                                                     # (2,9)
W1024 = [5, 17, 20, 65, 68, 80, 257, 260, 272, 320]                 # (5,2)

# ---------------------------------------------------------------- the stones
# (name, witness, k, N, expected size)
STONES = [
    # k = 3 ladder (all ten banked fibers)
    ("r3_216_ge",   W216,   3, 216,   6),
    ("r3_1296_ge",  W1296,  3, 1296,  12),
    ("r3_7776_ge",  W7776,  3, 7776,  30),
    ("r3_46656_ge", W46656, 3, 46656, 90),
    ("r3_1000_ge",  W1000,  3, 1000,   6),
    ("r3_10000_ge", W10000, 3, 10000, 24),
    ("r3_2744_ge",  W2744,  3, 2744,  12),
    ("r3_38416_ge", W38416, 3, 38416, 48),
    ("r3_324_ge",   W324,   3, 324,    2),
    ("r3_1024_ge",  W1024,  3, 1024,  10),
    # k = 4 ladder (the cheap scans; the 24- and 30+-element fibers are
    # named out of the k=4 decide set honestly — see the worklog)
    ("r4_216_ge",   W216,   4, 216,   6),
    ("r4_324_ge",   W324,   4, 324,   2),
    ("r4_1024_ge",  W1024,  4, 1024, 10),
    ("r4_1000_ge",  W1000,  4, 1000,  6),
    ("r4_1296_ge",  W1296,  4, 1296, 12),
    ("r4_2744_ge",  W2744,  4, 2744, 12),
    # k = 5 ladder (only the 6-element and 2-element fibers: the 5-fold
    # nested scan on bigger witnesses exceeds the decide budget)
    ("r5_216_ge",   W216,   5, 216,   6),
    ("r5_324_ge",   W324,   5, 324,   2),
    ("r5_1000_ge",  W1000,  5, 1000,  6),
]


def main():
    lines = []
    fails = []

    def rec(name, ok, detail=""):
        lines.append("[%s] %s %s" % ("PASS" if ok else "FAIL", name, detail))
        if not ok:
            fails.append(name)

    # negative controls FIRST: the mirrors are non-vacuous.
    rec("NEG-midFree3-{1,2,3}", not midFree3([1, 2, 3]),
        "planted 3-AP detected by the midpoint mirror")
    rec("NEG-k4Free-{1,2,3,4}", not k4Free([1, 2, 3, 4]),
        "planted 4-AP detected by the two-equation mirror")
    rec("NEG-k5Free-{1,2,3,4,5}", not k5Free([1, 2, 3, 4, 5]),
        "planted 5-AP detected by the three-equation mirror")
    rec("NEG-chainLt-[1,1]", not chainLt([1, 1]), "dup detected")
    rec("NEG-inRange", not inRange([0, 5], 5), "0 out of [1,N] detected")
    rec("NEG-noTernaryTwoStruct-2", not noTernaryTwoStruct(2, 3),
        "2 has ternary digit 2: reader false")
    rec("OK-noTernaryTwoStruct-1", noTernaryTwoStruct(1, 2),
        "1 is ternary-1: reader true")

    for (name, W, k, N, m) in STONES:
        ok = (len(W) == m and chainLt(W) and inRange(W, N)
              and (k != 3 or midFree3(W))
              and (k != 4 or k4Free(W))
              and (k != 5 or k5Free(W)))
        rec(name, ok,
            "|W|=%d (want %d), N=%d, chainLt=%s, inRange=%s%s" %
            (len(W), m, N, chainLt(W), inRange(W, N),
             ("" if k == 3 else (", k4Free=%s" % k4Free(W) if k == 4
                                 else ", k5Free=%s" % k5Free(W)))))

    # the arsenal bridge: every (5,2)-fiber element FAILS the Cantor reader
    # (base-3 digit 2 somewhere) — the m=2 digit-fiber family is strictly
    # richer than the Cantor {0,1}-ternary family; decided in Lean via
    # noTernaryTwoStruct x (x+1).
    arsen = all(not noTernaryTwoStruct(x, x + 1) for x in W1024)
    rec("ARSENAL-w1024-not-cantor", arsen,
        "noTernaryTwoStruct x (x+1) = false for all 10 m=2-fiber elements")

    print("\n".join(lines))
    total = len([l for l in lines if not l.startswith("[INFO")])
    npass = len([l for l in lines if l.startswith("[PASS]")])
    print("STONE-MIRROR: %d/%d passed" % (npass, total))
    if fails:
        print("STONE-MIRROR-RED=1")
        print("FAILED:", fails)
        return 1
    print("STONE-MIRROR-GREEN=1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
