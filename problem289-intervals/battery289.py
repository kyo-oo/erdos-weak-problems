#!/usr/bin/env python3
# battery289.py — THE LEAN-MIRROR BATTERY for Erdos289.lean (Kernel 64, E289).
#
# House law: every decide theorem in the Lean kernel is pre-verified here,
# with EXACT integer arithmetic mirroring the Lean defs 1:1 (no Fractions
# needed — everything is the cross-multiplied Nat encoding):
#
#   iprod a b   = product of [a..b]            (empty window -> 1)
#   inum  a b   = numerator of sum_{i in [a,b]} 1/i over denominator iprod a b
#   covers2 a b c d  :=  inum a b * iprod c d + inum c d * iprod a b
#                        = iprod a b * iprod c d     (sigma(a,b)+sigma(c,d)=1)
#   longWindow a b  :=  2 <= b + 1 - a          (|I| >= 2, the #289 constraint)
#
# Sections (each maps to a named Lean theorem):
#   S1  e289_anchor_values        (the five HM windows, exact fractions)
#   S2  e289_hm_family            (k=5 total-2 witness: shape + identity)
#   S3  e289_census_k1_le12       (no window in [2,12] sums to 1)
#   S4  e289_census_k2_gapped_le12 / adjacent / e289_no_pair_any_le12
#   S5  join_adjacent + adjacent_collapse + covers2_comm (structural checks)
#   S6  THE ENGINE FRONTIER at M=240: k=1 and k=2 (gapped AND adjacent)
#       exclusions, by two independent methods (crossing search + brute force
#       cross-check at M=80), mirroring engine289_round1.py's certified claim.

M_ENG = 240   # the engine's certified bound (engine289_round1.py)
M_TAB = 240   # shared exact-rational table bound

out = []
def P(*xs):
    line = " ".join(str(x) for x in xs)
    out.append(line)
    print(line)

def iprod(a, b):
    r = 1
    for i in range(a, b + 1):
        r *= i
    return r

def inum(a, b):
    if b < a:
        return 0
    h, p = 0, 1
    for i in range(a, b + 1):
        h = h * i + p
        p = p * i
    return h

def covers2(a, b, c, d):
    return inum(a, b) * iprod(c, d) + inum(c, d) * iprod(a, b) == iprod(a, b) * iprod(c, d)

def longWindow(a, b):
    return 2 <= b + 1 - a

# THE SHARED TABLE: (a,b) -> (inum a b, iprod a b), built incrementally.
tab = {}
for a in range(1, M_TAB + 1):
    h, p = 0, 1
    for b in range(a, M_TAB + 1):
        h = h * b + p
        p = p * b
        tab[(a, b)] = (h, p)

# sanity of the table against the fresh defs
for (a, b) in [(2, 7), (9, 10), (17, 18), (34, 35), (84, 85), (3, 11), (5, 40)]:
    assert tab[(a, b)] == (inum(a, b), iprod(a, b)), (a, b)

# ---------- S1 anchors (theorem e289_anchor_values) ----------
P("S1 anchors:",
  "inum 2 7 =", inum(2, 7), "iprod 2 7 =", iprod(2, 7),
  "inum 9 10 =", inum(9, 10), "iprod 9 10 =", iprod(9, 10),
  "inum 17 18 =", inum(17, 18), "iprod 17 18 =", iprod(17, 18),
  "inum 34 35 =", inum(34, 35), "iprod 34 35 =", iprod(34, 35),
  "inum 84 85 =", inum(84, 85), "iprod 84 85 =", iprod(84, 85))
assert tab[(2, 7)] == (8028, 5040)
assert tab[(9, 10)] == (19, 90)
assert tab[(17, 18)] == (35, 306)
assert tab[(34, 35)] == (69, 1190)
assert tab[(84, 85)] == (169, 7140)

# ---------- S2 the HM k=5 total-2 family (theorem e289_hm_family) ----------
FAM = [(2, 7), (9, 10), (17, 18), (34, 35), (84, 85)]
P("S2 HM family shape: longWindow:", [longWindow(a, b) for (a, b) in FAM],
  "gaps:", [FAM[i][1] + 1 < FAM[i + 1][0] for i in range(4)])
assert all(longWindow(a, b) for (a, b) in FAM)
assert all(FAM[i][1] + 1 < FAM[i + 1][0] for i in range(4))
lhs = (inum(2, 7) * (iprod(9, 10) * iprod(17, 18) * iprod(34, 35) * iprod(84, 85))
       + inum(9, 10) * (iprod(2, 7) * iprod(17, 18) * iprod(34, 35) * iprod(84, 85))
       + inum(17, 18) * (iprod(2, 7) * iprod(9, 10) * iprod(34, 35) * iprod(84, 85))
       + inum(34, 35) * (iprod(2, 7) * iprod(9, 10) * iprod(17, 18) * iprod(84, 85))
       + inum(84, 85) * (iprod(2, 7) * iprod(9, 10) * iprod(17, 18) * iprod(34, 35)))
rhs = 2 * (iprod(2, 7) * iprod(9, 10) * iprod(17, 18) * iprod(34, 35) * iprod(84, 85))
P("S2 HM total-2 identity:", lhs, "==", rhs, "->", lhs == rhs)
assert lhs == rhs

# ---------- S3 k=1 census mirror (theorem e289_census_k1_le12) ----------
bad_k1 = [(a, b) for a in range(0, 13) for b in range(0, 13)
          if 2 <= a and a <= b and inum(a, b) == iprod(a, b)]
P("S3 k=1 census <= 12 (windows summing to 1):", bad_k1)
assert bad_k1 == []

# ---------- S4 k=2 census mirrors at 12 ----------
bad_gap = [(a, b, c, d) for a in range(0, 13) for b in range(0, 13)
           for c in range(0, 13) for d in range(0, 13)
           if 2 <= a and a + 1 <= b and b + 1 < c and c + 1 <= d and covers2(a, b, c, d)]
P("S4 k=2 gapped census <= 12:", bad_gap)
assert bad_gap == []

bad_adj = [(a, b, d) for a in range(0, 13) for b in range(0, 13) for d in range(0, 13)
           if 2 <= a and a + 1 <= b and b + 2 <= d and covers2(a, b, b + 1, d)]
P("S4 k=2 adjacent census <= 12:", bad_adj)
assert bad_adj == []

bad_any = [(a, b, c, d) for a in range(0, 13) for b in range(0, 13)
           for c in range(0, 13) for d in range(0, 13)
           if 2 <= a and a + 1 <= b and b < c and c + 1 <= d and covers2(a, b, c, d)]
P("S4 k=2 COMPLETE classification <= 12 (adjacent + gapped):", bad_any)
assert bad_any == []

# ---------- S5 structural laws, full-range checks ----------
JB = 60
bad_join = []
for a in range(1, JB + 1):
    for b in range(a, JB + 1):
        for d in range(b + 1, JB + 1):
            Na, Da = tab[(a, d)]
            Nb, Db = tab[(a, b)]
            Nc, Dc = tab[(b + 1, d)]
            L = Na * (Db * Dc)
            R = (Nb * Dc + Nc * Db) * Da
            if L != R:
                bad_join.append((a, b, d))
P("S5 join_adjacent violations (a<=b<d<=%d):" % JB, bad_join)
assert bad_join == []

CB = 200
bad_collapse = []
for a in range(1, CB + 1):
    for b in range(a, CB + 1):
        for d in range(b + 1, CB + 1):
            cov = (tab[(a, b)][0] * tab[(b + 1, d)][1] + tab[(b + 1, d)][0] * tab[(a, b)][1]
                   == tab[(a, b)][1] * tab[(b + 1, d)][1])
            if cov != (tab[(a, d)][0] == tab[(a, d)][1]):
                bad_collapse.append((a, b, d))
P("S5 adjacent_collapse iff violations (a<=b<d<=%d):" % CB, bad_collapse)
assert bad_collapse == []

sym_bad = [(a, b, c, d) for a in range(0, 10) for b in range(0, 10)
           for c in range(0, 10) for d in range(0, 10)
           if covers2(a, b, c, d) != covers2(c, d, a, b)]
P("S5 covers2_comm violations <= 10:", sym_bad)
assert sym_bad == []

# ---------- S6 THE ENGINE FRONTIER at M=240 ----------
# S6a: k=1 exclusion at M=240 (no window [a,b] in [2,240] with sigma = 1).
bad_k1_240 = [(a, b) for (a, b), (h, p) in tab.items()
              if 2 <= a and a + 1 <= b and h == p]
P("S6a k=1 census <= 240 (windows summing to 1):", bad_k1_240)
assert bad_k1_240 == []

# S6b: k=2 gapped exclusion at M=240 by the crossing method.
# For a first window W1 (sigma1 = N1/D1 <= 1) the target for W2 is
# (D1-N1)/D1; sigma2(a2,b2) is STRICTLY increasing in b2, so for each
# (W1, a2) there is at most one candidate b2 — the largest with
# sigma2 <= target — checked exactly.  Complete by monotonicity.
def search_largest(a2, TN, TD, M):
    # largest b2 in [a2+1, M] with sigma2(a2,b2) <= TN/TD; a2 if none.
    lo, hi = a2, M
    while lo < hi:
        mid = (lo + hi + 1) // 2
        N2, D2 = tab[(a2, mid)]
        if N2 * TD <= TN * D2:
            lo = mid
        else:
            hi = mid - 1
    return lo

def k2_gapped_crossing(M, record):
    for (a1, b1), (N1, D1) in tab.items():
        if b1 > M or b1 < a1 + 1:  # stay inside [2,M]; length >= 2 required
            continue
        if a1 < 2:
            continue
        if N1 > D1:      # sigma1 > 1: impossible in any sum-to-1 pair
            continue
        TN, TD = D1 - N1, D1
        for a2 in range(b1 + 2, M):  # non-adjacent + a2 has room for b2 = a2+1 <= M
            lo = search_largest(a2, TN, TD, M)
            if lo >= a2 + 1:
                N2, D2 = tab[(a2, lo)]
                if N2 * TD == TN * D2:
                    record.append((a1, b1, a2, lo))

# S6b': POSITIVE validation of the crossing machinery: a window's own sum
# used as the target must be found exactly by the search (largest b2' with
# sigma2 <= target IS b2 by strict monotonicity, and the equality check
# fires there — exactly the mechanism the k=2 exclusion relies on).
val_hits, val_miss = 0, 0
for a2 in range(2, 30):
    for b2 in range(a2 + 1, 30):
        N2, D2 = tab[(a2, b2)]
        lo = search_largest(a2, N2, D2, 30)
        if lo == b2 and tab[(a2, lo)][0] * D2 == N2 * tab[(a2, lo)][1]:
            val_hits += 1
        else:
            val_miss += 1
P("S6b' crossing machinery validation: hits =", val_hits, "misses =", val_miss)
assert val_miss == 0 and val_hits > 0

witnesses_cross_240 = []
k2_gapped_crossing(M_ENG, witnesses_cross_240)
P("S6b k=2 gapped witnesses <= 240 (crossing method):", witnesses_cross_240)
assert witnesses_cross_240 == []

# S6c: brute-force cross-check of the crossing method at M=80.
def k2_gapped_brute(M):
    res = []
    for a1 in range(2, M + 1):
        for b1 in range(a1 + 1, M + 1):
            N1, D1 = tab[(a1, b1)]
            if N1 > D1:
                break  # sigma(a1,b1) is increasing in b1
            for a2 in range(b1 + 2, M + 1):
                for b2 in range(a2 + 1, M + 1):
                    N2, D2 = tab[(a2, b2)]
                    if N2 > D2:
                        break
                    if N1 * D2 + N2 * D1 == D1 * D2:
                        res.append((a1, b1, a2, b2))
    return res

brute_80 = k2_gapped_brute(80)
cross_80 = []
k2_gapped_crossing(80, cross_80)
P("S6c k=2 gapped witnesses <= 80 (brute):", brute_80,
  "| (crossing):", cross_80, "| methods agree:", brute_80 == cross_80)
assert brute_80 == [] and cross_80 == []

# S6d: k=2 adjacent exclusion at M=240 — by the collapse law (verified in S5)
# it equals the k=1 exclusion (verified in S6a); direct brute check at M=80:
bad_adj_80 = [(a1, b1, d) for a1 in range(2, 79) for b1 in range(a1 + 1, 78)
              for d in range(b1 + 2, 81) if covers2(a1, b1, b1 + 1, d)]
P("S6d k=2 adjacent witnesses <= 80 (brute):", bad_adj_80)
assert bad_adj_80 == []

P("BATTERY289_ALL_GREEN")

with open("battery289_output.txt", "w") as f:
    f.write("\n".join(out) + "\n")
print("wrote battery289_output.txt")
