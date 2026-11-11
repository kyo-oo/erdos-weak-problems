#!/usr/bin/env python3
"""BATTERY 711 — independent verification for the Erdos711 kernel (S034).

f(n,m) = minimal F such that the open interval (m, m+F) contains distinct
a_1..a_n with k | a_k for all k <= n.

GREEN requires:
(A) FULL-PERIOD census n=2..12: every m in one full period lcm(1..n) is
    matchable in a (2n-2)-integer window  =>  max_m f(n,m) <= 2n-1
    (dual method: greedy certificate first, exact Kuhn matching on failure);
(B) the forced-collision obstruction at m=(n-1)^2, n=2..15: NOT matchable
    in the (2n-3)-window, and the multiples of n and n-1 in the window are
    both EXACTLY {n^2-n};
(C) the fourteen embedded Lean witness lists re-verified by DIRECT
    arithmetic (divisibility, distinctness, bounds — no matching involved);
(D) f(n,(n-1)^2) = 2n-1 exact for n=2..15; f(n,n) for n=2..12;
(E) periodicity spot-checks f(n,m) = f(n,m+L).
"""
import sys
from math import gcd

def lcm_upto(n):
    L = 1
    for k in range(1, n + 1):
        L = L * k // gcd(L, k)
    return L

def matchable(n, m, win):
    """Window integers m+1..m+win. Greedy certificate; exact Kuhn fallback."""
    if win < n:
        return None
    lo, hi = m + 1, m + win
    used = set()
    assign = {}
    ok = True
    for k in range(n, 1, -1):
        v = (hi // k) * k
        while v >= lo and v in used:
            v -= k
        if v < lo:
            ok = False
            break
        used.add(v)
        assign[k] = v
    if ok:
        for v in range(lo, hi + 1):
            if v not in used:
                assign[1] = v
                return assign
        ok = False
    if not ok:
        # exact bipartite matching (Kuhn) on keys 2..n, then key 1
        matchR = {}
        def try_k(k, seen):
            v = ((lo + k - 1) // k) * k
            while v <= hi:
                if v not in seen:
                    seen.add(v)
                    if v not in matchR or try_k(matchR[v], seen):
                        matchR[v] = k
                        return True
                v += k
            return False
        for k in range(n, 1, -1):
            if not try_k(k, set()):
                return None
        for v in range(lo, hi + 1):
            if v not in matchR:
                return {k: v for v, k in matchR.items()} | {1: v}
        return None
    return None

def f711(n, m):
    F = n + 1
    while True:
        if matchable(n, m, F - 1) is not None:
            return F
        F += 1

fails = 0

# (A) full-period census
print("(A) full-period census n=2..12 (all m matchable in 2n-2 window)")
for n in range(2, 13):
    L = lcm_upto(n)
    bad = []
    for m in range(1, L + 1):
        if matchable(n, m, 2 * n - 2) is None:
            bad.append(m)
            if len(bad) >= 3:
                break
    if bad:
        print(f"  n={n}: LAW BROKEN at m={bad}")
        fails += 1
    else:
        print(f"  n={n:2d} L={L:6d}: max_m f(n,m) <= 2n-1 CONFIRMED")

# (B) forced collision at (n-1)^2
print("(B) forced-collision obstruction n=2..15")
for n in range(2, 16):
    m = (n - 1) * (n - 1)
    lo, hi = m + 1, n * n - 2
    mult_n = [v for v in range(lo, hi + 1) if v % n == 0]
    mult_n1 = [v for v in range(lo, hi + 1) if v % (n - 1) == 0]
    forced = (mult_n == [n * n - n]) and (mult_n1 == [n * n - n])
    no_low = matchable(n, m, 2 * n - 3) is None
    if not (forced and no_low):
        print(f"  n={n}: FAIL (forced={forced} obstructed={no_low})")
        fails += 1
    else:
        print(f"  n={n:2d}: both keys n, n-1 forced onto {n*n-n}; f >= 2n-1 = {2*n-1}")

# (C) the fourteen Lean witness lists (direct arithmetic — no matching)
WIT = {
    2: (1, [3, 2]),
    3: (4, [5, 8, 6]),
    4: (9, [10, 14, 15, 12]),
    5: (16, [17, 22, 21, 24, 20]),
    6: (25, [26, 34, 33, 32, 35, 30]),
    7: (36, [37, 46, 39, 44, 45, 48, 42]),
    8: (49, [50, 62, 57, 52, 55, 60, 63, 56]),
    9: (64, [65, 74, 69, 76, 75, 78, 77, 80, 72]),
    10: (81, [82, 94, 93, 92, 95, 84, 98, 96, 99, 90]),
    11: (100, [101, 118, 111, 116, 115, 114, 119, 112, 117, 120, 110]),
    12: (121, [122, 142, 141, 128, 130, 138, 133, 136, 135, 140, 143, 132]),
    13: (144, [145, 166, 159, 164, 155, 150, 161, 152, 162, 160, 165, 168, 156]),
    14: (169, [170, 194, 183, 188, 185, 186, 175, 184, 189, 190, 187, 192, 195, 182]),
    15: (196, [197, 218, 219, 212, 215, 222, 217, 208, 207, 200, 220, 216, 221, 224, 210]),
}
print("(C) fourteen Lean witnesses re-verified by direct arithmetic")
for n, (m, asl) in WIT.items():
    ok = (len(asl) == n
          and all(m < a < m + 2 * n - 1 for a in asl)
          and all(a % (i + 1) == 0 for i, a in enumerate(asl))
          and len(set(asl)) == n)
    if not ok:
        print(f"  n={n}: WITNESS FAIL {asl}")
        fails += 1
    else:
        print(f"  n={n:2d}: witness OK (a_1..a_n in ({m}, {m + 2*n - 1}), distinct, k|a_k)")

# (D) exactness + f(n,n)
print("(D) exact frontier n=2..15 and f(n,n) n=2..12")
for n in range(2, 16):
    m = (n - 1) * (n - 1)
    v = f711(n, m)
    if v != 2 * n - 1:
        print(f"  n={n}: f({n},{m}) = {v} != {2*n-1} FAIL")
        fails += 1
    else:
        print(f"  n={n:2d}: f({n},{m}) = {v} = 2n-1 EXACT")
for n in range(2, 13):
    v = f711(n, n)
    print(f"  f({n},{n}) = {v}")

# (E) periodicity spot-checks
print("(E) periodicity f(n,m) = f(n,m+L)")
pbad = 0
for n in range(2, 11):
    L = lcm_upto(n)
    for m in [1, 7, 40, 97, 233, 500, 997, 2003]:
        if m > L:
            continue
        if f711(n, m) != f711(n, m + L):
            print(f"  n={n} m={m}: PERIODICITY FAIL")
            pbad += 1
print(f"  periodicity spot-checks done (fails: {pbad})")
fails += pbad

if fails:
    print(f"ERDOS711_BATTERY_RED: {fails} failures")
    sys.exit(1)
print("ERDOS711_BATTERY_GREEN")
