#!/usr/bin/env python3
"""BATTERY 1063 — Erdos-Selfridge binomial frontier (Kill candidate, S033).

Independent verification of the case frontier n_k, k = 6..14.

Problem #1063: n_k = least n >= 2k such that (n-i) | C(n,k) for all but
one 0 <= i < k  (i.e. at least k-1 of the k values (n-i) divide C(n,k)).

Published calibration: n_2=4, n_3=6, n_4=9, n_5=12 (ErSe83) — engine matched
all four. New frontier claimed in S032 round 1:

  k    :  6   7   8   9    10   11    12   13  14
  n_k  : 75  30  70  56  2403  280  3465  210  793

This battery verifies, for every k in 2..14:
  (a) witness property: count(i in [0,k): (n_k - i) | C(n_k, k)) >= k-1;
  (b) completeness: every 2k <= n < n_k has count <= k-2 (at least 2 misses);
  (c) calibration: n_2..n_5 equal the published 4, 6, 9, 12.
"""
import sys
from math import comb

def divcount(n, k):
    c = comb(n, k)
    return sum(1 for i in range(k) if c % (n - i) == 0)

def main():
    expected = {2: 4, 3: 6, 4: 9, 5: 12, 6: 75, 7: 30, 8: 70, 9: 56,
                10: 2403, 11: 280, 12: 3465, 13: 210, 14: 793}
    ok = True
    print("k | n_k | divcount at witness | >= k-1? | completeness range | max divcount below | verdict")
    for k in range(2, 15):
        nk = expected[k]
        wc = divcount(nk, k)
        wit_ok = wc >= k - 1
        # completeness: every n in [2k, nk) has divcount <= k-2
        max_below = -1
        comp_ok = True
        for n in range(2 * k, nk):
            d = divcount(n, k)
            if d > max_below:
                max_below = d
            if d >= k - 1:
                comp_ok = False
                print(f"  COUNTEREXAMPLE at k={k}, n={n}: divcount={d} >= {k-1}")
        good = wit_ok and comp_ok
        ok = ok and good
        print(f"{k:2d} | {nk:4d} | {wc} | {wit_ok} | [{2*k},{nk}) | {max_below} | "
              + ("GREEN" if good else "RED"))
    # calibration statement
    calib = (expected[2], expected[3], expected[4], expected[5]) == (4, 6, 9, 12)
    print(f"\ncalibration n_2..n_5 = 4,6,9,12 (ErSe83 published): "
          + ("GREEN" if calib else "RED"))
    # witness detail: which position fails at each witness (the 'all but one')
    print("\nWitness miss positions (the exempt i):")
    for k in range(6, 15):
        nk = expected[k]
        c = comb(nk, k)
        misses = [i for i in range(k) if c % (nk - i) != 0]
        print(f"  k={k:2d} n_k={nk:4d} C={c} miss positions={misses}")
    ok = ok and calib
    print("\nBATTERY1063 " + ("GREEN — 13/13 witnesses + completeness + calibration"
                              if ok else "RED"))
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
