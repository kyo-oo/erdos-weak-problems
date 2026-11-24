#!/usr/bin/env python3
# FIRE-ROW DISTRIBUTION for natural exponents — where does the climb fire?
# For each K in range: extract the ternary digits of 4^K (exact big-int),
# derive 4^(K+1)'s digit stream via the x4 carry recurrence
#   C' = (C + 4d) / 3,  e = (C + 4d) % 3   (e = digit of 4x at that row)
# and find the FIRST row q >= 3 with digit_q(4^K) = 2 = digit_q(4^(K+1)).
# Measures: first fire row R(K) vs ntrits(K) = floor(log3 K) + 1.

import sys

def trits_of(n):
    ds = []
    while n:
        ds.append(n % 3)
        n //= 3
    return ds

def first_fire(K):
    d = trits_of(4 ** K)          # digits of 4^K, low first
    n = len(d)
    # digit stream of 4^(K+1) = 4 * 4^K via carry recurrence
    C = 0
    for q in range(n + 2):
        dq = d[q] if q < n else 0
        e = (C + 4 * dq) % 3
        if q >= 3 and dq == 2 and e == 2:
            return q
        C = (C + 4 * dq) // 3
    return None

def ntrits(K):
    return len(trits_of(K))

if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    stats = {}
    max_row = 0
    max_row_K = 0
    nofire = []
    rows = []
    for K in range(lo, hi):
        r = first_fire(K)
        if r is None:
            nofire.append(K)
            continue
        rows.append((K, r, ntrits(K)))
        if r > max_row:
            max_row = r
            max_row_K = K
    print(f"K in [{lo},{hi}): {len(rows)} fired, {len(nofire)} no-fire: {nofire[:20]}")
    print(f"max first-fire row = {max_row} at K = {max_row_K}")
    # distribution of (fire row - ntrits)
    from collections import Counter
    diff = Counter(r - nt for (_, r, nt) in rows)
    print("distribution of R(K) - ntrits(K):",
          sorted(diff.items())[:25])
    # the worst offenders (largest R - ntrits)
    worst = sorted(rows, key=lambda x: -(x[1] - x[2]))[:15]
    print("worst R(K)-ntrits(K):", worst)
    # distribution of R(K) itself
    rc = Counter(r for (_, r, _) in rows)
    print("R(K) histogram (top):", sorted(rc.items())[:20])
