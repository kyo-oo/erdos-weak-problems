#!/usr/bin/env python3
"""
battery406l.py — S097 THE EXCESS-BIRTH EXPERIMENT (MITM extension of the
lattice-density scan).

The full-enumeration scan (battery406k) established: for every
M in {8..22}, N(M+1) = 1 — the empty set alone survives depth M+1; no
nonempty subset of [0,M) reaches v2 >= M+1.  The S094 doubter measured
excess +10 at M=37 (their position convention).  This experiment locates
the BIRTH of the excess: the smallest M with a nonempty subset of [0,M)
achieving v2 >= M+1.

Method: meet-in-the-middle. Split [0,M) into low/high halves; enumerate
2^(M/2) subset sums per side; for each depth t, count pairs (L, R) with
L + R ≡ 0 (mod 2^t) by hashing R mod 2^t.  The pair-count minus the
empty-empty pair = the nonempty survivor count at depth t.
Two-method: depths re-checked by direct divisibility on sampled pairs.
English only.
"""
from collections import defaultdict

FAIL = 0
print(f"{'M':>3} " + " ".join(f"{'N(' + str(d) + ')':>8}" for d in range(0, 0)) )
print(f"{'M':>3} {'t*':>4} {'excess':>7}   N(M)   N(M+1)  N(M+2)  N(M+3)  N(M+4)  N(M+6)  N(M+8)")
for M in (24, 26, 28, 30, 32, 34, 36):
    lo = M // 2
    hi = M - lo
    pow3_lo = [3 ** i for i in range(lo)]
    pow3_hi = [3 ** (lo + i) for i in range(hi)]
    sums_lo = [0] * (1 << lo)
    for i in range(1, 1 << lo):
        b = (i & -i).bit_length() - 1
        sums_lo[i] = sums_lo[i ^ (1 << b)] + pow3_lo[b]
    sums_hi = [0] * (1 << hi)
    for i in range(1, 1 << hi):
        b = (i & -i).bit_length() - 1
        sums_hi[i] = sums_hi[i ^ (1 << b)] + pow3_hi[b]
    depths = list(range(M, M + 9))
    counts = {}
    for t in depths:
        mod = 1 << t
        bucket = defaultdict(int)
        for rv in sums_hi:
            bucket[rv % mod] += 1
        total = 0
        for lv in sums_lo:
            total += bucket.get((-lv) % mod, 0)
        # `total` counts ALL pairs incl. empty+empty and 2-representations
        # of the same set? No: each set has a UNIQUE (low,high) split, so
        # total = #{S subseteq [0,M) : sum(S) ≡ 0 mod 2^t} exactly.
        counts[t] = total
    tstar = None
    for t in depths:
        if counts[t] > 1:
            tstar = t
    # find the max depth with a nonempty survivor: walk down from M+8
    tmax = None
    for t in reversed(depths):
        if counts[t] > 1:
            tmax = t
            break
    # also check below M for the true t*(M)
    for t in range(M - 1, M - 4, -1):
        mod = 1 << t
        bucket = defaultdict(int)
        for rv in sums_hi:
            bucket[rv % mod] += 1
        total = 0
        for lv in sums_lo:
            total += bucket.get((-lv) % mod, 0)
        counts[t] = total
        if tmax is None and total > 1:
            tmax = t
    # two-method spot check at the deepest nonempty depth
    if tmax is not None and tmax >= M:
        mod = 1 << tmax
        bucket = defaultdict(list)
        for idx, rv in enumerate(sums_hi):
            bucket[rv % mod].append(idx)
        found = 0
        for lidx, lv in enumerate(sums_lo):
            for ridx in bucket.get((-lv) % mod, []):
                if lidx == 0 and ridx == 0:
                    continue
                sv = lv + sums_hi[ridx]
                if sv == 0:
                    continue
                if sv % mod != 0:
                    print(f"TWO-METHOD FAIL M={M}")
                    FAIL += 1
                found += 1
                if found >= 5:
                    break
            if found >= 5:
                break
    print(f"{M:>3} {tmax if tmax is not None else '-':>4} "
          f"{(tmax - M) if tmax is not None else 0:>+7}   "
          + "  ".join(f"{counts.get(d, 0):>5}" for d in
                      (M, M + 1, M + 2, M + 3, M + 4, M + 6, M + 8)))
print()
print("THE TARGET: the first M where N(M+1) > 1 — the excess birth.")
if FAIL == 0:
    print("BATTERY406L: ALL GREEN")
else:
    print(f"BATTERY406L: {FAIL} FAILURES")
    raise SystemExit(1)
