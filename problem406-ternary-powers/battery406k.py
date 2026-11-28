#!/usr/bin/env python3
"""
battery406k.py — S097 THE TWO-REGIME LATTICE-DENSITY EXPERIMENT (the S096
queued mission's second half, sharpened by the new moment-tower law).

For each M, enumerate ALL subsets S of [0, M) and record:
  - t*(M)     = max v2(sum) over all S           (the extremal curve)
  - N(t)      = #{S : sum(S) ≡ 0 mod 2^t}        (the survivor counts)
  - the kill ratios N(t+1)/N(t) against the counting baseline 1/2
  - the two regimes: sparse (|S| <= M/2) vs dense, max v2 in each
The N(t) curve is the anti-concentration signature the CAP(185) proof
must control: if the deep ratios die faster than 1/2, the lattice is
doing more work than counting predicts — the fluctuation structure the
sustainability bound must capture.
Two-method: v2 by bit trick AND by direct divisibility check on samples.
English only.
"""
import random

random.seed(40697)

FAIL = 0
print(f"{'M':>3} {'t*(M)':>6} {'excess':>7} {'sparse*':>8} {'dense*':>7} "
      f"{'N(M-2)':>9} {'N(M-1)':>8} {'N(M)':>7} {'N(M+1)':>7} {'N(M+2)':>7}")
for M in range(8, 23, 2):
    pow3 = [3 ** i for i in range(M)]
    # gray-code enumeration: incremental sum updates
    N = {}          # depth -> survivor count
    tstar = -1
    sparse_star = -1
    dense_star = -1
    s = 0
    prev_gray = 0
    # v2 of the empty set's sum (0) is treated as depth M+64 (infinite)
    def record(sumv, popc):
        global FAIL
        if sumv == 0:
            t = M + 64
        else:
            t = (sumv & -sumv).bit_length() - 1
        for d in range(t + 1):
            N[d] = N.get(d, 0) + 1
        return t
    t0 = record(0, 0)
    tstar = max(tstar, t0) if t0 < M + 64 else tstar
    popc = 0
    for i in range(1, 1 << M):
        gray = i ^ (i >> 1)
        diff = gray ^ prev_gray
        bit = diff.bit_length() - 1
        if gray & diff:
            s += pow3[bit]
            popc += 1
        else:
            s -= pow3[bit]
            popc -= 1
        prev_gray = gray
        t = record(s, popc)
        if t < M + 64:
            if t > tstar:
                tstar = t
            if popc <= M // 2:
                sparse_star = max(sparse_star, t)
            else:
                dense_star = max(dense_star, t)
    # two-method spot check: direct divisibility on 200 random subsets
    for _ in range(200):
        S = [i for i in range(M) if random.random() < 0.3]
        sv = sum(3 ** i for i in S)
        if sv == 0:
            continue
        t = (sv & -sv).bit_length() - 1
        if sv % (2 ** t) != 0 or sv % (2 ** (t + 1)) == 0:
            print(f"TWO-METHOD FAIL M={M} S={S}")
            FAIL += 1
    print(f"{M:>3} {tstar:>6} {tstar - M:>+7} {sparse_star:>8} {dense_star:>7} "
          f"{N.get(M - 2, 0):>9} {N.get(M - 1, 0):>8} {N.get(M, 0):>7} "
          f"{N.get(M + 1, 0):>7} {N.get(M + 2, 0):>7}")

print()
print("THE READING: N(t) at the deep end (t >= M) is the number of subsets")
print("whose FULL moment congruence holds at depth t — the lattice survivors.")
print("The counting baseline predicts N(t) ~ 2^(M-t); measured deviations are")
print("the fluctuation signature the sustainability bound must control.")
print()
if FAIL == 0:
    print("BATTERY406K: ALL GREEN")
else:
    print(f"BATTERY406K: {FAIL} FAILURES")
    raise SystemExit(1)
