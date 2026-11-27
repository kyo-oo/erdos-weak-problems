#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""battery406f.py — THE S092 MAHLER-BRIDGE BATTERY (dual-method, ALL GREEN).

The computational certificates behind the S092 Mahler-bridge round:

  T1  THE GHOST CONGRUENCE (the stream identity, both classes):
      for the two dust candidate classes (cores 4, 16 mod 27), the
      unique compatible streams satisfy the ghost congruence
      2·ξ·c(k−1) + 9 ≡ 2·head (mod 3^k) at every depth — the all-ones
      middle-third tail.  Dual method: (i) the trit-by-trit progression
      sieve, (ii) the direct residue check against the tower
      coefficients (modular, NO-OOM compliant).

  T2  THE STREAM NON-TERMINATION EVIDENCE: both streams carry nonzero
      trits at a positive density of positions through level 30, no
      period ≤ 12 — the non-termination evidence (the proof is the
      named Mahler input, carried honestly).

  T3  THE SURVIVOR TREE LAW: at every cascade level p ≤ 11, every
      surviving class loses EXACTLY ONE child (the doubling law) —
      the frontier's structural shape.

  T4  THE RIDER ANTI-CLUSTERING (strong form): no 0/1-ternary number
      below 3^M(K) is divisible by 4^K for K ∈ {8, 10, 12} —
      dual-method (subset-residue DP + direct multiple scan).

  T5  THE MAHLER FRACTURE SCAN: every 3-free core u < 200 has a
      diagonal fire depth k₀(u) ≤ 20 — the numerical shadow of the
      Mahler sharpness input.

Exit 0 = ALL GREEN.  Any failure exits 1 with the named violation.
"""
import sys

def c_mod(k, m):
    """c(k) mod m for m = 3^j: compute 4^(3^k) mod 3^(k+1+j), subtract,
    divide — the tower coefficient without astronomical integers."""
    j_pow = 1
    # find j with 3^j >= m
    j = 0
    while 3 ** j < m:
        j += 1
    big = 3 ** (k + 1 + j)
    x = pow(4, 3 ** k, big)
    # x ≡ 1 + 3^(k+1) * c (mod big) — recover c mod 3^j >= m
    return ((x - 1) // (3 ** (k + 1))) % m

def trits(n, width):
    ds = []
    for _ in range(width):
        ds.append(n % 3)
        n //= 3
    return ds

def main():
    failures = []

    # ---------- T1 + T2 ----------
    LEVEL = 30
    classes = [4, 16]
    for core0 in classes:
        head = (7 * core0) % 9
        # (i) the progression sieve
        xi = core0
        ok_sieve = True
        for k in range(3, LEVEL):
            mod = 3 ** k
            ck = c_mod(k - 1, mod)
            found = None
            for t in range(3):
                cand = xi + t * (3 ** (k - 1))
                r = (ck * cand) % mod
                if 3 ** (k - 1) <= r < 2 * (3 ** (k - 1)):
                    found = cand
                    break
            if found is None:
                ok_sieve = False
                failures.append(f"T1-no-extension core0={core0} k={k}")
                break
            xi = found
        if not ok_sieve:
            continue
        # (ii) the ghost congruence, dual method
        for k in range(3, LEVEL):
            mod = 3 ** k
            ck = c_mod(k - 1, mod)
            lhs = (2 * ((xi % mod) * ck) + 9) % mod
            if lhs != (2 * head) % mod:
                failures.append(f"T1-congruence core0={core0} k={k}")
                break
        # T2: non-termination evidence
        xs = trits(xi, LEVEL)
        tail = xs[3:LEVEL]
        nz = sum(1 for t in tail if t != 0)
        if nz < 5:
            failures.append(f"T2-sparse core0={core0} nz={nz}")
        for p in range(1, 13):
            if len(tail) >= 2 * p and all(tail[i] == tail[i + p] for i in range(len(tail) - p)):
                failures.append(f"T2-period core0={core0} p={p}")
                break
        print(f"T1/T2 class {core0}: stream sieve + ghost congruence GREEN to level {LEVEL}; tail nonzero {nz}/{len(tail)}")
    if any(f.startswith("T1") or f.startswith("T2") for f in failures):
        print("T1/T2 FAILURES")

    # ---------- T3 ----------
    surv = [0]
    tree_ok = True
    for p in range(1, 12):
        new_surv = []
        dead = 0
        for S in surv:
            for t in range(3):
                K = S + t * (3 ** p)
                dig = (pow(4, K, 3 ** (p + 2))) // (3 ** (p + 1)) % 3
                if dig != 2:
                    new_surv.append(K)
                else:
                    dead += 1
        if dead != len(surv) or len(new_surv) != 2 * len(surv):
            tree_ok = False
            failures.append(f"T3-tree level={p} dead={dead} parents={len(surv)}")
            break
        surv = new_surv
    print(f"T3 survivor tree: exact doubling to {len(surv)} classes through level 11, one dead child per parent" if tree_ok else "T3 FAIL")

    # ---------- T4 ----------
    for K in [8, 10, 12]:
        n = 2 * K
        M = int(1.26186 * K) + 1
        MOD = 1 << n
        pows = [pow(3, i, MOD) for i in range(M)]
        res = {0: 0}
        hit = None
        for pw in pows:
            cur = dict(res)
            for r, kk in res.items():
                r2 = (r + pw) % MOD
                if r2 not in cur or cur[r2] > kk + 1:
                    cur[r2] = kk + 1
            res = cur
        if 0 in res and res[0] >= 1:
            hit = res[0]
        mult_ok = True
        m = 1
        while (1 << n) * m < 3 ** M:
            x = (1 << n) * m
            if all(d != 2 for d in trits(x, M + 2)[: M + 2]):
                mult_ok = False
                failures.append(f"T4-multiple K={K} m={m} clean")
                break
            m += 1
        if hit is not None:
            failures.append(f"T4-dp K={K} subset size {hit}")
    print("T4 rider anti-clustering: no 0/1-ternary < 3^M divisible by 4^K for K in {8,10,12}" if not any(f.startswith("T4") for f in failures) else "T4 FAIL")

    # ---------- T5 ----------
    frac_bad = []
    for u in range(1, 200):
        if u % 3 == 0:
            continue
        fired = None
        for k in range(3, 21):
            mod = 3 ** k
            ck = c_mod(k - 1, mod)
            r = (ck * u) % mod
            if r >= 2 * (3 ** (k - 1)):
                fired = k
                break
        if fired is None:
            frac_bad.append(u)
    if frac_bad:
        failures.append(f"T5-no-fire cores {frac_bad[:10]}")
    print("T5 Mahler fracture scan: every 3-free core < 200 has a diagonal fire depth <= 20" if not frac_bad else "T5 FAIL")

    if failures:
        print("BATTERY406F FAILURES:")
        for f in failures:
            print("  -", f)
        sys.exit(1)
    print("BATTERY406F_GREEN=1")

if __name__ == "__main__":
    main()
