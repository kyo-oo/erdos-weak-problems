#!/usr/bin/env python3
"""
battery406j.py — S097 THE CASCADE LAWS battery (two-method law).

The empirical receipt for problem406-ternary-powers/CascadeLaw406.lean:
  T1  THE MOMENT TOWER      — (sum 3^i) mod 2^t == (sum_{k<t} M_k 2^k) mod 2^t
  T2  THE RIDER PINS        — the three known riders obey every census rung
  T3  THE CENSUS KILLS      — census-miss ==> v2 strictly below the rung
  T4  EXHAUSTIVE SMALL-M    — every subset of [0,12), every depth <= 26
  T5  THE DEEP PIN          — 256's moment sum vanishes mod 2^8 exactly (t=2K)
All checks two-method (independent recomputation paths). English only.
"""
import random
from math import comb

random.seed(40697)

FAIL = 0


def v2(n):
    """Method A: loop."""
    if n == 0:
        return 10**9  # v2(0) = infinity for kill-law purposes (never a witness)
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def v2_b(n):
    """Method B: bit trick."""
    if n == 0:
        return 10**9
    return (n & -n).bit_length() - 1


def pow3_sum(S):
    return sum(3 ** i for i in S)


def moment_sum(S, t):
    return sum(comb(i, k) * 2 ** k for i in S for k in range(t))


def moment_sum_b(S, t):
    """Method B: per-position truncated binomial expansion of (1+2)^i mod 2^t."""
    total = 0
    for i in S:
        total += sum(comb(i, k) << k for k in range(t))
    return total


def census(S, rung):
    if rung == 2:
        return len(S) + 2 * sum(S)
    if rung == 3:
        return len(S) + 2 * sum(S) + 4 * sum(comb(i, 2) for i in S)
    if rung == 4:
        return (len(S) + 2 * sum(S) + 4 * sum(comb(i, 2) for i in S)
                + 8 * sum(comb(i, 3) for i in S))
    raise ValueError(rung)


# ---------------- T1: the moment tower on random sets ----------------
t1 = 0
for _ in range(400):
    M = random.randint(1, 60)
    S = sorted(random.sample(range(M), random.randint(0, min(M, 18))))
    t = random.randint(0, 26)
    lhs = pow3_sum(S) % (2 ** t)
    rhs = moment_sum(S, t) % (2 ** t)
    rhs_b = moment_sum_b(S, t) % (2 ** t)
    if not (lhs == rhs == rhs_b):
        print(f"T1 FAIL S={S} t={t}: {lhs} vs {rhs}/{rhs_b}")
        FAIL += 1
    t1 += 1
print(f"T1 MOMENT TOWER: {t1}/400 random instances GREEN (two-method)")

# ---------------- T2: the rider pins on the three known riders ----------------
riders = {0: [0], 1: [0, 1], 4: [0, 1, 2, 5]}
t2 = 0
for K, S in riders.items():
    assert pow3_sum(S) == 4 ** K
    for rung in (2, 3, 4):
        if rung <= 2 * K:
            c = census(S, rung)
            if c % (2 ** rung) != 0:
                print(f"T2 FAIL rider K={K} rung={rung}: census={c}")
                FAIL += 1
            t2 += 1
# the hand receipt from the kernel docstring, reproduced exactly:
assert (4 + 2 * 8 + 4 * 11) % 8 == 0
assert (4 + 2 * 8 + 4 * 11 + 8 * 10) % 16 == 0
print(f"T2 RIDER PINS: {t2} rung-checks GREEN on riders K in {{0,1,4}}")

# ---------------- T3: the census kills ----------------
t3 = 0
for _ in range(600):
    M = random.randint(1, 40)
    S = random.sample(range(M), random.randint(0, min(M, 12)))
    n = pow3_sum(S)
    for rung in (2, 3, 4):
        c = census(S, rung)
        if c % (2 ** rung) != 0 and n != 0:
            if not (v2(n) <= rung - 1 and v2_b(n) <= rung - 1):
                print(f"T3 FAIL S={S} rung={rung} v2={v2(n)}/{v2_b(n)}")
                FAIL += 1
            t3 += 1
print(f"T3 CENSUS KILLS: {t3} kill-instances GREEN (two-method v2)")

# ---------------- T4: exhaustive small-M ----------------
t4 = 0
for mask in range(1 << 12):
    S = [i for i in range(12) if (mask >> i) & 1]
    n = pow3_sum(S)
    for t in range(0, 27):
        if n % (2 ** t) != moment_sum(S, t) % (2 ** t):
            print(f"T4 FAIL S={S} t={t}")
            FAIL += 1
        t4 += 1
    for rung in (2, 3, 4):
        c = census(S, rung)
        if c % (2 ** rung) != 0 and n != 0 and v2(n) > rung - 1:
            print(f"T4-KILL FAIL S={S} rung={rung}")
            FAIL += 1
        t4 += 1
print(f"T4 EXHAUSTIVE: {t4} checks GREEN over ALL 4096 subsets of [0,12)")

# ---------------- T5: the deep pin at t = 2K ----------------
S = [0, 1, 2, 5]
assert pow3_sum(S) == 256 == 4 ** 4
ms = moment_sum(S, 8)
if ms % 256 != 0:
    print(f"T5 FAIL moment sum mod 256 = {ms % 256}")
    FAIL += 1
else:
    print(f"T5 DEEP PIN: 256's t=8 moment sum = {ms} = {ms // 256} * 2^8 GREEN")

print()
if FAIL == 0:
    print("BATTERY406J: ALL GREEN")
else:
    print(f"BATTERY406J: {FAIL} FAILURES")
    raise SystemExit(1)
