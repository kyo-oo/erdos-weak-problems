#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
battery406h.py — THE TAILF DECOMPOSITION BATTERY (S084, Kernel 76)

Dual-method verification of every numeric receipt in
problem406-ternary-powers/TailFDecomposition406.lean:

  T1  THE OMEGA-CUT FACTORIZATION   (direct power vs recursive cut word)
  T2  THE TOWER DIAGONAL            (odd, 1 mod 3, stability, W61/W100 compat)
  T3  THE DIAGONAL CONGRUENCE       (cut word == diag*core mod 3^(s+1))
  T4  THE FULL OBSERVER             (power digit == cut-word digit, every depth)
  T5  THE RESIDUE-FIRE CLASSIFIER   (digit two iff top-third residue)
  T6  THE COMPRESSION LAW           (Cantorian power iff clean cut word)
  T7  THE ROW-FAMILY FIRE           (row primitive consistency with the census)
  T8  THE TOWER-FAMILY FIRE         (tower primitive consistency, s >= 1)
  T9  THE SIX-ADIC SATURATION       (3^k | d and k <= 2t  =>  6^k | 4^t*d)
  T10 THE GHOST-PAIR COLLAPSE       (depth-limited congruence mechanics)
  T11 THE TWELVE-CELL JUMP TABLE    (formula vs table, exact)
  T12 THE HAPPY SIGN LAW ON WAVES   (real cells of 4^K, K = 8..16)
  T13 THE FROZEN TAIL               (digit 0, carry 0, jump 10 beyond 3K+3)
  T14 THE CROWN'S SMALL CASES       (4^5, 4^6, 4^7 fire receipts)
  T15 THE W100 COMPATIBILITY        (kernel-75 constant, byte-for-byte)
  T16 NEGATIVE CONTROLS             (dirty cut words, non-happy cells, bad 6-adics)

ALL checks must PASS.  The engine never stops; it never lies.
"""

import random

random.seed(40676)

PASS = 0
FAIL = 0


def check(name, ok):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        print(f"FAIL: {name}")


# ---------------------------------------------------------------- kernel

def digit3(x, p):
    """The ternary digit at position p."""
    return (x // (3 ** p)) % 3


def lte_coeff(v):
    """The tower coefficient c_v, division-free cube recursion (the Lean def)."""
    c = 1
    for r in range(v):
        c = c + (3 ** (r + 1)) * c * c + (3 ** (2 * r + 1)) * c ** 3
    return c


def lte_coeff_mod(v, m):
    """c_v mod m, computed by the same recursion reduced mod m (method 2)."""
    c = 1 % m
    for r in range(v):
        c = (c + (pow(3, r + 1, m) * c * c + pow(3, 2 * r + 1, m) * c ** 3)) % m
    return c


def geo_sum(s, core):
    """geoSum s core = sum_{j<core} (4^(3^s))^j, iterative (dual to closed form)."""
    total = 0
    term = 1
    b = 4 ** (3 ** s)
    for _ in range(core):
        total += term
        term *= b
    return total


def cut_word(s, core):
    """omegaCutWord s core = lteCoeff s * geoSum s core."""
    return lte_coeff(s) * geo_sum(s, core)


def cut_word_mod(s, core, m):
    """omegaCutWord s core mod m, reduced at every step (method 2)."""
    total = 0
    term = 1
    b = pow(4, 3 ** s, m)
    for _ in range(core):
        total = (total + term) % m
        term = (term * b) % m
    return (lte_coeff_mod(s, m) * total) % m


def gst_u_charge(C):
    return 5 if C == 0 else (21 if C == 3 else 15)


def gst_step_carry(C, d):
    return (C + 4 * d) // 3


def gst_u_jump(C, d):
    """The exact handwritten-U jump (the Lean def)."""
    return 3 * gst_u_charge(gst_step_carry(C, d)) - gst_u_charge(C) - 24 * d


def carry4(R, p):
    """The x4 carry coordinate (the Lean def)."""
    return (4 * (R % (3 ** p))) // (3 ** p)


def has_two(x, fuel):
    """Does x own a ternary digit 2 at some position < fuel?"""
    for p in range(fuel):
        if digit3(x, p) == 2:
            return True
    return False


def no_digit_two_all(x):
    """No ternary digit 2 at any position (x is finite: terminate at x==0)."""
    while x > 0:
        if x % 3 == 2:
            return False
        x //= 3
    return True


# ---------------------------------------------------------------- T1

for (s, core) in [(0, 1), (0, 2), (0, 4), (0, 7), (1, 1), (1, 2), (1, 4),
                  (1, 5), (2, 1), (2, 2), (2, 4), (3, 1), (0, 13), (1, 13)]:
    lhs = 4 ** (3 ** s * core)
    rhs = 1 + 3 ** (s + 1) * cut_word(s, core)
    check(f"T1 cut factor s={s} core={core}", lhs == rhs)

# method 2: modular cross-check on a big case (s=2, core=100)
m = 3 ** 40
lhs = pow(4, 3 ** 2 * 100, m)
rhs = (1 + pow(3, 3, m) * cut_word_mod(2, 100, m)) % m
check("T1 cut factor modular (s=2, core=100)", lhs == rhs)

# ---------------------------------------------------------------- T2

vals = [lte_coeff(v) for v in range(9)]
check("T2 c_0..c_8 values", vals[:3] == [1, 7, 9709])
check("T2 all odd", all(c % 2 == 1 for c in vals))
check("T2 all 1 mod 3", all(c % 3 == 1 for c in vals))

ok_stable = True
for v in range(6):
    for w in range(v, 9):
        if (lte_coeff(w) - lte_coeff(v)) % 3 ** (v + 1) != 0:
            ok_stable = False
check("T2 frozen diagonal stability", ok_stable)

W61 = 60776643992856088575557123854  # the S080 constant
check("T2 W61 compat (kernel 74)", lte_coeff_mod(60, 3 ** 61) == W61)

W100 = 79542728300108260269642213640611567864276448732  # the S083 constant
check("T2/T15 W100 compat (kernel 75)",
      lte_coeff_mod(99, 3 ** 100) == W100)

# ---------------------------------------------------------------- T3

ok_diag = True
for (s, core) in [(1, 4), (1, 7), (2, 4), (2, 7), (3, 4), (0, 8), (1, 13),
                  (2, 100), (3, 250)]:
    if cut_word(s, core) % 3 ** (s + 1) != (lte_coeff(s) * core) % 3 ** (s + 1):
        ok_diag = False
check("T3 diagonal congruence grid", ok_diag)

# ---------------------------------------------------------------- T4

ok_obs = True
for (s, core) in [(0, 4), (0, 7), (1, 4), (1, 7), (2, 4), (2, 7), (3, 2)]:
    W = cut_word(s, core)
    for q in range(14):
        lhs = digit3(4 ** (3 ** s * core), s + 1 + q)
        rhs = digit3(W, q)
        if lhs != rhs:
            ok_obs = False
check("T4 full observer grid", ok_obs)

# ---------------------------------------------------------------- T5

ok_fire = True
for _ in range(300):
    W = random.randrange(1, 3 ** 12)
    q = random.randrange(0, 10)
    lhs = (digit3(W, q) == 2)
    rhs = (2 * 3 ** q <= W % 3 ** (q + 1))
    if lhs != rhs:
        ok_fire = False
check("T5 residue-fire classifier (300 random)", ok_fire)

# ---------------------------------------------------------------- T6

ok_comp = True
for (s, core) in [(0, 1), (0, 2), (0, 4), (0, 5), (0, 7), (0, 8), (0, 13),
                  (1, 1), (1, 2), (1, 4), (1, 5), (2, 1), (2, 2), (2, 4)]:
    K = 3 ** s * core
    verdict_power = no_digit_two_all(4 ** K)
    verdict_word = no_digit_two_all(cut_word(s, core))
    if verdict_power != verdict_word:
        ok_comp = False
check("T6 compression law grid (verdicts agree)", ok_comp)

check("T6 positive control: K=4 is Cantorian, cut word clean",
      no_digit_two_all(4 ** 4) and no_digit_two_all(cut_word(0, 4)))
check("T6 negative control: K=8 fires, cut word dirty",
      (not no_digit_two_all(4 ** 8)) and (not no_digit_two_all(cut_word(0, 8))))

# ---------------------------------------------------------------- T7

ok_row = True
row_fire_count = 0
for core in range(8, 500):  # the census base starts at 8 (kernel-75 law)
    if core % 3 != 0 and core % 9 in (1, 4):
        # the census: 4^core owns a digit two (kernel-75 base)
        if not has_two(4 ** core, 700):
            ok_row = False
        # the row primitive: the row word fires at some depth
        W = cut_word(0, core)
        fired = any(2 * 3 ** j <= W % 3 ** (j + 1) for j in range(700))
        if not fired:
            ok_row = False
        else:
            row_fire_count += 1
check(f"T7 row family (all {row_fire_count} class-one 3-free cores < 500 fire)",
      ok_row and row_fire_count > 100)

# ---------------------------------------------------------------- T8

ok_tower = True
tower_count = 0
for s in (1, 2):
    for core in range(1, 60):
        if core % 3 != 0 and core % 9 in (4, 7):
            K = 3 ** s * core
            W = cut_word(s, core)
            fire_power = has_two(4 ** K, 3 ** s * core * 2 + 20)
            fire_word = any(digit3(W, q) == 2 for q in range(220))
            if not fire_power or not fire_word:
                ok_tower = False
            if fire_power:
                tower_count += 1
check(f"T8 tower family ({tower_count} cores with s in {{1,2}} fire)",
      ok_tower and tower_count > 20)

# the fire position consistency: digit at s+1+q of the power == digit q of word
ok_pos = True
for s in (1, 2):
    for core in (4, 7, 13, 22):
        K = 3 ** s * core
        W = cut_word(s, core)
        for q in range(120):
            if digit3(4 ** K, s + 1 + q) != digit3(W, q):
                ok_pos = False
check("T8 fire-position consistency (observer on the tower family)", ok_pos)

# ---------------------------------------------------------------- T9

ok_six = True
for _ in range(200):
    k = random.randrange(0, 9)
    t = (k + 1) // 2 + random.randrange(0, 4)  # guarantees k <= 2t
    a = random.randrange(0, 40)
    d = (3 ** k) * a
    lhs = (6 ** k)
    rhs = (4 ** t) * d
    if lhs > 0 and rhs % lhs != 0:
        ok_six = False
check("T9 six-adic saturation (200 random, k <= 2t)", ok_six)

# directional check: k <= 2t is required (a counterexample style: k > 2t may fail)
k, t, a = 8, 2, 1  # k=8 > 2t=4: 6^8 | 4^2 * 3^8 * 1 ?  ->  2^8*3^8 | 2^4*3^8 : NO
check("T9 negative control (k > 2t breaks saturation)",
      (4 ** t * (3 ** k * a)) % (6 ** k) != 0)

# ---------------------------------------------------------------- T10

# the collapse engine: congruence at every depth forces equality.
# u - u' = 3^20 supports congruence only through depth 20.
u = lte_coeff_mod(30, 3 ** 40) + 3 ** 40  # any natural pinned mod 3^40
up = u + 3 ** 20
ok_depth = True
for k in range(3, 21):
    diff = (lte_coeff_mod(k - 1, 3 ** k) * (u - up)) % (3 ** k)
    if diff != 0:
        ok_depth = False
for k in range(22, 30):
    diff = (lte_coeff_mod(k - 1, 3 ** k) * (u - up)) % (3 ** k)
    if diff == 0:
        # can only happen if 3^(k-20) | lteCoeff(k-1); lteCoeff is a unit
        if lte_coeff_mod(k - 1, 3) != 0:
            ok_depth = False
check("T10 depth-limited congruence mechanics", ok_depth)

# the unit side: lteCoeff is never divisible by 3
check("T10 lteCoeff three-free (v < 60)",
      all(lte_coeff_mod(v, 3) == 1 for v in range(60)))

# ---------------------------------------------------------------- T11

table = {(0, 0): 10, (0, 1): 16, (0, 2): -8, (1, 0): 0, (1, 1): 6,
         (1, 2): 0, (2, 0): 0, (2, 1): 6, (2, 2): 0, (3, 0): 24,
         (3, 1): 0, (3, 2): -6}
check("T11 jump table (formula == table)",
      all(gst_u_jump(C, d) == v for (C, d), v in table.items()))

# ---------------------------------------------------------------- T12

ok_sign = True
happy_seen = 0
for K in range(8, 17):
    R = 4 ** K
    for p in range(2 * K + 12):
        C = carry4(R, p)
        d = digit3(R, p)
        j = gst_u_jump(C, d)
        happy = (d == 2 and C in (0, 3))
        if happy:
            happy_seen += 1
            if not j < 0:
                ok_sign = False
        else:
            if not j >= 0:
                ok_sign = False
check(f"T12 happy sign law on live waves ({happy_seen} happy cells seen)",
      ok_sign and happy_seen > 0)

# ---------------------------------------------------------------- T13

ok_frozen = True
for K in (8, 12, 16, 20):
    R = 4 ** K
    for p in range(3 * K + 3, 3 * K + 9):
        d = digit3(R, p)
        C = carry4(R, p)
        j = gst_u_jump(C, d)
        if not (d == 0 and C == 0 and j == 10):
            ok_frozen = False
check("T13 frozen tail (jump 10 beyond 3K+3)", ok_frozen)

# the tail really is beyond the tape: 4^K < 3^(3K+1)
check("T13 size bound", all(4 ** K < 3 ** (3 * K + 1) for K in range(0, 30)))

# ---------------------------------------------------------------- T14

check("T14 4^5 fires at position 2", digit3(4 ** 5, 2) == 2)
check("T14 4^6 fires at position 2", digit3(4 ** 6, 2) == 2)
check("T14 4^7 fires at position 8", digit3(4 ** 7, 8) == 2)

# ---------------------------------------------------------------- T16

# dirty cut words carry twos
check("T16 dirty row word (core=8)",
      any(digit3(cut_word(0, 8), q) == 2 for q in range(30)))
# non-happy cells on random junk: sign law
ok_junk = True
for _ in range(200):
    C = random.randrange(0, 4)
    d = random.randrange(0, 3)
    if not (d == 2 and C in (0, 3)):
        if gst_u_jump(C, d) < 0:
            ok_junk = False
check("T16 non-happy junk cells nonnegative", ok_junk)
# the W100 prefix stability under one more step (the frontier is live,
# computed mod 3^101: c_100 - c_99 vanishes mod 3^100 but not 3^101)
diff101 = (lte_coeff_mod(100, 3 ** 101)
           - lte_coeff_mod(99, 3 ** 101)) % (3 ** 101)
check("T16 W100 extends (c_100 - c_99 mod-wise)",
      diff101 % (3 ** 100) == 0 and diff101 % (3 ** 101) != 0)

# ---------------------------------------------------------------- verdict

print()
print(f"battery406h: {PASS} PASS, {FAIL} FAIL")
if FAIL == 0:
    print("BATTERY406H_ALL_GREEN")
else:
    print("BATTERY406H_RED")
    raise SystemExit(1)
