#!/usr/bin/env python3
"""
battery406c.py — THE 2-ADIC BUDGET-TOWER BATTERY (S077, Kernel 70)

Dual-method verification engine for TwoAdic406.lean:
  T1  the square certificate  3^(2^s) = 1 + 2^(s+2)*c, c odd      (s = 1..14)
  T2  the near-unity power    (1 + 2^(s+2)z)^k == 1 + 2^(s+2)K    (spot checks)
  T3  the period twin         3^i % 2^(s+2) == 3^(i%2^s) % 2^(s+2) (s<=7, i<500)
  T4  the budget tower        n % 2^(s+2) == censusSum % 2^(s+2)  (all 0/1-ternary n < 3^9)
  T5  the rider tower         riders {0,1,4}: census == 0 mod 2^(s+2) at all legal levels
  T6  the pairing laws        (9^a + 3*9^b) % 8 == 4; (9^a + 9^b) % 8 == 2 (a,b < 40)
  T7  THE LX REFUTATION       1603072 = 3^0+3^7+3^8+3^13, v2 = 9 > 8 (dual method)
      + the far-cap family    13 + 3^69: v2 = 11 (dual method)
  T8  the census kill-rate    tower levels s=1..4 as census pre-filters on riders
  T9  the dust-edge           dust members with 4^r < 3^(j+1) are riders (tree census)

ALL GREEN or the battery exits 1. The engine never stops; it never lies.
"""
import sys
from math import gcd

GREEN = 0
RED = 0

def check(name, cond, detail=""):
    global GREEN, RED
    if cond:
        GREEN += 1
        print(f"  [PASS] {name}" + (f" — {detail}" if detail else ""))
    else:
        RED += 1
        print(f"  [FAIL] {name}" + (f" — {detail}" if detail else ""))

def v2(n):
    v = 0
    while n > 0 and n % 2 == 0:
        v += 1
        n //= 2
    return v

def ternary_digits(n):
    """positions of 1-digits of the ternary expansion (n assumed 0/1-ternary)"""
    pos, p = [], 0
    while n > 0:
        d = n % 3
        assert d in (0, 1), f"not a Cantor number: digit {d} at pos {p}"
        if d == 1:
            pos.append(p)
        n //= 3
        p += 1
    return pos

def census_sum(s, n, M):
    """the level-s census sum: sum over i<M of digit_i(n) * 3^(i mod 2^s)"""
    total = 0
    for i in range(M):
        total += ((n // 3**i) % 3) * 3**(i % 2**s)
    return total

def no_two(n):
    while n > 0:
        if n % 3 == 2:
            return False
        n //= 3
    return True

print("=== T1: the square certificate 3^(2^s) = 1 + 2^(s+2)c, c odd (s=1..14) ===")
ok = True
for s in range(1, 15):
    val = 3**(2**s)
    q, r = divmod(val - 1, 2**(s + 2))
    if r != 0 or q % 2 != 1:
        ok = False
        print(f"    s={s}: FAILED (r={r}, c%2={q%2})")
check("square certificate s=1..14", ok)

print("=== T2: the near-unity power congruence (spot checks) ===")
ok = True
for s in (1, 2, 3, 5, 8):
    for z in (0, 1, 5, 17, 100):
        for k in (0, 1, 2, 3, 7, 20):
            lhs = (1 + 2**(s + 2) * z)**k
            if (lhs - 1) % 2**(s + 2) != 0:
                ok = False
check("near-unity congruence (1+2^(s+2)z)^k == 1 + 2^(s+2)K", ok)

print("=== T3: the period twin 3^i mod 2^(s+2) == 3^(i mod 2^s) mod 2^(s+2) ===")
ok = True
for s in range(1, 8):
    for i in range(500):
        if (3**i) % 2**(s + 2) != (3**(i % 2**s)) % 2**(s + 2):
            ok = False
            print(f"    s={s}, i={i}: MISMATCH")
            break
check("period twin s=1..7, i<500 (== the order law ord_{2^t}(3) | 2^(t-2))", ok)

print("=== T4: THE BUDGET TOWER on ALL 0/1-ternary n < 3^9 (exhaustive) ===")
# every subset of positions {0..8} is a 0/1-ternary number < 3^9
from itertools import combinations
ok = True
count = 0
positions = list(range(9))
for r in range(len(positions) + 1):
    for subset in combinations(positions, r):
        n = sum(3**i for i in subset)
        for s in (1, 2, 3, 4):
            M = 9
            if n % 2**(s + 2) != census_sum(s, n, M) % 2**(s + 2):
                ok = False
                print(f"    n={n} (S={subset}), s={s}: MISMATCH "
                      f"{n % 2**(s+2)} vs {census_sum(s, n, M) % 2**(s+2)}")
            count += 1
check(f"budget tower, 512 Cantor numbers x 4 levels ({count} checks)", ok)

print("=== T5: THE RIDER TOWER on the known riders {0,1,4} ===")
ok = True
for K in (0, 1, 4):
    n = 4**K
    M = 2 * K + 2  # 4^K = 2^(2K) < 3^(2K+2) always (2 < 3)
    for s in range(1, 2 * K - 1):  # s + 2 <= 2K
        cs = census_sum(s, n, M)
        if cs % 2**(s + 2) != 0:
            ok = False
            print(f"    K={K}, s={s}: census {cs} mod {2**(s+2)} = {cs % 2**(s+2)} != 0")
check("rider tower: census sum == 0 mod 2^(s+2) at every legal level", ok)
# the deepest level receipt: K=4, s=6 (s+2 = 8 = 2K)
cs = census_sum(6, 256, 6)
check("deepest rider receipt: censusSum 6 256 6 == 256 == 0 mod 256",
      cs == 256 and 256 % 2**8 == 0, f"census={cs}")

print("=== T6: the pairing laws ===")
ok1 = all((9**a + 3 * 9**b) % 8 == 4 for a in range(40) for b in range(40))
ok2 = all((9**a + 9**b) % 8 == 2 for a in range(40) for b in range(40) if a != b)
check("mixed-parity pairs: (9^a + 3*9^b) % 8 == 4 (a,b < 40)", ok1)
check("same-parity pairs: (9^a + 9^b) % 8 == 2 (a != b < 40)", ok2)

print("=== T7: THE LX REFUTATION (dual method) ===")
n1 = 3**0 + 3**7 + 3**8 + 3**13
check("the witness value: 3^0+3^7+3^8+3^13 == 1603072", n1 == 1603072)
check("the witness is 0/1-ternary (digits {0,7,8,13})",
      ternary_digits(n1) == [0, 7, 8, 13] and no_two(n1))
check("v2(witness) == 9 > 8 = 2*4 (method A: repeated halving)", v2(n1) == 9)
check("2^9 | witness and not 2^10 | witness (method B: divisibility)",
      n1 % 2**9 == 0 and n1 % 2**10 != 0)
n2 = 3**0 + 3**1 + 3**2 + 3**69
check("far-cap witness: 13 + 3^69 is 0/1-ternary, v2 == 11 (dual)",
      no_two(n2) and v2(n2) == 11 and n2 % 2**11 == 0 and n2 % 2**12 != 0)
# the refutation of LX as a POPCOUNT law: popcount 4, v2 9 > 8
check("LX REFUTED: popcount 4, v2 = 9 > 2*4 (one past the S076 census boundary)",
      len(ternary_digits(n1)) == 4 and v2(n1) == 9)

print("=== T8: the tower's lens — the census view of the 2-adic window ===")
# The identity (budget_tower) makes the census congruence EQUIVALENT to the
# 2-adic window: census(s) == 0 mod 2^(s+2)  <=>  n == 0 mod 2^(s+2).
# The tower's content: a rider's DIGIT CENSUS (the class counts c_r) must
# satisfy the congruences at every level — a structural constraint on the
# digit set, readable without computing the (astronomically large) number.
import random
random.seed(406)
ok_equiv = True
for _ in range(2000):
    M = random.randint(1, 10)
    digits = [random.randint(0, 1) for _ in range(M)]
    n = sum(d * 3**i for i, d in enumerate(digits))
    for s in (1, 2, 3):
        cs = sum(((n // 3**i) % 3) * 3**(i % 2**s) for i in range(M))
        if (cs % 2**(s + 2) == 0) != (n % 2**(s + 2) == 0):
            ok_equiv = False
check("the equivalence: census == 0 mod 2^(s+2) <=> n == 0 mod 2^(s+2) "
      "(2000 random digit sets, s<=3)", ok_equiv)
# the census constraint content on the rider 256: the class counts must solve
# Sigma c_r 3^r == 0 mod 2^(s+2) at every level s <= 2K-2 = 6
ok_constraint = True
for s in range(1, 7):
    counts = {}
    for i in (0, 1, 2, 5):
        counts[i % 2**s] = counts.get(i % 2**s, 0) + 1
    cs = sum(c * 3**r for r, c in counts.items())
    if cs % 2**(s + 2) != 0:
        ok_constraint = False
        print(f"    level {s}: census {cs} mod {2**(s+2)} != 0")
check("256's digit census solves the congruence at all 6 legal levels "
      "(the class-count view: (E,O)=(2,2) -> 2+6=8; level 2: 1+2*3+9=16; ...)",
      ok_constraint)
# the kill power (the 2-adic window read through the census): how many random
# 0/1-digit sets could masquerade as a rider at levels s <= 4 (census == 0 at
# all four levels)? Only those with v2 >= 6 — the rare deeply-even ones.
trials, survivors = 3000, 0
for _ in range(trials):
    M = random.randint(6, 12)
    digits = [random.randint(0, 1) for _ in range(M)]
    n = sum(d * 3**i for i, d in enumerate(digits))
    if all(sum(((n // 3**i) % 3) * 3**(i % 2**s) for i in range(M)) % 2**(s + 2) == 0
           for s in (1, 2, 3, 4)):
        survivors += 1
rate = 1 - survivors / trials
check("census-window kill power on random digit sets (the v2 filter's "
      "digit-side twin)", rate > 0.95,
      f"{survivors}/{trials} survive all four levels ({rate:.1%} killed)")

print("=== T9: the dust-edge theorem (tree census verification) ===")
# rebuild the dust tree to level 10; check: every member r with 4^r < 3^(j+1)
# is a rider (noTernaryTwo(4^r) == True)
def build_dust(maxlevel):
    levels = [[0]]
    for j in range(maxlevel):
        nxt = []
        for r in levels[-1]:
            # digit_{j+1}(4^r) determines the dead child
            d = (4**r // 3**(j + 1)) % 3
            children = [r, r + 3**j, r + 2 * 3**j]
            for t in (0, 1, 2):
                nd = (d + t) % 3
                if nd != 2:
                    nxt.append(r + t * 3**j)
        levels.append(sorted(nxt))
    return levels

levels = build_dust(10)
ok = True
edge_count = 0
for j in range(1, 11):
    for r in levels[j]:
        if 4**r < 3**(j + 1):
            edge_count += 1
            if not no_two(4**r):
                ok = False
                print(f"    DUST-EDGE VIOLATION: j={j}, r={r}")
check(f"dust-edge: all {edge_count} edge members are riders (levels 1..10)", ok)
# and the known riders are exactly the small edge members
edge_small = sorted({r for j in range(1, 11) for r in levels[j]
                     if 4**r < 3**(j + 1) and r < 100})
check("the edge members below 100 are exactly {0, 1, 4}",
      edge_small == [0, 1, 4], f"found {edge_small}")
# doubling receipts
ok = all(len(levels[j]) == 2**j for j in range(0, 11))
check("dust doubling |alive[j]| == 2^j through level 10 (the engine twin)", ok)

print()
print(f"BATTERY406C: {GREEN} PASS, {RED} FAIL")
if RED == 0:
    print("BATTERY406C_GREEN=1")
    print("ALL CHECKS GREEN — THE 2-ADIC BUDGET TOWER STANDS. "
          "LX IS DEAD; THE TOWER REPLACES IT.")
sys.exit(0 if RED == 0 else 1)
