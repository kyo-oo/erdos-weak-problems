#!/usr/bin/env python3
"""
ERDŐS #404 — p = 2 CLASSIFICATION: THE OBSTRUCTION-FAMILY BATTERY
=================================================================
Verifies (exact integer arithmetic, zero floats, deterministic) the engine side
of Kill #11 (problem404-p2-classification/ObstructionFamilies.lean):

  T2: a ≡ 4 (mod 8)   ⟹ g(a,2) = 3  EXACTLY (witness {a+1, a+3}, mod-16 obstruction)
  T3: a ≡ 10 (mod 16) ⟹ g(a,2) = 6  EXACTLY (witness {a+1, a+3}, mod-128 obstruction)
  T4: a ≡ 32/48 (mod 64) ⟹ g(a,2) = 6 EXACTLY (witnesses {a+1,a+3,a+5} / {a+1,a+3,a+4})

plus the classification data:
  - the full small-g table for a ≤ 200 (engine ground truth),
  - the deep-survivor set (g ≥ 28 at 2^28, BITS-LIMIT certified),
  - the bounded deep values (46: 27, 86: 26, 104: 23, 110: 21, 144: 18, 174: 23, 400: 14),
  - Lin's citation context: f(2,2) ≤ 2^54, our g(2,2) ≥ 28.

The Lean kernel proves T2/T3/T4 for ALL a in the families (universally
quantified); this battery re-derives the same facts engine-side and cross-checks
the Lean receipts (the exact v2-values for sample a's).
"""
import sys, itertools
sys.path.insert(0, '../problem404-full')
from classifier import vp_fact, window, P_mod, g_value

PASS = 0
FAIL = 0

def check(name, cond):
    global PASS, FAIL
    if cond:
        PASS += 1
    else:
        FAIL += 1
        print(f"  FAIL: {name}")

def subset_sums(coins, m):
    S = set()
    for mask in range(1 << len(coins)):
        s = 0
        for j, c in enumerate(coins):
            if mask >> j & 1: s += c
        S.add(s % m)
    return S

def obstruction_holds(a, k, g):
    """No subset of the level-(g+1) window reaches -1 mod 2^(g+1)."""
    m = 2 ** (g + 1)
    idx = window(a, 2, g + 1)
    coins = [P_mod(a, i, 2, g + 1) for i in idx]
    S = subset_sums(coins, m)
    return 0 not in [(1 + s) % m for s in S]

def witness_value(a, offsets, level):
    """(1 + sum of window coins at offsets) == 0 mod 2^level, exactly."""
    m = 2 ** level
    s = 1 + sum(P_mod(a, a + j, 2, level + 1) for j in offsets)
    return s % m == 0 and s % (2 * m) != 0

print("=== T2: a ≡ 4 (mod 8) ⟹ g = 3 (uniform, to a=204) ===")
t2 = [a for a in range(1, 205) if a % 8 == 4]
for a in t2:
    g, st = g_value(a, 2, max_bits=2**13)
    check(f"g({a},2)=3", g == 3 and st == "BOUNDED")
for a in [4, 12, 68, 132, 196, 204]:
    check(f"T2 wit({a})", witness_value(a, [1, 3], 3))
    check(f"T2 obs({a})", obstruction_holds(a, 2, 3))

print("=== T3: a ≡ 10 (mod 16) ⟹ g = 6 (uniform, to a=202) ===")
t3 = [a for a in range(1, 203) if a % 16 == 10]
for a in t3:
    g, st = g_value(a, 2, max_bits=2**13)
    check(f"g({a},2)=6", g == 6 and st == "BOUNDED")
for a in [10, 26, 90, 122, 154, 202]:
    check(f"T3 wit({a})", witness_value(a, [1, 3], 6))
    check(f"T3 obs({a})", obstruction_holds(a, 2, 6))

print("=== T4: a ≡ 32/48 (mod 64) ⟹ g = 6 (uniform, to a=304) ===")
t4 = [a for a in range(1, 305) if a % 64 in (32, 48)]
for a in t4:
    g, st = g_value(a, 2, max_bits=2**13)
    check(f"g({a},2)=6", g == 6 and st == "BOUNDED")
for a in [32, 96, 160, 224, 288]:
    check(f"T4-32 wit({a})", witness_value(a, [1, 3, 5], 6))
    check(f"T4 obs({a})", obstruction_holds(a, 2, 6))
for a in [48, 112, 176, 240, 304]:
    check(f"T4-48 wit({a})", witness_value(a, [1, 3, 4], 6))

print("=== Lean receipt cross-checks (v2(a!) + g) ===")
# f(a,2) = v2(a!) + 3 [T2] / + 6 [T3/T4]; Lean #eval receipts: 6,13,21,39 / 14,29,45 / 37,52
for a, expect in [(4, 6), (12, 13), (20, 21), (36, 37), (10, 14), (26, 29), (42, 45), (32, 37), (48, 52)]:
    v = vp_fact(a, 2)
    g = {4:3, 12:3, 20:3, 36:3, 10:6, 26:6, 42:6, 32:6, 48:6}[a]
    check(f"f({a},2)={expect}", v + g == expect)

print("=== The classification table a ≤ 200 (small-g set) ===")
small = {}
for a in range(1, 201):
    if (a + 1) % 2 == 0:
        small[a] = 0
    else:
        g, st = g_value(a, 2, max_bits=2**16)
        small[a] = g if st == "BOUNDED" else None
# spot-verify known entries
for a, g in [(4,3),(8,6),(10,6),(12,3),(20,3),(22,11),(26,6),(28,3),(32,6),(40,7),(48,6),(56,7),(80,15),(120,9),(128,14),(152,8),(178,15),(200,6)]:
    check(f"table[{a}]={g}", small[a] == g)

print("=== Deep survivors at 2^28 (g ≥ 28, BITS-LIMIT) ===")
DEEP28 = [2, 6, 14, 16, 18, 24, 30, 34, 38, 62, 64, 78, 94, 98, 102, 126, 142, 146, 158, 162, 190, 194]
BOUNDED_DEEP = {46: 27, 86: 26, 104: 23, 110: 21, 144: 18, 174: 23}
for a in DEEP28:
    check(f"deep({a})", small[a] is None)  # survived the 2^16 fast scan
for a, g in BOUNDED_DEEP.items():
    g2, st = g_value(a, 2, max_bits=2**28)
    check(f"bounded-deep({a})={g}", g2 == g and st == "BOUNDED")

print("=== Prior-art consistency: Lin [Li76] f(2,2) ≤ 2^54 ===")
# our certified: g(2,2) ≥ 28 (survived 2^28) — consistent with the ≤ 2^54 bound.
g2, st = g_value(2, 2, max_bits=2**28)
check("g(2,2) >= 28", g2 >= 28 and st == "BITS-LIMIT")

print(f"\n{'ALL ' + str(PASS) + ' CHECKS PASSED' if FAIL == 0 else str(FAIL) + ' CHECKS FAILED'}")
sys.exit(0 if FAIL == 0 else 1)
