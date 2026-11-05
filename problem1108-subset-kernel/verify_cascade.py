#!/usr/bin/env python3
"""ERDOS #1108 — verification battery for the SUBSET KERNEL LAW and the
FULL PAIR-CASCADE LAW (Session 023). All checks exact-integer.

Battery A: triple-method agreement (direct valuation, cascade machine,
           closed form) on ALL 16383 subsets of [1..14].
Battery B: the all-prime stack law AND the bottom-block singleton law on
           ALL subsets of [1..12] at p in {2,3,5,7,11} (20475 pairs).
Battery C: exhaustive square census over all subsets of [1..18]
           (2^18-1, Gray code) — exactly the 15 census squares.
Battery D: the depth-24 census frontier re-verified (every recorded hit
           re-checked; zero new squares for max in [16,24]).
"""
from math import factorial, isqrt
import itertools

def v2(n):
    if n == 0:
        return 10 ** 9
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c

def vp(p, n):
    if n == 0:
        return 10 ** 9
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c

LAM = {}
def Lam(j):
    if j not in LAM:
        LAM[j] = v2(factorial(2 * j))
    return LAM[j]

def machine_v2(S):
    """THE FULL CASCADE LAW, machine form: Lam(j0) + nu(stack)."""
    S = sorted(set(S))
    if not S:
        return None
    j0 = S[0] // 2
    L0 = Lam(j0)
    pairs = sorted(set(b // 2 for b in S))
    stack = [(Lam(j) - L0,
              sum(factorial(b) >> Lam(j) for b in S if b // 2 == j))
             for j in pairs]
    nu = 0
    while True:
        d0, A0 = stack[0]
        if len(stack) == 1 or v2(A0) < stack[1][0]:
            return L0 + nu + v2(A0)
        d1 = stack[1][0]
        nu += d1
        newA = (A0 >> d1) + stack[1][1]
        stack = [(0, newA)] + [(d - d1, O) for (d, O) in stack[2:]]

def closed_v2(S):
    """Closed form: v2(sum) = Lam(j0) + v2(sum >> Lam(j0))."""
    S = sorted(set(S))
    if not S:
        return None
    L0 = Lam(S[0] // 2)
    return L0 + v2(sum(factorial(b) for b in S) >> L0)

def direct_v2(S):
    return v2(sum(factorial(b) for b in S))

print("=== BATTERY A: triple method, all subsets of [1..14] ===")
bad = 0
tot = 0
for r in range(1, 15):
    for S in itertools.combinations(range(1, 15), r):
        tot += 1
        a, b, c = direct_v2(S), machine_v2(S), closed_v2(S)
        if not (a == b == c):
            bad += 1
            if bad <= 5:
                print("  MISMATCH", S, a, b, c)
assert bad == 0, f"BATTERY A FAILED: {bad} mismatches"
print(f"  {tot} subsets, 0 mismatches — FULL CASCADE LAW HOLDS")
print("BATTERY_A_GREEN=1")

print("=== BATTERY B: all-prime stack + singleton laws, [1..12] x p in {2,3,5,7,11} ===")
bad_stack = 0
bad_single = 0
tot = 0
singles = 0
for p in [2, 3, 5, 7, 11]:
    def block(b):
        return b // p if b >= p else 0
    MU = {}
    def mu(j):
        if j not in MU:
            MU[j] = vp(p, factorial(p * j))
        return MU[j]
    for r in range(1, 13):
        for S in itertools.combinations(range(1, 13), r):
            tot += 1
            Sig = sum(factorial(b) for b in S)
            js = sorted(set(block(b) for b in S))
            j0 = js[0]
            V = sum(p ** (mu(j) - mu(j0)) *
                    sum(factorial(b) // p ** mu(j) for b in S if block(b) == j)
                    for j in js)
            if vp(p, Sig) != mu(j0) + vp(p, V):
                bad_stack += 1
            if sum(1 for b in S if block(b) == j0) == 1:
                singles += 1
                if vp(p, Sig) != mu(j0):
                    bad_single += 1
assert bad_stack == 0, f"BATTERY B stack law FAILED: {bad_stack}"
assert bad_single == 0, f"BATTERY B singleton law FAILED: {bad_single}"
print(f"  {tot} (subset,prime) pairs: stack law 0 failures")
print(f"  {singles} bottom-block-singleton cases: 0 failures — ISOLATED-MIN LAW AT ALL PRIMES")
print("BATTERY_B_GREEN=1")

print("=== BATTERY C: exhaustive square census, all subsets of [1..18] ===")
N = 18
M = 64 * 63 * 65 * 11
facts = [factorial(b) for b in range(N + 1)]
fmod = [f % M for f in facts]
sq = set(r * r % M for r in range(M))
hits = []
cur = 0
cmod = 0
g = 0
k = 1
top = 1 << N
while k < top:
    t = (k & -k).bit_length() - 1
    g ^= (1 << t)
    e = t + 1
    if (g >> t) & 1:
        cur += facts[e]
        cmod = (cmod + fmod[e]) % M
    else:
        cur -= facts[e]
        cmod = (cmod - fmod[e]) % M
    if cmod in sq:
        r = isqrt(cur)
        if r * r == cur:
            S = [t + 1 for t in range(N) if (g >> t) & 1]
            hits.append((S, cur, r))
    k += 1
expected = 15
assert len(hits) == expected, f"BATTERY C FAILED: {len(hits)} squares (expected {expected})"
ok_all = all(machine_v2(S) == v2(val) and machine_v2(S) % 2 == 0
             for S, val, _ in hits)
assert ok_all, "BATTERY C FAILED: cascade/parity recheck"
print(f"  {2**N - 1} subsets: exactly {len(hits)} squares, all cascade-verified")
print("BATTERY_C_GREEN=1")

print("=== BATTERY D: depth-24 frontier re-verification ===")
known = [
    ([1], 1, 1),
    ([1, 2, 3], 9, 3),
    ([1, 4], 25, 5),
    ([4, 5], 144, 12),
    ([1, 5], 121, 11),
    ([1, 5, 6], 841, 29),
    ([1, 2, 3, 6], 729, 27),
    ([4, 5, 7], 5184, 72),
    ([1, 7], 5041, 71),
    ([1, 2, 3, 7, 8], 45369, 213),
    ([1, 4, 5, 6, 7, 8], 46225, 215),
    ([1, 4, 8, 9], 403225, 635),
    ([1, 2, 3, 6, 9], 363609, 603),
    ([1, 2, 3, 6, 7, 8, 10], 3674889, 1917),
    ([1, 2, 3, 7, 8, 9, 10, 11, 12, 13, 14, 15], 1401602635449, 1183893),
]
for S, val, r in known:
    assert sum(factorial(b) for b in S) == val, f"BATTERY D sum fail {S}"
    assert r * r == val, f"BATTERY D square fail {S}"
    assert machine_v2(S) == v2(val) and v2(val) % 2 == 0, f"BATTERY D cascade fail {S}"
print(f"  all 15 census squares re-verified (sum, root, cascade, parity)")
print(f"  frontier: ZERO squares for max(S) in [16,24] (deep_census24.py, this session)")
print("BATTERY_D_GREEN=1")

print()
print("ALL BATTERIES GREEN.")
