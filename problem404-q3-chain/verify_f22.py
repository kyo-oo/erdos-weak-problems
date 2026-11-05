#!/usr/bin/env python3
"""ERDŐS #404 — THE f(2,2) = 254 BATTERY (Kill #14).
Verifies, by exact integer arithmetic (zero floats):
1. The witness: v2(2! + Σ_{i∈B} i!) = 254 for the explicit 118-element B.
2. The sound scheduled-precision class-DP: g(2,2) = 253, first unreachable 254.
3. The independent raw-bitset DP cross-check (definition-level): -1 ∈ R_k, k ≤ 25.
4. The cross-validation against the campaign's Lean-proven kills: g(4,2)=3,
   g(8,2)=6, g(10,2)=6, g(12,2)=3.
5. The a-sweep exact values (the p=2 candidate classification).
6. Lin consistency: the obstruction level 254 = Lin's upper bound f(2,2) ≤ 254 (TIGHT).
"""
import sys
from collections import defaultdict

def fact(n):
    r = 1
    for i in range(2, n + 1): r *= i
    return r

def v2(n):
    c = 0
    while n and n % 2 == 0: n //= 2; c += 1
    return c

WITNESS = [3, 5, 6, 7, 11, 12, 15, 16, 19, 21, 22, 24, 25, 27, 31, 33, 34, 36, 39, 41,
           42, 44, 46, 48, 52, 55, 56, 57, 60, 62, 63, 65, 67, 68, 69, 70, 71, 74, 76,
           77, 78, 80, 81, 82, 84, 85, 86, 88, 89, 91, 93, 94, 95, 96, 99, 104, 107,
           110, 111, 117, 118, 121, 123, 126, 129, 130, 134, 136, 139, 141, 143, 144,
           145, 147, 148, 149, 157, 158, 161, 164, 166, 167, 168, 169, 170, 173, 178,
           183, 184, 187, 189, 191, 198, 200, 202, 206, 207, 208, 211, 215, 217, 219,
           221, 222, 223, 224, 225, 226, 227, 235, 237, 240, 241, 244, 245, 249, 250, 254]

def vp_fact(n, p):
    v, q = 0, p
    while q <= n: v += n // q; q *= p
    return v

def class_dp(a, p, L, slack=8):
    CP = L + slack
    imax = a + 1
    while vp_fact(imax + 1, p) - vp_fact(a, p) < L: imax += 1
    classes = defaultdict(list)
    MODP = 1 << (CP + 64)
    q = 1
    for i in range(a + 1, imax + 1):
        q = (q * i) % MODP
        V = vp_fact(i, 2) - vp_fact(a, 2)
        if 0 <= V < L:
            classes[V].append((i, (q >> V) & ((1 << (CP - V)) - 1)))
    states = {(0, 1)}
    maxt = 0
    for V in range(L):
        units = [u for (i, u) in classes.get(V, [])]
        sigmas = {0}
        for u in units: sigmas |= {s + u for s in sigmas}
        precV = CP - V
        sigmas = {s % (1 << precV) for s in sigmas}
        sigmas.discard(0)
        new = set()
        for (t, u) in states:
            if t < V: continue
            new.add((t, u))
            for sig in sigmas:
                if t >= V:
                    sh = t - V
                    s = sig % (1 << precV) if sh >= precV else ((u << sh) + sig) % (1 << precV)
                    if s == 0:
                        new.add((CP, 1)); maxt = max(maxt, CP)
                    else:
                        d = (s & -s).bit_length() - 1
                        t2 = V + d
                        new.add((t2, s >> d)); maxt = max(maxt, t2)
        states = new
    return maxt

CHECKS = 0
def check(name, cond):
    global CHECKS
    if not cond:
        print(f"FAIL: {name}"); sys.exit(1)
    CHECKS += 1

# 1. The witness
S = 2 + sum(fact(i) for i in WITNESS)
check("witness v2 = 254", v2(S) == 254)
check("witness size 118", len(WITNESS) == 118)
check("witness range [3,254]", all(3 <= i <= 254 for i in WITNESS))
check("witness distinct", len(set(WITNESS)) == len(WITNESS))

# 2. The sound class-DP for (2,2) at the Lin window
g22 = class_dp(2, 2, 254)
check("g(2,2) = 253 (sound DP)", g22 == 253)

# 3. Independent raw bitset DP (definition level) for k in [2, 25]
for k in range(2, 26):
    mod = 1 << k
    mask = (1 << mod) - 1
    coins = []
    i = 3
    while True:
        Pi = fact(i) // 2
        if v2(Pi) >= k: break
        coins.append(Pi % mod); i += 1
    bs = 1
    for c in coins:
        bs |= (((bs << c) & mask) | (bs >> (mod - c)))
    check(f"-1 in R_{k} (raw bitset)", (bs >> (mod - 1)) & 1 == 1)

# 4. Cross-validation against Lean-proven kills
for a, expect in [(4, 3), (8, 6), (10, 6), (12, 3)]:
    got = class_dp(a, 2, expect + 6)
    check(f"g({a},2) = {expect} (matches Lean kernel)", got == expect)

# 5. The a-sweep exact values (sound DP; obstruction levels)
for a, expect in [(6, 129), (16, 533), (18, 45), (24, 39), (30, 100), (38, 793)]:
    got = class_dp(a, 2, expect + 6)
    check(f"g({a},2) = {expect}", got == expect)

# 6. Lin consistency: f(2,2) = 254 = Lin's upper bound (TIGHT)
check("f(2,2) = 1 + g(2,2) = 254 = Lin bound (tight)", 1 + g22 == 254)

print(f"ALL {CHECKS} CHECKS PASSED — f(2,2) = 254 EXACT (witness + sound-DP + bitset + cross-refs + Lin-tight)")
