#!/usr/bin/env python3
"""#404 gadget-supply battery: reachable-set DP + DFS chains + coverage tables.
Exact integer arithmetic throughout. ALL CHECKS MUST PASS."""
import sys
from itertools import combinations
from collections import defaultdict

def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r

def v2(n):
    if n == 0: return 10**9
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

IMAX = 300
P = {i: fact(i)//2 for i in range(3, IMAX+1)}
vP = {i: v2(P[i]) for i in P}

FAIL = 0
def check(name, ok):
    global FAIL
    print(("PASS" if ok else "FAIL"), name)
    if not ok: FAIL += 1

# --- 1. The pair law (all u in [3, 60]) ---
ok = all(v2(P[u] + P[u+1]) == v2(P[u]) + v2(u+2) for u in range(3, 61))
check("pair law v2(P_u+P_{u+1}) = v2(P_u)+v2(u+2), u in [3,60]", ok)

# --- 2. The triple law (all u in [3, 60]) ---
ok = all(v2(P[u] + P[u+1] + P[u+2]) == v2(P[u]) + 2*v2(u+2)
         for u in range(3, 61))
check("triple law v2 = v2(P_u) + 2*v2(u+2), u in [3,60]", ok)

# --- 3. The lift law (random exact pairs) ---
import random
random.seed(20261103)
ok = True
for _ in range(500):
    V = random.randrange(0, 30)
    x = (2**V) * (2*random.randrange(1, 10**6) + 1)
    y = (2**V) * (2*random.randrange(1, 10**6) + 1)
    if v2(x + y) < V + 1: ok = False; break
check("lift law: v2(x)=v2(y)=V => v2(x+y) >= V+1 (500 exact pairs)", ok)

# --- 4. The certified chain (the DFS witness, by ADD GROUPS) ---
ADDS = [(3,), (5,), (6, 7), (11,), (12,), (15,), (16,), (19,), (20,), (23,)]
B = []
vals = []
for g in ADDS:
    B += list(g)
    vals.append(v2(2 + sum(fact(i) for i in B)))
check("chain valuations == [3,7,8,10,11,15,16,18,19,23]",
      vals == [3, 7, 8, 10, 11, 15, 16, 18, 19, 23])
check("terminal witness v2 == 23",
      v2(2 + sum(fact(i) for i in B)) == 23)

# --- 5. The dead-end law: no valuation-4 gadget disjoint from {3,4} ---
# residues mod 32 beyond index 4 span {28,8,24,0}: 16 unreachable.
res = set()
idxs = [i for i in range(5, 20)]
for sz in range(0, 6):
    for c in combinations(idxs, sz):
        res.add(sum(P[i] for i in c) % 32)
check("dead-end: 16 mod 32 unreachable beyond index 4", 16 not in res)

# --- 6. Reachable-set DP: -1 in R_k for all k <= 24 ---
ok = True
for k in range(1, 25):
    coins = [P[i] % (1 << k) for i in range(3, 61) if vP[i] < k]
    R = {0}
    for c in coins:
        R |= {(r + c) % (1 << k) for r in R}
    if (1 << k) - 1 not in R:
        ok = False
        print(f"  LEVEL {k}: -1 NOT reachable")
        break
check("reachable-set DP: -1 in R_k for all k <= 24", ok)

# --- 7. Coverage tables (single/pair/triple supply) ---
single = sorted({vP[i] for i in range(3, 60)})
pair = sorted({v2(P[u]+P[u+1]) for u in range(3, 60)})
triple = sorted({v2(P[u]+P[u+1]+P[u+2]) for u in range(3, 60)})
print("  single-coin levels:", single[:14])
print("  pair levels:       ", pair[:18])
print("  triple levels:     ", triple[:18])
gap = [k for k in range(0, 25) if k not in single]
pt_cov = [k for k in gap if k in pair or k in triple]
mitm = [k for k in gap if k not in pair and k not in triple]
print(f"  gap levels (no single coin) <= 24: {gap}")
print(f"  of those, pair/triple-covered:    {pt_cov}")
print(f"  needing MITM gadgets:             {mitm}")
# the TRUE coverage claim: every level k <= 24 EXCEPT k=1 is attainable by
# SOME subset (exact valuation k).  Level 1 is provably UNATTAINABLE
# (mod 4: P_3 = 3, P_i = 0 for i >= 4: subset sums are 0 or 3 mod 4,
# never 2 mod 4) and UNNECESSARY (the chain jumps V=0 -> V=2 via {3}:
# 1 + 3 = 4).  A subset of exact valuation k exists iff 2^k in R_{k+1}.
ok = True
for k in range(0, 25):
    if k == 1: continue
    kk = k + 1
    coins = [P[i] % (1 << kk) for i in range(3, 61) if vP[i] < kk]
    R = {0}
    for c in coins:
        R |= {(r + c) % (1 << kk) for r in R}
    if (1 << k) % (1 << kk) not in R:
        ok = False
        print(f"  LEVEL {k}: no subset of exact valuation {k}")
check("every level k <= 24 except k=1 is gadget-attainable "
      "(k=1: unattainable AND skipped by the chain)", ok)
# the unattainability certificate for level 1:
res4 = set()
for sz in range(0, 5):
    for c in combinations(range(3, 12), sz):
        res4.add(sum(P[i] for i in c) % 4)
check("level-1 unattainability: subset sums mod 4 in {0,3} only", res4 == {0, 3})

print()
if FAIL:
    print(f"*** {FAIL} CHECK(S) FAILED ***"); sys.exit(1)
print("ALL GADGET-SUPPLY CHECKS PASSED")
