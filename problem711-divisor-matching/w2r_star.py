#!/usr/bin/env python3
"""E9: test Bonferroni-2 inequality (star) and aggregate overlap bound (starstar):
   (star)   S1 - S2 >= s   (S1 = sum |M_k|, S2 = sum pairwise |M_i^M_j|), antichains, W=2n-2, all m in full period.
   (starstar) sum_{i<j} |M_i^M_j| <= sum_i (floor(W/k_i) - 1)  [with floor(W/k)=1 contributing 0]
"""
import sys
from math import gcd
from functools import reduce
def lcm(a,b): return a*b//gcd(a,b)

def census(n, per):
    W = 2*n-2
    worst_star = 10**9; worst_star_at = None
    worst_ss = 10**9; worst_ss_at = None
    for m in range(1, per+1):
        ints = list(range(m+1, m+W+1))
        # exact membership lists
        Ms = {k: frozenset(x for x in ints if x % k == 0) for k in range(1, n+1)}
        for S in range(1, 1<<n):
            ks = [i+1 for i in range(n) if S>>i & 1]
            if len(ks) < 2: continue
            # antichain filter
            ok = True
            for a in range(len(ks)):
                for b in range(a+1, len(ks)):
                    if ks[b] % ks[a] == 0: ok = False; break
                if not ok: break
            if not ok: continue
            S1 = sum(len(Ms[k]) for k in ks)
            S2 = 0
            for a in range(len(ks)):
                for b in range(a+1, len(ks)):
                    S2 += len(Ms[ks[a]] & Ms[ks[b]])
            if S1 - S2 < len(ks):
                if S1 - S2 < worst_star: worst_star = S1 - S2 - len(ks); worst_star_at = (m, tuple(ks))
            if S2 > sum(max(0, W//k - 1) for k in ks):
                if S2 - sum(max(0, W//k -1) for k in ks) < worst_ss:
                    worst_ss = S2 - sum(max(0, W//k -1) for k in ks); worst_ss_at = (m, tuple(ks))
    return worst_star, worst_star_at, worst_ss, worst_ss_at

for n in range(2, 11):
    L = reduce(lcm, range(1, n+1), 1)
    per = min(L, 2520)
    ws, wsa, wss, wssa = census(n, per)
    print(f"n={n}: min(S1-S2-s) = {ws} at {wsa};  min(S2 - sum(floor(W/k)-1)) = {wss} at {wssa}")
