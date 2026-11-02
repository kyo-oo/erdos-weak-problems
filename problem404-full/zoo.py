#!/usr/bin/env python3
"""Gadget zoo coverage: for each k, find a SUBSET of a local window with v_2(sum of factorials) == k exactly.
Uses meet-in-the-middle over windows of consecutive indices. Fresh windows (disjoint ranges)."""
import sys
from itertools import combinations

def v2(n):
    if n == 0: return 10**9
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r

F = [fact(i) for i in range(0, 220)]

def gadget_for(k, lo, hi):
    """Find a subset of indices in [lo, hi] with v_2(sum) == k. MITM: split window in half."""
    idx = list(range(lo, hi+1))
    n = len(idx)
    if n > 34: idx = idx[:34]; n = 34
    half = n // 2
    A, B = idx[:half], idx[half:]
    # sums of subsets of A (as (sum mod 2^{k+4}, exact-v check later))
    mod = 1 << (k + 3)
    from collections import defaultdict
    sumsA = defaultdict(list)
    for mask in range(1 << len(A)):
        s = 0
        for b in range(len(A)):
            if mask >> b & 1: s += F[A[b]]
        sumsA[s % mod].append(mask)
    for mask in range(1 << len(B)):
        s = 0
        for b in range(len(B)):
            if mask >> b & 1: s += F[B[b]]
        # want total = s + sA with v_2 == k  ->  total ≡ 2^k mod 2^{k+1}
        # enumerate needed residues for sA: 2^k - s mod 2^{k+1} (+ multiples of 2^{k+1} up to mod)
        for j in range(0, 8):
            need = ((1 << k) - s + j * (1 << (k+1))) % mod
            if need in sumsA:
                ma = sumsA[need][0]
                total = s
                for b in range(len(A)):
                    if ma >> b & 1: total += F[A[b]]
                if v2(total) == k:
                    sub = sorted([A[b] for b in range(len(A)) if ma >> b & 1] + [B[b] for b in range(len(B)) if mask >> b & 1])
                    return sub
    return None

def main():
    print("=== GADGET ZOO: exact-valuation-k subsets of fresh windows ===")
    lo = 3
    misses = []
    plan = []
    for k in range(3, 121):
        # window: fresh, near k + 12 (terms there have v_2(i!) ~ k+..)
        w_lo = max(lo, k + 2)
        g = None
        for off in range(0, 6):
            g = gadget_for(k, w_lo + off, w_lo + off + 21)
            if g: break
        if g:
            plan.append((k, g))
            lo = max(lo, max(g) + 1)
        else:
            misses.append(k)
    print("covered:", len(plan), "misses:", misses)
    print("gadget type histogram:")
    from collections import Counter
    def gtype(g):
        if len(g) == 1: return "single"
        if g == list(range(g[0], g[-1]+1)): return f"block-{len(g)}"
        return f"subset-{len(g)}"
    print(Counter(gtype(g) for _, g in plan))
    print("first 30 gadgets:")
    for k, g in plan[:30]:
        s = sum(F[i] for i in g)
        print(f"  k={k:>3}: {g}   v2={v2(s)}")
    # Save the full plan as the explicit induction table
    import json
    json.dump(plan, open('/home/z/erdos-recovery/problem404/gadget_plan.json', 'w'))
    print("saved gadget_plan.json")

if __name__ == "__main__":
    main()
