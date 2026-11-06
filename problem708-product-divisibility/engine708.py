#!/usr/bin/env python3
"""#708 round 1 (Erdos $100, ErSu59): g(n) evidence engine.
g(n) = min g such that for ANY A (|A|=n, A subset [2,inf)) and ANY interval
I of max(A) consecutive integers, exists B in I, |B|=g, prod(A) | prod(B).
This engine computes, for given A and interval start t, the exact min |B|.
Known: g(2)=2, g(3)=4 (ErSu59). Target: g(4) evidence."""
from itertools import combinations
from sympy import factorint

def min_B(A, t):
    """A: list of ints; I = {t+1, ..., t+max(A)}; exact min |B| with prod(A)|prod(B).
    Returns (min_size, example B)."""
    M = max(A)
    I = list(range(max(2, t+1), t+M+1))
    P = 1
    for a in A: P *= a
    # prime-power demand: for each prime p^e || P, B must supply >= e
    need = factorint(P)
    # each b: its factor contribution
    bfacts = [factorint(b) for b in I]
    n = len(I)
    best = [n+1]; bestB = [None]
    # DP over subsets is 2^n — n up to ~50 too big; use branch & bound
    # order b's by usefulness; recursive with pruning on remaining demand
    primes = sorted(need)
    def rec(i, chosen, rem):
        # rem: dict prime->remaining exponent
        if all(v <= 0 for v in rem.values()):
            if len(chosen) < best[0]:
                best[0] = len(chosen); bestB[0] = list(chosen)
            return
        if i >= n or len(chosen) + 1 >= best[0]: return
        # prune: max possible supply from remaining
        b = I[i]
        # take b
        rem2 = dict(rem)
        for p, e in bfacts[i].items():
            if p in rem2: rem2[p] -= e
        rec(i+1, chosen+[b], rem2)
        # skip b
        rec(i+1, chosen, rem)
    rec(0, [], dict(need))
    return best[0], bestB[0]

def worst_over_intervals(A, t_max=60):
    w = 0; wt = None; wB = None
    M = max(A)
    for t in range(1, t_max+1):
        s, B = min_B(A, t)
        if s > w: w, wt, wB = s, t, B
    return w, wt, wB

print("=== #708 round 1: exact min-B values for adversarial small A ===")
cases = {
  "A={2,3} (n=2, g(2)=2 check)": [2, 3],
  "A={6,10,15} (n=3 semiprime triangle)": [6, 10, 15],
  "A={2,3,5} (n=3 primes)": [2, 3, 5],
  "A={6,10,14,15} (n=4)": [6, 10, 14, 15],
  "A={6,10,15,21} (n=4 tri+21)": [6, 10, 15, 21],
  "A={2,3,5,7} (n=4 primes)": [2, 3, 5, 7],
  "A={6,10,14,15,21} (n=5)": [6, 10, 14, 15, 21],
  "A={6,10,14,15,21,35} (n=6 K4-edge)": [6, 10, 14, 15, 21, 35],
}
for name, A in cases.items():
    w, wt, wB = worst_over_intervals(A, t_max=40)
    print(f"{name}: worst min|B| = {w} at t={wt}, B={wB}")

print("\nKey known-check: g(2)=2 (A={2,3}: worst should be 2), g(3)>=4 evidence")
