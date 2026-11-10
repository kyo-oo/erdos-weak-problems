#!/usr/bin/env python3
"""
engine273j.py — THE GREEDY-COVER ENGINE (P273, round 3): construct the
covering DIRECTLY.

THE REDUCTION (Lemma 1 + the parity lift): it suffices to construct ONE
covering of Z by distinct-residue classes (b_i mod m_i) with DISTINCT
moduli m_i drawn from M_even = {m even : 2m+1 prime}.  (The even/odd lifts
then use M_even for the even side and M_odd for the odd side.)

CONSTRUCTION (the classical greedy, DFS over the m-choice):
  x = 0, 1, 2, ...: the first UNCOVERED x receives an unused modulus m,
  class (x mod m).  Branch over the unused m's; prune by density; verify
  with the CRT-TREE (recursive interval-lattice covering check), never the
  raw lcm sweep (lcm ~ 10^16).
"""

import sys
from fractions import Fraction
from sympy import isprime

def build_M_even(bound):
    return [m for m in range(2, bound + 1) if m % 2 == 0 and isprime(2 * m + 1)]

# ---------------------------------------------------------------- CRT-tree verifier
def covers_Z(classes):
    """classes: list of (a, m).  Recursive check: does U (a mod m) = Z?
    Method: process the classes; maintain pending residue classes as
    (c mod M) intervals; a pending node (c, M) is covered if some class
    (a, m) with m | M has c = a (mod m); else split by the smallest
    modulus class not yet dividing M.  Bounded by the over-density."""
    if not classes:
        return False
    # order classes by modulus descending (split by the big ones first)
    cls = sorted(classes, key=lambda t: -t[1])
    from functools import lru_cache
    sys.setrecursionlimit(100000)

    # iterative worklist of (c, M) with the class-index bound:
    # node (c, M) must be covered by classes[0..i) structure; we process
    # classes one at a time in order; a node meets class i:
    #   if m_i | M: covered iff c == a_i (mod m_i)
    #   else: split into m_i children (c + j*M mod M*m_i/g) — only the
    #         NOT-covered children survive... careful: m_i need not divide M.
    # Standard approach: split M up to L = lcm step by step.
    work = [(0, 1, 0)]           # (residue, modulus, next class index)
    nodes = 0
    while work:
        nodes += 1
        if nodes > 3_000_000:
            return False         # too big — treat as not-covering
        c, M, i = work.pop()
        if i == len(cls):
            return False         # an uncovered residue class survives
        a, m = cls[i]
        # bring M up to a multiple of m: split by g = m/gcd(M, m) steps
        g = m // gcd_(M, m)
        # the node (c mod M) splits into g children (c + j*M) mod (M*g)
        # (M*g = lcm(M, m)); each child then checks the class:
        Mg = M * g
        for j in range(g):
            cj = (c + j * M) % Mg
            if cj % m == a % m:
                continue          # covered by class i
            work.append((cj, Mg, i + 1))
    return True

def gcd_(a, b):
    while b:
        a, b = b, a % b
    return a

# ---------------------------------------------------------------- the greedy DFS
def greedy_cover(pool, verbose=True):
    """returns the class list or None"""
    pool = sorted(pool)
    inv = {m: Fraction(1, m) for m in pool}
    total_density = sum(inv.values())
    n = len(pool)
    nodes = [0]

    def covered_by(x, chosen):
        for (a, m) in chosen:
            if x % m == a % m:
                return True
        return False

    def dfs(chosen, used, x0, density_used):
        nodes[0] += 1
        if nodes[0] % 100000 == 0 and verbose:
            print('  nodes=%d chosen=%d next_x~%d' % (nodes[0], len(chosen), x0))
        # find the first uncovered x >= x0 (scan; also cap)
        x = x0
        while x < x0 + 60000 and covered_by(x, chosen):
            x += 1
        if x >= x0 + 60000:
            # long covered run — verify fully
            if covers_Z(chosen):
                return chosen
            return None
        # prune: remaining density must be able to matter
        remaining = total_density - density_used
        if remaining < Fraction(1, 4 * x + 4) and len(chosen) >= 6:
            # heuristic: not enough density left to cover a gap at x —
            # actually gaps near x have density ~ ... weak prune; skip
            pass
        # choose an unused m for the class (x mod m)
        cands = [m for m in pool if m not in used]
        for m in sorted(cands):
            chosen2 = chosen + [(x % m, m)]
            if len(chosen2) == n:
                if covers_Z(chosen2):
                    return chosen2
                continue
            r = dfs(chosen2, used | {m}, x + 1, density_used + inv[m])
            if r is not None:
                return r
        return None

    return dfs([], set(), 0, Fraction(0)), nodes[0]

def main():
    pool = build_M_even(120)
    print('M_even <= 120 (%d):' % len(pool), pool)
    print('density:', float(sum(Fraction(1, m) for m in pool)))
    res, nodes = greedy_cover(pool)
    print('nodes:', nodes)
    if res is None:
        print('NO COVERING within the greedy budget')
        return 1
    print('\n*** COVERING FOUND (%d classes) ***' % len(res))
    for (a, m) in sorted(res, key=lambda t: t[1]):
        print('  y = %4d (mod %4d)   [p = %d]' % (a, m, 2 * m + 1))
    # full verify
    assert covers_Z(res)
    print('CRT-tree verify: COVERING CONFIRMED')
    # window sweep check
    L = 1
    for (_, m) in res:
        L = L * m // gcd_(L, m)
        if L > 5_000_000:
            break
    if L <= 5_000_000:
        cov = [False] * L
        for (a, m) in res:
            for x in range(a % m, L, m):
                cov[x] = True
        assert all(cov)
        print('window sweep OK at L = %d' % L)
    with open('COVER273_even.txt', 'w') as f:
        for (a, m) in sorted(res, key=lambda t: t[1]):
            f.write('%d %d\n' % (a, m))
    print('written: COVER273_even.txt')
    return 0

if __name__ == '__main__':
    sys.exit(main())
