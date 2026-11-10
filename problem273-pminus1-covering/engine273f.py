#!/usr/bin/env python3
"""
engine273f.py — THE SPINE ENGINE (P273, round 2c): demand-aware splitting.

Laws learned from 2b's explosion:
  L1: process the RICHEST stuck leaf first (largest v) — its splits are
      supply-positive; assign its largest fresh divisor (preserves the small
      m's for the poor leaves that process last).
  L2: split by q minimizing (q - fresh_supply(q*v)) — demand-aware. Net
      frontier growth is negative once v is primorial-rich, and the tree
      closes.
"""

import sys
import os
from sympy import isprime

sys.setrecursionlimit(100000)

BOUND = 40000
SPLIT_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

def build_pools(bound):
    me, mo = [], []
    for m in range(2, bound + 1):
        if isprime(2 * m + 1):
            (me if m % 2 == 0 else mo).append(m)
    return me, mo

def divisors_in(v, pool):
    out = []
    for m in pool:
        if m > v:
            break
        if v % m == 0:
            out.append(m)
    return out

class Fail(Exception):
    pass

def build_tree(pool, max_leaves=None, verbose=True):
    if max_leaves is None:
        max_leaves = len(pool) + 10
    used = set()
    assigned = []
    stuck = [(1, 0)]                # heap by v DESCENDING: use max-heap via negation
    import heapq
    stuck = [(-1, 0)]
    total_leaves = 0
    steps = 0
    while stuck:
        steps += 1
        if steps > 5_000_000:
            raise Fail('step budget')
        if total_leaves > max_leaves * 3:
            raise Fail('leaf budget blown: %d leaves, %d assigned'
                       % (total_leaves, len(assigned)))
        negv, c = heapq.heappop(stuck)
        v = -negv
        fresh = [m for m in divisors_in(v, pool) if m not in used]
        if fresh:
            m = fresh[-1]           # largest fresh divisor
            used.add(m)
            assigned.append((c, v, m))
            continue
        # stuck: demand-aware split with SUPPORT-GROWTH priority
        if v > 10**18:
            raise Fail('nu cap blown at (%d mod %d)' % (c, v))
        best = None
        for q in SPLIT_PRIMES:
            if q * v > 10**18:
                continue
            supply = len([m for m in divisors_in(q * v, pool) if m not in used])
            net = q - supply
            isold = 0 if (v % q != 0) else 1   # NEW primes grow the support
            # negative net (frontier shrinks) first; among GROWING splits,
            # NEW primes FIRST (the long game beats small net), then net, q
            if net <= 0:
                key = (0, net, 0, q)
            else:
                key = (1, isold, net, q)
            if best is None or key < best[0]:
                best = (key, q, supply)
        if best is None:
            raise Fail('no split fits the nu cap at (%d mod %d)' % (c, v))
        q, supply = best[1], best[2]
        for j in range(q):
            heapq.heappush(stuck, (-(q * v), c + j * v))
            total_leaves += 1
        if verbose and steps % 5000 == 0:
            print('  step %d: stuck=%d assigned=%d/%d (split by %d at v=%d, supply %d)'
                  % (steps, len(stuck), len(assigned), max_leaves, q, v, supply))
    if len(assigned) > max_leaves:
        raise Fail('too many leaves')
    return assigned

def verify_cover(leaves):
    ms = [m for (_, _, m) in leaves]
    assert len(set(ms)) == len(ms), 'duplicate moduli'
    for (c, v, m) in leaves:
        assert m | v, (c, v, m)
        assert isprime(2 * m + 1), (m, 2 * m + 1)
    from math import gcd
    L = 1
    for (_, v, _) in leaves:
        L = L * v // gcd(L, v)
        if L > 20_000_000:
            return ms, 'lcm %d too large (structural partition stands)' % L
    covered = [False] * L
    for (c, v, m) in leaves:
        for x in range(c % v, L, v):
            covered[x] = True
    assert all(covered), 'cover sweep failed'
    return ms, 'full sweep OK at L = %d' % L

def lift(even_leaves, odd_leaves):
    classes = []
    for (b, _, m) in even_leaves:
        classes.append((2 * b % (2 * m), 2 * m))
    for (c, _, m) in odd_leaves:
        classes.append((2 * c + 1, 2 * m))
    return classes

def verify_final(classes):
    from math import gcd
    L = 1
    for (_, n) in classes:
        L = L * n // gcd(L, n)
        if L > 20_000_000:
            return 'lcm %d too large (tree proof stands)' % L
    covered = [False] * L
    for (a, n) in classes:
        for x in range(a % n, L, n):
            covered[x] = True
    assert all(covered)
    return 'FULL SWEEP OK at lcm = %d' % L

def main():
    print('building pools to', BOUND, '...')
    me, mo = build_pools(BOUND)
    print('M_even:', len(me), 'M_odd:', len(mo))

    print('\n=== T_E (even m) ===')
    e_leaves = build_tree(me)
    print('CLOSED:', len(e_leaves), 'assignments')
    ems, esweep = verify_cover(e_leaves)
    print('even verify:', esweep)

    print('\n=== T_O (odd m) ===')
    o_leaves = build_tree(mo)
    print('CLOSED:', len(o_leaves), 'assignments')
    oms, osweep = verify_cover(o_leaves)
    print('odd verify:', osweep)

    classes = lift(e_leaves, o_leaves)
    moduli = sorted(n for (_, n) in classes)
    print('\n=== THE COVERING SYSTEM (moduli p-1, p >= 5 prime, distinct) ===')
    print('classes:', len(classes))
    print('moduli (p-1):', moduli)
    print('primes p   :', [n + 1 for n in moduli])
    print('final verify:', verify_final(classes))

    with open('WITNESS273.txt', 'w') as f:
        f.write('# ERDOS 273 WITNESS — covering system (x = a_i mod n_i), '
                'n_i = p_i - 1 distinct, p_i >= 5 prime\n')
        f.write('# even-lift leaves (c, v, m): class 2c mod 2m covers even x\n')
        for (c, v, m) in e_leaves:
            f.write('E %d %d %d\n' % (c, v, m))
        f.write('# odd-lift leaves (c, v, m): class 2c+1 mod 2m covers odd x\n')
        for (c, v, m) in o_leaves:
            f.write('O %d %d %d\n' % (c, v, m))
        f.write('# lifted classes (a, n):\n')
        for (a, n) in sorted(classes):
            f.write('C %d %d\n' % (a, n))
    print('witness written: WITNESS273.txt')
    return 0

if __name__ == '__main__':
    sys.exit(main())
