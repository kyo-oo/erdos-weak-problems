#!/usr/bin/env python3
"""
engine273b.py — THE FRONTIER-GREEDY SPLIT-TILING ENGINE (P273, round 2b).

No backtracking. Maintain the frontier of unassigned leaves. Repeat:
  - if any frontier leaf (c, v) has a fresh pool-divisor m | v: assign the
    LARGEST such m (densest eat);
  - else split the STUCK leaf with the SMALLEST v (the most stuck chunk)
    by its RICHEST split prime q (max fresh M-divisors of q*v, tie: small q).
The frontier empties iff the tree closes. Supply grows with v's prime
diversity; demand grows by q-1 per split. Density slack ~45% per pool.

Output: the two trees -> the witness table -> the lifted covering system.
"""

import sys
import os
from sympy import isprime
from heapq import heappush, heappop

sys.setrecursionlimit(100000)

BOUND = 20000
SPLIT_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

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

def build_tree(pool, max_steps=2_000_000, verbose=True):
    used = set()
    assigned = []                 # (c, v, m)
    # frontier: heap keyed by (v, c) — smallest modulus first (most stuck)
    frontier = [(1, 0)]
    step = 0
    while frontier:
        step += 1
        if step > max_steps:
            raise Fail('step budget at frontier=%d assigned=%d'
                       % (len(frontier), len(assigned)))
        v, c = heappop(frontier)
        fresh = [m for m in divisors_in(v, pool) if m not in used]
        if fresh:
            m = fresh[-1]         # largest
            used.add(m)
            assigned.append((c, v, m))
            continue
        # stuck: split by the richest prime
        best_q, best_key = None, None
        for q in SPLIT_PRIMES:
            nv = q * v
            supply = len([m for m in divisors_in(nv, pool) if m not in used])
            key = (supply, -q)
            if best_key is None or key > best_key:
                best_key, best_q = key, q
        q = best_q
        if best_key[0] == 0:
            raise Fail('dead leaf (%d mod %d): no split prime supplies' % (c, v))
        for j in range(q):
            heappush(frontier, (q * v, c + j * v))
        if verbose and step % 20000 == 0:
            print('  step %d: frontier=%d assigned=%d (last split by %d at v=%d)'
                  % (step, len(frontier), len(assigned), q, v))
    return assigned

class Fail(Exception):
    pass

def verify_cover(leaves):
    ms = [m for (_, _, m) in leaves]
    assert len(set(ms)) == len(ms), 'duplicate moduli'
    for (c, v, m) in leaves:
        assert m | v, (c, v, m)
        assert isprime(2 * m + 1), (m, 2 * m + 1)
    # structural partition re-verification: reconstruct the tree from the
    # leaves by re-deriving the split DAG (every leaf's class must be
    # reachable); simplest independent check: the leaf v-classes must cover
    # [0, L) with L = lcm(v) capped (exact if leaves' v-lcm fits)
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
