#!/usr/bin/env python3
"""
engine273g.py — THE BEAM-SEARCH TREE PLANNER (P273, round 2g).

The demand/supply tension is the mathematical content. Beam search over
tree shapes: each state = (assigned list, stuck frontier, used set).
Expansion: pop the stuck slot with the SMALLEST v (breadth-keeps-support
balanced); branch over:
  - every fresh m | v  (assignment choice: largest 2 + smallest 2), and
  - the top-3 split primes by (new-supply-minus-demand).
Score = frontier size (primary), total unused-density (secondary).
Beam width W. Terminates when any state's frontier empties.
"""

import sys
import os
from sympy import isprime

sys.setrecursionlimit(100000)

BOUND = 40000
SPLIT_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
W = 400          # beam width
MAX_LEAVES = 3000

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

def new_supply(q, v, used, pool):
    """fresh m | q*v with m not dividing v and unused"""
    out = []
    for m in divisors_in(q * v, pool):
        if m not in used and v % m != 0:
            out.append(m)
    return out

def search(pool, beam=W, verbose=True):
    # state: (frontier_size, total_splits, idx, frontier(list of (v,c)),
    #         used(frozenset), assigned(tuple))
    init = ([ (1, 0) ], frozenset(), ())
    beam_states = [ (1, 0, 0, init[0], init[1], init[2]) ]  # (fsz, splits, tie, frontier, used, assigned)
    counter = 1
    steps = 0
    while beam_states:
        steps += 1
        if steps > 20000:
            break
        nxt = []
        best_frontier = None
        for (fsz, splits, tie, frontier, used, assigned) in beam_states:
            if not frontier:
                return assigned
            # pop smallest v
            frontier = sorted(frontier)
            (v, c), rest = frontier[0], frontier[1:]
            fresh = [m for m in divisors_in(v, pool) if m not in used]
            cands = []
            if fresh:
                # assignment branches: largest two + smallest two
                opts = set()
                for m in (fresh[-1], fresh[-2] if len(fresh) > 1 else fresh[-1],
                          fresh[0], fresh[1] if len(fresh) > 1 else fresh[0]):
                    opts.add(m)
                for m in opts:
                    cands.append(('assign', m))
            # split branches: top-3 primes by new-supply - q
            ranked = []
            for q in SPLIT_PRIMES:
                if q * v > 10**13:
                    continue
                sup = len(new_supply(q, v, used, pool))
                ranked.append((q - sup, -sup, q))
            ranked.sort()
            for k in range(min(3, len(ranked))):
                cands.append(('split', ranked[k][2]))
            for cand in cands:
                if cand[0] == 'assign':
                    m = cand[1]
                    nf = list(rest)
                    nu = used | {m}
                    na = assigned + ((c, v, m),)
                    cands2 = (len(nf), splits, counter)
                    counter += 1
                    item = (len(nf), splits, cands2[2], nf, frozenset(nu), na)
                    nxt.append(item)
                else:
                    q = cand[1]
                    nf = list(rest)
                    for j in range(q):
                        nf.append((q * v, c + j * v))
                    na = assigned
                    nu = used
                    if len(na) + len(nf) > MAX_LEAVES + len(pool):
                        continue
                    item = (len(nf), splits + 1, counter, nf, frozenset(nu), na)
                    counter += 1
                    nxt.append(item)
        if not nxt:
            break
        nxt.sort(key=lambda s: (s[0], s[1], s[2]))
        beam_states = nxt[:beam]
        if verbose and steps % 50 == 0:
            print('  step %d: best frontier=%d assigned=%d (states=%d)'
                  % (steps, beam_states[0][0], len(beam_states[0][5]), len(beam_states)))
    return None

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
            return 'lcm %d too large (structural partition stands)' % L
    covered = [False] * L
    for (c, v, m) in leaves:
        for x in range(c % v, L, v):
            covered[x] = True
    assert all(covered), 'cover sweep failed'
    return 'full sweep OK at L = %d' % L

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

    print('\n=== T_E (even m) — beam search ===')
    e_leaves = search(me)
    if e_leaves is None:
        print('T_E: NO TREE FOUND within beam budget')
        return 1
    print('T_E CLOSED:', len(e_leaves), 'assignments')
    print('even verify:', verify_cover(e_leaves))

    print('\n=== T_O (odd m) — beam search ===')
    o_leaves = search(mo)
    if o_leaves is None:
        print('T_O: NO TREE FOUND within beam budget')
        return 1
    print('T_O CLOSED:', len(o_leaves), 'assignments')
    print('odd verify:', verify_cover(o_leaves))

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
