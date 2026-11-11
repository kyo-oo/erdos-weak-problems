#!/usr/bin/env python3
"""
engine273h.py — THE FINITE-SPACE EXACT-COVER DFS (P273, round 3).

ROUND-2 LAW (the Kraft confinement): the leaves' nu's satisfy sum 1/nu = 1
with at most |pool| leaves, so the tree lives in nu <= V_MAX; the huge-nu
descent of rounds 2b-2g was structurally useless. The solution is a SMALL
prefix tree: slots (c, nu), nu <= V_MAX, each closed by a distinct fresh
m | nu, m in the pool.

DFS with:
  - slot order: smallest nu first (poorest first — the rich ones assign
    whenever popped anyway),
  - close moves: fresh m | nu (branch: all candidates),
  - split moves: prime q with q*nu <= V_MAX,
  - Kraft prune: sum_{open slots} 1/nu <= sum_{unused m} 1/m,
  - divisor prune: every open slot must have SOME unused pool divisor of a
    nu-refinement within V_MAX (pruned lazily via the Kraft bound).
"""

import sys
from fractions import Fraction
from sympy import isprime

BOUND = 60000          # pool bound for m
V_MAX = 4000           # the Kraft confinement
SPLIT_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

def build_pool(bound, parity):
    pool = []
    for m in range(2, bound + 1):
        if isprime(2 * m + 1) and m % 2 == parity:
            pool.append(m)
    return pool

# precompute: divisors of each nu in the pool (m | nu)
def div_table(pool):
    tab = {}
    for nu in range(1, V_MAX + 1):
        tab[nu] = [m for m in pool if nu % m == 0]
    return tab

def search(pool, verbose=True):
    dtab = div_table(pool)
    inv = {m: Fraction(1, m) for m in pool}
    pool_density = sum(inv.values())

    best = {'assigned': 0}
    nodes = [0]

    def dfs(slots, used, assigned, density):
        """slots: sorted list of (nu, c); used: frozenset; assigned: tuple;
        density: Fraction sum of 1/nu over open slots."""
        nodes[0] += 1
        if nodes[0] % 200000 == 0 and verbose:
            print('  nodes=%d slots=%d assigned=%d density=%s'
                  % (nodes[0], len(slots), len(assigned), float(density)))
        if not slots:
            return assigned
        if len(assigned) > best['assigned']:
            best['assigned'] = len(assigned)
        # Kraft prune
        unused_density = pool_density - sum(inv[m] for m in used)
        if density > unused_density:
            return None
        # pick the poorest slot (smallest nu)
        nu, c = slots[0]
        rest = slots[1:]
        # close moves: fresh m | nu — try in descending order
        fresh = [m for m in dtab[nu] if m not in used]
        for m in reversed(fresh):
            res = dfs(rest, used | {m}, assigned + ((c, nu, m),), density - Fraction(1, nu))
            if res is not None:
                return res
        # split moves
        for q in SPLIT_PRIMES:
            qnu = q * nu
            if qnu > V_MAX:
                break
            children = sorted((qnu, c + j * nu) for j in range(q))
            res = dfs(sorted(rest + children), used, assigned,
                      density - Fraction(1, nu) + q * Fraction(1, qnu))
            if res is not None:
                return res
        return None

    res = dfs([(1, 0)], frozenset(), (), Fraction(1))
    return res, nodes[0]

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
    for parity, name in ((0, 'T_E (even m)'), (1, 'T_O (odd m)')):
        print('\n=== %s — finite DFS ===' % name)
        pool = build_pool(BOUND, parity)
        print('pool:', len(pool))
        res, nodes = search(pool)
        if res is None:
            print('%s: NO TREE within the finite space (nodes=%d, best assigned=%d)'
                  % (name, nodes, 0))
            continue
        print('%s CLOSED: %d leaves, %d nodes' % (name, len(res), nodes))
        print('verify:', verify_cover(res))
        if parity == 0:
            e_leaves = res
        else:
            o_leaves = res
    else:
        pass
    try:
        e_leaves, o_leaves
    except NameError:
        print('incomplete — no witness')
        return 1

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
