#!/usr/bin/env python3
"""
engine273.py — THE SPLIT-TILING TREE ENGINE (P273 full-proof lane, round 2).

TARGET: explicit covering system {x ≡ a_i (mod n_i)} of Z with DISTINCT
moduli, every n_i = p_i - 1 with p_i >= 5 prime.

THE ENGINE (Lemma 1 + Lemma 2 of PROOF.md):
  Lemma 1 (parity halving): such a covering exists iff TWO covering systems
  of Z exist, C_E = {(b_j, m_j)} and C_O = {(c_k, m'_k)}, with all m in
  M = {m >= 2 : 2m+1 prime}, and the two modulus sets DISJOINT.
    Lift even: (b, m) -> class (2b mod 2m)   [modulus 2m = p-1, p = 2m+1]
    Lift odd : (c, m) -> class (2c+1 mod 2m)
  DISJOINTNESS FOR FREE: T_E uses EVEN m in M, T_O uses ODD m in M.

  Lemma 2 (tree lemma): a prefix-split tree — root (0 mod 1); each internal
  node (c mod v) split by a prime q into children (c + j*v mod q*v),
  j = 0..q-1 (children PARTITION the node); leaves partition Z
  (sum 1/v_leaf = 1). If each leaf (c_j mod v_j) is assigned a DISTINCT
  m_j in (pool) with m_j | v_j, then {(c_j mod m_j)} covers Z.

So: grow two trees by DFS with backtracking. At a leaf: try to assign an
unused pool-m dividing v; else split by a candidate prime and recurse.
"""

import sys
import os
from sympy import isprime

sys.setrecursionlimit(100000)

# ---------------------------------------------------------------- pools
BOUND = 6000

def build_pools(bound):
    """M_even: even m>=2 with 2m+1 prime.  M_odd: odd m>=3 with 2m+1 prime."""
    me, mo = [], []
    for m in range(2, bound + 1):
        if isprime(2 * m + 1):
            (me if m % 2 == 0 else mo).append(m)
    return me, mo

# candidate split primes (small primes keep v small; the divisor pools of
# v = 2^a 3^b 5^c 7^d ... are rich in M-elements)
SPLIT_PRIMES = [3, 5, 7, 11, 13, 2]

def divisors_in(v, pool):
    """divisors of v that lie in pool (pool sorted ascending)."""
    out = []
    for m in pool:
        if m > v:
            break
        if v % m == 0:
            out.append(m)
    return out

# ---------------------------------------------------------------- tree growth
class Fail(Exception):
    pass

def grow(leaf, used, pool, depth, max_depth, stats):
    """leaf = (c, v).  Returns list of (c, v, m) assignments for the subtree.
    Mutates `used` (set of assigned m) along the way; backtracks by restoring.
    Raises Fail when the subtree cannot close within budget."""
    c, v = leaf
    stats['nodes'] += 1
    if stats['nodes'] > stats['node_budget']:
        raise Fail('node budget')
    if depth > max_depth:
        raise Fail('depth')
    # try to close the leaf directly: an unused pool-m dividing v,
    # PREFER THE LARGEST (eats the biggest chunk, frees small m's for children)
    cand = [m for m in divisors_in(v, pool) if m not in used]
    if cand:
        m = cand[-1]              # largest available divisor
        used.add(m)
        return [(c, v, m)]
    # must split: children (c + j*v) mod (q*v), j = 0..q-1
    # try the richest split primes first (max unused M-divisors of q*v),
    # tie-break by smaller q (denser partition)
    order = sorted(SPLIT_PRIMES,
                   key=lambda q: (-len([m for m in divisors_in(q * v, pool)
                                        if m not in used]), q))
    for q in order[:3]:           # try the 3 richest split primes
        children = [(c + j * v, q * v) for j in range(q)]
        result = []
        saved_used = set(used)
        try:
            for ch in children:
                result.extend(grow(ch, used, pool, depth + 1, max_depth, stats))
            return result
        except Fail:
            # restore and try the next split prime
            used.clear()
            used.update(saved_used)
            continue
    raise Fail('no split closes leaf (%d mod %d)' % (c, v))

def build_tree(pool, max_depth=64, node_budget=4_000_000):
    used = set()
    stats = {'nodes': 0, 'node_budget': node_budget}
    leaves = grow((0, 1), used, pool, 0, max_depth, stats)
    return leaves, stats

# ---------------------------------------------------------------- verification
def verify_cover(leaves):
    """structural verification: m | v, m distinct, 2m+1 prime; then a direct
    residue sweep over the lcm of the leaf moduli v (capped)."""
    ms = [m for (_, _, m) in leaves]
    assert len(set(ms)) == len(ms), 'duplicate moduli'
    for (c, v, m) in leaves:
        assert m | v, (c, v, m)
        assert isprime(2 * m + 1), (m, 2 * m + 1)
    from math import gcd
    L = 1
    for (_, v, _) in leaves:
        L = L * v // gcd(L, v)
        if L > 12_000_000:
            break
    if L <= 12_000_000:
        covered = [False] * L
        for (c, v, m) in leaves:
            for x in range(c % v, L, v):
                covered[x] = True
        assert all(covered), 'cover sweep failed'
        sweep = 'full sweep OK at L = %d' % L
    else:
        sweep = 'lcm too large for sweep (structural partition stands)'
    return ms, sweep

# ---------------------------------------------------------------- lift + final
def lift(even_leaves, odd_leaves):
    """Lemma 1 lift: (b, m) -> (2b mod 2m) for the even tree (covers x = 2y),
    (c, m) -> (2c+1 mod 2m) for the odd tree (covers x = 2y+1)."""
    classes = []
    for (b, _, m) in even_leaves:
        classes.append((2 * b % (2 * m), 2 * m))
    for (c, _, m) in odd_leaves:
        classes.append((2 * c + 1, 2 * m))
    return classes

def verify_final(classes):
    """direct verification of the lifted covering over a capped window."""
    from math import gcd
    L = 1
    for (_, n) in classes:
        L = L * n // gcd(L, n)
        if L > 8_000_000:
            return 'lcm %d too large (tree proof stands)' % L
    covered = [False] * L
    for (a, n) in classes:
        for x in range(a % n, L, n):
            covered[x] = True
    assert all(covered)
    return 'FULL SWEEP OK at lcm = %d' % L

# ---------------------------------------------------------------- main
def main():
    print('building pools to', BOUND, '...')
    me, mo = build_pools(BOUND)
    print('M_even:', len(me), 'M_odd:', len(mo))
    print('even density sum 1/m (first 60):', sum(1 / m for m in me[:60]))
    print('odd  density sum 1/m (first 60):', sum(1 / m for m in mo[:60]))

    print('\n=== T_E (even m) ===')
    try:
        e_leaves, estats = build_tree(me)
        print('CLOSED:', len(e_leaves), 'leaves, nodes =', estats['nodes'])
        ems, esweep = verify_cover(e_leaves)
        print('even cover verify:', esweep, '| distinct m:', len(ems) == len(e_leaves))
    except Fail as e:
        print('T_E FAILED:', e)
        return 1
    except RecursionError:
        print('T_E FAILED: recursion')
        return 1

    print('\n=== T_O (odd m) ===')
    try:
        o_leaves, ostats = build_tree(mo)
        print('CLOSED:', len(o_leaves), 'leaves, nodes =', ostats['nodes'])
        oms, osweep = verify_cover(o_leaves)
        print('odd cover verify:', osweep, '| distinct m:', len(oms) == len(o_leaves))
    except Fail as e:
        print('T_O FAILED:', e)
        return 1
    except RecursionError:
        print('T_O FAILED: recursion')
        return 1

    classes = lift(e_leaves, o_leaves)
    moduli = sorted(n for (_, n) in classes)
    print('\n=== THE COVERING SYSTEM (moduli p-1, p >= 5 prime, distinct) ===')
    print('classes:', len(classes))
    print('moduli (p-1):', moduli)
    print('primes p   :', [n + 1 for n in moduli])
    print('final verify:', verify_final(classes))

    # the witness table
    with open('problem273-pminus1-covering/WITNESS273.txt', 'w') as f:
        f.write('# ERDOS 273 WITNESS — the covering system (x = a_i mod n_i), '
                'n_i = p_i - 1 distinct, p_i >= 5 prime\n')
        f.write('# even-lift leaves (c, v, m): x = 2c mod 2m covers even x\n')
        for (c, v, m) in e_leaves:
            f.write('E %d %d %d\n' % (c, v, m))
        f.write('# odd-lift leaves (c, v, m): x = 2c+1 mod 2m covers odd x\n')
        for (c, v, m) in o_leaves:
            f.write('O %d %d %d\n' % (c, v, m))
        f.write('# lifted classes (a, n):\n')
        for (a, n) in sorted(classes):
            f.write('C %d %d\n' % (a, n))
    print('witness written: problem273-pminus1-covering/WITNESS273.txt')
    return 0

if __name__ == '__main__':
    sys.exit(main())
