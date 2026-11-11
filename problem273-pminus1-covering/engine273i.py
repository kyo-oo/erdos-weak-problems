#!/usr/bin/env python3
"""
engine273i.py — THE EGYPTIAN-CARVER ENGINE (P273, round 3).

ROUND-2 LAWS (2a-2h):
  L-A (Kraft confinement): the leaves' nu satisfy sum 1/nu = 1; the tree is
      a SMALL object (nu <= ~V_MAX; huge-nu descent useless).
  L-B (residue freedom): assignability depends ONLY on nu (m | nu), never c.
  L-C (trivial matching): a leaf at nu = m*k takes ITS OWN m — distinctness
      is F's distinctness. The matching problem DISAPPEARS.
  L-D (Mirsky-Newman): exact covers need repeated moduli — so k = 1 for all
      is impossible; dilution k > 1 is the freedom.

REDUCTION: find F = {m_1 < ... < m_r} subseteq M_even and dilutions
k_i (products of small primes) with
  (a) sum_i 1/(m_i k_i) = 1 EXACTLY,
  (b) the multiset {m_i k_i} is prefix-tree realizable — checked by THE
      SLOT CARVER: process leaves ascending; maintain slots; leaf nu needs
      a slot (c, nu') with nu' | nu; the slot splits into nu/nu' children
      (one consumed, the rest new slots at nu); success iff all slots die.

Search: iterative deepening over small F (density carriers, m <= 120) and
k in the small-prime products, exact Fraction arithmetic.
"""

import sys
from fractions import Fraction
from sympy import isprime

def build_M_even(bound):
    return [m for m in range(2, bound + 1) if m % 2 == 0 and isprime(2 * m + 1)]

K_CHOICES = [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54, 64, 72]

def carver_ok(nus):
    """prefix-tree realizability: process ascending; slots as multiset of
    moduli; leaf nu consumes a slot nu' | nu, spawning nu/nu' - 1 slots at nu.
    Returns (ok, residue_slots) — residues are irrelevant (L-B) so slots are
    just moduli with multiplicity."""
    from collections import Counter
    # slots: Counter of moduli; each slot needs a residue but any residue
    # works — the carver only tracks moduli (L-B).
    slots = Counter({1: 1})
    for nu in nus:  # ascending
        # find a slot modulus d with d | nu, prefer the LARGEST such d
        best = None
        for d in slots:
            if d > 0 and nu % d == 0 and slots[d] > 0:
                if best is None or d > best:
                    best = d
        if best is None:
            return False
        slots[best] -= 1
        if slots[best] == 0:
            del slots[best]
        # children: nu/best of them at modulus nu; one is the leaf
        extra = nu // best - 1
        if extra:
            slots[nu] += extra
    # all slots must be consumed
    return all(v == 0 for v in slots.values()) and not slots

def egyptian_search(M, target=Fraction(1), max_terms=14, verbose=True):
    """DFS over F (ascending m) and k-choices, exact Fractions.
    Prune: remaining density of the m's below the current one must cover
    the residual target."""
    # density available from m >= M[i], undiluted (k=1) — upper bound
    suffix = [Fraction(0)] * (len(M) + 1)
    for i in range(len(M) - 1, -1, -1):
        suffix[i] = suffix[i + 1] + Fraction(1, M[i])

    best = {'gap': Fraction(10), 'sol': None}
    nodes = [0]

    def dfs(i, resid, chosen):
        nodes[0] += 1
        if nodes[0] % 2_000_000 == 0 and verbose:
            print('  nodes=%d resid=%s chosen=%d' % (nodes[0], float(resid), len(chosen)))
        if resid == 0:
            # check the carver on the nu multiset
            nus = sorted(m * k for (m, k) in chosen)
            if carver_ok(nus):
                best['gap'] = Fraction(0)
                best['sol'] = list(chosen)
                return True
            return False
        if i >= len(M) or len(chosen) >= max_terms:
            return False
        if resid < 0:
            return False
        # prune: even undiluted, the tail can't reach
        if suffix[i] < resid:
            # track the best near-miss
            gap = resid
            if gap < best['gap']:
                best['gap'] = gap
                best['sol'] = list(chosen)
            return False
        m = M[i]
        # option 1: skip m
        if dfs(i + 1, resid, chosen):
            return True
        # option 2: use m with some dilution k: contributes 1/(m*k)
        # (k=1 first — biggest chunk; then larger k)
        for k in K_CHOICES:
            c = Fraction(1, m * k)
            if c <= resid:
                if dfs(i + 1, resid - c, chosen + [(m, k)]):
                    return True
        return False

    ok = dfs(0, target, [])
    return ok, best, nodes[0]

def verify(leaves):
    """leaves: (m, k). nu = m*k. Structural verify: m | nu trivial, distinct
    m, 2m+1 prime; the carver already verified the tree."""
    ms = [m for (m, k) in leaves]
    assert len(set(ms)) == len(ms)
    for (m, k) in leaves:
        assert isprime(2 * m + 1)
        assert (m * k) % m == 0
    from math import gcd
    L = 1
    for (m, k) in leaves:
        L = L * (m * k) // gcd(L, m * k)
        if L > 20_000_000:
            return 'lcm too large (carver stands)'
    covered = [False] * L
    # re-derive the residues via the full carver (this time tracking c)
    from collections import Counter
    slots = {(0, 1)}
    out_classes = []
    for (m, k) in sorted(leaves, key=lambda mk: mk[0] * mk[1]):
        nu = m * k
        # find slot with d | nu
        pick = None
        for (c, d) in slots:
            if nu % d == 0:
                if pick is None or d > pick[1]:
                    pick = (c, d)
        (c, d) = pick
        slots.discard((c, d))
        for j in range(nu // d):
            if j == 0:
                out_classes.append((c % m, m))       # the leaf: covered by m
            else:
                slots.add((c + j * d, nu))
    assert not slots
    for (a, n) in out_classes:
        for x in range(a % n, L, n):
            covered[x] = True
    assert all(covered), 'cover sweep failed'
    return 'FULL SWEEP OK at L = %d (%d classes)' % (L, len(out_classes))

def main():
    M = build_M_even(120)
    print('M_even <= 120:', M)
    print('total density:', float(sum(Fraction(1, m) for m in M)))
    ok, best, nodes = egyptian_search(M)
    print('nodes:', nodes)
    if ok:
        print('\n*** TREE FOUND ***')
        for (m, k) in best['sol']:
            print('  m = %5d  k = %-3d  nu = %d   (p = %d)' % (m, k, m * k, 2 * m + 1))
        print('verify:', verify(best['sol']))
    else:
        print('\nno exact tree; best gap:', float(best['gap']), 'at')
        if best['sol']:
            for (m, k) in best['sol']:
                print('  m = %5d  k = %-3d' % (m, k))
    return 0

if __name__ == '__main__':
    sys.exit(main())
