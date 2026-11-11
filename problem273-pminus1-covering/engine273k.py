#!/usr/bin/env python3
"""
engine273k.py — THE SIEVE-GREEDY COVER (P273, round 3): deterministic first
path + swap-repair hill-climb + the CRT-tree verification.

Target: distinct classes (b_i mod m_i), m_i in M_even distinct, covering Z.
(The parity lift then builds the p-1 covering: even side M_even, odd side
M_odd.)
"""

import sys
import random
from sympy import isprime

def build_M_even(bound):
    return [m for m in range(2, bound + 1) if m % 2 == 0 and isprime(2 * m + 1)]

def gcd_(a, b):
    while b:
        a, b = b, a % b
    return a

# ---------------------------------------------------------------- CRT-tree verify
def covers_Z(classes):
    cls = sorted(classes, key=lambda t: -t[1])
    work = [(0, 1, 0)]
    nodes = 0
    while work:
        nodes += 1
        if nodes > 2_000_000:
            return False
        c, M, i = work.pop()
        if i == len(cls):
            return False
        a, m = cls[i]
        g = m // gcd_(M, m)
        if g == 1:
            # m | M: covered iff c == a mod m
            if c % m == a % m:
                continue
            work.append((c, M, i + 1))
            continue
        Mg = M * g
        for j in range(g):
            cj = (c + j * M) % Mg
            if cj % m == a % m:
                continue
            work.append((cj, Mg, i + 1))
    return True

# ---------------------------------------------------------------- the sieve greedy
W = 1 << 20

def build(order):
    """deterministic greedy with the given modulus order; returns
    (classes, gap_count, first_gaps)."""
    cov = bytearray(W)
    chosen = []
    for m in order:
        try:
            x = cov.index(0)
        except ValueError:
            break                     # fully covered in-window
        a = x % m
        chosen.append((a, m))
        n = (W - a + m - 1) // m
        cov[a::m] = b'\x01' * n
    gaps = cov.count(0)
    first = []
    if gaps:
        idx = 0
        it = 0
        while len(first) < 8:
            try:
                idx = cov.index(0, idx)
            except ValueError:
                break
            first.append(idx)
            idx += 1
    return chosen, gaps, first

def main():
    pool = build_M_even(400)
    print('M_even <= 400:', len(pool), 'density %.4f' % sum(1.0/m for m in pool))
    # first path: ascending order
    chosen, gaps, first = build(sorted(pool))
    print('ascending order: %d classes, window gaps = %d' % (len(chosen), gaps))
    if gaps:
        print('first gaps:', first)
    if gaps == 0 and covers_Z(chosen):
        print('*** COVERING FOUND (ascending) ***')
        report(chosen)
        return 0
    # swap-repair hill-climb with restarts
    best = (gaps, sorted(pool))
    rng = random.Random(2718281)
    for trial in range(400):
        order = list(best[1])
        if trial > 0:
            # random perturbation: shuffles + swaps targeting gap positions
            for _ in range(rng.randint(1, 6)):
                i, j = rng.randrange(len(order)), rng.randrange(len(order))
                order[i], order[j] = order[j], order[i]
        ch, g, _ = build(order)
        if g < best[0]:
            best = (g, order)
            print('trial %d: gaps -> %d' % (trial, g))
            if g == 0 and covers_Z(ch):
                print('*** COVERING FOUND (trial %d) ***' % trial)
                report(ch)
                return 0
    print('no covering; best gap count = %d' % best[0])
    ch, g, first = build(best[1])
    print('best first gaps:', first)
    return 1

def report(chosen):
    for (a, m) in sorted(chosen, key=lambda t: t[1]):
        print('  y = %6d (mod %4d)   [p = %d]' % (a, m, 2 * m + 1))
    assert covers_Z(chosen)
    print('CRT-tree verify: COVERING CONFIRMED')
    with open('COVER273_even.txt', 'w') as f:
        for (a, m) in sorted(chosen, key=lambda t: t[1]):
            f.write('%d %d\n' % (a, m))
    print('written: COVER273_even.txt')

if __name__ == '__main__':
    sys.exit(main())
