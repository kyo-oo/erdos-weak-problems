#!/usr/bin/env python3
# engine389b.py — the FAST valuation scanner for minimal k(n) (Erdos #389).
#
# P1 | P2 iff for every prime p: v_p(P1) <= v_p(P2) (unique factorization).
# Track D[p] = v_p(P2) - v_p(P1) incrementally as k grows:
#   k -> k+1:  (n+k) moves from block 2 to block 1 (D -= 2 v_p(n+k)),
#              (n+2k), (n+2k+1) join block 2 (D += v_p of each).
# Solution iff all D[p] >= 0, maintained via a negative-entry counter.
# Every scanner hit is re-verified by exact big-integer division, and the
# whole table is cross-checked against the naive engine389.py brute force.

import sys
from collections import defaultdict

sys.set_int_max_str_digits(2_000_000)


def spf_sieve(N):
    """Smallest-prime-factor sieve up to N (inclusive)."""
    spf = list(range(N + 1))
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == i:  # i is prime
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factor(spf, m):
    """Prime factorization dict of m >= 1 via the SPF sieve."""
    fs = {}
    while m > 1:
        p = spf[m]
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        fs[p] = fs.get(p, 0) + e
    return fs


def scan_min_k(n, Kmax, spf=None):
    """First k in [1, Kmax] with n..(n+k-1) | (n+k)..(n+2k-1), else None."""
    if spf is None:
        spf = spf_sieve(n + 2 * Kmax + 16)
    D = defaultdict(int)
    state = {"neg": 0}

    def touch(p, d):
        old = D[p]
        new = old + d
        D[p] = new
        if old < 0 and new >= 0:
            state["neg"] -= 1
        elif old >= 0 and new < 0:
            state["neg"] += 1

    # k = 1: B1 = {n}, B2 = {n+1}
    for p, e in factor(spf, n + 1).items():
        touch(p, +e)
    for p, e in factor(spf, n).items():
        touch(p, -e)
    if state["neg"] == 0:
        return 1
    for k in range(1, Kmax):
        for p, e in factor(spf, n + k).items():
            touch(p, -2 * e)
        for p, e in factor(spf, n + 2 * k).items():
            touch(p, +e)
        for p, e in factor(spf, n + 2 * k + 1).items():
            touch(p, +e)
        if state["neg"] == 0:
            return k + 1
    return None


def prod_range(n, k):
    r = 1
    for i in range(k):
        r *= n + i
    return r


def exact_ok(n, k):
    """Exact-divide re-verification of a scanner hit."""
    P1 = prod_range(n, k)
    P2 = prod_range(n + k, k)
    return P2 % P1 == 0


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    Kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 6
    import time
    t0 = time.time()
    k = scan_min_k(n, Kmax)
    t1 = time.time()
    if k is None:
        print("n=%d: NO k <= %d (%.1fs)" % (n, Kmax, t1 - t0))
    else:
        ok = exact_ok(n, k)
        print("n=%d: minimal k = %d  exact-divide-recheck=%s  (%.1fs)"
              % (n, k, ok, t1 - t0))
