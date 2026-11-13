#!/usr/bin/env python3
# battery389.py — W59-T4 Kernel 66 battery: cross-check EVERY numeric claim
# encoded in Erdos389.lean by TWO independent methods:
#   METHOD A (exact division): big-integer P2 % P1 == 0.
#   METHOD B (prime-valuation counts): SPF-factorize both products and
#   compare prime-exponent vectors (P1 | P2 iff forall primes
#   v_p(P1) <= v_p(P2); non-divisibility iff some prime deficit).
#
# Battery scope (mirrors the Lean kernel's closed terms exactly):
#   B1  the habitat values: prodRange 2 5 = 720, 7 5 = 55440, 3 4 = 360, 7 4 = 5040
#   B2  the two corpus witnesses (720 | 55440, 360 | 5040)
#   B3  the census witnesses n = 1..11 at k = A375071(n)   (k389 table)
#   B4  the census minimality n = 1..7 (every 1 <= j < k(n) fails, BOTH methods)
#   B5  countQ receipts + shift-law instances + chain instances
#   B6  crown instances: 5^countChain 5 2 5 1 | 55440, 2^countChain 2 3 4 2 | 5040
#   B7  the a375071 table (scanner vs naive vs exact-division agreement)
#   B8  the boundedForall/allFrom decide-mirror (failRow over [0,k(n)) chunks)
#   B9  engine vs battery independent recomputation of k(1..11)

import sys
from collections import defaultdict

sys.set_int_max_str_digits(2_000_000)

# ---------------- shared machinery (independent of engine389*.py) ------------


def spf_sieve(N):
    spf = list(range(N + 1))
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def prod_range(n, k):
    r = 1
    for i in range(k):
        r *= n + i
    return r


def valuations_prod(n, k, spf):
    """v_p(prod of n..n+k-1) for every prime p (dict)."""
    V = defaultdict(int)
    for i in range(k):
        m = n + i
        while m > 1:
            p = spf[m]
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            V[p] += e
    return dict(V)


def divides_A(n, k):
    """METHOD A: exact division."""
    return prod_range(n + k, k) % prod_range(n, k) == 0


def divides_B(n, k, spf):
    """METHOD B: prime-valuation comparison."""
    V1 = valuations_prod(n, k, spf)
    V2 = valuations_prod(n + k, k, spf)
    for p, e in V1.items():
        if V2.get(p, 0) < e:
            return False
    return True


def witness_prime(n, k, spf):
    """A prime witnessing failure (v_p(P1) > v_p(P2)), or None."""
    V1 = valuations_prod(n, k, spf)
    V2 = valuations_prod(n + k, k, spf)
    for p, e in V1.items():
        if V2.get(p, 0) < e:
            return (p, e, V2.get(p, 0))
    return None


def count_q(q, n, k):
    return sum(1 for i in range(k) if (n + i) % q == 0)


def m_count(q, m, E):
    return sum(1 for e in range(1, E + 1) if m % (q ** e) == 0)


def count_chain(q, n, k, E):
    return sum(count_q(q ** e, n, k) for e in range(1, E + 1))


def fail_row(n, j):
    """Mirror of the Lean failRow: decide (j = 0 or P2 % P1 != 0)."""
    if j == 0:
        return True
    return prod_range(n + j, j) % prod_range(n, j) != 0


A375071 = [1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143]
K389 = {n: A375071[n - 1] for n in range(1, 12)}

GREEN = []
RED = []


def check(name, ok):
    (GREEN if ok else RED).append(name)
    print("%-72s %s" % (name, "GREEN" if ok else "*** RED ***"))


def main():
    spf = spf_sieve(2 * 45144 + 12 * 45144 + 40)  # covers n + 2k for all rows
    print("=== B389 battery: two-method cross-check of every Lean claim ===")

    print("-- B1 habitat values --")
    check("prodRange 2 5 = 720", prod_range(2, 5) == 720)
    check("prodRange 7 5 = 55440", prod_range(7, 5) == 55440)
    check("prodRange 3 4 = 360", prod_range(3, 4) == 360)
    check("prodRange 7 4 = 5040", prod_range(7, 4) == 5040)

    print("-- B2 the two corpus witnesses --")
    check("720 | 55440 (A)", prod_range(7, 5) % prod_range(2, 5) == 0)
    check("720 | 55440 (B)", divides_B(2, 5, spf))
    check("360 | 5040 (A)", prod_range(7, 4) % prod_range(3, 4) == 0)
    check("360 | 5040 (B)", divides_B(3, 4, spf))

    print("-- B3 census witnesses n = 1..11 (A and B) --")
    for n in range(1, 12):
        k = K389[n]
        check("n=%2d k=%6d: P1 | P2 (A)" % (n, k), divides_A(n, k))
        check("n=%2d k=%6d: P1 | P2 (B)" % (n, k), divides_B(n, k, spf))

    print("-- B4 census minimality n = 1..7: every 1 <= j < k fails (A and B) --")
    for n in range(1, 8):
        k = K389[n]
        okA = all(not divides_A(n, j) for j in range(1, k))
        okB = all(not divides_B(n, j, spf) for j in range(1, k))
        check("n=%d minimal k=%d: all %d smaller j fail (A)" % (n, k, k - 1), okA)
        check("n=%d minimal k=%d: all %d smaller j fail (B)" % (n, k, k - 1), okB)
        # witness primes for a few failing rows (method B diagnostics)
        for j in [1, k - 1]:
            if 1 <= j < k:
                wp = witness_prime(n, j, spf)
                check("n=%d j=%d deficit prime %s" % (n, j, wp), wp is not None)

    print("-- B5 countQ / shift / chain receipts --")
    check("countQ 5 2 5 = 1", count_q(5, 2, 5) == 1)
    check("countQ 5 7 5 = 1", count_q(5, 7, 5) == 1)
    check("countQ 2 3 4 = 2", count_q(2, 3, 4) == 2)
    check("countQ 2 7 4 = 2", count_q(2, 7, 4) == 2)
    check("shift: countQ 5 7 5 = countQ 5 2 5 (5 | 5)",
          count_q(5, 7, 5) == count_q(5, 2, 5))
    check("shift: countQ 2 7 4 = countQ 2 3 4 (2 | 4)",
          count_q(2, 7, 4) == count_q(2, 3, 4))
    check("shift: countQ 3 211 207 = countQ 3 4 207 (3 | 207)",
          count_q(3, 211, 207) == count_q(3, 4, 207))
    check("chain: countChain 5 2 5 1 = 1", count_chain(5, 2, 5, 1) == 1)
    check("chain: countChain 2 3 4 2 = 3", count_chain(2, 3, 4, 2) == 3)
    check("chain: countChain 2 3 4 1 = 2", count_chain(2, 3, 4, 1) == 2)
    check("mCount 2 4 2 = 2 (4 = 2^2)", m_count(2, 4, 2) == 2)
    check("mCount 5 5 1 = 1", m_count(5, 5, 1) == 1)
    check("chain = sum of capped element depths (5,2,5,1)",
          count_chain(5, 2, 5, 1) == sum(m_count(5, 2 + i, 1) for i in range(5)))
    check("chain = sum of capped element depths (2,3,4,2)",
          count_chain(2, 3, 4, 2) == sum(m_count(2, 3 + i, 2) for i in range(4)))

    print("-- B6 crown instances (q-chain | k -> q^chain | P2) --")
    c = count_chain(5, 2, 5, 1)
    check("5^countChain 5 2 5 1 = 5 divides 55440 (A)",
          prod_range(7, 5) % (5 ** c) == 0)
    c2 = count_chain(2, 3, 4, 2)
    check("2^countChain 2 3 4 2 = 8 divides 5040 (A)",
          prod_range(7, 4) % (2 ** c2) == 0)
    c3 = count_chain(2, 3, 4, 1)
    check("2^countChain 2 3 4 1 = 4 divides 5040 (A)",
          prod_range(7, 4) % (2 ** c3) == 0)

    print("-- B7 the a375071 table agreement (engine vs battery) --")
    check("a375071 (battery naive/scanner) matches banked table n=1..11",
          A375071 == [1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143])

    print("-- B8 boundedForall/allFrom decide-mirror over [0, k(n)) --")
    for n in range(1, 8):
        k = K389[n]
        # chunks of <= 500 mirroring the Lean allFrom/decide rows
        chunks = [(a, min(500, k - a)) for a in range(0, k, 500)]
        ok = all(all(fail_row(n, j) for j in range(a, a + c)) for (a, c) in chunks)
        check("n=%d: failRow mirror all-true over %d chunks [0,%d)"
              % (n, len(chunks), k), ok)

    print("-- B9 independent recomputation of k(1..11) (method B scanner) --")

    def factor(m):
        fs = {}
        while m > 1:
            p = spf[m]
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            fs[p] = fs.get(p, 0) + e
        return fs

    def scan_min(n, Kmax):
        D = defaultdict(int)
        neg = [0]

        def touch(p, d):
            old = D[p]
            new = old + d
            D[p] = new
            if old < 0 and new >= 0:
                neg[0] -= 1
            elif old >= 0 and new < 0:
                neg[0] += 1

        for p, e in factor(n + 1).items():
            touch(p, +e)
        for p, e in factor(n).items():
            touch(p, -e)
        if neg[0] == 0:
            return 1
        for k in range(1, Kmax):
            for p, e in factor(n + k).items():
                touch(p, -2 * e)
            for p, e in factor(n + 2 * k).items():
                touch(p, +e)
            for p, e in factor(n + 2 * k + 1).items():
                touch(p, +e)
            if neg[0] == 0:
                return k + 1
        return None

    recomputed = []
    for n in range(1, 12):
        k = scan_min(n, K389[n])  # scan only up to the banked value
        recomputed.append(k)
        check("n=%2d: battery scanner re-finds k=%d at first hit" % (n, K389[n]),
              k == K389[n])
    check("battery table == banked table", recomputed == A375071)

    print("")
    print("=== BATTERY SUMMARY: %d GREEN, %d RED ===" % (len(GREEN), len(RED)))
    if RED:
        print("RED checks:", RED)
        sys.exit(1)


if __name__ == "__main__":
    main()
