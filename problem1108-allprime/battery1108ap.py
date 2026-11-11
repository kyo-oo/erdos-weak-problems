#!/usr/bin/env python3
# Independent dual-method battery for Kernel 30 — Erdős #1108
# THE ALL-PRIME ISOLATED-MINIMUM LAW + THE RESIDUE-1 LAW.
# Method A: direct p-adic valuation of the big-int sum (division loop).
# Method B: Legendre formula v_p(b!) = sum(floor(b/p^i)) + the residue-1
#           structural check (sum = b! * Q with Q % p == 1).
# Plus: the kernel receipt instances verified exactly; the not-square /
# not-cube witness 362910 checked by isqrt.
import random
from itertools import combinations

random.seed(1108)

def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r

def vp_direct(n, p):
    if n == 0:
        return 0
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c

def vp_legendre(n, p):
    c, q = 0, p
    while q <= n:
        c += n // q
        q *= p
    return c

def singleton_bottom_ok(p, b, S):
    if S.count(b) != 1:
        return False
    thresh = p * (b // p + 1)
    return all(a >= thresh for a in S if a != b)

PRIMES = [2, 3, 5, 7, 11, 13]
cases = 0

# Exhaustive: every singleton-bottom list over small universes,
# all primes 2..13, subsets of the higher-block pool up to size 3.
for p in PRIMES:
    for b in range(0, 14):
        thresh = p * (b // p + 1)
        pool = [a for a in range(thresh, 15) if a != b]
        for r in range(0, 4):
            for extra in combinations(pool, r):
                S = [b] + list(extra)
                assert singleton_bottom_ok(p, b, S), (p, b, S)
                tot = sum(fact(a) for a in S)
                A = vp_direct(tot, p)
                B = vp_legendre(b, p)
                assert A == B, ("LAW", p, b, S, A, B)
                Q, R = divmod(tot, fact(b))
                assert R == 0 and Q % p == 1, ("RESIDUE", p, b, S)
                cases += 1

# Random deep: bigger lists, bigger elements.
for _ in range(3000):
    p = random.choice(PRIMES)
    b = random.randint(0, 40)
    thresh = p * (b // p + 1)
    extra = [random.randint(thresh, 400) for _ in range(random.randint(0, 6))]
    S = [b] + extra
    if not singleton_bottom_ok(p, b, S):
        continue
    tot = sum(fact(a) for a in S)
    A = vp_direct(tot, p)
    B = vp_legendre(b, p)
    assert A == B, ("LAW-DEEP", p, b, S, A, B)
    Q, R = divmod(tot, fact(b))
    assert R == 0 and Q % p == 1, ("RESIDUE-DEEP", p, b, S)
    cases += 1

# The kernel receipt instances, exactly as in the Lean file.
RECEIPTS = [
    (2, 3, [3, 4, 9], 1),
    (3, 2, [2, 9, 13], 0),
    (5, 7, [7, 25, 31], 1),
    (7, 13, [13, 49, 55], 1),
    (11, 5, [5, 121, 130], 0),
]
for p, b, S, expect in RECEIPTS:
    assert singleton_bottom_ok(p, b, S), (p, b, S)
    tot = sum(fact(a) for a in S)
    A = vp_direct(tot, p)
    assert A == expect == vp_legendre(b, p), (p, b, S, A, expect)
    Q, R = divmod(tot, fact(b))
    assert R == 0 and Q % p == 1, ("RECEIPT-RESIDUE", p, b, S)
    cases += 1

# The not-square / not-cube witness: 3! + 4! + 9! = 362910.
W = fact(3) + fact(4) + fact(9)
assert W == 362910, W
r = isqrt = int(W ** 0.5)
while r * r > W:
    r -= 1
while (r + 1) * (r + 1) <= W:
    r += 1
assert r * r != W and (r + 1) * (r + 1) != W
# exact integer cube check
c = round(W ** (1.0 / 3.0))
for cc in (c - 1, c, c + 1):
    assert cc ** 3 != W
cases += 1

print(f"ERDOS1108_ALLPRIME_BATTERY_GREEN cases={cases}")
