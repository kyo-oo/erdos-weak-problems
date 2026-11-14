#!/usr/bin/env python3
"""PROBE v3: 127 Pell fundamentals for S={2,3,5,7,11,13,17}, OPTIMIZED.
Per-step cost O(size) via mod-M filter; exact p^2-aq^2==1 check only on mod-hits."""
from math import isqrt
import time, json, sys
S = [2, 3, 5, 7, 11, 13, 17]
AS = []
for mask in range(1, 128):
    a = 1
    for i, p in enumerate(S):
        if (mask >> i) & 1:
            a *= p
    AS.append(a)
AS = sorted(set(AS))
assert len(AS) == 127 and AS[0] == 2 and AS[-1] == 510510
M = (1 << 61) - 1   # prime modulus for the cheap filter
def pell_fundamental(a, cap=3_000_000):
    a0 = isqrt(a)
    if a0 * a0 == a:
        return None
    am = a % M
    m, d, aj = 0, 1, a0
    pjm2, qjm2 = 0, 1
    pjm1, qjm1 = 1, 0
    steps = 0
    lastq = 0
    nhit = 0
    while True:
        p = aj * pjm1 + pjm2
        q = aj * qjm1 + qjm2
        assert q >= lastq, "denominators non-decreasing"
        lastq = q
        pm = p % M
        if pm * pm % M == (am * (q % M) % M * (q % M) + 1) % M:
            nhit += 1
            if p * p - a * q * q == 1 and q >= 1:
                return (p, q, steps, nhit)
        m = d * aj - m
        d = (a - m * m) // d
        aj = (a0 + m) // d
        pjm2, pjm1 = pjm1, p
        qjm2, qjm1 = qjm1, q
        steps += 1
        if steps > cap:
            raise RuntimeError("runaway a=%d steps>%d" % (a, cap))
# anchors from the certified k13 tier (subset of AS)
ANCH = {2: (3, 2), 3: (2, 1), 5: (9, 4), 6: (5, 2), 7: (8, 3), 13: (649, 180),
        61: (1766319049, 226153980), 5005: (44268809311, 625742712)}
T0 = time.time()
rows = []
for a in AS:
    t = time.time()
    X1, Y1, steps, nhit = pell_fundamental(a)
    assert X1 * X1 - a * Y1 * Y1 == 1
    if a in ANCH:
        assert (X1, Y1) == ANCH[a], "anchor FAIL a=%d" % a
    rows.append((a, X1, Y1, steps))
    dt = time.time() - t
    if dt > 1.0 or len(str(Y1)) > 8:
        print("a=%7d: Y1digits=%-6d X1digits=%-6d steps=%-7d modhits=%d %.1fs"
              % (a, len(str(Y1)), len(str(X1)), steps, nhit, dt), flush=True)
print("ALL 127 fundamentals done, total %.1fs" % (time.time() - T0), flush=True)
def strip(n):
    for p in S:
        while n % p == 0:
            n //= p
    return n
alive = [(a, Y1) for (a, X1, Y1, st) in rows if strip(Y1) == 1]
dead = [(a, Y1) for (a, X1, Y1, st) in rows if strip(Y1) != 1]
print("alive (Y1 17-smooth): %d ; dead: %d" % (len(alive), len(dead)), flush=True)
print("heavy alive rows (Y1 > 10^6):")
for (a, Y1) in sorted(alive, key=lambda r: -r[1])[:12]:
    if Y1 > 10 ** 6:
        print("   a=%7d Y1=%d" % (a, Y1), flush=True)
json.dump([(a, str(X1), str(Y1), st) for (a, X1, Y1, st) in rows],
          open("probe_k17_fund.json", "w"))
print("saved probe_k17_fund.json", flush=True)
