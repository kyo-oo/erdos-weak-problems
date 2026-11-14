#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""BRUTE MINIMALITY for the four feasible heavy Pell rows of the 17-tier
(the W63 companion job — the analogue of the W62 logs/brute5005.log job).

Rows (a, Y1) with Y1 > 10^6 but within brute reach (the five monster rows
a=1309/3094/36465/85085/2431 with Y1 in [3.8e9, 2.2e13] are certified by the
p-th-power descent certificate (A2) of stormer961_k17.py — a complete proof;
the a=5005 row carries the W62 receipt logs/brute5005.log: 625,742,711 checks):

    a=17017   Y1=   2 373 732    ( 2 373 731 checks)
    a=34034   Y1=  13 786 506   (13 786 505 checks)
    a= 1105   Y1=  48 828 432   (48 828 431 checks)
    a=13090   Y1=  87 429 738   (87 429 737 checks)

Independent-of-CF certificate per row: for EVERY 1 <= Y' < Y1, a*Y'^2+1 is
NOT a perfect square  =>  (X1,Y1) is the value-least solution (X = sqrt(aY^2+1)
strictly increasing in Y).  Chunked with progress + checkpoint state so a
killed chunk resumes (L75)."""
from math import isqrt
import time, sys, json, os

ROWS = [(17017, 2373732), (34034, 13786506), (1105, 48828432), (13090, 87429738)]
STATE = "brute_k17_heavy_state.json"

def pell_cf(a):
    a0 = isqrt(a)
    m, d, aj = 0, 1, a0
    pjm2, qjm2 = 0, 1
    pjm1, qjm1 = 1, 0
    qs = []
    while True:
        p = aj * pjm1 + pjm2
        q = aj * qjm1 + qjm2
        if qs:
            assert q >= qs[-1], "convergent denominators must be non-decreasing"
        qs.append(q)
        if p * p - a * q * q == 1 and q >= 1:
            return p, q
        m = d * aj - m
        d = (a - m * m) // d
        aj = (a0 + m) // d
        pjm2, pjm1 = pjm1, p
        qjm2, qjm1 = qjm1, q

done = {}
if os.path.exists(STATE):
    done = json.load(open(STATE))
    print("resuming from checkpoint: %s" % done, flush=True)

# cross-check source: the engine's fundamentals (probe JSON == engine CF)
FUND = {int(r[0]): (int(r[1]), int(r[2])) for r in json.load(open("probe_k17_fund.json"))}

T00 = time.time()
for (a, Y1) in ROWS:
    if str(a) in done:
        print("a=%d already certified in a previous chunk — skip" % a, flush=True)
        continue
    X1, Y1c = pell_cf(a)
    assert (X1, Y1c) == FUND[a], \
        "CF row mismatch a=%d: %s vs engine %s" % (a, (X1, Y1c), FUND[a])
    assert Y1c == Y1, "row table mismatch a=%d" % a
    assert X1 * X1 - a * Y1 * Y1 == 1
    print("a=%d X1=%d Y1=%d (CF re-derived, identity GREEN)" % (a, X1, Y1), flush=True)
    T0 = time.time()
    bad = None
    CH = 5_000_000
    for lo in range(1, Y1, CH):
        hi = min(lo + CH, Y1)
        for Yp in range(lo, hi):
            t = a * Yp * Yp + 1
            Xp = isqrt(t)
            if Xp * Xp == t:
                bad = Yp
                break
        if bad:
            break
        print("  a=%d chunk [%d,%d) done, %.0fs elapsed (total %.0fs)"
              % (a, lo, hi, time.time() - T0, time.time() - T00), flush=True)
        done[str(a)] = hi
        json.dump(done, open(STATE, "w"))
    if bad is None:
        print("BRUTE MINIMALITY a=%d GREEN: no Y' < %d solves (%d checks)"
              % (a, Y1, Y1 - 1), flush=True)
        done[str(a)] = Y1
        json.dump(done, open(STATE, "w"))
    else:
        print("BRUTE MINIMALITY FAIL a=%d at Y'=%d" % (a, bad))
        sys.exit(1)

assert all(done[str(a)] == y for (a, y) in ROWS)
print("ALL FOUR HEAVY ROWS GREEN — %d total checks, %.0fs"
      % (sum(y - 1 for (_, y) in ROWS), time.time() - T00))
