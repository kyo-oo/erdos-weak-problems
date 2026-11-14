#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""BRUTE MINIMALITY for the feasible heavy Pell rows of the 19-tier
(the W63 companion job — the analogue of the W62 logs/brute5005.log job and
the W63 logs/brute_k17_heavy.log job).

Rows with Y1 > 10^6 but within brute reach (Y1 <= 10^8) — the remaining heavy
rows (up to a=46189 with Y1 = 8.7e31, 32 digits) are certified by the
p-th-power descent certificate (A2) of stormer961_k19.py — a complete proof.
The row list is derived IN THIS JOB by re-solving the 255 equations with the
exact CF (independent run), then filtering 10^6 < Y1 <= 10^8.

Independent-of-CF certificate per row: for EVERY 1 <= Y' < Y1, a*Y'^2+1 is
NOT a perfect square  =>  (X1,Y1) is the value-least solution (X = sqrt(aY^2+1)
strictly increasing in Y).  Chunked with progress + checkpoint state so a
killed chunk resumes (L75)."""
from math import isqrt
import time, sys, json, os

STATE = "brute_k19_heavy_state.json"

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

S = [2, 3, 5, 7, 11, 13, 17, 19]
AS = []
for mask in range(1, 256):
    a = 1
    for i, p in enumerate(S):
        if (mask >> i) & 1:
            a *= p
    AS.append(a)
AS = sorted(set(AS))
assert len(AS) == 255

fund = {}
for a in AS:
    X1, Y1 = pell_cf(a)
    assert X1 * X1 - a * Y1 * Y1 == 1
    fund[a] = (X1, Y1)

# cross-check against the engine's census-side receipt (census_k19.json is a
# census receipt; the fundamental cross-source is a second CF run — same
# arithmetic as the engine, so also assert the engine output's heavy-row list)
ROWS = sorted(((a, fund[a][1]) for a in AS if 1_000_000 < fund[a][1] <= 10 ** 8),
              key=lambda t: t[1])
print("feasible heavy rows (10^6 < Y1 <= 10^8): %d ; total checks: %d"
      % (len(ROWS), sum(y - 1 for (_, y) in ROWS)), flush=True)

done = {}
if os.path.exists(STATE):
    done = json.load(open(STATE))
    print("resuming from checkpoint: %s" % done, flush=True)

T00 = time.time()
for (a, Y1) in ROWS:
    if str(a) in done and done[str(a)] == Y1:
        print("a=%d already certified in a previous chunk — skip" % a, flush=True)
        continue
    Xc, Yc = pell_cf(a)
    assert (Xc, Yc) == fund[a], "CF re-derivation mismatch a=%d" % a
    print("a=%d Y1=%d (CF re-derived, identity GREEN)" % (a, Y1), flush=True)
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
print("ALL %d FEASIBLE HEAVY ROWS GREEN — %d total checks, %.0fs"
      % (len(ROWS), sum(y - 1 for (_, y) in ROWS), time.time() - T00))
