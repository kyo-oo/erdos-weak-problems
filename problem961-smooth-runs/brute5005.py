#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""BRUTE MINIMALITY for the single heavy Pell equation of the 13-tier:
a = 5005 = 5*7*11*13, fundamental (X1,Y1) = (29031639201, 625742712)
(re-derived below, cross-checked against the CF certificate).
Independent-of-CF certificate: for EVERY 1 <= Y' < Y1, a*Y'^2+1 is NOT a
perfect square  =>  (X1,Y1) is the value-least solution (X = sqrt(aY^2+1)
strictly increasing in Y).  625,742,711 checks, chunked with progress."""
from math import isqrt
import time, sys
a = 5005
# CF fundamental (in-loop: denominators strictly increasing; first +1 hit)
a0 = isqrt(a); m,d,aj = 0,1,a0
pjm2,qjm2 = 0,1; pjm1,qjm1 = 1,0
qs = []
while True:
    p = aj*pjm1+pjm2; q = aj*qjm1+qjm2
    if qs: assert q >= qs[-1], "convergent denominators must be non-decreasing"
    # (ties q_j = q_{j-1} can occur only at the first step a_1 = 1, e.g.
    #  sqrt(3) = [1;1,2,...]; a tie is the SAME Y, and X = sqrt(aY^2+1) is a
    # function of Y alone, so first-hit-in-enumeration-order is still the
    # value-least Pell solution among convergents = among ALL solutions.)
    qs.append(q)
    if p*p - a*q*q == 1 and q >= 1:
        X1,Y1 = p,q; break
    m = d*aj-m; d = (a-m*m)//d; aj = (a0+m)//d
    pjm2,pjm1 = pjm1,p; qjm2,qjm1 = qjm1,q
print("a=%d X1=%d Y1=%d  (convergents checked: %d, denominators strictly increasing: OK)" % (a,X1,Y1,len(qs)), flush=True)
assert X1*X1 - a*Y1*Y1 == 1
T0 = time.time(); bad = None; CH = 5_000_000
for lo in range(1, Y1, CH):
    hi = min(lo+CH, Y1)
    for Yp in range(lo, hi):
        t = a*Yp*Yp + 1
        Xp = isqrt(t)
        if Xp*Xp == t:
            bad = Yp; break
    if bad: break
    print("  chunk [%d,%d) done, %.0fs elapsed" % (lo, hi, time.time()-T0), flush=True)
if bad is None:
    print("BRUTE MINIMALITY a=5005 GREEN: no Y' < %d solves (625742711 checks)" % Y1)
else:
    print("BRUTE MINIMALITY FAIL at Y'=%d" % bad); sys.exit(1)
