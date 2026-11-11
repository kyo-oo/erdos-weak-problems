#!/usr/bin/env python3
"""Verification battery for the periodic-tower analysis (session 011).

All arithmetic EXACT (Fraction). Every theorem of
PERIODIC_TOWER_ANALYSIS.md is checked here. A check failing = the note
is wrong. Run: python3 verify_periodic_tower.py
"""
from fractions import Fraction
from itertools import chain, combinations
import random
import sys

PASS = 0
FAIL = 0

def check(name, cond):
    global PASS, FAIL
    if cond:
        PASS += 1
        print(f"  PASS  {name}")
    else:
        FAIL += 1
        print(f"  FAIL  {name}")

def sig(J): return sum(Fraction(1, 2**j) for j in J)
def tau(J): return sum(Fraction(j, 2**j) for j in J)
def v(s): return Fraction(s, 2**s)
def run_mass(s, d): return sum(Fraction(a, 2**a) for a in range(s+1, s+d))

print("=== Theorem 1: AP identity (rationality engine) ===")
c, d = 9, 24
q = Fraction(1, 2**d)
closed = Fraction(c, 2**c) / (1 - q) + Fraction(d, 2**c) * q / (1 - q)**2
partial = sum(Fraction(c + k*d, 2**(c + k*d)) for k in range(40))
check("AP partial (K=40) matches closed form to < 2^-90", abs(partial - closed) < Fraction(1, 2**90))
check("AP closed form is rational (finite denominator)", closed.denominator < 10**30)
check("AP value == 1649267605504/93824981052075", closed == Fraction(1649267605504, 93824981052075))

print("=== tau identity: sum_{j=1}^{d-1} j 2^-j = 2 - (d+1) 2^{1-d} ===")
for d_ in [3, 5, 6, 11, 24]:
    check(f"d={d_}", tau(range(1, d_)) == 2 - Fraction(d_+1, 2**(d_-1)))

print("=== Corollary 2.1: Tower family reproduction (Pi=empty, full window) ===")
tower_receipts = [4, 11, 26, 57, 120, 247, 502]  # Kill #6 CI receipts
for d_ in range(3, 12):
    J = list(range(1, d_))
    s = tau(J) / (1 - sig(J))
    m = 2**(d_) - d_ - 1                     # = m_{d-2} = 2^{(d-2)+2} - (d-2) - 3
    check(f"d={d_}: s == 2^d-d-1 == m_(d-2) == {m}", s == m and s.denominator == 1)
for k, m_k in enumerate(tower_receipts):
    check(f"m_{k+1} = {m_k} in reproduced family", (2**(k+3) - (k+3) - 1) == m_k)

print("=== Corollary 2.2: census reproduction (Kill #6 min-support family) ===")
census = {9: [10, 11, 13, 14], 13: [14, 15, 16, 20, 21, 24],
          21: [22, 23, 24, 26, 27, 32], 35: [36, 37, 38, 39, 42, 43, 45, 46]}
for s, Q in census.items():
    check(f"{{{s}}} == {Q}", v(s) == sum(Fraction(a, 2**a) for a in Q))
    J = [a - s for a in Q]
    check(f"  s={s} from gadget equation (Pi=empty)", (tau(J) / (1 - sig(J))) == s)

print("=== Theorem 2: general gadget equation (random triples) ===")
random.seed(7)
ok = True
n_solvable = 0
for _ in range(300):
    d_ = random.randint(3, 9)
    perm = list(range(1, d_)); random.shuffle(perm)
    k1 = random.randint(0, d_-1); k2 = random.randint(0, d_-1-k1)
    Pi, J = sorted(perm[:k1]), sorted(perm[k1:k1+k2])
    if not J: continue
    den = 1 + sig(Pi) - sig(J)
    if den == 0: continue
    s = (tau(J) - tau(Pi)) / den
    if s.denominator == 1 and s > 0:
        n_solvable += 1
        s = int(s)
        dv = Fraction(s) + sum(Fraction(s+j, 2**j) for j in Pi)
        ev = sum(Fraction(s+j, 2**j) for j in J)
        if dv != ev: ok = False
check(f"gadget equation balanced on all {n_solvable} solvable random triples", ok)

print("=== Theorem 3: finite image at fixed d ===")
powerset = lambda r: chain.from_iterable(combinations(r, k) for k in range(len(r)+1))
for d_, expected in [(3, {1, 4}), (4, {1, 4, 11}), (5, {1, 2, 4, 6, 11, 26})]:
    sols = set()
    for Pi in powerset(range(1, d_)):
        rest = [j for j in range(1, d_) if j not in Pi]
        for J in powerset(rest):
            if not J: continue
            den = 1 + sig(Pi) - sig(J)
            if den == 0: continue
            s = (tau(J) - tau(Pi)) / den
            if s.denominator == 1 and s > 0: sols.add(int(s))
    check(f"d={d_}: solvable set == {sorted(expected)}", sols == expected)
    check(f"d={d_}: |image| <= 3^(d-1)", len(sols) <= 3**(d_-1))

print("=== Theorem 4: run-surplus identity + boundary ===")
for s in [9, 35, 1000, 16777190, 16777191, 16777192, 2**24, 2**24 + 100]:
    derived = Fraction(1, 2**s) * (2 - (s + 25) * Fraction(1, 2**23))  # d=24
    check(f"s={s}: R-v identity (d=24)", run_mass(s, 24) - v(s) == derived)
check("boundary at s=2^24-25=16777191 (zero surplus)",
      run_mass(16777191, 24) - v(16777191) == 0)
check("s=16777192 already negative", run_mass(16777192, 24) - v(16777192) < 0)

print("=== Theorem 5: funding death beyond the boundary ===")
s = 2**24 + 100
borrow = v(s) - run_mass(s, 24)
later_capacity = sum(Fraction(1, 2**(s + j*24 - 1)) for j in range(1, 50))
check("borrow > ALL later runs' surplus combined (d=24, s=2^24+100)", borrow > later_capacity)
s2 = 2**25 + 7
borrow2 = v(s2) - run_mass(s2, 24)
later2 = sum(Fraction(1, 2**(s2 + j*24 - 1)) for j in range(1, 50))
check("same at s=2^25+7", borrow2 > later2)

print("=== Singleton family engine (window <= 20) ===")
W = 20
states = {(0, 0): 0}
for j in range(1, W + 1):
    wA, wB = 1 << (W - j), j << (W - j)
    new = dict(states)
    for (A, B), mj in states.items():
        key = (A + wA, B + wB)
        nmj = max(mj, j)
        if key not in new or new[key] > nmj:
            new[key] = nmj
    states = new
sols = {}
for (A, B), mj in states.items():
    if A == 0 and B == 0: continue
    den = (1 << W) - A
    if den <= 0: continue
    if B % den == 0:
        s = B // den
        if 1 <= s <= 200 and (s not in sols or mj < sols[s]):
            sols[s] = mj
expected = {1:1, 2:4, 3:5, 4:2, 5:9, 6:8, 7:17, 9:5, 11:3, 12:12, 13:11,
            15:7, 17:15, 18:14, 19:13, 21:11, 26:4, 27:19, 32:14, 35:11,
            57:5, 73:15, 78:16, 116:12, 120:6, 125:17, 166:18, 197:9,
            198:16, 199:15, 200:16}
check("family (s -> min window) matches session receipts", sols == expected)
check("tower members 4,11,26,57,120 present with windows 2,3,4,5,6",
      all(sols.get(m) == w for m, w in [(4,2),(11,3),(26,4),(57,5),(120,6)]))
# spot-verify two family members directly:
check("{57} == {58,59,60,61,62} (direct)",
      v(57) == sum(Fraction(a, 2**a) for a in [58,59,60,61,62]))

print()
print(f"RESULT: {PASS} passed, {FAIL} failed")
sys.exit(1 if FAIL else 0)
