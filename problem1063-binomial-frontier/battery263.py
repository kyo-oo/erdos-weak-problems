#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BATTERY 263 — Erdős #1063: INDEPENDENT verification of the W63 extension rows
n_18 = 31110, n_19 = 612, n_20 = 67203 (engine_round3.py claims), plus the
calibration rows k = 2..17. Second methods, disjoint from the engine's stack:

  (a) stdlib math.comb (CPython 3.12 C implementation — NOT gmpy2/GMP):
      full witness + completeness recount of every row k = 2..20.
  (b) KUMMER CARRY-COUNT route for v_q(C(n,k)) — digit-addition carries of
      k + (n-k) in base q, an algorithm disjoint from the engine's Legendre
      floor sums: witness receipts re-derived (exempt position + deficits),
      and wcount crosschecked on boundaries (first/last 500 points of every
      extension sweep) + 1000 pseudo-random interior points per new row.
  (c) sympy.binomial (third big-int implementation) at the three new witnesses.
"""
import sys, time
from math import comb, isqrt
import sympy

T0 = time.time()
FRONTIER = {2: 4, 3: 6, 4: 9, 5: 12, 6: 75, 7: 30, 8: 70, 9: 56, 10: 2403,
            11: 280, 12: 3465, 13: 210, 14: 793, 15: 4732, 16: 3213, 17: 1456,
            18: 31110, 19: 612, 20: 67203}

# ---------------------------------------------------------------- method (a)
def divcount(n, k):
    c = comb(n, k)
    return sum(1 for i in range(k) if c % (n - i) == 0)

def misses_comb(n, k):
    c = comb(n, k)
    return [i for i in range(k) if c % (n - i) != 0]

# ---------------------------------------------------------------- method (b)
def factor_small(m):
    f = {}
    for q in range(2, isqrt(m) + 1):
        while m % q == 0:
            f[q] = f.get(q, 0) + 1
            m //= q
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def vC_kummer(n, k, q):
    """v_q(C(n,k)) = number of carries when adding k and n-k in base q (Kummer)."""
    a, b, carries, c = k, n - k, 0, 0
    while a > 0 or b > 0 or c > 0:
        s = (a % q) + (b % q) + c
        a //= q; b //= q
        c = 1 if s >= q else 0
        carries += c
    return carries

def wcount_kummer(n, k):
    c = 0
    for i in range(k):
        x = n - i
        if all(e <= vC_kummer(n, k, q) for q, e in factor_small(x).items()):
            c += 1
    return c

def kummer_receipt(n, k):
    """exempt positions + all prime-power deficits via the Kummer route."""
    out = []
    for i in range(k):
        x = n - i
        deficits = [(q, e, vC_kummer(n, k, q)) for q, e in sorted(factor_small(x).items())
                    if e > vC_kummer(n, k, q)]
        if deficits:
            out.append((i, x, deficits))
    return out

# ---------------------------------------------------------------- run (a)
print("=" * 72)
print("BATTERY 263 — independent verification of the #1063 frontier k = 2..20")
print("=" * 72)
ok = True
print("(a) stdlib math.comb full recount (witness + completeness), k = 2..20:")
print("  k |  n_k | wcount | =k-1? | completeness pts | max wcount below | verdict")
for k in sorted(FRONTIER):
    nk = FRONTIER[k]
    wc = divcount(nk, k)
    wit_ok = wc >= k - 1
    max_below, comp_ok = -1, True
    for n in range(2 * k, nk):
        d = divcount(n, k)
        if d > max_below:
            max_below = d
        if d >= k - 1:
            comp_ok = False
            print("  COUNTEREXAMPLE k=%d n=%d divcount=%d" % (k, n, d))
    good = wit_ok and comp_ok
    ok = ok and good
    print("  %2d | %5d | %6d | %5s | %8d | %8d | %s"
          % (k, nk, wc, wit_ok, nk - 2 * k, max_below, "GREEN" if good else "RED"))

# ---------------------------------------------------------------- run (b)
print()
print("(b) Kummer carry-count route (disjoint algorithm), new rows k = 18, 19, 20:")
for k in (18, 19, 20):
    nk = FRONTIER[k]
    # witness receipt re-derivation
    rec = kummer_receipt(nk, k)
    wk = wcount_kummer(nk, k)
    print("  k=%d n_k=%d: Kummer wcount = %d (math.comb wcount = %d)  exempt receipts:"
          % (k, nk, wk, divcount(nk, k)))
    for (i, x, deficits) in rec:
        print("     i=%d  n-i=%d  deficits (q, v_q(n-i), v_q(C)) = %s" % (i, x, deficits))
    ok = ok and (wk == divcount(nk, k) == k - 1) and len(rec) == 1
    # boundary + interior sample crosscheck vs math.comb
    lo, hi = 2 * k, nk
    pts = list(range(lo, min(lo + 500, hi))) + list(range(max(hi - 500, lo), hi))
    rng = 92821
    r = rng
    for _ in range(1000):
        r = (r * 1103515245 + 12345) % 2147483648
        pts.append(lo + (r % (hi - lo)))
    bad = 0
    for n in sorted(set(pts)):
        if wcount_kummer(n, k) != divcount(n, k):
            bad += 1
            print("  KUMMER/COMB DISAGREEMENT k=%d n=%d" % (k, n))
    ok = ok and bad == 0
    print("     crosscheck %d boundary+interior points vs math.comb: %s"
          % (len(set(pts)), "GREEN" if bad == 0 else "RED(%d)" % bad))

# ---------------------------------------------------------------- run (c)
print()
print("(c) sympy.binomial third-implementation check at the new witnesses:")
for k in (18, 19, 20):
    nk = FRONTIER[k]
    c = sympy.binomial(nk, k)
    wc = sum(1 for i in range(k) if c % (nk - i) == 0)
    ok = ok and wc == k - 1
    print("  k=%d n_k=%d: sympy wcount = %d  -> %s" % (k, nk, wc, "GREEN" if wc == k - 1 else "RED"))

print()
print("BATTERY 263 %s — %.1fs" % ("ALL GREEN" if ok else "RED", time.time() - T0))
sys.exit(0 if ok else 1)
