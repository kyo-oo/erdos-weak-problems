#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ENGINE ROUND 2 — Erdős #1063: THE BINOMIAL FRONTIER EXTENSION (S063 W62 volley).

Extends the certified frontier n_k (k = 2..14, engine_round1.py / battery1063.py /
COMPLETE_PROOF.md §3.5) by three new exact values:

    n_15, n_16, n_17  —  each certified BOTH ways, dual independent code paths.

THE DEFINITION (verbatim, COMPLETE_PROOF.md §0): n_k >= 2k is the least n such
that n-i divides C(n,k) for all but one 0 <= i < k.  With
    wcount(n,k) := #{i in [0,k) : (n-i) | C(n,k)},
the definition is: n_k = least n >= 2k with wcount(n,k) >= k-1.

CERTIFICATION ARCHITECTURE (the round-1 pattern, dual paths):
  (W) WITNESS: wcount(n_k, k) computed on the exact binomial — must equal k-1
      (exactly one exempt position; the miss position and the prime-power
      deficit v_q(n-i) > v_q(C(n,k)) are exhibited — the §3.7 force analysis).
  (C) COMPLETENESS: every 2k <= n < n_k has wcount <= k-2, i.e. at least two
      positions i with (n-i) ∤ C(n,k).
  (A) PATH A — exact big-integer path: gmpy2.comb (== math.comb semantics,
      GMP arithmetic), direct divisibility of the literal binomial.
  (B) PATH B — valuation path, independent of any big binomial:
      (n-i) | C(n,k)  <=>  for every prime q | (n-i):
          v_q(n-i)  <=  v_q(C(n,k))
      where (Legendre / Kummer)
          v_q(C(n,k)) = sum_{j>=1} (floor(n/q^j) - floor((n-k)/q^j) - floor(k/q^j))
                       = v_q(n!) - v_q((n-k)!) - v_q(k!).
      Both paths must AGREE on every single n in [2k, n_k] for every k swept —
      a per-point dual certificate.
  (K) CALIBRATION LAW: the engine re-derives n_2..n_14 with the same code path
      and matches the certified table (4,6,9,12,75,30,70,56,2403,280,3465,210,793).
"""
import sys
from math import isqrt
import gmpy2
from gmpy2 import comb as gcomb
from gmpy2 import mpz

T0 = __import__('time').time()

# ---------------------------------------------------------------- small primes
def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, isqrt(N) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

PMAX_LOCAL = 200          # primes up to here cover factoring n-i for n <= ~2e4
PRIMES = primes_upto(PMAX_LOCAL)

def factor_small(m):
    """factor m (<= PMAX_LOCAL^2 safely for our ranges) -> dict prime->exp"""
    f = {}
    for q in PRIMES:
        if q * q > m:
            break
        while m % q == 0:
            f[q] = f.get(q, 0) + 1
            m //= q
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def vC(n, k, q):
    """v_q(C(n,k)) via the Legendre floor sums — NO binomial is formed."""
    tot = 0
    p = q
    while p <= n:
        tot += n // p - (n - k) // p - k // p
        p *= q
    return tot

def wcount_valuations(n, k):
    """PATH B: wcount via valuations only."""
    c = 0
    for i in range(k):
        x = n - i
        ok = True
        for q, e in factor_small(x).items():
            if e > vC(n, k, q):
                ok = False
                break
        if ok:
            c += 1
    return c

def wcount_exact(n, k):
    """PATH A: wcount via the exact binomial (gmpy2)."""
    c = gcomb(mpz(n), k)
    return sum(1 for i in range(k) if c % (n - i) == 0)

def wcount_dual(n, k):
    a = wcount_exact(n, k)
    b = wcount_valuations(n, k)
    assert a == b, "DUAL PATH DISAGREEMENT at k=%d n=%d: exact=%d valuations=%d" % (k, n, a, b)
    return a

def find_nk(k, cap):
    """least n >= 2k with wcount >= k-1 (dual path per point), scanning to cap."""
    n = 2 * k
    while n <= cap:
        if wcount_dual(n, k) >= k - 1:
            return n
        n += 1
    return None

def certify(k, nk):
    """Full certificate for the row (k, nk): witness + completeness +
    dual-path agreement on the whole swept range + miss positions + deficit."""
    # (W) witness
    wc = wcount_dual(nk, k)
    assert wc >= k - 1, "witness FAILS k=%d" % k
    c = gcomb(mpz(nk), k)
    misses = [i for i in range(k) if c % (nk - i) != 0]
    deficits = []
    for i in misses:
        x = nk - i
        d = None
        for q, e in factor_small(x).items():
            if e > vC(nk, k, q):
                d = (q, e, vC(nk, k, q))
                break
        assert d is not None, "no prime-power deficit found at exempt position k=%d i=%d" % (k, i)
        deficits.append(d)
    # (C) completeness — every 2k <= n < nk has wcount <= k-2, dual path
    nbelow = 0
    for n in range(2 * k, nk):
        w = wcount_dual(n, k)
        assert w <= k - 2, "COMPLETENESS FAILS k=%d n=%d wcount=%d" % (k, n, w)
        nbelow += 1
    return wc, misses, deficits, nbelow

# ---------------------------------------------------------------- CALIBRATION
print("=" * 72)
print("ENGINE ROUND 2 — #1063 frontier extension: calibration then n_15..n_17")
print("=" * 72)
CERTIFIED = {2: 4, 3: 6, 4: 9, 5: 12, 6: 75, 7: 30, 8: 70, 9: 56, 10: 2403,
             11: 280, 12: 3465, 13: 210, 14: 793}
print("(K) CALIBRATION — re-deriving the certified frontier k=2..14:")
calib_ok = True
for k in range(2, 15):
    v = find_nk(k, 4000 if k <= 9 else 4000)
    if v != CERTIFIED[k]:
        calib_ok = False
        print("  k=%2d: derived %s != certified %s  RED" % (k, v, CERTIFIED[k]))
print("  k=2..14 re-derived: %s  -> %s"
      % ([find_nk(k, 4000) for k in range(2, 15)],
         "CALIBRATION GREEN (engine reproduces the certified tip n_14=793)" if calib_ok else "RED"))
assert calib_ok

# ---------------------------------------------------------------- EXTENSION
print()
print("(X) THE EXTENSION — new certified exact values k = 15, 16, 17:")
NEW = {}
for k in (15, 16, 17):
    nk = find_nk(k, 6000)
    assert nk is not None, "no witness <= 6000 for k=%d" % k
    wc, misses, deficits, nbelow = certify(k, nk)
    NEW[k] = nk
    print("  n_%d = %d" % (k, nk))
    print("     witness wcount = %d  (= k-1: exactly one exempt position)"
          % wc)
    print("     exempt i = %s  (n-i = %s)" % (misses, [nk - i for i in misses]))
    print("     prime-power deficits (q, v_q(n-i), v_q(C(n,k))): %s" % deficits)
    print("     completeness: %d points swept in [%d, %d), all wcount <= k-2  GREEN"
          % (nbelow, 2 * k, nk))

print()
print("(D) DUAL-PATH TOTALS — every swept point certified by BOTH the exact")
print("    gmpy2 binomial and the Legendre valuation route:")
tot = sum(nk - 2 * k + 1 for k in (15, 16, 17))
tot_calib = sum(CERTIFIED[k] - 2 * k + 1 for k in range(2, 15))
print("    dual-agreeing points: %d (calibration) + %d (extension) = %d"
      % (tot_calib, tot, tot_calib + tot))

# final table
print()
print("THE CERTIFIED FRONTIER EXTENDED TO k = 17:")
row_k = [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
vals = {**CERTIFIED, **NEW}
row_n = [vals[k] for k in row_k]
print("  k   : " + " ".join("%5d" % k for k in row_k))
print("  n_k : " + " ".join("%5d" % vals[k] for k in row_k))
print()
print("ENGINE ROUND 2 ALL GREEN — %.1fs" % (__import__('time').time() - T0))
