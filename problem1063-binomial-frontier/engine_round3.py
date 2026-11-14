#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ENGINE ROUND 3 — Erdős #1063: THE BINOMIAL FRONTIER EXTENSION TO k = 18, 19, 20.
(W63, task W63-C2.) Extends the certified frontier (k = 2..17, engine_round2.py /
STATUS_EXTENSION.md, W62) by three new exact values — SAME dual-path discipline:

  (W) WITNESS: wcount(n_k, k) = k-1 (exactly one exempt position); the miss position
      i and its prime-power deficits v_q(n-i) > v_q(C(n_k,k)) exhibited (§3.7 force
      analysis receipt).
  (C) COMPLETENESS: every 2k <= n < n_k has wcount <= k-2 (at least two misses) —
      the full sweep [2k, n_k) is executed, dual path per point.
  (A) PATH A — exact big-integer path: gmpy2.comb (GMP exact), direct divisibility
      of the literal binomial C(n,k) by each n-i.
  (B) PATH B — valuation path, independent of any big binomial:
        (n-i) | C(n,k)  <=>  for every prime q | (n-i):  v_q(n-i) <= v_q(C(n,k)),
      with (Legendre / Kummer)
        v_q(C(n,k)) = sum_{j>=1} (floor(n/q^j) - floor((n-k)/q^j) - floor(k/q^j)).
      Both paths must AGREE on every single swept point — asserted; any disagreement
      aborts the engine.
  (K) CALIBRATION LAW: k = 2..17 re-derived FIRST with the same code path and
      matched against the certified table
      (4,6,9,12,75,30,70,56,2403,280,3465,210,793,4732,3213,1456) — GREEN required.

DEFINITION (verbatim, COMPLETE_PROOF.md §0): n_k >= 2k is the least n such that
n-i divides C(n,k) for all but one 0 <= i < k; with wcount(n,k) := #{i in [0,k) :
(n-i) | C(n,k)}, n_k = least n >= 2k with wcount >= k-1.

PRIME TABLE: PRIMES = primes <= 300 (W62 used 200, safe only to n ~ 4e4). For every
swept n <= 67203 < 300^2 = 90000, factor_small returns the TRUE factorization of
n-i (a composite leftover would need two prime factors both > 300, hence > 90000),
so every Path B receipt is a literal prime-power statement.

CHECKPOINTING (L75): state in run263/engine3_state.json; resume with --resume.
A chunk killed mid-k restarts that k's scan from 2k (worst-case loss ~35 s).
"""
import json, os, sys, time
from math import isqrt
import gmpy2
from gmpy2 import comb as gcomb
from gmpy2 import mpz

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
RUN = os.path.join(HERE, "run263")
STATE = os.path.join(RUN, "engine3_state.json")
os.makedirs(RUN, exist_ok=True)

DUAL_POINTS = 0   # global count of dual-certified points (Path A AND Path B, asserted)

# ---------------------------------------------------------------- small primes
def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, isqrt(N) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

PRIMES = primes_upto(300)          # true factorizations for all m <= 90000

def factor_small(m):
    """TRUE factorization of m for all m <= 300^2 = 90000 -> dict prime -> exponent."""
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
    global DUAL_POINTS
    a = wcount_exact(n, k)
    b = wcount_valuations(n, k)
    assert a == b, "DUAL PATH DISAGREEMENT at k=%d n=%d: exact=%d valuations=%d" % (k, n, a, b)
    DUAL_POINTS += 1
    return a

def find_nk(k, cap, tag=""):
    """least n >= 2k with wcount >= k-1 (dual path per point), scanning to cap."""
    n = 2 * k
    t = time.time()
    while n <= cap:
        if wcount_dual(n, k) >= k - 1:
            return n
        n += 1
        if n % 16384 == 0:
            print("    ...%s k=%d swept to %d (%.0f pts/s, %.0fs)" % (tag, k, n, n / (time.time() - T0), time.time() - t), flush=True)
    return None

def certify(k, nk):
    """Full certificate for the row (k, nk): witness + completeness + dual-path
    agreement on the whole swept range + miss positions + ALL prime-power deficits."""
    # (W) witness
    wc = wcount_dual(nk, k)
    assert wc >= k - 1, "witness FAILS k=%d" % k
    c = gcomb(mpz(nk), k)
    misses = [i for i in range(k) if c % (nk - i) != 0]
    assert len(misses) == k - wc, "miss/wcount bookkeeping k=%d" % k
    all_deficits = []
    for i in misses:
        x = nk - i
        deficits = [(q, e, vC(nk, k, q)) for q, e in sorted(factor_small(x).items())
                    if e > vC(nk, k, q)]
        assert deficits, "no prime-power deficit found at exempt position k=%d i=%d" % (k, i)
        all_deficits.append((i, x, deficits))
    # (C) completeness — every 2k <= n < nk has wcount <= k-2, dual path
    nbelow = 0
    t = time.time()
    for n in range(2 * k, nk):
        w = wcount_dual(n, k)
        assert w <= k - 2, "COMPLETENESS FAILS k=%d n=%d wcount=%d" % (k, n, w)
        nbelow += 1
        if nbelow % 16384 == 0:
            print("    ...certify k=%d swept %d/%d points (%.0fs)" % (k, nbelow, nk - 2 * k, time.time() - t), flush=True)
    return wc, misses, all_deficits, nbelow

# ---------------------------------------------------------------- state (L75)
def load_state():
    if "--resume" in sys.argv and os.path.exists(STATE):
        st = json.load(open(STATE))
        st["ext_rows"] = {int(kk): v for kk, v in st.get("ext_rows", {}).items()}
        print("[resume] state: %s" % st, flush=True)
        return st
    return {"calib_done": [], "ext_rows": {}}

def save_state(st):
    json.dump(st, open(STATE, "w"))

# ---------------------------------------------------------------- CALIBRATION
print("=" * 72)
print("ENGINE ROUND 3 — #1063 frontier extension: calibration k=2..17, then n_18..n_20")
print("=" * 72)
CERTIFIED = {2: 4, 3: 6, 4: 9, 5: 12, 6: 75, 7: 30, 8: 70, 9: 56, 10: 2403,
             11: 280, 12: 3465, 13: 210, 14: 793, 15: 4732, 16: 3213, 17: 1456}
st = load_state()
print("(K) CALIBRATION — re-deriving the certified frontier k=2..17:")
calib_ok = True
derived17 = {}
for k in range(2, 18):
    if k in st["calib_done"]:
        v = CERTIFIED[k]          # already re-derived GREEN in a previous chunk
    else:
        v = find_nk(k, 6000, tag="calib")
        if v != CERTIFIED[k]:
            calib_ok = False
            print("  k=%2d: derived %s != certified %s  RED" % (k, v, CERTIFIED[k]))
        else:
            st["calib_done"].append(k); save_state(st)
    derived17[k] = v
print("  k=2..17 re-derived: %s" % ([derived17[k] for k in range(2, 18)]))
print("  -> %s" % ("CALIBRATION GREEN (engine reproduces the certified tip n_17=1456)"
                  if calib_ok else "RED"))
assert calib_ok

# ---------------------------------------------------------------- EXTENSION
print()
print("(X) THE EXTENSION — new certified exact values k = 18, 19, 20:")
CAP = 70000                      # > 67203; every found row certified below

def fac_str(x):
    f = factor_small(x)
    return " * ".join("%d^%d" % (q, e) if e > 1 else "%d" % q for q, e in sorted(f.items()))

NEW = dict(st["ext_rows"])
receipts = {}
for k in (18, 19, 20):
    if k in NEW:
        nk = NEW[k]["nk"]
    else:
        nk = find_nk(k, CAP, tag="find")
        assert nk is not None, "no witness <= %d for k=%d" % (CAP, k)
        NEW[k] = {"nk": nk}
        save_state(st)
    wc, misses, all_deficits, nbelow = certify(k, nk)
    NEW[k] = {"nk": nk, "wc": wc, "misses": misses, "nbelow": nbelow}
    st["ext_rows"] = {str(kk): NEW[kk] for kk in NEW}
    save_state(st)
    receipts[k] = (nk, wc, misses, all_deficits, nbelow)
    print("  n_%d = %d" % (k, nk))
    print("     witness wcount = %d  (= k-1: exactly one exempt position)" % wc)
    for (i, x, deficits) in all_deficits:
        print("     exempt i = %d  (n-i = %d = %s)" % (i, x, fac_str(x)))
        print("     prime-power deficits (q, v_q(n-i), v_q(C(n,k))): %s" % (deficits,))
    print("     completeness: %d points swept in [%d, %d), all wcount <= k-2  GREEN"
          % (nbelow, 2 * k, nk))

# ---------------------------------------------------------------- BOUNDS (corpus-recorded)
print()
print("(B) BOUNDS CONSISTENCY on the new rows (corpus-recorded upper bounds):")
import math
def lcm_upto(m):
    L = 1
    for j in range(1, m + 1):
        L = L * j // math.gcd(L, j)
    return L
for k in (18, 19, 20):
    nk = receipts[k][0]
    cambie = k * lcm_upto(k - 1)
    monier = math.factorial(k)
    print("  k=%2d: n_k=%6d  <=  k*lcm(1..k-1) = %-12d (ratio %.2e)  and  <= k! (ratio %.2e)"
          % (k, nk, cambie, nk / cambie, nk / monier))
    assert nk <= cambie and nk <= monier

# ---------------------------------------------------------------- DUAL TOTALS
print()
print("(D) DUAL-PATH TOTALS — every swept point certified by BOTH the exact")
print("    gmpy2 binomial (Path A) and the Legendre/Kummer valuation route (Path B):")
ext_pts = sum(receipts[k][4] + 1 for k in receipts)
calib_pts = DUAL_POINTS - ext_pts
print("    dual-agreeing points this run: %d (calibration+find) + %d (extension) = %d"
      % (calib_pts, ext_pts, DUAL_POINTS))

# ---------------------------------------------------------------- final table
print()
print("THE CERTIFIED FRONTIER EXTENDED TO k = 20:")
row_k = list(range(2, 21))
vals = {**CERTIFIED, **{k: receipts[k][0] for k in receipts}}
print("  k   : " + " ".join("%6d" % k for k in row_k))
print("  n_k : " + " ".join("%6d" % vals[k] for k in row_k))
print()
print("ENGINE ROUND 3 ALL GREEN — %.1fs" % (time.time() - T0))
