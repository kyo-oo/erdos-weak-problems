#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
STORMER961_K17 — THE COMPLETE STØRMER–PELL CENSUS for S = {2,3,5,7,11,13,17}
(the 17-tier — S063 W63 volley, task W63-C1r: f(17) = f(18) EXACT + the
complete 7-prime witness-pair census, dual-brute-verified).

The 7-prime tier of the campaign's certification architecture (T8 of
COMPLETE_PROOF.md — every finite prime set closes by the same laws; executed
at S={2,3,5,7,11} (K25, stormer961.py) and S={2,3,5,7,11,13} (W62,
stormer961_k13.py)).  For k in {17,18} the primes <= k are EXACTLY
S = {2,3,5,7,11,13,17} (18 = 2*3^2 adds no new prime), so k-smooth =
17-smooth for both k, and by the window law (L0):

    f(k) = 1 + max{ L : a run of L consecutive 17-smooth integers all > k }.

THE CERTIFICATION ARCHITECTURE (machine-verifies every component; identical
laws to the 13-tier, SODD = {3,5,7,11,13,17}):

(A) For each of the 127 squarefree S-units a (nonempty subset products):
    fundamental solution (X1,Y1) of X^2-aY^2=1 by exact integer continued
    fractions of sqrt(a); certification X1^2-aY1^2=1 direct; convergent
    denominators machine-checked NON-decreasing (ties only at the first
    step, same Y hence same solution), every pre-hit convergent checked
    p^2-aq^2<>1, so the first +1 convergent is value-least (Legendre: every
    solution has |X/Y-sqrt(a)| < 1/(2Y^2), hence is a convergent).
    (A1) CROSS-IMPLEMENTATION: the W63 salvage probe probe_k17_fund.py
    (mod-M filtered CF, M = 2^61-1 prime: a true solution always satisfies
    p^2 = a q^2 + 1 hence passes the congruence mod M, so the filter never
    skips a hit; false mod-hits are exactly checked) computed the same 127
    fundamentals — asserted EQUAL here (probe_k17_fund.json, 127 rows).
    (A2) THE P-TH-POWER DESCENT CERTIFICATE (NEW W63 LAW — a complete proof
    of fundamentality INDEPENDENT of CF/Legendre, valid at every Y1 size,
    including the 9 heavy rows beyond any brute scan):
      positive solutions of X^2-aY^2=1 are the norm-1 units u = X+Y sqrt(a)
      > 1 (X>=2, Y>=1; negative X or Y gives u <= 0 or u in (0,1)); by the
      campaign law L3 (descent — the minimal unit eps_min exists by
      well-ordering of Y, since the solution value sqrt(aY^2+1)+Y sqrt(a) is
      strictly increasing in Y, and u/eps_min^n lands in [1,eps_min) with
      norm 1, forcing the sqrt(a)-coefficient v = 0 by value-minimality):
      the solutions are EXACTLY eps_min^k, k >= 1.  Our (X1,Y1) is a
      solution, hence eps_a = X1+Y1 sqrt(a) = eps_min^k; it is FUNDAMENTAL
      iff k = 1.  If k >= 2 then some prime p | k, p <= k <=
      log_{2+sqrt3}(eps) (eps_min >= 2+sqrt3: for Y=1, X^2=a+1 squarefree
      a=X^2-1>=3 with least X=2 (a=3; X>=3 gives a>=8 non-squarefree or
      a>=15 -> eps>=4+sqrt15>2+sqrt3); for Y>=2, X>=sqrt(4a+1)>=3 ->
      eps>=3+2sqrt2>2+sqrt3), and delta := eps_min^(k/p) is a norm-1 unit
      > 1 with delta^p = eps_a.  The machine search: for every prime
      p <= P_max := floor(log_{2+sqrt3} eps_a) (+3 margin), the real root
      r = eps_a^(1/p) (mpmath, 130 digits) nominates the ONLY possible
      delta = X+Y sqrt(a) with X = (r+1/r)/2, Y = (r-1/r)/(2 sqrt a)
      (integers if delta is integral — delta+delta^(-1) = 2X,
      delta-delta^(-1) = 2Y sqrt a); then EXACT integer verification:
      X>=2, Y>=1, X^2-aY^2 == +1 (a NORM-1 root — norm -1 roots like
      1+sqrt2 at a=2 do NOT decompose the norm-1 chain), and Brahmagupta
      binary powering of (X,Y) to the p-th == (X1,Y1).  NO prime admits
      such a delta => k = 1 => (X1,Y1) is the fundamental.  QED.
    (A3) BRUTE minimality (independent of CF/Legendre AND of the p-power
    law): for every 1<=Y'<Y1, aY'^2+1 is not a square — executed in-engine
    for every a with Y1 <= 10^6; the a=5005 row (Y1=625742712) carries the
    W62 companion receipt logs/brute5005.log (625,742,711 checks GREEN);
    the feasible mid-heavy rows get the W63 companion job
    brute_k17_heavy.py; the monster rows (a=1309 Y1=2.2e13, a=3094
    Y1=9.9e10, a=36465/a=85085 Y1=1.8e10, a=2431 Y1=3.8e9) are certified
    by (A2) alone — a complete proof, not evidence.

(B) PRUNE: Y1 must be 17-smooth else a yields no pair at all (n=1: Y1=2b;
    n>=2: Y1 | Y_n = Y1 U_n).  Kill receipt: the prime > 17 dividing Y1.

(C) LUCAS VALUATION LAWS (instance-verified over the whole used range):
    U_0=0, U_1=1, U_{n+2}=2X1 U_{n+1}-U_n; Y_n = Y1 U_n.
    - parity: X_{2m} odd; v2(X_odd) = v2(X1); v2(U_n) = v2(n)+[n even]v2(X1).
    - entry point z_p := min{m>=1: p | U_m} satisfies z_p <= p+1 <= 18 for
      every odd p <= 17 (unramified: z_p | p-(a/p); intrinsic: z_p = p).
    - valuation law: p | U_n iff z_p | n; and when z_p | n:
      v_p(U_n) = v_p(U_{z_p}) + v_p(n/z_p)  ->  v_p(U_n) <= B_{a,p}+v_p(n),
      B_{a,p} := max_{1<=m<=18} v_p(U_m).

(D) SIZE BOUND (termination): if Y_n is 17-smooth then
        log2 Y_n <= C_a + 2 log2 n,   C_a = log2(Y1)+v2(X1)+sum_{odd p<=17} B_{a,p} log2 p,
    while log2 Y_n >= n log2(alpha) - log2(3 sqrt(a)), alpha = X1+Y1 sqrt(a) >= 2+sqrt3.
    -> n <= N_a (explicit per-a cap; g(n)=n log2 alpha - 2 log2 n increasing for
    n >= 2: log2 alpha >= 1.90 > 2 log2(3/2) = 1.170).  Census loop n = 1..N_a only.

(E) THE CENSUS: for surviving a, n = 1..N_a (gmpy2 mpz powers): keep n with
    X_n odd, Y_n even, x=(X_n-1)/2 and x+1 both 17-smooth.  Completeness:
    every consecutive 17-smooth pair (x,x+1) has a := sf(x(x+1)) among the
    127, (2x+1,2b) solving that Pell equation, hence = (X_n,Y_n) for a
    unique n <= N_a by (D).  THE ANSWER: printed below (count + largest x).

(F) THE f(k) TABLE k=17,18: L(k) = max over maximal runs r of |{j in r: j>k}|
    (elements > k form a suffix of a run); f(k) = L(k)+1.  WITNESS: the run
    (24,25,26,27,28) — all 17-smooth, all > 18 — gives f(k) >= 6 for both k;
    EXCLUSION: no census pair x > k with x..x+L(k) all 17-smooth (machine
    scan of the complete census) gives f(k) <= L(k)+1.
    CALIBRATION LAW: the same 17-tier census re-derives the certified rows
    f(2..16) (filter pairs to k-smooth), and CONTAINS the certified 68-pair
    13-tier census and the 40-pair 11-tier census verbatim (full list
    equality against the W62/K25 constants).

(G) DUAL CROSS-CHECK: brute enumeration of ALL 17-smooth numbers <= B18
    (B18 = max(10^18, 4 * largest census pair) — the full census range);
    consecutive pairs must equal the Pell census pairs; direct check of
    the no-(L+1)-run law for k=17,18 (independent of Pell); run
    decompositions must agree; brute L recount must equal the Pell L.
"""
import math
import json
import time
from math import isqrt, log2
from gmpy2 import mpz
from mpmath import mp as _mp, mpf

T0 = time.time()
_mp.dps = 130

S = [2, 3, 5, 7, 11, 13, 17]
SODD = [3, 5, 7, 11, 13, 17]
ZMAX = 18            # z_p <= p+1 <= 18 for every odd p <= 17
PRE = 400            # U-table length; N_a asserted < PRE - 2

def sf_a_values():
    out = []
    for mask in range(1, 128):
        a = 1
        for i, p in enumerate(S):
            if (mask >> i) & 1:
                a *= p
        out.append(a)
    return sorted(out)

AS = sf_a_values()
assert len(AS) == 127 and AS[0] == 2 and AS[-1] == 510510

def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def strip_S(n):
    for p in S:
        while n % p == 0:
            n //= p
    return n

def smooth17(n):
    return n >= 1 and strip_S(n) == 1

def maxprime(n):
    mp_ = 1
    for p in S:
        while n % p == 0:
            n //= p
            mp_ = p
    return mp_ if n == 1 else 10 ** 9

# ---------------------------------------------------------------- (A) CF Pell
def pell_fundamental(a):
    """Fundamental (minimal-X) solution of X^2-aY^2=1 via exact CF of sqrt(a).
    Certifications carried in-loop: convergent denominators NON-decreasing
    (standard CF law q_j = a_j q_{j-1}+q_{j-2}; a tie only at the first step,
    and a tie is the same Y = same solution since X = sqrt(aY^2+1)); every
    convergent BEFORE the returned one is checked p^2-aq^2 != 1; hence the
    first +1-convergent is the value-least solution among convergents = among
    all solutions (Legendre |X/Y-sqrt(a)| < 1/(2Y^2))."""
    a0 = isqrt(a)
    if a0 * a0 == a:
        return None
    m, d, aj = 0, 1, a0
    pjm2, qjm2 = 0, 1   # p_{-2}, q_{-2}
    pjm1, qjm1 = 1, 0   # p_{-1}, q_{-1}
    steps = 0
    lastq = 0
    while True:
        p = aj * pjm1 + pjm2
        q = aj * qjm1 + qjm2
        assert q >= lastq, "convergent denominators must be non-decreasing (a=%d)" % a
        lastq = q
        if p * p - a * q * q == 1 and q >= 1:
            return (p, q)
        m = d * aj - m
        d = (a - m * m) // d
        aj = (a0 + m) // d
        pjm2, pjm1 = pjm1, p
        qjm2, qjm1 = qjm1, q
        steps += 1
        if steps > 400000:
            raise RuntimeError("CF runaway for a=%d" % a)

# sanity anchors (classical Pell data + the W62 13-tier heavy row + 17-tier row)
assert pell_fundamental(2) == (3, 2)
assert pell_fundamental(3) == (2, 1)
assert pell_fundamental(5) == (9, 4)
assert pell_fundamental(6) == (5, 2)
assert pell_fundamental(7) == (8, 3)
assert pell_fundamental(13) == (649, 180)
assert pell_fundamental(17) == (33, 8)
assert pell_fundamental(5005) == (44268809311, 625742712)

print("(A) Pell fundamentals for the 127 squarefree S-units (S={2,3,5,7,11,13,17}):")
fund = {}
for a in AS:
    X1, Y1 = pell_fundamental(a)
    assert X1 * X1 - a * Y1 * Y1 == 1
    fund[a] = (X1, Y1)
print("   127 equations solved; largest X1 = %d (a=%d), largest Y1 = %d (a=%d)"
      % (max(fund[a][0] for a in AS),
         max(AS, key=lambda a: fund[a][0]),
         max(fund[a][1] for a in AS),
         max(AS, key=lambda a: fund[a][1])))

# (A1) cross-implementation: the W63 salvage probe (mod-M filtered CF)
probe = json.load(open("probe_k17_fund.json"))
assert len(probe) == 127, "probe must carry all 127 rows"
pmap = {int(row[0]): (int(row[1]), int(row[2])) for row in probe}
assert set(pmap) == set(AS), "probe a-set mismatch"
for a in AS:
    assert pmap[a] == fund[a], "PROBE CROSS-CHECK FAILS a=%d" % a
print("   (A1) CROSS-IMPLEMENTATION GREEN: all 127 fundamentals equal the W63")
print("       salvage probe (mod-M filtered CF, probe_k17_fund.json)")

# (A2) the p-th-power descent certificate
def compose_pair(a, x1, y1, x2, y2):
    # (x1+y1 sqrt a)(x2+y2 sqrt a) = (x1x2+a y1y2) + (x1y2+y1x2) sqrt a
    return (x1 * x2 + a * y1 * y2, x1 * y2 + y1 * x2)

def unit_pow(a, X, Y, p):
    """(X+Y sqrt a)^p by binary powering — exact integers throughout."""
    A, B = 1, 0
    bx, by = X, Y
    e = p
    while e:
        if e & 1:
            A, B = compose_pair(a, A, B, bx, by)
        e >>= 1
        if e:
            bx, by = compose_pair(a, bx, by, bx, by)
    return A, B

def pth_power_unit(a, X1, Y1, p):
    """Exact search for a NORM-1 unit delta = X+Y sqrt a (X>=2, Y>=1) with
    delta^p = X1+Y1 sqrt a.  Numeric root (130 digits) nominates the unique
    real candidate; EXACT integer verification decides."""
    ra = _mp.sqrt(a)
    eps = mpf(X1) + mpf(Y1) * ra
    r = eps ** (mpf(1) / mpf(p))
    Xc = (r + 1 / r) / 2
    Yc = (r - 1 / r) / (2 * ra)
    X = int(Xc + mpf('0.5'))
    Y = int(Yc + mpf('0.5'))
    if X < 2 or Y < 1:
        return None
    if X * X - a * Y * Y != 1:          # norm +1 required (norm -1 roots
        return None                      # do not decompose the norm-1 chain)
    if unit_pow(a, X, Y, p) != (X1, Y1):
        return None
    return (X, Y)

def primes_upto(n):
    out = []
    for q in range(2, n + 1):
        if all(q % d for d in range(2, isqrt(q) + 1)):
            out.append(q)
    return out

def fundamental_certificate(a, X1, Y1):
    """(A2) Returns the list of primes p for which 'eps_a is not a p-th power
    of a norm-1 unit > 1' was verified.  Completeness of the certificate:
    solutions = eps_min^k (law L3); if k >= 2 a prime p | k, p <= k <=
    log_{2+sqrt3}(eps_a) (eps_min >= 2+sqrt3), would exhibit
    delta = eps_min^(k/p), a norm-1 unit > 1 with delta^p = eps_a — the
    search over primes <= P_max+3 would FIND it (assert failure).
    No such delta  =>  k = 1  =>  (X1,Y1) is THE fundamental solution."""
    ra = _mp.sqrt(a)
    eps = mpf(X1) + mpf(Y1) * ra
    pmax = int(_mp.log(eps) / _mp.log(mpf(2) + _mp.sqrt(3))) + 3
    plist = primes_upto(max(pmax, 2))
    for p in plist:
        if pth_power_unit(a, X1, Y1, p) is not None:
            raise AssertionError(
                "NOT FUNDAMENTAL: a=%d, eps = delta^%d for the found norm-1"
                " unit delta — CF error!" % (a, p))
    return plist

pcert_rows = 0
pcert_primes = 0
for a in AS:
    X1, Y1 = fund[a]
    plist = fundamental_certificate(a, X1, Y1)
    pcert_rows += 1
    pcert_primes += len(plist)
print("   (A2) P-TH-POWER DESCENT CERTIFICATE GREEN: %d equations certified"
      " fundamental" % pcert_rows)
print("       (%d prime-exponent searches, exact integer verification; valid"
      " at every Y1 size)" % pcert_primes)

# (A3) brute minimality for every a with Y1 <= 10^6 (independent of CF/Legendre
# AND of the p-power law); heavy rows: a=5005 -> W62 receipt logs/brute5005.log
# (625,742,711 checks); mid-heavy rows -> W63 companion brute_k17_heavy.py;
# monster rows -> (A2) alone (complete proof).
minim_it = 0
skipped = []
for a in AS:
    X1, Y1 = fund[a]
    if Y1 > 1_000_000:
        skipped.append((a, Y1))
        continue
    for Yp in range(1, Y1):
        Xp = isqrt(a * Yp * Yp + 1)
        assert Xp * Xp != a * Yp * Yp + 1, \
            "minimality FAILS a=%d Y'=%d" % (a, Yp)
        minim_it += 1
print("   (A3) brute minimality certified (Y1 <= 10^6 rows): %d checks, no Y'<Y1 solves"
      % minim_it)
print("       heavy rows beyond 10^6 (p-power certified; brute companions where feasible):")
for (a, Y1) in sorted(skipped, key=lambda t: -t[1]):
    print("         a=%-6d Y1=%-15d %s" % (a, Y1,
          "(W62 receipt logs/brute5005.log)" if a == 5005 else
          "(W63 companion brute_k17_heavy.py)" if Y1 <= 10 ** 8 else
          "(A2) p-th-power certificate only"))

# ---------------------------------------------------------------- (B) prune
alive = [a for a in AS if smooth17(fund[a][1])]
dead = [a for a in AS if not smooth17(fund[a][1])]
print()
print("(B) THE PRUNE: %d equations solved; survivors (Y1 17-smooth): %d ; dead: %d"
      % (len(AS), len(alive), len(dead)))
for a in dead:
    Y1 = fund[a][1]
    # explicit kill receipt: the smallest prime > 17 dividing Y1
    r = Y1
    for p in S:
        while r % p == 0:
            r //= p
    assert r > 1, "dead a=%d has smooth Y1?!" % a
    q = 2
    while r % q != 0:
        q += 1
    kp = q  # smallest prime factor of the 17-stripped part, hence > 17
    print("   DEAD a=%-6d: Y1=%-15d killed by prime %d > 17" % (a, Y1, kp))

# ---------------------------------------------------------------- (C)+(D)+(E)
print()
print("(C/D/E) Lucas laws + size bound + census per surviving a:")
census = []   # (x, a, n, Xn, Yn)
for a in alive:
    X1, Y1 = fund[a]
    X1, Y1 = int(X1), int(Y1)
    alpha_log2 = log2(X1 + Y1 * math.sqrt(a))
    assert alpha_log2 >= log2(2 + math.sqrt(3))   # alpha >= 2+sqrt3
    P = 2 * X1
    U = [0, 1]
    for t in range(2, PRE + 1):
        U.append(P * U[-1] - U[-2])
    # entry points z_p (odd p <= 17), law z_p <= p+1 <= 18
    ztab = {}
    for p in SODD:
        z = None
        for m in range(1, ZMAX + 1):
            if U[m] % p == 0:
                z = m
                break
        ztab[p] = z
        assert z is None or z <= ZMAX
    # B_{a,p}, C_a, N_a
    B = {p: (max(vp(U[m], p) for m in range(1, ZMAX + 1)) if ztab[p] is not None else 0)
         for p in SODD}
    C_a = log2(Y1) + vp(X1, 2) + sum(B[p] * log2(p) for p in SODD)
    D = C_a + log2(3 * math.sqrt(a))
    n = 2
    while n * alpha_log2 - 2 * log2(n) <= D:
        n += 1
    N_a = n + 5  # safety margin
    assert N_a < PRE - 2
    # g monotone over the used range (log2 alpha >= 1.90 > 2 log2 3/2 = 1.17)
    for m in range(2, N_a):
        assert (m + 1) * alpha_log2 - 2 * log2(m + 1) > m * alpha_log2 - 2 * log2(m)
    # valuation-law instances over the full used range n = 2..N_a
    for p in SODD:
        z = ztab[p]
        for m in range(2, N_a + 1):
            if z is None:
                assert U[m] % p != 0, "p=%d divides U_%d but no entry<=%d" % (p, m, ZMAX)
            elif m % z == 0:
                assert vp(U[m], p) == vp(U[z], p) + vp(m // z, p), \
                    "valuation law FAILS a=%d p=%d n=%d" % (a, p, m)
            else:
                assert U[m] % p != 0, "entry law FAILS a=%d p=%d n=%d" % (a, p, m)
    # parity-law + identity + size-bound instances; census scan (gmpy2 powers)
    npairs = 0
    Xn, Yn = mpz(X1), mpz(Y1)
    for m in range(1, N_a + 1):
        assert Yn == Y1 * U[m]                       # Y_n = Y1 U_n
        if m % 2 == 0:
            assert Xn % 2 == 1                        # X_{2m} odd
        else:
            assert vp(int(Xn), 2) == vp(X1, 2)       # v2(X_odd) = v2(X1)
        assert vp(U[m], 2) == vp(m, 2) + (1 if vp(m, 2) >= 1 else 0) * vp(X1, 2)
        if smooth17(int(Yn)):
            # size-bound instance (the theorem applies to 17-smooth Y_n)
            assert log2(int(Yn)) <= C_a + 2 * log2(m), \
                "size bound FAILS a=%d n=%d" % (a, m)
        if Xn % 2 == 1 and Yn % 2 == 0:
            x = (Xn - 1) // 2
            if smooth17(int(x)) and smooth17(int(x + 1)):
                census.append((int(x), a, m, int(Xn), int(Yn)))
                npairs += 1
        Xn, Yn = X1 * Xn + a * Y1 * Yn, X1 * Yn + Y1 * Xn
    if N_a >= 30 or npairs > 0:
        print("   a=%-6d: N_a=%3d  C_a=%7.2f  pairs_here=%d"
              % (a, N_a, C_a, npairs))

census.sort()
print()
print("(E) THE COMPLETE CENSUS — consecutive 17-smooth pairs (x, x+1):")
for (x, a, n, Xn, Yn) in census:
    assert Xn * Xn - a * Yn * Yn == 1
    assert Xn == 2 * x + 1 and Yn % 2 == 0
    assert x * (x + 1) == a * (Yn // 2) ** 2
    assert smooth17(x) and smooth17(x + 1) and smooth17(Yn // 2)
    print("   x=%-12d a=%-6d n=%-3d X=%-18d Y=%-15d b=%d"
          % (x, a, n, Xn, Yn, Yn // 2))
TOTAL = len(census)
MAXX = max(x for (x, *_ ) in census)
print("   TOTAL PAIRS: %d ; LARGEST x = %d" % (TOTAL, MAXX))
assert TOTAL >= 68 and MAXX >= 123200     # containment of the W62 tier
json.dump([(x, a, n, str(Xn), str(Yn)) for (x, a, n, Xn, Yn) in census],
          open("census_k17.json", "w"))
print("   saved census_k17.json (checkpoint + receipt)")

# helper re-declared post-census (needed by the assert loop above via closure)
def sf_a_of_pair(x):
    r = x * (x + 1)
    out = 1
    for p in S:
        if vp(r, p) % 2:
            out *= p
    return out
for (x, a, n, Xn, Yn) in census:
    assert sf_a_of_pair(x) == a, "dictionary FAILS x=%d" % x  # a = sf(x(x+1))

# ---------------------------------------------------------------- (F) f(k)
print()
print("(F) THE f(k) TABLE — k = 17, 18 (primes <= k = {2,3,5,7,11,13,17} for both):")
pairs = sorted(set((x, x + 1) for (x, _, _, _, _) in census))
runs = []
cur = [pairs[0][0], pairs[0][1]]
for (u, v) in pairs[1:]:
    if u == cur[-1]:
        cur.append(v)
    else:
        runs.append(tuple(cur))
        cur = [u, v]
runs.append(tuple(cur))
print("   maximal runs of consecutive 17-smooth (length >= 3):")
for r in runs:
    if len(r) >= 3:
        print("      start=%-8d len=%d  %s" % (r[0], len(r),
              (tuple(r) if len(r) <= 8 else "(%d, ..., %d)" % (r[0], r[-1]))))
print("   (maximal run length overall: %d — the run (1..18), inside every k>=19"
      % max(len(r) for r in runs))
assert max(len(r) for r in runs) == 18 and runs[0][0] == 1
assert runs[0] == tuple(range(1, 19))          # (1,...,18): 17 and 18 join

def Lmax(k):
    """L(k) = max over maximal runs of the number of elements > k (a suffix)."""
    best = 0
    for r in runs:
        s = sum(1 for j in r if j > k)
        if s > best:
            best = s
    return best

FK = {}
for k in (17, 18):
    L = Lmax(k)
    FK[k] = L + 1
    print("   k=%2d: longest run of %d-smooth entirely > %d has length %d  ->  f(%d) = %d"
          % (k, k, k, L, k, L + 1))

# WITNESS LAW (the lower bound, explicit): the run (24,25,26,27,28)
wit = (24, 25, 26, 27, 28)
for j in wit:
    assert smooth17(j) and j > 18
print("   WITNESS: (24,25,26,27,28) = (2^3·3, 5^2, 2·13, 3^3, 2^2·7), all > 18")
print("   -> f(k) >= 6 for k = 17, 18 (a 5-run of 17-smooth above every k <= 18)")
assert FK[17] >= 6 and FK[18] >= 6

# EXCLUSION (the upper bound, dual receipt): no (L+1)-run of 17-smooth above k
for k in (17, 18):
    L = Lmax(k)
    hits = [x for (x, a, n, Xn, Yn) in census
            if x > k and all(smooth17(x + t) for t in range(L + 1))]
    assert not hits, "(L+1)-run found above k=%d: %s" % (k, hits)
    print("   EXCLUSION k=%d: no census pair x > k with x..x+%d all 17-smooth"
          " -> no %d-run above %d -> f(%d) <= %d" % (k, L, L + 1, k, k, L + 1))
print()
print("   *** f(17) = %d, f(18) = %d — THE CERTIFIED FRONTIER EXTENDED ***"
      % (FK[17], FK[18]))

# CALIBRATION LAW — the 17-tier census re-derives the certified lower tiers:
# (i) the 40 certified 11-smooth pairs (K25) and the 68 certified 13-smooth
#     pairs (W62) appear VERBATIM (full list equality by k-smooth filtering);
OLD40 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 20, 21, 24, 27, 32, 35,
         44, 48, 49, 54, 55, 63, 80, 98, 99, 120, 125, 175, 224, 242, 384,
         440, 539, 2400, 3024, 4374, 9800]
OLD68 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 24, 25,
         26, 27, 32, 35, 39, 44, 48, 49, 54, 55, 63, 64, 65, 77, 80, 90, 98,
         99, 104, 120, 125, 143, 168, 175, 195, 224, 242, 324, 350, 351, 363,
         384, 440, 539, 624, 675, 728, 1000, 1715, 2079, 2400, 3024, 4095,
         4224, 4374, 6655, 9800, 10647, 123200]
def pairs_k(k):
    return sorted(set((x, x + 1) for (x, _, _, _, _) in census
                      if maxprime(x) <= k and maxprime(x + 1) <= k))
assert [u for (u, v) in pairs_k(11)] == OLD40, "K25 11-tier census mismatch"
assert [u for (u, v) in pairs_k(13)] == OLD68, "W62 13-tier census mismatch"
print("   CALIBRATION (i): the 40 K25 11-smooth pairs and the 68 W62 13-smooth")
print("   pairs appear VERBATIM (full-list equality by k-smooth filtering) — GREEN")
# (ii) f(2..16) re-derived from this census by k-smooth filtering:
def runs_from(pl):
    if not pl:
        return []
    rr = []
    c = [pl[0][0], pl[0][1]]
    for (u, v) in pl[1:]:
        if u == c[-1]:
            c.append(v)
        else:
            rr.append(tuple(c)); c = [u, v]
    rr.append(tuple(c))
    return rr
def Lmax_k(k):
    best = 1  # a single k-smooth integer > k always exists (2k is k-smooth, 2k>k)
    for r in runs_from(pairs_k(k)):
        s = sum(1 for j in r if j > k)
        if s > best:
            best = s
    return best
CAL = {2: 2, 3: 3, 4: 3, 5: 4, 6: 4, 7: 4, 8: 4, 9: 4, 10: 4, 11: 4, 12: 4,
       13: 6, 14: 6, 15: 6, 16: 6}
recal = {k: Lmax_k(k) + 1 for k in range(2, 17)}
assert recal == CAL, "calibration mismatch: %s vs %s" % (recal, CAL)
print("   CALIBRATION (ii): f(2..16) re-derived from THIS census by k-smooth")
print("   filtering: %s" % ([recal[k] for k in range(2, 17)]))
print("   (matches the certified table f(2)=2, f(3)=f(4)=3, f(5..12)=4,")
print("    f(13..16)=6 — GREEN)")

# ---------------------------------------------------------------- (G) cross
print()
B18 = max(10 ** 18, 4 * MAXX)
print("(G) DUAL CROSS-CHECK — brute enumeration of all 17-smooth <= %d:" % B18)
nums = []
p2 = 1
while p2 <= B18:
    p23 = p2
    while p23 <= B18:
        p235 = p23
        while p235 <= B18:
            p2357 = p235
            while p2357 <= B18:
                p235711 = p2357
                while p235711 <= B18:
                    p23571113 = p235711
                    while p23571113 <= B18:
                        n = p23571113
                        while n <= B18:
                            nums.append(n)
                            n *= 17
                        p23571113 *= 13
                    p235711 *= 11
                p2357 *= 7
            p235 *= 5
        p23 *= 3
    p2 *= 2
nums.sort()
print("   17-smooth count <= %s: %d" % ("{:,}".format(B18), len(nums)))
brute_pairs = [(u, v) for u, v in zip(nums, nums[1:]) if v == u + 1]
census_pairs = [(x, x + 1) for (x, _, _, _, _) in census]
assert MAXX + 2 < B18, "brute bound must cover the full census range"
print("   brute pairs: %d ; census pairs: %d ; EQUAL: %s"
      % (len(brute_pairs), len(census_pairs), brute_pairs == census_pairs))
assert brute_pairs == census_pairs
brute_set = set(nums)
for k in (17, 18):
    L = Lmax(k)
    bad = []
    for (u, v) in brute_pairs:
        if u > k and all((u + t) in brute_set for t in range(L + 1)):
            bad.append(u)
    assert not bad, "brute (L+1)-run found k=%d: %s" % (k, bad)
    print("   brute %d-run check k=%d (<= %s): CLEAN (no %d consecutive 17-smooth"
          " integers all > %d below the bound, independent of Pell)"
          % (L + 1, k, "{:,}".format(B18), L + 1, k))
# brute run decomposition must agree (full range: no run crosses B18)
bruns = []
cur = [brute_pairs[0][0], brute_pairs[0][1]]
for (u, v) in brute_pairs[1:]:
    if u == cur[-1]:
        cur.append(v)
    else:
        bruns.append(tuple(cur)); cur = [u, v]
bruns.append(tuple(cur))
assert bruns == runs
print("   brute maximal-run decomposition EQUALS the census decomposition (full range)")
w6 = [r for r in bruns if len(r) >= 3]
print("   runs of length >= 3 (brute, entire range): %s"
      % [(r[0], len(r)) for r in w6])
# brute L recount (dual of Lmax)
for k in (17, 18):
    Lb = max((sum(1 for j in r if j > k) for r in bruns), default=0)
    assert Lb == Lmax(k), "brute L recount mismatch k=%d" % k
    print("   brute L recount k=%d: %d == Pell L — GREEN" % (k, Lb))

print()
print("THE CERTIFIED FRONTIER OF ERDOS #961 NOW READS:")
print("   f(2)=2, f(3)=f(4)=3, f(k)=4 for 5<=k<=12, f(k)=6 for 13<=k<=16,")
print("   f(k)=%d for 17<=k<=18" % FK[17])
json.dump({"f17": FK[17], "f18": FK[18], "total_pairs": TOTAL, "max_x": MAXX,
           "alive": len(alive), "dead": len(dead),
           "brute_minimality_checks": minim_it,
           "pcert_rows": pcert_rows, "pcert_primes": pcert_primes,
           "brute_enum": len(nums)},
          open("summary_k17.json", "w"))
print("STORMER961_K17 ALL GREEN — %.1fs" % (time.time() - T0))
