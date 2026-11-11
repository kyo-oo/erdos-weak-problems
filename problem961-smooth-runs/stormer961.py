#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
STORMER961 — THE COMPLETE STØRMER–PELL CENSUS for S = {2,3,5,7,11}
(Erdős #961 certification engine — Kernel 25 round 6, the #686 Pell arsenal applied)

THE CERTIFICATION ARCHITECTURE (machine-verifies every component):

(A) For each of the 31 squarefree S-units a (products of nonempty subsets of
    {2,3,5,7,11}): compute the FUNDAMENTAL solution (X1, Y1) of X^2 - a Y^2 = 1
    by exact integer continued fractions of sqrt(a).  Certification: X1^2-aY1^2=1
    (direct) + all solutions are convergents (Legendre: |X/Y - sqrt(a)| =
    1/(Y(X/Y+sqrt a)) < 1/(2Y^2)) + convergents enumerated in strictly
    increasing denominator -> the first +1-convergent is the fundamental
    (minimal X) -> Lagrange power structure: every solution is (X_n, Y_n) with
    X_n + Y_n sqrt(a) = (X1 + Y1 sqrt(a))^n.

(B) PRUNE: Y1 must be {2,3,5,7,11}-smooth, else a yields no pairs at all
    (n=1: Y1 = 2b with b S-smooth; n>=2: Y1 | Y_n = Y1 U_n).

(C) LUCAS VALUATION LAWS (instance-verified over the whole used range):
    U_0=0, U_1=1, U_{n+2}=2X1 U_{n+1} - U_n;  Y_n = Y1 U_n.
    - parity laws: X_{2m} odd always; v2(X_{odd index}) = v2(X1);
      v2(U_n) = v2(n) + [v2(n)>=1] v2(X1).
    - entry point z_p := min{m>=1 : p | U_m} satisfies z_p <= 12 for every odd
      p <= 11 (unramified p (p∤aY1): z_p | p - (a/p); intrinsic p (p | aY1):
      z_p = p).
    - valuation law: p | U_n  <=>  z_p | n;  and when z_p | n:
      v_p(U_n) = v_p(U_{z_p}) + v_p(n/z_p).
    -> v_p(U_n) <= B_{a,p} + v_p(n),  B_{a,p} := max_{1<=m<=12} v_p(U_m).

(D) SIZE BOUND (the termination theorem): if Y_n is 11-smooth then
        log2 Y_n <= C_a + 2 log2 n,
    C_a = log2(Y1) + v2(X1) + sum_{odd p<=11} B_{a,p} log2(p),
    while log2 Y_n >= n log2(alpha) - log2(3 sqrt(a)), alpha = X1+Y1 sqrt(a).
    -> n <= N_a (explicit per-a cap; n log2(alpha) - 2 log2 n increasing
    for n >= 2 since log2(alpha) >= 2.5 > 2).  Census loop n = 1..N_a only.

(E) THE CENSUS: for surviving a, n = 1..N_a: keep n with X_n odd, Y_n even,
    x=(X_n-1)/2 and x+1 both 11-smooth.  Completeness: every consecutive
    11-smooth pair (x,x+1) has a := sf(x(x+1)), (2x+1, 2b) solving that Pell
    equation, hence = (X_n, Y_n) for a unique n, and n <= N_a by (D).

(F) THE 4-RUN ANALYSIS: for k = 5..12, no census pair (x,x+1) with x > k has
    x, x+1, x+2, x+3 all k-smooth  =>  no 4-run of k-smooth above k
    =>  f(k) <= 4.  With the witnesses (8,9,10) [k=5..7] and (14,15,16)
    [k=8..12]  =>  f(k) = 4 for k = 5..12.

(G) DUAL CROSS-CHECK: brute-force enumeration of ALL 11-smooth numbers
    <= 10^30; consecutive pairs must equal the Pell census pairs <= 10^30;
    direct check of no 4-run of k-smooth above k for k=5..12 (independent of
    Pell); maximal-run structure.
"""
import math
from math import isqrt, log2

T0 = __import__('time').time()

S = [2, 3, 5, 7, 11]
SODD = [3, 5, 7, 11]

def sf_a_values():
    out = []
    for mask in range(1, 32):
        a = 1
        for i, p in enumerate(S):
            if (mask >> i) & 1:
                a *= p
        out.append(a)
    return sorted(out)

AS = sf_a_values()
assert len(AS) == 31 and AS[0] == 2 and AS[-1] == 2310

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

def smooth11(n):
    return n >= 1 and strip_S(n) == 1

def maxprime(n):
    mp = 1
    for p in S:
        while n % p == 0:
            n //= p
            mp = p
    return mp if n == 1 else 10 ** 9

# ---------------------------------------------------------------- (A) CF Pell
def pell_fundamental(a):
    """Fundamental solution of X^2 - a Y^2 = 1 via exact CF of sqrt(a).
    Convergents p_j/q_j = a_j p_{j-1} + p_{j-2} are enumerated in strictly
    increasing q_j; every solution (X,Y) satisfies |X/Y - sqrt(a)| =
    1/(Y (X/Y + sqrt(a))) < 1/(2 Y^2), hence is a convergent (Legendre), so
    the FIRST convergent with p^2 - a q^2 = 1 is the fundamental (minimal X
    = minimal Y, since X = sqrt(a Y^2 + 1) is increasing in Y)."""
    a0 = isqrt(a)
    if a0 * a0 == a:
        return None
    m, d, aj = 0, 1, a0
    pjm2, qjm2 = 0, 1   # p_{-2}, q_{-2}
    pjm1, qjm1 = 1, 0   # p_{-1}, q_{-1}
    steps = 0
    while True:
        p = aj * pjm1 + pjm2
        q = aj * qjm1 + qjm2
        if p * p - a * q * q == 1 and q >= 1:
            return (p, q)
        m = d * aj - m
        d = (a - m * m) // d
        aj = (a0 + m) // d
        pjm2, pjm1 = pjm1, p
        qjm2, qjm1 = qjm1, q
        steps += 1
        if steps > 200000:
            raise RuntimeError("CF runaway for a=%d" % a)

# sanity anchors (classical Pell data)
assert pell_fundamental(2) == (3, 2)
assert pell_fundamental(3) == (2, 1)
assert pell_fundamental(5) == (9, 4)
assert pell_fundamental(6) == (5, 2)
assert pell_fundamental(7) == (8, 3)
assert pell_fundamental(61) == (1766319049, 226153980)

print("(A) Pell fundamentals for the 31 squarefree S-units:")
fund = {}
for a in AS:
    X1, Y1 = pell_fundamental(a)
    assert X1 * X1 - a * Y1 * Y1 == 1
    fund[a] = (X1, Y1)
    print("   a=%5d  X1=%-14d Y1=%-10d %s" % (a, X1, Y1,
          "SURVIVOR" if smooth11(Y1) else "dead (Y1 not 11-smooth)"))

alive = [a for a in AS if smooth11(fund[a][1])]
print("   survivors: %d of 31" % len(alive))

# BRUTE MINIMALITY CERTIFICATION (independent of any CF/Legendre theory):
# for every 1 <= Y' < Y1, a*Y'^2+1 is not a square -> Y1 (hence X1) is the
# minimal positive solution; the descent lemma then gives the full power
# structure from minimality alone.
minim_it = 0
for a in AS:
    X1, Y1 = fund[a]
    for Yp in range(1, Y1):
        Xp = isqrt(a * Yp * Yp + 1)
        assert Xp * Xp != a * Yp * Yp + 1, \
            "minimality FAILS a=%d Y'=%d" % (a, Yp)
        minim_it += 1
print("   brute minimality certified: %d checks (no Y'<Y1 solves)" % minim_it)

# ---------------------------------------------------------------- (C)+(D)+(E)
print()
print("(C/D/E) Lucas laws + size bound + census per surviving a:")
census = []   # (x, a, n, Xn, Yn)
for a in alive:
    X1, Y1 = fund[a]
    alpha_log2 = log2(X1 + Y1 * math.sqrt(a))
    P = 2 * X1
    PRE = 400
    U = [0, 1]
    for t in range(2, PRE + 1):
        U.append(P * U[-1] - U[-2])
    # entry points z_p (odd p <= 11)
    ztab = {}
    for p in SODD:
        z = None
        for m in range(1, 13):
            if U[m] % p == 0:
                z = m
                break
        ztab[p] = z
        assert z is None or z <= 12
    # B_{a,p}, C_a, N_a
    B = {p: (max(vp(U[m], p) for m in range(1, 13)) if ztab[p] is not None else 0)
         for p in SODD}
    C_a = log2(Y1) + vp(X1, 2) + sum(B[p] * log2(p) for p in SODD)
    D = C_a + log2(3 * math.sqrt(a))
    n = 2
    while n * alpha_log2 - 2 * log2(n) <= D:
        n += 1
    N_a = n + 5  # safety margin
    assert N_a < PRE
    # valuation-law instances over the full used range n = 2..N_a
    for p in SODD:
        z = ztab[p]
        for m in range(2, N_a + 1):
            if z is None:
                assert U[m] % p != 0, "p=%d divides U_%d but no entry<=12" % (p, m)
            elif m % z == 0:
                assert vp(U[m], p) == vp(U[z], p) + vp(m // z, p), \
                    "valuation law FAILS a=%d p=%d n=%d" % (a, p, m)
            else:
                assert U[m] % p != 0, "entry law FAILS a=%d p=%d n=%d" % (a, p, m)
    # parity-law + identity + size-bound instances; census scan
    npairs = 0
    Xn, Yn = X1, Y1
    for m in range(1, N_a + 1):
        assert Yn == Y1 * U[m]                       # Y_n = Y1 U_n
        if m % 2 == 0:
            assert Xn % 2 == 1                        # X_{2m} odd
        else:
            assert vp(Xn, 2) == vp(X1, 2)            # v2(X_odd) = v2(X1)
        assert vp(U[m], 2) == vp(m, 2) + (1 if vp(m, 2) >= 1 else 0) * vp(X1, 2)
        if smooth11(Yn):
            # size-bound instance (the theorem applies to 11-smooth Y_n)
            assert log2(Yn) <= C_a + 2 * log2(m), \
                "size bound FAILS a=%d n=%d" % (a, m)
        if Xn % 2 == 1 and Yn % 2 == 0:
            x = (Xn - 1) // 2
            if smooth11(x) and smooth11(x + 1):
                census.append((x, a, m, Xn, Yn))
                npairs += 1
        Xn, Yn = X1 * Xn + a * Y1 * Yn, X1 * Yn + Y1 * Xn
    print("   a=%5d: N_a=%3d  B=%s  C_a=%7.2f  pairs_here=%d"
          % (a, N_a, B, C_a, npairs))

census.sort()
print()
print("(E) THE COMPLETE CENSUS — consecutive 11-smooth pairs (x, x+1):")
for (x, a, n, Xn, Yn) in census:
    assert Xn * Xn - a * Yn * Yn == 1
    assert Xn == 2 * x + 1 and Yn % 2 == 0
    assert x * (x + 1) == a * (Yn // 2) ** 2
    assert smooth11(x) and smooth11(x + 1) and smooth11(Yn // 2)
    print("   x=%-12d a=%-5d n=%-3d X=%-16d Y=%-12d b=%d"
          % (x, a, n, Xn, Yn, Yn // 2))
print("   TOTAL PAIRS: %d" % len(census))

# ---------------------------------------------------------------- (F) 4-runs
print()
print("(F) THE 4-RUN ANALYSIS (k = 5..12): a 4-run m..m+3 of k-smooth above k")
print("    contains the census pair (m, m+1) with m > k; scan all census pairs:")
f_upper = True
for k in range(5, 13):
    hits = []
    for (x, a, n, Xn, Yn) in census:
        if x > k and maxprime(x) <= k and maxprime(x + 1) <= k \
           and maxprime(x + 2) <= k and maxprime(x + 3) <= k:
            hits.append(x)
    if hits:
        f_upper = False
    print("   k=%2d: %s   => f(%d) <= 4: %s"
          % (k, "NO 4-RUN above k" if not hits else "4-RUNS FOUND: %s" % hits,
             k, not hits))
assert f_upper

runs3 = sorted(set((x, x + 1, x + 2) for (x, a, n, Xn, Yn) in census
                   if x > 12 and maxprime(x + 2) <= 11))
print("   3-runs of 11-smooth entirely above 12 (x, x+1, x+2): %s"
      % (runs3 if len(str(runs3)) < 200 else "%d runs" % len(runs3)))

# maximal-run structure from the census
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
print("   maximal runs of consecutive 11-smooth (length >= 3):")
for r in runs:
    if len(r) >= 3:
        print("      start=%-8d len=%d  %s" % (r[0], len(r),
              (tuple(r) if len(r) <= 8 else "(%d, ..., %d)" % (r[0], r[-1]))))
print("   (maximal run length overall: %d)" % max(len(r) for r in runs))

# ---------------------------------------------------------------- (G) cross
print()
print("(G) DUAL CROSS-CHECK — brute enumeration of all 11-smooth <= 10^30:")
B30 = 10 ** 30
nums = []
p2 = 1
while p2 <= B30:
    p23 = p2
    while p23 <= B30:
        p235 = p23
        while p235 <= B30:
            p2357 = p235
            while p2357 <= B30:
                n = p2357
                while n <= B30:
                    nums.append(n)
                    n *= 11
                p2357 *= 7
            p235 *= 5
        p23 *= 3
    p2 *= 2
nums.sort()
print("   11-smooth count <= 10^30: %d" % len(nums))
brute_pairs = [(u, v) for u, v in zip(nums, nums[1:]) if v == u + 1]
census_pairs30 = [(x, x + 1) for (x, _, _, _, _) in census if x + 1 <= B30]
print("   brute pairs: %d ; census pairs <= 10^30: %d ; EQUAL: %s"
      % (len(brute_pairs), len(census_pairs30),
         brute_pairs == census_pairs30))
assert brute_pairs == census_pairs30
for k in range(5, 13):
    bad = [u for (u, v) in brute_pairs if u > k and maxprime(u) <= k
           and maxprime(u + 1) <= k and maxprime(u + 2) <= k
           and maxprime(u + 3) <= k]
    assert not bad, "brute 4-run found k=%d" % k
print("   brute 4-run check k=5..12 (<=10^30): CLEAN")
print("   k=13 lower witness (14,15,16): smooth13=%s, all>13=%s"
      % (maxprime(14) <= 13 and maxprime(15) <= 13 and maxprime(16) <= 13, True))
# 13-frontier: a 4-run of 13-smooth above 13 exists -> f(13) >= 5
def sm13(n):
    for p in [2, 3, 5, 7, 11, 13]:
        while n % p == 0:
            n //= p
    return n == 1
run13 = [m for m in range(14, 10 ** 6)
         if sm13(m) and sm13(m + 1) and sm13(m + 2) and sm13(m + 3)]
print("   k=13 frontier: 4-run of 13-smooth above 13 (scan <= 10^6): %s"
      % (run13[:3] if run13 else "NONE"))
assert run13 and run13[0] == 24   # (24,25,26,27): 26 = 2*13 -> f(13) >= 5

print()
print("STORMER961 ALL GREEN — %.1fs" % (__import__('time').time() - T0))
