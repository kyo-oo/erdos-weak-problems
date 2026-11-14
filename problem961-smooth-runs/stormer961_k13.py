#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
STORMER961_K13 — THE COMPLETE STØRMER–PELL CENSUS for S = {2,3,5,7,11,13}
(the 13-tier — S063 W62 volley, task 1-c: f(k) EXACT for k = 13..16).

The 6-prime tier of the campaign's certification architecture (stormer961.py,
COMPLETE_PROOF.md §3 executed at S={2,3,5,7,11}, T8 "the generic certification
architecture" — every finite prime set closes by the same laws).  For k in
{13,14,15,16} the primes <= k are EXACTLY S = {2,3,5,7,11,13} (14=2·7, 15=3·5,
16=2^4 add no new prime), so k-smooth = 13-smooth for all four k, and

    f(k) = 1 + max{ L : a run of L consecutive 13-smooth integers all > k } .

THE CERTIFICATION ARCHITECTURE (machine-verifies every component; identical
laws to the 5-prime tier, SODD = {3,5,7,11,13}):

(A) For each of the 63 squarefree S-units a (nonempty subset products):
    fundamental solution (X1,Y1) of X^2-aY^2=1 by exact integer continued
    fractions of sqrt(a); certification X1^2-aY1^2=1 direct; convergent
    denominators machine-checked NON-decreasing (ties only at the first step,
    same Y hence same solution), every pre-hit convergent checked p^2-aq^2<>1,
    so the first +1 convergent is value-least (Legendre: every solution has
    |X/Y-sqrt(a)| < 1/(2Y^2), hence is a convergent).  BRUTE minimality
    (independent of CF/Legendre): for every 1<=Y'<Y1, aY'^2+1 is not a square
    — executed here for every a with Y1 <= 10^6 (62 of the 63 equations); the
    single heavy equation a=5005 (Y1=625742712) is brute-certified by the
    companion job logs/brute5005.log (625,742,711 checks).

(B) PRUNE: Y1 must be 13-smooth else a yields no pair at all (n=1: Y1=2b;
    n>=2: Y1 | Y_n = Y1 U_n).  Kill receipt: the prime > 13 dividing Y1.

(C) LUCAS VALUATION LAWS (instance-verified over the whole used range):
    U_0=0, U_1=1, U_{n+2}=2X1 U_{n+1}-U_n; Y_n = Y1 U_n.
    - parity: X_{2m} odd; v2(X_odd) = v2(X1); v2(U_n) = v2(n)+[n even]v2(X1).
    - entry point z_p := min{m>=1: p | U_m} satisfies z_p <= p+1 <= 14 for
      every odd p <= 13 (unramified: z_p | p-(a/p); intrinsic: z_p = p).
    - valuation law: p | U_n iff z_p | n; and when z_p | n:
      v_p(U_n) = v_p(U_{z_p}) + v_p(n/z_p)  ->  v_p(U_n) <= B_{a,p}+v_p(n),
      B_{a,p} := max_{1<=m<=14} v_p(U_m).

(D) SIZE BOUND (termination): if Y_n is 13-smooth then
        log2 Y_n <= C_a + 2 log2 n,   C_a = log2(Y1)+v2(X1)+sum_{odd p<=13} B_{a,p} log2 p,
    while log2 Y_n >= n log2(alpha) - log2(3 sqrt(a)), alpha = X1+Y1 sqrt(a) >= 2+sqrt3.
    -> n <= N_a (explicit per-a cap; g(n)=n log2 alpha - 2 log2 n increasing for
    n >= 2: log2 alpha >= 1.90 > 2 log2(3/2) = 1.170).  Census loop n = 1..N_a only.

(E) THE CENSUS: for surviving a, n = 1..N_a (gmpy2 mpz powers): keep n with
    X_n odd, Y_n even, x=(X_n-1)/2 and x+1 both 13-smooth.  Completeness:
    every consecutive 13-smooth pair (x,x+1) has a := sf(x(x+1)) among the 63,
    (2x+1,2b) solving that Pell equation, hence = (X_n,Y_n) for a unique n
    <= N_a by (D).  THE ANSWER: exactly 68 pairs, largest x = 123200.

(F) THE f(k) TABLE k=13..16: L(k) = max over maximal runs r of |{j in r: j>k}|
    (elements > k form a suffix of a run); f(k) = L(k)+1.  Witness: the run
    (24,25,26,27,28) — all 13-smooth, all > 16 — gives f(k) >= 6 for all four
    k; the exclusion (no 6-run of 13-smooth above k, from the complete census)
    gives f(k) <= 6.  Hence f(13)=f(14)=f(15)=f(16)=6.
    CALIBRATION LAW: the same 13-tier census re-derives the certified rows
    f(3..12) (filter pairs to k-smooth) and f(2)=2 (singleton 2k argument),
    and contains the certified 40 11-smooth pairs verbatim.

(G) DUAL CROSS-CHECK: brute enumeration of ALL 13-smooth numbers <= 10^18;
    consecutive pairs must equal the Pell census pairs <= 10^18; direct check
    of the no-6-run law for k=13..16 (independent of Pell); run decompositions
    must agree.
"""
import math
from math import isqrt, log2
from gmpy2 import mpz

T0 = __import__('time').time()

S = [2, 3, 5, 7, 11, 13]
SODD = [3, 5, 7, 11, 13]
ZMAX = 14            # z_p <= p+1 <= 14 for every odd p <= 13

def sf_a_values():
    out = []
    for mask in range(1, 64):
        a = 1
        for i, p in enumerate(S):
            if (mask >> i) & 1:
                a *= p
        out.append(a)
    return sorted(out)

AS = sf_a_values()
assert len(AS) == 63 and AS[0] == 2 and AS[-1] == 30030

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

def smooth13(n):
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
        if steps > 200000:
            raise RuntimeError("CF runaway for a=%d" % a)

# sanity anchors (classical Pell data + the 13-tier heavy row)
assert pell_fundamental(2) == (3, 2)
assert pell_fundamental(3) == (2, 1)
assert pell_fundamental(5) == (9, 4)
assert pell_fundamental(6) == (5, 2)
assert pell_fundamental(7) == (8, 3)
assert pell_fundamental(13) == (649, 180)
assert pell_fundamental(61) == (1766319049, 226153980)
assert pell_fundamental(5005) == (44268809311, 625742712)

print("(A) Pell fundamentals for the 63 squarefree S-units (S={2,3,5,7,11,13}):")
fund = {}
for a in AS:
    X1, Y1 = pell_fundamental(a)
    assert X1 * X1 - a * Y1 * Y1 == 1
    fund[a] = (X1, Y1)

alive = [a for a in AS if smooth13(fund[a][1])]
dead = [a for a in AS if not smooth13(fund[a][1])]
print("   63 equations solved; survivors (Y1 13-smooth): %d ; dead: %d"
      % (len(alive), len(dead)))
for a in dead:
    Y1 = fund[a][1]
    # explicit kill receipt: the smallest prime > 13 dividing Y1
    r = Y1
    for p in [2, 3, 5, 7, 11, 13]:
        while r % p == 0:
            r //= p
    assert r > 1, "dead a=%d has smooth Y1?!" % a
    q = 2
    while r % q != 0:
        q += 1
    kp = q  # smallest prime factor of the 13-stripped part, hence > 13
    print("   DEAD a=%5d: Y1=%-10d killed by prime %d > 13" % (a, Y1, kp))

# BRUTE MINIMALITY (independent of any CF/Legendre theory): for every
# 1 <= Y' < Y1, a*Y'^2+1 is not a square.  Executed for every a with
# Y1 <= 10^6 (62 of 63).  The heavy a=5005 row (Y1=625742712) is certified by
# the companion job logs/brute5005.log.
minim_it = 0
for a in AS:
    X1, Y1 = fund[a]
    if Y1 > 1_000_000:
        print("   [a=%d: Y1=%d > 10^6 -> brute in companion job logs/brute5005.log]"
              % (a, Y1))
        continue
    for Yp in range(1, Y1):
        Xp = isqrt(a * Yp * Yp + 1)
        assert Xp * Xp != a * Yp * Yp + 1, \
            "minimality FAILS a=%d Y'=%d" % (a, Yp)
        minim_it += 1
print("   brute minimality certified (Y1 <= 10^6 rows): %d checks, no Y'<Y1 solves"
      % minim_it)

# ---------------------------------------------------------------- (C)+(D)+(E)
print()
print("(C/D/E) Lucas laws + size bound + census per surviving a:")
census = []   # (x, a, n, Xn, Yn)
for a in alive:
    X1, Y1 = fund[a]
    X1, Y1 = int(X1), int(Y1)
    alpha_log2 = log2(X1 + Y1 * math.sqrt(a))
    P = 2 * X1
    PRE = 1000
    U = [0, 1]
    for t in range(2, PRE + 1):
        U.append(P * U[-1] - U[-2])
    # entry points z_p (odd p <= 13), law z_p <= p+1 <= 14
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
    assert N_a < PRE
    assert alpha_log2 >= log2(2 + math.sqrt(3))  # alpha >= 2+sqrt3 (X1>=2, Y1>=1)
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
            assert vp(int(Xn), 2) == vp(X1, 2)      # v2(X_odd) = v2(X1)
        assert vp(U[m], 2) == vp(m, 2) + (1 if vp(m, 2) >= 1 else 0) * vp(X1, 2)
        if smooth13(int(Yn)):
            # size-bound instance (the theorem applies to 13-smooth Y_n)
            assert log2(int(Yn)) <= C_a + 2 * log2(m), \
                "size bound FAILS a=%d n=%d" % (a, m)
        if Xn % 2 == 1 and Yn % 2 == 0:
            x = (Xn - 1) // 2
            if smooth13(int(x)) and smooth13(int(x + 1)):
                census.append((int(x), a, m, int(Xn), int(Yn)))
                npairs += 1
        Xn, Yn = X1 * Xn + a * Y1 * Yn, X1 * Yn + Y1 * Xn
    print("   a=%5d: N_a=%3d  B=%s  C_a=%7.2f  pairs_here=%d"
          % (a, N_a, B, C_a, npairs))

census.sort()
print()
print("(E) THE COMPLETE CENSUS — consecutive 13-smooth pairs (x, x+1):")
for (x, a, n, Xn, Yn) in census:
    assert Xn * Xn - a * Yn * Yn == 1
    assert Xn == 2 * x + 1 and Yn % 2 == 0
    assert x * (x + 1) == a * (Yn // 2) ** 2
    assert smooth13(x) and smooth13(x + 1) and smooth13(Yn // 2)
    print("   x=%-12d a=%-5d n=%-3d X=%-16d Y=%-12d b=%d"
          % (x, a, n, Xn, Yn, Yn // 2))
print("   TOTAL PAIRS: %d" % len(census))
assert len(census) == 68
assert max(x for (x, *_ ) in census) == 123200

# ---------------------------------------------------------------- (F) f(k)
print()
print("(F) THE f(k) TABLE — k = 13..16 (primes <= k = {2,3,5,7,11,13} for all four):")
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
print("   maximal runs of consecutive 13-smooth (length >= 3):")
for r in runs:
    if len(r) >= 3:
        print("      start=%-8d len=%d  %s" % (r[0], len(r),
              (tuple(r) if len(r) <= 8 else "(%d, ..., %d)" % (r[0], r[-1]))))
print("   (maximal run length overall: %d — the run (1..16), below every k>=17"
      % max(len(r) for r in runs))
assert max(len(r) for r in runs) == 16 and runs[0][0] == 1

def Lmax(k):
    """L(k) = max over maximal runs of the number of elements > k (a suffix)."""
    best = 0
    for r in runs:
        s = sum(1 for j in r if j > k)
        if s > best:
            best = s
    return best

for k in (13, 14, 15, 16):
    L = Lmax(k)
    print("   k=%2d: longest run of %d-smooth entirely > %d has length %d  ->  f(%d) = %d"
          % (k, k, k, L, k, L + 1))
    assert L == 5
FK = {k: Lmax(k) + 1 for k in (13, 14, 15, 16)}
assert FK == {13: 6, 14: 6, 15: 6, 16: 6}

# WITNESS LAW (the lower bound, explicit): the run (24,25,26,27,28)
wit = (24, 25, 26, 27, 28)
for j in wit:
    assert smooth13(j) and j > 16
print("   WITNESS: (24,25,26,27,28) = (2^3·3, 5^2, 2·13, 3^3, 2^2·7), all > 16")
print("   -> f(k) >= 6 for k = 13..16 (a 5-run of 13-smooth above every k <= 16)")

# EXCLUSION (the upper bound): no 6-run of 13-smooth above k, from the census
for k in (13, 14, 15, 16):
    hits = [x for (x, a, n, Xn, Yn) in census
            if x > k and smooth13(x + 2) and smooth13(x + 3)
            and smooth13(x + 4) and smooth13(x + 5)]
    assert not hits, "6-run found above k=%d: %s" % (k, hits)
print("   EXCLUSION: no census pair x > k with x..x+5 all 13-smooth (k=13..16)")
print("   -> no 6-run of 13-smooth above k  ->  f(k) <= 6")
print()
print("   *** f(13) = f(14) = f(15) = f(16) = 6 — THE CERTIFIED FRONTIER EXTENDED ***")

# CALIBRATION LAW — the 13-tier census re-derives the certified lower tier:
# (i) all 40 certified 11-smooth pairs are 13-smooth pairs of this census;
OLD40 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 20, 21, 24, 27, 32, 35,
         44, 48, 49, 54, 55, 63, 80, 98, 99, 120, 125, 175, 224, 242, 384,
         440, 539, 2400, 3024, 4374, 9800]
newx = set(x for (x, _, _, _, _) in census)
assert all(x in newx for x in OLD40), "old census not contained"
# (ii) f(3..12) re-derived from this census by k-smooth filtering:
def pairs_k(k):
    return sorted(set((x, x + 1) for (x, _, _, _, _) in census
                      if maxprime(x) <= k and maxprime(x + 1) <= k))
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
CAL = {3: 3, 4: 3, 5: 4, 6: 4, 7: 4, 8: 4, 9: 4, 10: 4, 11: 4, 12: 4}
recal = {k: Lmax_k(k) + 1 for k in range(3, 13)}
assert recal == CAL, "calibration mismatch: %s vs %s" % (recal, CAL)
assert Lmax_k(2) + 1 == 2  # f(2)=2: no 2-run of 2-smooth above 2 (pairs filter empty), singleton 4
print("   CALIBRATION: the 40 certified 11-smooth pairs all present; f(2..12)")
print("   re-derived from THIS census by k-smooth filtering: %s"
      % ([2] + [Lmax_k(k) + 1 for k in range(3, 13)]))
print("   (matches the certified table f(2)=2, f(3)=f(4)=3, f(5..12)=4 — GREEN)")

# ---------------------------------------------------------------- (G) cross
print()
print("(G) DUAL CROSS-CHECK — brute enumeration of all 13-smooth <= 10^18:")
B18 = 10 ** 18
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
                    n = p235711
                    while n <= B18:
                        nums.append(n)
                        n *= 13
                    p235711 *= 11
                p2357 *= 7
            p235 *= 5
        p23 *= 3
    p2 *= 2
nums.sort()
print("   13-smooth count <= 10^18: %d" % len(nums))
brute_pairs = [(u, v) for u, v in zip(nums, nums[1:]) if v == u + 1]
census_pairs18 = [(x, x + 1) for (x, _, _, _, _) in census if x + 1 <= B18]
print("   brute pairs: %d ; census pairs <= 10^18: %d ; EQUAL: %s"
      % (len(brute_pairs), len(census_pairs18),
         brute_pairs == census_pairs18))
assert brute_pairs == census_pairs18
brute_set = set(nums)
for k in (13, 14, 15, 16):
    bad = []
    for (u, v) in brute_pairs:
        if u > k and all((u + t) in brute_set for t in range(6)):
            bad.append(u)
    assert not bad, "brute 6-run found k=%d: %s" % (k, bad)
print("   brute 6-run check k=13..16 (<=10^18): CLEAN (no 6 consecutive")
print("   13-smooth integers all > 16 below 10^18, independent of Pell)")
# brute run decomposition must agree below 10^18
bruns = []
cur = [brute_pairs[0][0], brute_pairs[0][1]]
for (u, v) in brute_pairs[1:]:
    if u == cur[-1]:
        cur.append(v)
    else:
        bruns.append(tuple(cur)); cur = [u, v]
bruns.append(tuple(cur))
cruns18 = [r for r in runs if r[0] + 1 <= B18]
assert bruns == cruns18
print("   brute maximal-run decomposition EQUALS the census decomposition (<=10^18)")
w186 = [r for r in bruns if len(r) >= 3]
print("   runs of length >= 3 (brute, entire range): %s"
      % [(r[0], len(r)) for r in w186])

print()
print("THE CERTIFIED FRONTIER OF ERDOS #961 NOW READS:")
print("   f(2)=2, f(3)=f(4)=3, f(k)=4 for 5<=k<=12, f(k)=6 for 13<=k<=16")
print("STORMER961_K13 ALL GREEN — %.1fs" % (__import__('time').time() - T0))
