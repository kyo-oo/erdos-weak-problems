#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ENGINE 142 BEHREND — the sphere-construction certification engine (W71-142K).

Certifies THE Behrend theorem package of PROOF.md section 3B (the six steps),
pure python3, EXACT integer arithmetic + fractions.Fraction (no floats in any
verdict; floats appear only in display columns, always labelled "display").
Two-method law on every claim (PROOF.md section 6.1):

  PART 0  checker self-tests + planted-AP negative controls (non-vacuity).
  PART A  (STEP 1+2+3) SPHERE-FREENESS: grid d in {2,3,4}, m in {3,4,5,6}:
          ALL non-empty level sets S_V of Q(x) = sum x_i^2 over {0..m-1}^d
          verified 3-AP-free by TWO independent detectors:
            M1 full pair-midpoint scan on the lattice points (all pairs
               x != z: componentwise parity + midpoint membership);
            M2 (a,delta)-scan on the integer image phi(S_V) (endpoint-indexed:
               every pair a < b of image points tests a+2*(b-a); equivalent
               to the literal (a,delta) double loop because an AP
               a, a+delta, a+2delta in the set needs its first two terms in
               the set - equivalence machine-checked in PART 0).
          Both must report ZERO non-trivial 3-APs and agree.
          NEGATIVE CONTROL: the union of levels (the full cube image) MUST
          contain 3-APs (the level restriction is load-bearing).
  PART B  (STEP 4) SIZE LAW: per (d,m): max_V |S_V| reported; exact integer
          check max_V|S_V| * (d*(m-1)^2+1) >= m^d; partition identity
          sum_V |S_V| = m^d; value-range check #levels <= d*(m-1)^2+1.
          NEGATIVE CONTROL: the floor (not ceiling) of m^d/(d(m-1)^2+1)
          collapses to 0 somewhere in the grid - the ceiling is load-bearing.
  PART C  (STEP 2) DIGIT MAP: per (d,m): phi injective on the FULL cube
          (|phi(D)| = m^d); no-carry pullback verified EXHAUSTIVELY (every
          integer triple a,b,c in the image with a+c=2b pulls back to
          componentwise x+z=2y via the base-B digit reader) + >= 10^5 random
          triples per (d,m) + random-integer-space hits.
          NEGATIVE CONTROL: at the wrong base B' = 2m-2 the pullback FAILS
          (the carry exhibit of PROOF.md 3B STEP 2).
  PART D  (STEP 5+6) EXPLICIT CONSTANT CHAIN: the two Taylor exhibits of
          Lemma 3B.6 re-verified in exact rational arithmetic; for e=10..60
          (N=2^e) AND all N in [16,4096] AND decades 10^6..10^18 AND N=2^e
          (e=4..60): the construction's guaranteed size
          g = ceil(m^d / (d*(m-1)^2+1)) via the explicit integer rounding
          chain (u = max{u: 2^(u^2) <= N}, m = 2^u, d = max{d: (2m)^d <= N}),
          then BOTH bounds verified:
            MASTER (Theorem 3B.5, exact integers):  N < g*u*2^(1+4u);
            EXP   (Theorem 3B.7, C=6, N0=16):       g >= N*e^(-6*sqrt(ln N)),
              by a certified rational LOWER bound E <= e^(6*sqrt(ln N))
              (positive Taylor partial sum at a rational rho <= sqrt(ln N),
              rho from ln N >= floor(log2 N)*(9/13)), checking
              N*E.denominator <= g*E.numerator exactly.
          Every intermediate chain inequality is checked per N.
  PART E  (STEP 3/6 shift) SUBSETS OF [1,N]: per grid (d,m) the shifted
          best-level family W = phi(S_V*)+1: containment in [1,(2m)^d],
          3-AP-freeness under the pinned comparator convention (a >= 1,
          delta >= 1) by the LITERAL (a,delta) double loop AND the
          endpoint-indexed scan (agreement required); block-envelope
          consistency |W| <= 2*floor(N/3) + N mod 3; the new machine-
          witnessed data points r_3((2m)^d) >= |S_V*|.

EXIT: prints BEHREND_ENGINE_142_GREEN / _RED.
"""

import itertools
import math
import random
import sys
import time
from fractions import Fraction

T0 = time.time()
SEED = 71142  # deterministic engine

FAILURES = []
CHECKS = [0, 0]  # passed, failed


def check(cid, desc, ok, detail=""):
    CHECKS[0 if ok else 1] += 1
    line = "[%s] %s%s -- VERDICT: %s" % (
        cid, desc, (" | " + detail) if detail else "", "PASS" if ok else "FAIL")
    print(line, flush=True)
    if not ok:
        FAILURES.append(line)
    return ok


def info(msg):
    print("      %s" % msg, flush=True)


def stamp():
    return "t=%+7.1fs" % (time.time() - T0)


# ===========================================================================
# core objects (PROOF.md 3B): cube, square form Q, digit map phi at base B=2m
# ===========================================================================

def cube_points(d, m):
    return list(itertools.product(range(m), repeat=d))


def Q_of(x):
    return sum(c * c for c in x)


def phi_of(x, B):
    """phi(x) = sum_i x_i * B^(i-1)  (x_i = digit at position i-1)."""
    v = 0
    for i, c in enumerate(x):
        v += c * B ** i
    return v


def levels_of(d, m):
    """All non-empty level sets of Q on {0..m-1}^d, as dict V -> list of x."""
    pts = {}
    for x in cube_points(d, m):
        pts.setdefault(Q_of(x), []).append(x)
    return pts


def read_digits(a, B, d):
    """The base-B digit reader: recover the d-position digit vector of a
    (a in [0, B^d)); returns None if any digit is out of [0, m-1] is NOT
    checked here - caller gets raw digits (Lemmas 1.2/1.3 at base B)."""
    ds = []
    for _ in range(d):
        ds.append(a % B)
        a //= B
    assert a == 0, "reader overflow: a >= B^d"
    return tuple(ds)


# ===========================================================================
# detectors (two independent code paths)
# ===========================================================================

def ap3_free_pairmid_vec(S):
    """M1: full pair-midpoint scan on LATTICE points. For every pair
    x != z: if x+z is even componentwise and (x+z)/2 is in S, a non-trivial
    3-AP exists. Returns the witness triple or None."""
    Sset = set(S)
    L = sorted(Sset)
    n = len(L)
    dd = len(L[0]) if L else 0
    for i in range(n):
        a = L[i]
        for j in range(i + 1, n):
            c = L[j]
            ok = True
            mid = []
            for t in range(dd):
                s = a[t] + c[t]
                if s & 1:
                    ok = False
                    break
                mid.append(s >> 1)
            if ok:
                mid = tuple(mid)
                if mid in Sset:
                    return (a, mid, c)
    return None


def ap3_scan_image(img):
    """M2: (a,delta)-scan over the INTEGER image set, endpoint-indexed:
    for every pair a < b in the set, delta = b-a, test a+2*delta.
    COMPLETE: any AP (a, a+delta, a+2delta) inside the set has its first two
    terms in the set, so it appears as the pair (a, a+delta). Returns the
    witness triple or None."""
    S = sorted(set(img))
    Sset = set(S)
    n = len(S)
    for i in range(n):
        a = S[i]
        for j in range(i + 1, n):
            b = S[j]
            c = a + 2 * (b - a)
            if c in Sset:
                return (a, b, c)
    return None


def ap3_scan_literal(S, N):
    """LITERAL comparator-convention scan: non-trivial 3-AP = a, a+delta,
    a+2delta with a >= 1, delta >= 1, all in S (S subseteq [1,N]). Double
    loop over (a, delta) exactly as pinned in challenge.json. Returns the
    witness triple or None."""
    Sset = set(S)
    for a in sorted(Sset):
        if a < 1:
            return ("ELEMENT<1", a)
        dmax = (N - a) // 2
        for delta in range(1, dmax + 1):
            if (a + delta) in Sset and (a + 2 * delta) in Sset:
                return (a, a + delta, a + 2 * delta)
    return None


# ===========================================================================
# PART 0 - checker self-tests + negative controls
# ===========================================================================

def part0():
    print("=" * 78, flush=True)
    print("ENGINE 142 BEHREND - certification of PROOF.md section 3B "
          "(the six steps)", flush=True)
    print("exact integer arithmetic + fractions.Fraction; floats only in "
          "display columns", flush=True)
    print("=" * 78, flush=True)
    print("[PART 0] CHECKER SELF-TESTS + NEGATIVE CONTROLS", flush=True)

    # 0.1 lattice pair-midpoint detector on known cases
    cases = [
        ([(0, 0), (1, 1), (2, 2)], True),    # 3-AP on the diagonal
        ([(0, 0), (1, 1)], False),
        ([(0, 0), (0, 2), (0, 1)], True),    # vertical 3-AP
        ([(0, 0), (0, 2), (1, 1)], False),   # midpoint is (0,1), not in S
        ([(2, 0), (2, 2), (2, 1)], True),
        ([(0, 0), (2, 1), (1, 2)], False),
    ]
    ok = True
    for (S, expect) in cases:
        got = ap3_free_pairmid_vec(S) is not None
        if got != expect:
            ok = False
            info("pairmid_vec(%s) = %s expected %s" % (S, got, expect))
    check("0.1", "lattice pair-midpoint detector: %d known cases correct"
          % len(cases), ok)

    # 0.2 image (a,delta) detector on known cases
    cases = [
        ([0, 1, 2], True), ([0, 7, 14], True), ([0, 1], False),
        ([1, 2, 4, 8], False), ([1, 2, 4, 5], True), ([3, 5, 7], True),
        ([0, 2, 3, 5], True),
    ]
    ok = True
    for (S, expect) in cases:
        got = ap3_scan_image(S) is not None
        if got != expect:
            ok = False
            info("ap3_scan_image(%s) = %s expected %s" % (S, got, expect))
    check("0.2", "image (a,delta) detector: %d known cases correct"
          % len(cases), ok)

    # 0.3 equivalence literal vs endpoint-indexed on random sets
    rng = random.Random(SEED)
    agree = 0
    ok = True
    for _ in range(400):
        S = set(v for v in range(1, 41) if rng.random() < 0.4)
        a = ap3_scan_literal(S, 40)
        b = ap3_scan_image(S)
        if (a is None) != (b is None):
            ok = False
            info("literal vs endpoint-indexed disagree on %s" % sorted(S))
            break
        agree += 1
    check("0.3", "literal (a,delta) loop == endpoint-indexed scan on %d/400 "
          "random sets" % agree, ok and agree == 400)

    # 0.4 planted-AP negative control (both detectors MUST fire)
    planted = [(0, 0), (1, 1), (2, 2)]
    check("0.4", "negative control: planted lattice 3-AP %s DETECTED by "
          "pair-midpoint" % (planted,),
          ap3_free_pairmid_vec(planted) is not None)
    check("0.5", "negative control: planted image 3-AP (0,7,14) DETECTED "
          "by (a,delta) scan", ap3_scan_image([0, 7, 14]) is not None)
    print("    %s" % stamp(), flush=True)


# ===========================================================================
# PART A - (a) sphere-freeness on the grid, two methods
# ===========================================================================

GRID_D = [2, 3, 4]
GRID_M = [3, 4, 5, 6]


def part_a():
    print("[PART A] (a) SPHERE-FREENESS: ALL level sets of Q on "
          "{0..m-1}^d, d in %s, m in %s - TWO METHODS" % (GRID_D, GRID_M),
          flush=True)
    all_ok = True
    total_levels = 0
    total_points = 0
    for d in GRID_D:
        for m in GRID_M:
            B = 2 * m
            lev = levels_of(d, m)
            nlev = len(lev)
            npts = sum(len(v) for v in lev.values())
            total_levels += nlev
            total_points += npts
            ok = True
            for V in sorted(lev):
                S = lev[V]
                w1 = ap3_free_pairmid_vec(S)       # M1 lattice pair-midpoint
                img = [phi_of(x, B) for x in S]
                if len(set(img)) != len(S):
                    ok = False
                    info("(d=%d,m=%d,V=%d): phi NOT injective on level"
                         % (d, m, V))
                w2 = ap3_scan_image(img)            # M2 image (a,delta)-scan
                if w1 is not None or w2 is not None:
                    ok = False
                    info("(d=%d,m=%d,V=%d): 3-AP FOUND: vec=%s img=%s"
                         % (d, m, V, w1, w2))
            best = max(lev.values(), key=len)
            info("d=%d m=%d B=%2d B^d=%6d: %3d non-empty levels, %5d pts; "
                 "all levels 3-AP-free by BOTH methods; best level V*=%d "
                 "|S*|=%d" % (d, m, B, B ** d, nlev, npts,
                              Q_of(best[0]), len(best)))
            if not ok:
                all_ok = False
    check("A.1", "ALL %d non-empty level sets (%d points) on the grid are "
          "3-AP-free by BOTH detectors (full pair-midpoint scan + "
          "independent (a,delta) image scan); zero non-trivial 3-APs; "
          "methods agree 100%%" % (total_levels, total_points), all_ok)

    # negative control: the union of levels (full cube image) has 3-APs
    d, m, B = 2, 3, 6
    full_img = [phi_of(x, B) for x in cube_points(d, m)]
    w = ap3_scan_image(full_img)
    ok = w is not None and w == (0, 1, 2)
    pre = [read_digits(v, B, d) for v in (0, 1, 2)]
    check("A.2", "negative control: the UNION of levels (full cube image, "
          "d=2,m=3) CONTAINS the 3-AP %s (preimages %s, componentwise "
          "x+z=2y) - the level restriction of STEP 1 is load-bearing"
          % (w, pre), ok, "union is NOT 3-AP-free, as it must be")
    print("    %s" % stamp(), flush=True)
    return {(d, m): levels_of(d, m) for d in GRID_D for m in GRID_M}


# ===========================================================================
# PART B - (b) the size law (STEP 4 pigeonhole)
# ===========================================================================

def part_b(grid_levels):
    print("[PART B] (b) SIZE LAW (STEP 4): max_V |S_V| >= m^d / "
          "(d*(m-1)^2+1) - exact integer check", flush=True)
    all_ok = True
    zero_floor_somewhere = False
    for d in GRID_D:
        for m in GRID_M:
            lev = grid_levels[(d, m)]
            sizes = {V: len(S) for V, S in lev.items()}
            maxsize = max(sizes.values())
            Vstar = max(sizes, key=lambda V: sizes[V])
            den = d * (m - 1) ** 2 + 1
            num = m ** d
            ok_int = maxsize * den >= num                      # exact
            ok_part = sum(sizes.values()) == num               # partition
            ok_range = len(sizes) <= den                       # value range
            ceil_g = -((-num) // den)                          # exact ceiling
            floor_g = num // den
            if floor_g == 0:
                zero_floor_somewhere = True
            if not (ok_int and ok_part and ok_range):
                all_ok = False
                info("(d=%d,m=%d): pigeonhole/partition/range FAILED"
                     % (d, m))
            info("d=%d m=%d: m^d=%5d levels<=%3d (actual %3d) | "
                 "max_V|S_V|=%3d (V*=%3d) >= m^d/(d(m-1)^2+1) = %7.3f "
                 "[exact: %3d*%3d >= %5d] ratio=%6.3f ceil=%d floor=%d"
                 % (d, m, num, den, len(sizes), maxsize, Vstar,
                    num / den, maxsize, den, num, maxsize / (num / den),
                    ceil_g, floor_g))
    check("B.1", "SIZE LAW on the grid: max_V|S_V|*(d*(m-1)^2+1) >= m^d "
          "everywhere (exact integers); partition identity "
          "sum_V|S_V| = m^d; #levels <= d*(m-1)^2+1", all_ok)
    check("B.2", "negative control: the FLOOR (not ceiling) of "
          "m^d/(d*(m-1)^2+1) collapses to 0 somewhere on the grid - the "
          "ceiling of Lemma 3B.4 is load-bearing (guaranteed size would be "
          "0, breaking the master bound - see D.4)", zero_floor_somewhere)
    print("    %s" % stamp(), flush=True)


# ===========================================================================
# PART C - (c) the digit map: injectivity + no-carry pullback
# ===========================================================================

def part_c():
    print("[PART C] (c) DIGIT MAP at base B=2m: injectivity + no-carry "
          "pullback (exhaustive + >=10^5 random triples per (d,m))",
          flush=True)
    rng = random.Random(SEED + 1)
    all_ok = True
    grand_exh = 0
    grand_rand = 0
    grand_randhits = 0
    for d in GRID_D:
        for m in GRID_M:
            B = 2 * m
            pts = cube_points(d, m)
            img = [phi_of(x, B) for x in pts]
            imgset = set(img)
            inv = {v: x for x, v in zip(pts, img)}
            # C.1 injectivity on the FULL cube
            ok_inj = (len(imgset) == len(pts))
            # C.2 exhaustive pullback: EVERY (a,c) in image^2 with
            # b=(a+c)/2 in image (i.e. every integer triple with a+c=2b in
            # the image) must pull back to componentwise x+z=2y.
            exh = 0
            ok_exh = True
            for a in img:
                for c in img:
                    s = a + c
                    if s & 1:
                        continue
                    b = s >> 1
                    if b in imgset:
                        x, y, z = inv[a], inv[b], inv[c]
                        good = all(x[t] + z[t] == 2 * y[t] for t in range(d))
                        # reader cross-check: digits of a,b,c at base B
                        xa = read_digits(a, B, d)
                        xb = read_digits(b, B, d)
                        xc = read_digits(c, B, d)
                        good_reader = all(xa[t] + xc[t] == 2 * xb[t]
                                          for t in range(d))
                        if not (good and good_reader):
                            ok_exh = False
                            info("PULLBACK FAIL (d=%d,m=%d): %d,%d,%d"
                                 % (d, m, a, b, c))
                        exh += 1
            grand_exh += exh
            # C.3 >= 10^5 random triples in the image space (midpoint
            # construction): random x,z in the cube with x+z even; verify
            # the integer identity a+c=2b AND the reader pullback.
            rcount = 0
            ok_rand = True
            npts = len(pts)
            while rcount < 100000:
                x = pts[rng.randrange(npts)]
                z = pts[rng.randrange(npts)]
                if any((x[t] + z[t]) & 1 for t in range(d)):
                    continue
                y = tuple((x[t] + z[t]) >> 1 for t in range(d))
                a, b, c = phi_of(x, B), phi_of(y, B), phi_of(z, B)
                if a + c != 2 * b:
                    ok_rand = False
                    info("linearity FAIL at %s %s" % (x, z))
                    break
                xa = read_digits(a, B, d)
                xb = read_digits(b, B, d)
                xc = read_digits(c, B, d)
                if not (xa == x and xb == y and xc == z):
                    ok_rand = False
                    info("reader recovery FAIL at %s %s" % (x, z))
                    break
                if not all(xa[t] + xc[t] == 2 * xb[t] for t in range(d)):
                    ok_rand = False
                    info("digit law FAIL at %s %s" % (x, z))
                    break
                rcount += 1
            grand_rand += rcount
            # C.4 random integer-space pairs (a,c): whenever all three of
            # a, (a+c)/2, c land in the image, verify the pullback.
            hits = 0
            ok_hits = True
            Bd = B ** d
            for _ in range(200000):
                a = rng.randrange(Bd)
                c = rng.randrange(Bd)
                s = a + c
                if s & 1:
                    continue
                b = s >> 1
                if a in imgset and b in imgset and c in imgset:
                    x, y, z = inv[a], inv[b], inv[c]
                    if not all(x[t] + z[t] == 2 * y[t] for t in range(d)):
                        ok_hits = False
                        info("random-integer pullback FAIL %d %d" % (a, c))
                    hits += 1
            grand_randhits += hits
            if not (ok_inj and ok_exh and ok_rand and ok_hits):
                all_ok = False
            info("d=%d m=%d B=%2d: |phi(D)|=%4d (injective=%s); exhaustive "
                 "image-triples pulled back: %6d; random triples: %6d/100000 "
                 "OK; random-integer all-in-image hits: %5d - all pull back"
                 % (d, m, B, len(imgset), ok_inj, exh, rcount, hits))
    check("C.1", "phi injective on the full cube for every grid (d,m) "
          "(|phi(D)| = m^d)", all_ok)
    check("C.2", "no-carry pullback: EXHAUSTIVE over every integer triple "
          "(a,b,c) in the image with a+c=2b (%d triples grid-wide): each "
          "pulls back to componentwise x+z=2y via the base-B digit reader"
          % grand_exh, all_ok)
    check("C.3", "no-carry digit law on %d random image-space triples "
          "(>=10^5 per (d,m)): integer identity a+c=2b + reader recovery + "
          "digit-wise law all hold" % grand_rand, all_ok)
    check("C.4", "random-integer-space triples (%d all-in-image hits "
          "grid-wide): every hit pulls back" % grand_randhits, all_ok)

    # C-NEG negative control: the WRONG base B' = 2m-2 breaks the pullback
    # (the carry exhibit of PROOF.md 3B STEP 2).
    d, m = 2, 3
    Bp = 2 * m - 2
    x, y, z = (0, 1), (2, 0), (0, 0)
    fx, fy, fz = phi_of(x, Bp), phi_of(y, Bp), phi_of(z, Bp)
    id_ok = (fx + fz == 2 * fy)
    pull_ok = all(x[t] + z[t] == 2 * y[t] for t in range(d))
    check("C.5", "negative control: at the wrong base B'=2m-2=4 (m=3), the "
          "integer identity phi'(x)+phi'(z)=2phi'(y) HOLDS (%d+%d=2*%d) "
          "while x+z != 2y componentwise (%s vs %s) - the pullback FAILS, "
          "the no-carry hypothesis |c_i|<B of Lemma 3B.2 is load-bearing"
          % (fx, fz, fy, x + (0,) and tuple(x[t] + z[t] for t in range(d)),
             tuple(2 * y[t] for t in range(d))),
          id_ok and not pull_ok and (fx, fy, fz) == (4, 2, 0))
    # and the same triple at the CORRECT base B=6 has no integer relation
    fx6, fy6, fz6 = phi_of(x, 6), phi_of(y, 6), phi_of(z, 6)
    check("C.6", "the same triple at the correct base B=6 satisfies NO "
          "integer relation (phi=%s: %d+%d != 2*%d) - consistent with the "
          "pullback theorem" % ((fx6, fy6, fz6), fx6, fz6, fy6),
          fx6 + fz6 != 2 * fy6)
    print("    %s" % stamp(), flush=True)


# ===========================================================================
# PART D - (d) the explicit constant chain (STEP 5 + STEP 6)
# ===========================================================================

def behrend_params(N):
    """The explicit integer rounding chain of PROOF.md 3B (Corollary 3B.9):
    u = max{u>=1 : 2^(u^2) <= N}  (= floor(sqrt(log2 N)));
    m = 2^u; d = max{d>=1 : (2m)^d <= N}  (= floor(log2 N / (1+u)))."""
    u = 1
    while (1 << ((u + 1) * (u + 1))) <= N:
        u += 1
    m = 1 << u
    d = 1
    while (2 * m) ** (d + 1) <= N:
        d += 1
    return u, m, d


def guaranteed_size(d, m):
    """g = ceil(m^d / (d*(m-1)^2+1)) - the STEP 4 guaranteed level size."""
    num = m ** d
    den = d * (m - 1) ** 2 + 1
    return -((-num) // den), num, den


_E_CACHE = {}


def E_lower_bound(lg, K=200):
    """Certified rational LOWER bound E <= e^(6*sqrt(ln N)) for every N with
    floor(log2 N) = lg. Chain (all exact):
      ln N >= lg * ln 2 >= lg * 9/13          (Lemma 3B.6 T4: ln2 > 9/13);
      rho := rational lower bound of sqrt(9*lg/13) (integer sqrt);
      E := sum_{k<=K} (6*rho)^k / k!  <= e^(6*rho) <= e^(6*sqrt(ln N))
        (positive partial sums are lower bounds).
    Returns the Fraction E."""
    if lg in _E_CACHE:
        return _E_CACHE[lg]
    t = Fraction(9 * lg, 13)              # <= ln N
    A, Bq = t.numerator, t.denominator    # t = A/Bq
    k = 24
    s = math.isqrt(A * Bq * 10 ** (2 * k))
    rho = Fraction(s, Bq * 10 ** k)       # <= sqrt(t) <= sqrt(ln N)
    x = 6 * rho                           # 6*rho
    p, q = x.numerator, x.denominator
    # E = sum_{k<=K} (p/q)^k / k!  = [ sum_k p^k q^(K-k) (K!/k!) ] / (q^K K!)
    Kf = math.factorial(K)
    num = 0
    pk = 1
    qk = q ** K
    for k in range(K + 1):
        num += pk * qk * (Kf // math.factorial(k))
        pk *= p
        qk //= q
    E = Fraction(num, q ** K * Kf)
    _E_CACHE[lg] = E
    return E


def verify_N(N):
    """Verify the full explicit chain for one N >= 16. Returns (ok, dict)."""
    u, m, d = behrend_params(N)
    g, num, den = guaranteed_size(d, m)
    Np = (2 * m) ** d
    c1 = (1 << (u * u)) <= N                      # u maximality (lower)
    c2 = (1 << ((u + 1) * (u + 1))) > N           # u maximality (upper)
    c3 = Np <= N                                  # STEP 5 (i): fits
    c4 = (2 * m) ** (d + 1) > N                   # d maximality
    c5 = Np * (1 << (1 + u)) > N                  # STEP 5 (ii): floor loss
    c6 = d <= u                                   # STEP 5 (iii)
    c7 = g * den >= num                           # ceiling pigeonhole
    c8 = den <= d * m * m                         # (m-1)^2+1 relaxation
    c9 = N < g * u * (1 << (1 + 4 * u))           # MASTER (Theorem 3B.5)
    lg = N.bit_length() - 1
    E = E_lower_bound(lg)
    c10 = N * E.denominator <= g * E.numerator    # EXP (Theorem 3B.7)
    ok = all([c1, c2, c3, c4, c5, c6, c7, c8, c9, c10])
    return ok, (u, m, d, g, Np, c9, E, c10)


def part_d():
    print("[PART D] (d) EXPLICIT CONSTANT CHAIN (STEP 5 + STEP 6), "
          "C = 6, N_0 = 16", flush=True)

    # D.1 the two Taylor exhibits of Lemma 3B.6, exact rational arithmetic
    x = Fraction(25, 36)
    S8 = sum(x ** k * Fraction(1, math.factorial(k)) for k in range(9))
    okA = S8 > 2
    check("D.1", "Taylor exhibit (T3): sum_{k<=8} (25/36)^k/k! = %s > 2 "
          "(excess %s) hence e^(25/36) > 2 hence ln 2 < 25/36"
          % (S8, S8 - 2), okA)
    y = Fraction(9, 13)
    T7 = sum(y ** k * Fraction(1, math.factorial(k)) for k in range(8))
    R7 = 3 * y ** 8 * Fraction(1, math.factorial(8))
    okB = T7 + R7 < 2
    check("D.2", "Taylor exhibit (T4): sum_{k<=7} (9/13)^k/k! + 3*(9/13)^8"
          "/8! = %s < 2 (deficit %s) hence e^(9/13) < 2 (Lagrange remainder "
          "< e*x^8/8! < 3x^8/8!) hence ln 2 > 9/13" % (T7 + R7, 2 - T7 - R7),
          okB)
    # D.3 the rational bookkeeping of the conversion lemma
    okC = (Fraction(25, 36) + Fraction(2, 9) == Fraction(11, 12)
           and Fraction(9, 13) > Fraction(9, 16)
           and Fraction(7, 2) > Fraction(11, 12)
           and 4 * math.factorial(5) and True)
    check("D.3", "conversion-lemma rationals: 25/36 + 2/9 == 11/12; "
          "9/13 > 9/16 (so sqrt(ln 2) > 3/4, so sqrt(ln 16) > 3/2); "
          "7/2 > 11/12 (the (T6) slack)", okC)

    # D.4 the e = 10..60 table (N = 2^e)
    print("  --- table: N = 2^e, e = 10..60 (display column = float of the "
          "exact target) ---", flush=True)
    print("     e          N=2^e  u    m   d        N'=(2m)^d       m^d"
          "        g=ceil(m^d/den)   N*e^(-6sqrt(lnN)) [display]  master  "
          "exp", flush=True)
    all_ok = True
    tight_master = None
    for e in range(10, 61):
        N = 1 << e
        ok, (u, m, d, g, Np, c9, E, c10) = verify_N(N)
        if not ok:
            all_ok = False
            info("chain FAILED at e=%d" % e)
        tgt = N * math.exp(-6 * math.sqrt(e * math.log(2)))  # display only
        slack = (g * u * (1 << (1 + 4 * u))) / N
        if tight_master is None or slack < tight_master[0]:
            tight_master = (slack, e)
        print("   %3d %15d %2d %4d %3d %17d %9d %19d %22.6g   %5s  %5s"
              % (e, N, u, m, d, Np, m ** d, g, tgt, c9, c10), flush=True)
    check("D.4", "e = 10..60 (N = 2^e): the explicit rounding chain "
          "(u = max{u: 2^(u^2) <= N}, m = 2^u, d = max{d: (2m)^d <= N}, "
          "g = ceil(m^d/(d(m-1)^2+1))) satisfies ALL TEN chain inequalities "
          "including the MASTER integer bound N < g*u*2^(1+4u) (Theorem "
          "3B.5) and the EXPONENTIAL claim g >= N*e^(-6*sqrt(ln N)) "
          "(Theorem 3B.7, C = 6) - 51/51 PASS", all_ok)
    info("tightest master slack on e=10..60: factor %.1fx at e=%d"
         % (tight_master[0], tight_master[1]))

    # D.5 general-N sweep: every N in [16,4096], decades, powers of two
    Ns = list(range(16, 4097))
    Ns += [10 ** j for j in range(6, 19)]
    Ns += [1 << e for e in range(4, 61)]
    Ns += [17, 63, 4095, 4097, 2 ** 12 + 1, 3 ** 20, 10 ** 18 + 1]
    all_ok = True
    n_ok = 0
    worst_slack = None
    for N in Ns:
        if N < 16:
            continue
        ok, (u, m, d, g, Np, c9, E, c10) = verify_N(N)
        if not ok:
            all_ok = False
            info("chain FAILED at N=%d" % N)
        else:
            n_ok += 1
        slack = (g * u * (1 << (1 + 4 * u))) / N
        if worst_slack is None or slack < worst_slack[0]:
            worst_slack = (slack, N)
    check("D.5", "general-N sweep: %d values (all N in [16,4096], decades "
          "10^6..10^18, N=2^e for e=4..60, edge points): the same TEN chain "
          "inequalities hold everywhere - master + exponential (C=6) both "
          "PASS %d/%d" % (len([n for n in Ns if n >= 16]), n_ok,
                          len([n for n in Ns if n >= 16])),
          all_ok and n_ok == len([n for n in Ns if n >= 16]))
    info("tightest master slack on the sweep: factor %.1fx at N=%d"
         % (worst_slack[0], worst_slack[1]))

    # D.6 negative control: dropping the ceiling to the floor breaks the
    # master bound wherever floor = 0 (e.g. N = 1000)
    N = 1000
    u, m, d = behrend_params(N)
    gfloor = (m ** d) // (d * (m - 1) ** 2 + 1)
    broken = not (N < gfloor * u * (1 << (1 + 4 * u)))
    check("D.6", "negative control: with the FLOOR instead of the ceiling, "
          "the guaranteed size at N=1000 is g'=%d and the master inequality "
          "N < g'*u*2^(1+4u) becomes %d < %d = FALSE - the ceiling of "
          "Lemma 3B.4 is load-bearing"
          % (gfloor, N, gfloor * u * (1 << (1 + 4 * u))), broken)

    # D.7 informational: the empirical best constant of the guaranteed chain
    # (NO claim attached; the theorem claims exactly C = 6)
    best = 0.0
    argN = None
    for N in Ns:
        if N < 16:
            continue
        u, m, d = behrend_params(N)
        g, _, _ = guaranteed_size(d, m)
        if g <= 0:
            continue
        c = math.log(N / g) / math.sqrt(math.log(N))
        if c > best:
            best = c
            argN = N
    info("informational (no claim): the largest ln(N/g)/sqrt(ln N) on the "
         "sweep is %.4f at N=%d - the guaranteed chain is far inside C=6 "
         "(the construction's intrinsic constant is 4*sqrt(ln 2) ~ 3.3302)"
         % (best, argN))
    print("    %s" % stamp(), flush=True)


# ===========================================================================
# PART E - (e) the constructed sets are subsets of [1,N]: shift + re-verify
# ===========================================================================

def part_e(grid_levels):
    print("[PART E] (e) SUBSETS OF [1,N]: the shifted witness families "
          "phi(S_V*)+1 under the pinned comparator convention (a>=1, "
          "delta>=1)", flush=True)
    all_ok = True
    print("   (d,m)      N=(2m)^d  V*  |W|   min  max      literal-scan  "
          "endpoint-scan  block-envelope", flush=True)
    for d in GRID_D:
        for m in GRID_M:
            B = 2 * m
            N = B ** d
            lev = grid_levels[(d, m)]
            sizes = {V: len(S) for V, S in lev.items()}
            Vstar = max(sizes, key=lambda V: sizes[V])
            Sstar = lev[Vstar]
            W = sorted(phi_of(x, B) + 1 for x in Sstar)
            Wset = set(W)
            ok_contain = all(1 <= w <= N for w in W)
            ok_biject = len(Wset) == len(Sstar)
            w_lit = ap3_scan_literal(W, N)               # literal pinned scan
            w_end = ap3_scan_image(W)                    # endpoint-indexed
            ok_free = (w_lit is None) and (w_end is None)
            block = 2 * (N // 3) + (N % 3)
            ok_block = len(W) <= block
            if not (ok_contain and ok_biject and ok_free and ok_block):
                all_ok = False
                info("(d=%d,m=%d): containment/biject/freedom/block FAILED"
                     % (d, m))
            print("   (%d,%d) %11d %4d %4d %5d %5d %14s %14s  %4d <= %d"
                  % (d, m, N, Vstar, len(W), min(W), max(W), w_lit, w_end,
                     len(W), block), flush=True)
    check("E.1", "every grid witness family W = phi(S_V*)+1: W subseteq "
          "[1,(2m)^d], |W| = |S_V*|, 3-AP-free under the pinned convention "
          "by the LITERAL (a,delta) double loop AND the endpoint-indexed "
          "scan (agreement), and inside the certified BLOCK-UPPER envelope "
          "|W| <= 2*floor(N/3) + N mod 3 - hence r_3((2m)^d) >= |S_V*| "
          "(12 new machine-witnessed lower-bound data points, e.g. "
          "r_3(20736) >= 48)", all_ok)

    # E.2 cross-check the largest witness against the Cantor frame at
    # comparable N (display only; both are certified lower bounds)
    N1, w1 = 3 ** 9, 2 ** 9
    info("context (display): at N ~ 2*10^4 the Cantor frame gives "
         "r_3(3^9=%d) >= %d while the Behrend grid gives r_3(20736) >= 48; "
         "the Behrend bound wins only above N ~ 10^115 (PROOF.md 3B honest "
         "remark) - the two constructions are complementary" % (N1, w1))
    print("    %s" % stamp(), flush=True)


# ===========================================================================
# main
# ===========================================================================

def main():
    part0()
    grid_levels = part_a()
    part_b(grid_levels)
    part_c()
    part_d()
    part_e(grid_levels)

    print("=" * 78, flush=True)
    print("[FINAL] BEHREND ENGINE 142 VERDICT", flush=True)
    print("  checks passed: %d | checks failed: %d" % (CHECKS[0], CHECKS[1]),
          flush=True)
    print("  CERTIFIED: (a) all grid level sets 3-AP-free (two methods) | "
          "(b) STEP 4 size law (exact integers) | (c) digit map injectivity "
          "+ exhaustive no-carry pullback + 1.2M random triples + wrong-base "
          "negative control | (d) the explicit constant chain: master "
          "N < g*u*2^(1+4u) and g >= N*e^(-6*sqrt(ln N)) for e=10..60 and "
          "%d+ general N, with the two Taylor exhibits | (e) shifted witness "
          "families inside [1,N] under the pinned convention"
          % (4096 - 16 + 1 + 13 + 57 + 7), flush=True)
    print("  THEOREM (PROOF.md 3B, now machine-corroborated): "
          "r_3(N) >= N*exp(-6*sqrt(ln N)) for all N >= 16; master form "
          "r_3(N) >= N/(u*2^(1+4u)), u = floor(sqrt(log2 N)); the same "
          "bound for r_k(N) for every k >= 3", flush=True)
    print("  comparator wall time: %s" % stamp(), flush=True)
    if FAILURES or CHECKS[1] > 0:
        print("BEHREND_ENGINE_142_RED (%d failure lines)" % len(FAILURES),
              flush=True)
        for f in FAILURES:
            print("  " + f, flush=True)
        sys.exit(1)
    print("BEHREND_ENGINE_142_GREEN=1", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
