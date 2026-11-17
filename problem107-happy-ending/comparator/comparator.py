#!/usr/bin/env python3
"""comparator.py — DeepMind-style DIRECT comparator for Erdos #107 (Happy Ending).

The FunSearch/AlphaCode grading pattern, applied to the campaign's #107 package:
  challenge.json  — frozen statement, PINNED conventions, parameter space, acceptance criteria
  solution.json   — the campaign's claimed results, each with an EXACT honest label
  comparator.py   — THIS FILE: the independent evaluator. It re-derives every
                    machine-checkable claim from scratch. It does NOT import engine107,
                    does NOT trust any prior receipt, and uses NO floats in ANY
                    geometric predicate: exact integer cross products (PROOF.md's
                    orient convention), exact Fractions for slope comparisons, z3
                    (optional) as a third method via LP feasibility.

Parts:
  A  f(3)=3 both directions on the finite universe (exhaustive grids + convention encoding)
  B  f(4)>=5 : the 4-point interior witness, regenerated + grid census
  C  f(4)<=5 : 10^4 uniform random GP 5-sets + adversarial structured sets + EXHAUSTIVE
               all GP 5-subsets of the 4x4 and 5x5 grids — every one contains convex 4
  D  f(5)>=9 : the five 8-point witnesses regenerated (4 lattice + interleaved cup/cap),
               all C(8,5)=56 subsets swept, two-method checker; PLUS an independent
               re-derivation sweep (4-column x 2-point subsets of the 5x5 grid); PLUS
               9-point GP extensions must contain convex 5 (corroborates cited f(5)=9)
  E  checker self-agreement: two independent exact convex-position methods must agree
               on EVERY query (global tally + dedicated battery)
  F  Erdos-Szekeres monotone subsequence lemma, finite core: exhaustive over ALL order
               types up to length 8 + tightness witnesses + random corroboration
  G  negative controls: corrupted witnesses, collinear triples, GP-gate rejections,
               positive detection control
  H  cited dichotomy corroboration at (a,b) in {(3,3),(3,4),(4,3),(4,4)} (labeled
               CORROBORATION, not proof)
  I  frontier arithmetic n=3..40 (exact integers)
  Z3 optional third-method lane (LP feasibility vs orientation signs)

Verdict: prints COMPARATOR_107_GREEN=1 and exits 0 iff every gate passes.
"""
import functools
import itertools
import json
import math
import os
import random
import sys
import time
from fractions import Fraction

X, Y = 0, 1
T0 = time.time()
FAILURES = []
GATES = []


def gate(name, ok, detail=""):
    GATES.append((name, ok))
    if not ok:
        FAILURES.append(name + (" :: " + detail if detail else ""))
        print("  !! GATE FAIL: %s %s" % (name, detail))


def sep(title):
    print("=" * 78)
    print(title)


# ----------------------------------------------------------------------------
# EXACT GEOMETRIC PREDICATES (integers only; no floats anywhere in decisions)
# ----------------------------------------------------------------------------

def orient(a, b, c):
    """orient(P,Q,R) := (Q-P) x (R-P)  — the PROOF.md section-0 convention."""
    return (b[X] - a[X]) * (c[Y] - a[Y]) - (b[Y] - a[Y]) * (c[X] - a[X])


def general_position(S):
    """GP = no 3 collinear. Direct C(n,3) orient sweep (independent of engine107's
    gcd-direction-normalization route). Returns (ok, offending_triple)."""
    n = len(S)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if orient(S[i], S[j], S[k]) == 0:
                    return False, (S[i], S[j], S[k])
    return True, None


STATS = {"queries": 0, "disagree": 0, "true": 0, "false": 0}


def convex_position_A(pts):
    """Method A — exact angular tour around the CENTROID.
    Integer direction vectors w_p = n*p - sum(S) (parallel to p - centroid, since
    w_p = n*(p - centroid)); exact angular sort via half-plane + integer cross
    products; the tour is a convex-polygon traversal iff every cyclic consecutive
    triple turns the same nonzero way, with no zero cross between cyclic neighbours
    (same-ray ties and opposite-ray adjacencies both forbid convex position:
    for a set in convex position the centroid is strictly interior, so no vertex
    sits on the centroid, no two vertices share a radial ray, and no hull edge
    passes through the strictly-interior centroid)."""
    n = len(pts)
    if n < 3:
        return False
    if n == 3:
        return orient(pts[0], pts[1], pts[2]) != 0
    sx = sum(p[X] for p in pts)
    sy = sum(p[Y] for p in pts)
    w = [(n * p[X] - sx, n * p[Y] - sy) for p in pts]
    if any(u == (0, 0) for u in w):
        return False  # a point AT the centroid cannot be extreme

    def half(u):
        return 0 if (u[1] > 0 or (u[1] == 0 and u[0] > 0)) else 1

    def angcmp(i, j):
        u, v = w[i], w[j]
        hu, hv = half(u), half(v)
        if hu != hv:
            return -1 if hu < hv else 1
        cr = u[0] * v[1] - u[1] * v[0]
        if cr > 0:
            return -1  # u comes first counter-clockwise
        if cr < 0:
            return 1
        return 0

    order = sorted(range(n), key=functools.cmp_to_key(angcmp))
    for t in range(n):
        u, v = w[order[t]], w[order[(t + 1) % n]]
        if u[0] * v[1] - u[1] * v[0] == 0:
            return False  # same ray (tie) or opposite rays (edge through centroid)
    sgn = 0
    for t in range(n):
        a = pts[order[t]]
        b = pts[order[(t + 1) % n]]
        c = pts[order[(t + 2) % n]]
        o = orient(a, b, c)
        if o == 0:
            return False
        s = 1 if o > 0 else -1
        if sgn == 0:
            sgn = s
        elif s != sgn:
            return False
    return True


def point_in_closed_triangle(a, b, c, p):
    """Exact closed containment via three orientation signs (zeros allowed)."""
    o1 = orient(a, b, p)
    o2 = orient(b, c, p)
    o3 = orient(c, a, p)
    return (o1 >= 0 and o2 >= 0 and o3 >= 0) or (o1 <= 0 and o2 <= 0 and o3 <= 0)


def convex_position_B(pts):
    """Method B — no point in the CLOSED triangle of three others.
    Exact by Caratheodory in R^2 (a point in conv(others) is in the closed triangle
    of <= 3 of them; the <= 2 case collapses onto a triangle edge). n=3 special:
    convex position iff not collinear."""
    n = len(pts)
    if n < 3:
        return False
    if n == 3:
        return orient(pts[0], pts[1], pts[2]) != 0
    for i in range(n):
        p = pts[i]
        rest = pts[:i] + pts[i + 1:]
        for tri in itertools.combinations(rest, 3):
            if point_in_closed_triangle(tri[0], tri[1], tri[2], p):
                return False
    return True


def in_convex_position(pts):
    """The query wrapper: BOTH methods run; agreement tallied globally."""
    a = convex_position_A(pts)
    b = convex_position_B(pts)
    STATS["queries"] += 1
    if a:
        STATS["true"] += 1
    else:
        STATS["false"] += 1
    if a != b:
        STATS["disagree"] += 1
        print("  !! CHECKER DISAGREEMENT A=%s B=%s on %r" % (a, b, pts))
    return a and b


def has_convex_k_subset(S, k):
    """Decisive brute sweep over all C(|S|,k) subsets (early exit on first hit)."""
    for sub in itertools.combinations(S, k):
        if in_convex_position(list(sub)):
            return True, list(sub)
    return False, None


# ----------------------------------------------------------------------------
# generators
# ----------------------------------------------------------------------------

def rand_gp(rng, n, lo=-777, hi=777):
    while True:
        pts = [(rng.randint(lo, hi), rng.randint(lo, hi)) for _ in range(n)]
        if len(set(pts)) != n:
            continue
        ok, _ = general_position(pts)
        if ok:
            return pts


def rand_gp_distinct_x(rng, n, lo=-60, hi=60):
    while True:
        xs = rng.sample(range(lo, hi), n)
        pts = [(x, rng.randint(lo * 12, hi * 12)) for x in xs]
        ok, _ = general_position(pts)
        if ok:
            return pts


def collinear_triple_dict(grid):
    """Precompute collinearity of every triple of a grid point list (dict lookup
    replaces repeated orientation calls in the exhaustive sweeps)."""
    tri = {}
    for i, j, k in itertools.combinations(range(len(grid)), 3):
        tri[frozenset((i, j, k))] = orient(grid[i], grid[j], grid[k]) == 0
    return tri


def gp_subset_by_dict(idxs, tridict):
    for t in itertools.combinations(sorted(idxs), 3):
        if tridict[frozenset(t)]:
            return False
    return True


# ----------------------------------------------------------------------------
# the campaign's witness data (regenerated from receipts107.txt / engine107.py
# formulas — re-verified from scratch below; engine107 itself is NOT imported)
# ----------------------------------------------------------------------------

W4 = [(0, 0), (6, 0), (3, 9), (3, 2)]  # PROOF.md S2(i): 3 hull + (3,2) interior

LATTICE_WITNESSES = [
    [(0, 0), (0, 3), (1, 1), (1, 2), (3, 1), (3, 2), (4, 0), (4, 3)],
    [(0, 0), (0, 4), (1, 1), (1, 3), (2, 1), (2, 3), (3, 0), (3, 4)],
    [(0, 1), (0, 4), (1, 2), (1, 3), (3, 2), (3, 3), (4, 1), (4, 4)],
    [(1, 0), (1, 4), (2, 1), (2, 3), (3, 1), (3, 3), (4, 0), (4, 4)],
]


def interleaved_family(m=4):
    """{(2t, t^2)}_t  U  {(2t+1, -(m-1-t)^2 + 2)}_t  — even-x cup high, odd-x cap low."""
    S = [(2 * t, t * t) for t in range(m)]
    S += [(2 * t + 1, -((m - 1 - t) ** 2) + 2) for t in range(m)]
    return S


GRID4 = [(x, y) for x in range(4) for y in range(4)]
GRID5 = [(x, y) for x in range(5) for y in range(5)]
TRI4 = collinear_triple_dict(GRID4)
TRI5 = collinear_triple_dict(GRID5)


# ----------------------------------------------------------------------------
# PART A — f(3) = 3, both directions, on the finite universe
# ----------------------------------------------------------------------------

def part_A():
    sep("A  f(3)=3 — BOTH DIRECTIONS (finite universe; PROOF.md S1 is the R^2 proof)")
    ok_all = True
    # (i) lower: a 2-point GP set with no convex 3-gon
    two = [(0, 0), (1, 2)]
    gp2, _ = general_position(two)
    has3, _ = has_convex_k_subset(two, 3)
    print("  2-point witness GP=%s  no-convex-3=%s (C(2,3)=0 subsets — vacuous sweep)"
          % (gp2, not has3))
    ok_all &= gp2 and not has3
    # (ii) upper: every GP 3-subset of the grids is in convex position
    for gname, grid, trid in (("4x4", GRID4, TRI4), ("5x5", GRID5, TRI5)):
        nGP = nBad = nColl = 0
        for tri in itertools.combinations(range(len(grid)), 3):
            if trid[frozenset(tri)]:
                nColl += 1
                continue
            nGP += 1
            if not in_convex_position([grid[i] for i in tri]):
                nBad += 1
        print("  grid %s: GP triples=%d  collinear triples=%d  GP-triples NOT in "
              "convex position=%d" % (gname, nGP, nColl, nBad))
        ok_all &= nGP > 0 and nBad == 0 and nColl > 0
    # random triples corroboration
    rng = random.Random(10701)
    bad = 0
    for _ in range(3000):
        t = rand_gp(rng, 3)
        if not in_convex_position(t):
            bad += 1
    print("  random GP triples: 3000 checked, non-convex=%d" % bad)
    ok_all &= bad == 0
    # (iii) the CONVENTION is encoded: collinear triples exist, fail GP, fail convexity
    conv_ok = True
    for col in ([(0, 0), (1, 1), (2, 2)], [(0, 0), (5, 0), (9, 0)],
                [(3, 0), (3, 4), (3, 9)], [(0, 0), (2, 6), (3, 9)],
                [(-4, 6), (0, -1), (4, -8)]):
        gp, trip = general_position(col)
        cv = in_convex_position(col)
        conv_ok &= (not gp) and (trip is not None) and (not cv)
        print("  collinear triple %-34s GP-gate=REJECTED (triple %s) convex-position=%s"
              % (col, trip is not None, cv))
    ok_all &= conv_ok
    gate("A-f(3)=3", ok_all)
    if ok_all:
        print("CMP107-A f(3)=3 BOTH-DIRECTIONS GREEN")


# ----------------------------------------------------------------------------
# PART B — f(4) >= 5 (the 4-point interior witness, regenerated)
# ----------------------------------------------------------------------------

def part_B():
    sep("B  f(4)>=5 — THE 4-POINT INTERIOR WITNESS (regenerated, two-method verified)")
    ok_all = True
    gp, trip = general_position(W4)
    ok_all &= gp
    print("  W4 = %s" % (W4,))
    print("  GP check: all C(4,3)=4 triples non-collinear -> GP=%s" % gp)
    has4, found = has_convex_k_subset(W4, 4)
    ok_all &= not has4
    print("  unique 4-subset in convex position: %s (must be False)" % has4)
    # identify the interior point by exact closed-triangle containment
    interior = [p for p in W4
                if any(point_in_closed_triangle(a, b, c, p)
                       for a, b, c in itertools.combinations([q for q in W4 if q != p], 3))]
    print("  interior point(s) by exact containment: %s (expected [(3, 2)])" % interior)
    ok_all &= interior == [(3, 2)]
    # grid census: GP 4-subsets NOT in convex position exist in both grids
    for gname, grid, trid in (("4x4", GRID4, TRI4), ("5x5", GRID5, TRI5)):
        nGP = nNC = 0
        for quad in itertools.combinations(range(len(grid)), 4):
            if not gp_subset_by_dict(quad, trid):
                continue
            nGP += 1
            if not in_convex_position([grid[i] for i in quad]):
                nNC += 1
        print("  grid %s: GP 4-subsets=%d  of which NOT in convex position=%d "
              "(3 hull + interior sets exist)" % (gname, nGP, nNC))
        ok_all &= nGP > 0 and nNC > 0
    gate("B-f(4)>=5", ok_all)
    if ok_all:
        print("CMP107-B f(4)>=5 WITNESS GREEN")


# ----------------------------------------------------------------------------
# PART C — f(4) <= 5 (random + adversarial + EXHAUSTIVE grid sweeps)
# ----------------------------------------------------------------------------

def adversarial_five(rng):
    mode = rng.randrange(4)
    if mode == 0:  # near-collinear jittered line
        a, b = rng.randint(-3, 3), rng.randint(-2, 2)
        xs = rng.sample(range(-40, 40), 5)
        pts = [(x, a + b * x + rng.randint(-2, 2)) for x in xs]
    elif mode == 1:  # shallow parabola arc
        k = rng.choice([40, 60, 100, 150])
        xs = rng.sample(range(-30, 30), 5)
        pts = [(x, (x * x) // k + rng.randint(-1, 1)) for x in xs]
    elif mode == 2:  # two tight clusters (forces the interior-pair mechanism)
        c1 = (rng.randint(-50, 50), rng.randint(-50, 50))
        c2 = (rng.randint(-50, 50), rng.randint(-50, 50))
        pts = [(c1[0] + rng.randint(-2, 2), c1[1] + rng.randint(-2, 2)) for _ in range(2)]
        pts += [(c2[0] + rng.randint(-2, 2), c2[1] + rng.randint(-2, 2)) for _ in range(3)]
    else:  # near-duplicate pairs
        base = [(rng.randint(-50, 50), rng.randint(-50, 50)) for _ in range(3)]
        pts = list(base)
        pts.append((base[0][0] + rng.choice([-1, 1]), base[0][1]))
        pts.append((base[1][0], base[1][1] + rng.choice([-1, 1])))
    if len(set(pts)) != 5:
        return None
    ok, _ = general_position(pts)
    return pts if ok else None


def part_C():
    sep("C  f(4)<=5 — EVERY 5-POINT GP SET CONTAINS A CONVEX 4-SUBSET (sweeps)")
    ok_all = True
    # (i) 10^4 uniform random GP 5-sets
    rng = random.Random(20260207)
    fails = 0
    for _ in range(10 ** 4):
        pts = rand_gp(rng, 5)
        has, _ = has_convex_k_subset(pts, 4)
        if not has:
            fails += 1
            print("  COUNTEREXAMPLE:", pts)
    print("  uniform random sweep: 10^4 GP 5-sets, failures=%d (zero required)" % fails)
    ok_all &= fails == 0
    # (ii) 2500 adversarial structured GP 5-sets
    rng2 = random.Random(10702)
    made = fails2 = 0
    while made < 2500:
        pts = adversarial_five(rng2)
        if pts is None:
            continue
        made += 1
        has, _ = has_convex_k_subset(pts, 4)
        if not has:
            fails2 += 1
            print("  ADVERSARIAL COUNTEREXAMPLE:", pts)
    print("  adversarial structured sweep (near-collinear/arc/cluster/near-dup): "
          "%d GP 5-sets, failures=%d" % (made, fails2))
    ok_all &= fails2 == 0
    # (iii) EXHAUSTIVE: all GP 5-subsets of the 4x4 and 5x5 grids
    for gname, grid, trid in (("4x4", GRID4, TRI4), ("5x5", GRID5, TRI5)):
        nGP = nBad = 0
        for quint in itertools.combinations(range(len(grid)), 5):
            if not gp_subset_by_dict(quint, trid):
                continue
            nGP += 1
            has, _ = has_convex_k_subset([grid[i] for i in quint], 4)
            if not has:
                nBad += 1
                print("  GRID COUNTEREXAMPLE:", [grid[i] for i in quint])
        print("  EXHAUSTIVE grid %s: GP 5-subsets=%d (non-vacuous), without convex "
              "4-subset=%d" % (gname, nGP, nBad))
        ok_all &= nGP > 0 and nBad == 0
    gate("C-f(4)<=5", ok_all)
    if ok_all:
        print("CMP107-C f(4)<=5 SWEEP GREEN")


# ----------------------------------------------------------------------------
# PART D — f(5) >= 9 (five 8-point witnesses + re-derivation + 9-pt extensions)
# ----------------------------------------------------------------------------

def part_D():
    sep("D  f(5)>=9 — 8-POINT NO-CONVEX-5 WITNESSES (regenerated + re-derived)")
    ok_all = True
    witnesses = [("lattice-%d" % (i + 1), w) for i, w in enumerate(LATTICE_WITNESSES)]
    witnesses.append(("interleaved-cup-cap", interleaved_family(4)))
    # pairwise distinctness
    sigs = {tuple(sorted(w)) for _, w in witnesses}
    print("  distinct witnesses supplied: %d (>=3 required)" % len(sigs))
    ok_all &= len(sigs) >= 3
    for name, w in witnesses:
        gp, trip = general_position(w)
        has5, found = has_convex_k_subset(w, 5)
        ok_all &= gp and not has5
        print("  %-20s GP=%s  C(8,5)=56 subsets swept, convex 5-gons found=%s"
              % (name, gp, has5))
    # independent re-derivation: ALL 4-column x 2-point subsets of the 5x5 grid
    sep2 = time.time()
    found_sets = set()
    cand = gp_count = 0
    for colchoice in itertools.combinations(range(5), 4):
        for ypairs in itertools.product(itertools.combinations(range(5), 2), repeat=4):
            idx_of = {xy: i for i, xy in enumerate(GRID5)}
            pts = []
            for c, yp in zip(colchoice, ypairs):
                pts.append((c, yp[0]))
                pts.append((c, yp[1]))
            cand += 1
            idxs = [idx_of[p] for p in pts]
            if not gp_subset_by_dict(idxs, TRI5):
                continue
            gp_count += 1
            has, _ = has_convex_k_subset(pts, 5)
            if not has:
                found_sets.add(tuple(sorted(pts)))
    known = {tuple(sorted(w)) for w in LATTICE_WITNESSES}
    print("  re-derivation sweep: %d structured candidates, GP=%d, no-convex-5 "
          "witnesses found=%d  [%.1fs]" % (cand, gp_count, len(found_sets), time.time() - sep2))
    print("  the four known lattice witnesses rediscovered: %s" % (known <= found_sets))
    for t in sorted(found_sets):
        print("    witness: %s" % (list(t),))
    ok_all &= len(found_sets) >= 3 and known <= found_sets
    # full two-method verification of every rediscovered witness (56 subsets each)
    for t in sorted(found_sets):
        gp, _ = general_position(list(t))
        has5, _ = has_convex_k_subset(list(t), 5)
        ok_all &= gp and not has5
    print("  all rediscovered witnesses re-verified two-method: %s" % ok_all)
    # 9-point GP extensions must contain a convex 5-subset (f(5)<=9 corroboration)
    ext_cands = [(100, 0), (0, 100), (100, 100), (-50, 37), (63, -11), (-7, -90)]
    ext_ok = ext_done = 0
    for name, w in witnesses:
        for c in ext_cands:
            ext = w + [c]
            gp, _ = general_position(ext)
            if not gp:
                continue
            ext_done += 1
            has, _ = has_convex_k_subset(ext, 5)
            if has:
                ext_ok += 1
            else:
                print("  !! 9-point extension WITHOUT convex 5:", ext)
            break  # one GP extension per witness is enough for the corroboration
    print("  9-point GP extensions of the 5 witnesses: %d built, all contain convex "
          "5-subset=%s (corroborates cited f(5)=9 on these instances)"
          % (ext_done, ext_ok == ext_done and ext_done == 5))
    ok_all &= ext_ok == ext_done == 5
    gate("D-f(5)>=9", ok_all)
    if ok_all:
        print("CMP107-D f(5)>=9 WITNESSES GREEN")


# ----------------------------------------------------------------------------
# PART E — checker self-agreement battery (global tally printed)
# ----------------------------------------------------------------------------

def part_E():
    sep("E  CHECKER SELF-AGREEMENT — two independent exact methods on every query")
    rng = random.Random(10703)
    # dedicated battery: all 3/4/5-subsets of every witness + random sets' subsets
    for name, w in [("lattice-%d" % (i + 1), x) for i, x in enumerate(LATTICE_WITNESSES)] \
            + [("interleaved", interleaved_family(4))]:
        for k in (3, 4, 5):
            for sub in itertools.combinations(w, k):
                in_convex_position(list(sub))
    for _ in range(400):
        n = rng.randint(6, 8)
        S = rand_gp(rng, n)
        idxs = list(range(n))
        for _ in range(40):
            k = rng.randint(3, n)
            sub = [S[i] for i in sorted(rng.sample(idxs, k))]
            in_convex_position(sub)
    # degenerate + positive controls through the same wrapper
    in_convex_position([(0, 0), (1, 1), (2, 2)])
    in_convex_position([(0, 0), (5, 0), (9, 0)])
    in_convex_position([(0, 0), (1, 0), (2, 0), (5, 7)])
    in_convex_position([(0, 0), (2, 0), (4, 0), (1, 5), (3, -4)])
    pent = [(0, 0), (4, 1), (5, 4), (2, 6), (-1, 3)]
    pos = in_convex_position(pent)
    print("  positive control pentagon %s in convex position: %s" % (pent, pos))
    print("  global tally: queries=%d  verdict-True=%d  verdict-False=%d  "
          "A/B disagreements=%d" % (STATS["queries"], STATS["true"], STATS["false"],
                                   STATS["disagree"]))
    gate("E-checker-agreement", STATS["disagree"] == 0 and STATS["queries"] > 10000
         and STATS["true"] > 1000 and STATS["false"] > 1000 and pos)
    if STATS["disagree"] == 0:
        print("CMP107-E CHECKER-AGREEMENT GREEN")


# ----------------------------------------------------------------------------
# PART F — Erdos-Szekeres monotone subsequence lemma, finite core
# ----------------------------------------------------------------------------

def lis_lds(seq):
    n = len(seq)
    inc = [1] * n
    dec = [1] * n
    for i in range(n):
        for j in range(i):
            if seq[j] < seq[i]:
                if inc[j] + 1 > inc[i]:
                    inc[i] = inc[j] + 1
            elif seq[j] > seq[i]:
                if dec[j] + 1 > dec[i]:
                    dec[i] = dec[j] + 1
    return (max(inc) if n else 0), (max(dec) if n else 0)


def part_F():
    sep("F  MONOTONE SUBSEQUENCE LEMMA — finite core (order types <= 8, exhaustive)")
    ok_all = True
    pairs = []
    for a in range(2, 10):
        for b in range(2, 10):
            if (a - 1) * (b - 1) + 1 <= 8:
                pairs.append((a, b))
    print("  (a,b) pairs with (a-1)(b-1)+1 <= 8: %d pairs" % len(pairs))
    checked = 0
    for a, b in pairs:
        L = (a - 1) * (b - 1) + 1
        bad = 0
        for perm in itertools.permutations(range(1, L + 1)):
            checked += 1
            li, ld = lis_lds(perm)
            if not (li >= a or ld >= b):
                bad += 1
                print("  !! COUNTEREXAMPLE ORDER TYPE:", perm, (a, b))
        # tightness: the block construction of length (a-1)(b-1) has neither
        m = b - 1
        blocks = []
        for j in range(a - 1):
            blocks.extend(range((j + 1) * m, j * m, -1))
        li2, ld2 = lis_lds(blocks)
        tight = (li2 <= a - 1 and ld2 <= b - 1 and len(blocks) == (a - 1) * (b - 1))
        if not tight:
            print("  !! TIGHTNESS WITNESS FAILED at (a,b)=(%d,%d)" % (a, b))
        ok_all &= bad == 0 and tight
        print("  (a,b)=(%d,%d) L=%d: all %d order types have a-increase or b-decrease; "
              "tightness witness len=%d lis=%d lds=%d" %
              (a, b, L, math.factorial(L), len(blocks), li2, ld2))
    # random distinct-value sequences, all applicable (a,b)
    rng = random.Random(10704)
    rbad = rchk = 0
    for _ in range(3000):
        L = rng.randint(2, 8)
        seq = tuple(rng.sample(range(1, 9), L))
        li, ld = lis_lds(seq)
        for a, b in pairs:
            if L >= (a - 1) * (b - 1) + 1:
                rchk += 1
                if not (li >= a or ld >= b):
                    rbad += 1
    print("  random distinct-value sequences: 3000 sequences, %d applicable (a,b) "
          "checks, violations=%d" % (rchk, rbad))
    ok_all &= rbad == 0 and checked > 100000
    print("  exhaustive order types checked in total: %d" % checked)
    gate("F-monotone-core", ok_all)
    if ok_all:
        print("CMP107-F MONOTONE-SUBSEQUENCE FINITE-CORE GREEN")


# ----------------------------------------------------------------------------
# PART G — negative controls
# ----------------------------------------------------------------------------

def part_G():
    sep("G  NEGATIVE CONTROLS — corruption, collinearity, gate rejection, detection")
    ok_all = True
    # (i) corrupted witnesses: one point moved. Three batteries:
    #     unit moves (local-robustness measurement, informational),
    #     near moves (|dx|,|dy| <= 3), far moves (large displacements).
    all_w = [("interleaved", interleaved_family(4))] + \
        [("lattice-%d" % (i + 1), x) for i, x in enumerate(LATTICE_WITNESSES)]
    unit_moves = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    near_moves = [(dx, dy) for dx in range(-3, 4) for dy in range(-3, 4)
                  if (dx, dy) != (0, 0)]
    far_moves = [(7, 5), (-7, 5), (7, -5), (-7, -5), (9, 0), (0, 9), (-9, 0),
                 (0, -9), (20, 13), (-20, 13), (20, -13), (-20, -13)]

    def corrupt(witnesses, moves):
        tot = found = 0
        per_witness = {}
        for name, w in witnesses:
            pw = 0
            for i in range(8):
                for dx, dy in moves:
                    cw = list(w)
                    cw[i] = (cw[i][0] + dx, cw[i][1] + dy)
                    gp, _ = general_position(cw)
                    if not gp:
                        continue
                    tot += 1
                    pw += 1
                    has, _ = has_convex_k_subset(cw, 5)
                    if has:
                        found += 1
            per_witness[name] = pw
        return tot, found, per_witness

    u_tot, u_found, _ = corrupt(all_w[:3], unit_moves)
    print("  unit moves (3 witnesses x 8 pts x 4 moves): GP-preserving=%d, convex-5 "
          "induced=%d (%.1f%%) — MEASUREMENT: the witnesses are locally robust; "
          "single-unit corruption often preserves the no-convex-5 property"
          % (u_tot, u_found, 100 * u_found / u_tot if u_tot else 0))
    n_tot, n_found, n_pw = corrupt(all_w, near_moves)
    f_tot, f_found, f_pw = corrupt(all_w, far_moves)
    c_tot, c_found = n_tot + f_tot, n_found + f_found
    print("  near moves (5 witnesses x 8 pts x 48 moves): GP-preserving=%d, convex-5 "
          "induced=%d (%.1f%%)" % (n_tot, n_found, 100 * n_found / n_tot if n_tot else 0))
    print("  far moves (5 witnesses x 8 pts x 12 moves): GP-preserving=%d, convex-5 "
          "induced=%d (%.1f%%)" % (f_tot, f_found, 100 * f_found / f_tot if f_tot else 0))
    print("  combined corruption battery: GP-preserving=%d, convex-5 induced=%d "
          "(%.1f%%); every witness individually corrupted into a convex-5 carrier: %s"
          % (c_tot, c_found, 100 * c_found / c_tot if c_tot else 0,
             all(v > 0 for v in list(n_pw.values()) + list(f_pw.values()))))
    ok_all &= (n_tot >= 400 and n_found >= 0.5 * n_tot
               and f_tot >= 300 and f_found >= 0.65 * f_tot
               and c_found >= 0.6 * c_tot
               and all(v > 0 for v in list(n_pw.values()) + list(f_pw.values())))
    # (ii) collinear triples rejected by the GP gate, with the triple identified
    coll_ok = True
    for col in ([(0, 0), (1, 2), (2, 4)], [(0, 0), (0, 5), (0, 9)],
                [(3, 0), (3, 4), (3, 9)], [(0, 0), (3, 1), (6, 2)],
                [(-6, -4), (0, 0), (9, 6)], [(0, 0), (4, 6), (6, 9)]):
        gp, trip = general_position(col)
        coll_ok &= (not gp) and trip is not None
    print("  collinear triple battery (6 slopes): all rejected by GP gate with the "
          "offending triple identified: %s" % coll_ok)
    ok_all &= coll_ok
    # (iii) a 5-set with an embedded collinear triple is rejected by the sweep gate
    sneaky = [(0, 0), (2, 4), (4, 8), (1, 7), (6, 1)]
    gp, trip = general_position(sneaky)
    print("  non-GP 5-set %s: GP gate=%s (embedded triple %s)" % (sneaky, gp, trip))
    ok_all &= not gp
    # (iv) positive detection control: known convex sets are found
    pent = [(0, 0), (4, 1), (5, 4), (2, 6), (-1, 3)]
    rng = random.Random(10705)
    det = 0
    for _ in range(50):
        S = rand_gp(rng, 8)
        has, _ = has_convex_k_subset(S, 5)
        det += 1 if has else 0
    print("  positive detection: pentagon in convex position=%s; random 8-point GP "
          "sets with a convex 5-subset: %d/50" % (in_convex_position(pent), det))
    ok_all &= in_convex_position(pent) and det == 50
    gate("G-negative-controls", ok_all)
    if ok_all:
        print("CMP107-G NEGATIVE-CONTROLS GREEN")


# ----------------------------------------------------------------------------
# PART H — cited dichotomy corroboration (small parameters, random instances)
# ----------------------------------------------------------------------------

def is_cup(sub):
    s = sorted(sub)
    if len({p[X] for p in s}) != len(s):
        return False
    sl = [Fraction(s[i + 1][Y] - s[i][Y], s[i + 1][X] - s[i][X]) for i in range(len(s) - 1)]
    return all(sl[i] < sl[i + 1] for i in range(len(sl) - 1))


def is_cap(sub):
    s = sorted(sub)
    if len({p[X] for p in s}) != len(s):
        return False
    sl = [Fraction(s[i + 1][Y] - s[i][Y], s[i + 1][X] - s[i][X]) for i in range(len(s) - 1)]
    return all(sl[i] > sl[i + 1] for i in range(len(sl) - 1))


def part_H():
    sep("H  CITED DICHOTOMY CORROBORATION — cup/cap at small (a,b) (NOT a proof)")
    ok_all = True
    rng = random.Random(10706)
    for (a, b) in ((3, 3), (3, 4), (4, 3), (4, 4)):
        N = math.comb(a + b - 4, a - 2) + 1
        bad = 0
        for _ in range(1500):
            S = rand_gp_distinct_x(rng, N)
            hit = any(is_cup(list(c)) for c in itertools.combinations(S, a)) or \
                any(is_cap(list(c)) for c in itertools.combinations(S, b))
            if not hit:
                bad += 1
                print("  !! DICH COUNTEREXAMPLE:", S)
        print("  (a,b)=(%d,%d): N=binom(%d,%d)+1=%d, 1500 random GP distinct-x sets, "
              "missing cup/cap=%d" % (a, b, a + b - 4, a - 2, N, bad))
        ok_all &= bad == 0
    print("  label: CORROBORATION ONLY — the Erdos-Szekeres dichotomy is cited-classical")
    print("  (the naive injective-label route FAILS 263/300, receipts107.txt part D)")
    gate("H-dich-corroboration", ok_all)
    if ok_all:
        print("CMP107-H DICH-CORROBORATION GREEN")


# ----------------------------------------------------------------------------
# PART I — frontier arithmetic n = 3..40 (exact integers)
# ----------------------------------------------------------------------------

def part_I():
    sep("I  FRONTIER ARITHMETIC — 2^{n-2}+1 <= f(n) <= binom(2n-4,n-2)+1, n=3..40")
    ok_all = True
    known = {3: 3, 4: 5, 5: 9, 6: 17}
    for n in range(3, 41):
        lo = 2 ** (n - 2) + 1
        up = math.comb(2 * n - 4, n - 2) + 1
        if not (lo <= up):
            ok_all = False
            print("  !! bound inversion at n=%d" % n)
        if n in known and not (lo <= known[n] <= up):
            ok_all = False
            print("  !! known value outside bounds at n=%d" % n)
        if n <= 12 or n == 40:
            print("  n=%2d  lower=2^{%d}+1=%d  upper=binom(%d,%d)+1=%d  exact=%s  "
                  "log2(upper)/n=%.4f" %
                  (n, n - 2, lo, 2 * n - 4, n - 2, up,
                   known.get(n, "OPEN"), math.log2(up) / n))
    f7 = (2 ** 5 + 1, math.comb(10, 5) + 1)
    print("  f(7) in [33, 253]: certified interval %s" % (f7,))
    ok_all &= f7 == (33, 253)
    print("  exact values: f(3)=3, f(4)=5, f(5)=9, f(6)=17 — each = 2^{n-2}+1 and "
          "each inside the classical bounds: %s" % all(
              2 ** (n - 2) + 1 == v for n, v in known.items()))
    ok_all &= all(2 ** (n - 2) + 1 == v for n, v in known.items())
    print("  the conjecture f(n)=2^{n-2}+1 is OPEN for n>=7; HMPT20 upper "
          "2^{n+O(sqrt(n log n))} is cited (asymptotic, no machine check)")
    gate("I-frontier-arithmetic", ok_all)
    if ok_all:
        print("CMP107-I FRONTIER-ARITHMETIC GREEN")


# ----------------------------------------------------------------------------
# PART Z3 — optional third-method lane (LP feasibility vs orientation signs)
# ----------------------------------------------------------------------------

def part_Z3():
    sep("Z3 OPTIONAL THIRD-METHOD LANE — LP feasibility vs orientation containment")
    try:
        import z3
    except Exception as e:
        print("  z3 not importable (%s) — optional lane SKIPPED (pure-python "
              "comparator remains decisive)" % type(e).__name__)
        print("CMP107-Z3 SKIPPED")
        return
    try:
        print("  z3 version: %s" % z3.get_version_string())
    except Exception:
        pass
    rng = random.Random(10707)
    queries = []
    for w in LATTICE_WITNESSES + [interleaved_family(4)]:
        for p in w:
            rest = [q for q in w if q != p]
            for tri in itertools.combinations(rest, 3):
                queries.append((tri[0], tri[1], tri[2], p))
    queries += [((0, 0), (6, 0), (3, 9), (3, 2)), ((0, 0), (6, 0), (3, 9), (3, 9)),
                ((0, 0), (6, 0), (3, 9), (6, 0)), ((0, 0), (6, 0), (3, 9), (0, 0))]
    # random 6-point GP sets: rich in both inside and outside verdicts
    for _ in range(10):
        S = rand_gp(rng, 6, -60, 60)
        for p in S:
            rest = [q for q in S if q != p]
            for tri in itertools.combinations(rest, 3):
                queries.append((tri[0], tri[1], tri[2], p))
    rng.shuffle(queries)
    queries = queries[:2200]
    mism = ins = out = 0
    for a, b, c, p in queries:
        v_orient = point_in_closed_triangle(a, b, c, p)
        l1, l2, l3 = z3.Reals("l1 l2 l3")
        s = z3.Solver()
        s.add(l1 >= 0, l2 >= 0, l3 >= 0, l1 + l2 + l3 == 1)
        s.add(l1 * a[X] + l2 * b[X] + l3 * c[X] == p[X])
        s.add(l1 * a[Y] + l2 * b[Y] + l3 * c[Y] == p[Y])
        v_lp = (s.check() == z3.sat)
        if v_orient != v_lp:
            mism += 1
            print("  !! Z3 MISMATCH:", (a, b, c, p), v_orient, v_lp)
        if v_orient:
            ins += 1
        else:
            out += 1
    print("  LP-vs-orientation on %d real (point,triangle) queries: inside=%d "
          "outside=%d mismatches=%d" % (len(queries), ins, out, mism))
    ok = mism == 0 and ins > 80 and out > 300
    gate("Z3-third-method", ok)
    if ok:
        print("CMP107-Z3 THIRD-METHOD GREEN")


# ----------------------------------------------------------------------------
# statement integrity + claim wiring (challenge.json <-> solution.json)
# ----------------------------------------------------------------------------

def part_S():
    sep("S  STATEMENT INTEGRITY + CLAIM WIRING (challenge.json <-> solution.json)")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "challenge.json")) as f:
        ch = json.load(f)
    with open(os.path.join(here, "solution.json")) as f:
        so = json.load(f)
    same = (so["statement_frozen_copy"]["corpus_verbatim"]
            == ch["statement_frozen"]["corpus_verbatim"])
    print("  frozen statements identical (byte-for-byte): %s" % same)
    ids = {c["id"] for c in so["claims"]}
    expected = {"CLAIM-S1", "CLAIM-S2", "CLAIM-S2-LOW", "CLAIM-S2-UP", "CLAIM-V5-LOW",
                "CLAIM-V5", "CLAIM-V6", "CLAIM-M", "CLAIM-CC", "CLAIM-DICH",
                "CLAIM-U", "CLAIM-L", "CLAIM-CONJ"}
    print("  solution claim ids complete: %s" % (ids == expected))
    labeled = all(("UNCONDITIONAL" in c["label"]) or ("CITED" in c["label"])
                  or ("MACHINE" in c["label"]) or ("OPEN" in c["label"])
                  for c in so["claims"])
    print("  every claim carries an honest label (unconditional/cited/machine/open): %s"
          % labeled)
    acs = {a["id"] for a in ch["acceptance_criteria"]}
    need = {"AC-A", "AC-B", "AC-C", "AC-D", "AC-E", "AC-F", "AC-G", "AC-H", "AC-I",
            "AC-Z", "AC-S"}
    print("  acceptance criteria complete: %s" % (acs == need))
    gate("S-statement-integrity", same and ids == expected and labeled and acs == need)
    if same:
        print("  frozen statement: %s" % ch["statement_frozen"]["corpus_verbatim"][:96]
              + "...")


# ----------------------------------------------------------------------------

def main():
    print("COMPARATOR 107 — DeepMind-style DIRECT verification (challenge/solution/"
          "evaluator)")
    print("problem: Erdos #107 Happy Ending — f(n) = 2^{n-2}+1 conjecture")
    print("exact integer arithmetic only; no floats in any geometric predicate")
    part_S()
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    part_H()
    part_I()
    part_Z3()
    sep("VERDICT")
    for name, ok in GATES:
        print("  %-28s %s" % (name, "GREEN" if ok else "FAIL"))
    n_fail = sum(0 if ok else 1 for _, ok in GATES)
    if n_fail == 0 and STATS["disagree"] == 0:
        print("COMPARATOR_107_GREEN=1")
        print("total wall %.1fs; checker queries=%d (A/B disagreements=%d)"
              % (time.time() - T0, STATS["queries"], STATS["disagree"]))
        return 0
    print("COMPARATOR_107_GREEN=0 (%d gate failures, %d checker disagreements)"
          % (n_fail, STATS["disagree"]))
    for f in FAILURES:
        print("  FAILED:", f)
    return 1


if __name__ == "__main__":
    sys.exit(main())
