#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine107f5v2.py — W76-107K — THE CORRECTION WAVE — THEOREM F5: f(5) = 9.

W75 state: order-type machinery (chirotope, canonical form, line-arrangement
cells by exact slab sampling) certified n=3..7 (1,2,3,16,135 mirror-identified)
but n=8 stalled at 3313/3315: the cell set of the pair-line arrangement is NOT
an order-type invariant — within one order type's realization space, cells are
born and killed at ARRANGEMENT WALLS (3 pair-lines concurrent; 2 pair-lines
parallel), so single-realization insertion provably misses children.

THE V2 FIX (this file) — the wall-crossing-complete insertion enumeration.
Every generated type carries an exact-rational REALIZATION (the realizability
filter: no junk can enter), and the completeness certificate is the classical
count anchor at EVERY level: 1, 2, 3, 16, 135, 3315, 158817 (n = 3..9),
together with mirror closure.  The finite exhaustive check IS the proof.

Insertion sources per parent type S (n points, arrangement-generic
realization, chi = chirotope):
  S1 CELLS      all cells of the pair-line arrangement of S (slab sampling,
                 exact); sample coordinates realize the child.
  S2 WALL SWEEP every arrangement wall crossed exactly, both sides:
                 - concurrency walls: every triple of pair-lines with 6
                   distinct endpoints (3-matchings of K_n); for every moving
                   point m among the 6, the wall locus (the line through m's
                   partner and the intersection of the other two lines) is
                   intersected with m's chi-cell (the maximal chi-preserving
                   region for m: sign vector vs pair-lines of S\\m); each
                   reachable locus interval is crossed (nudge to a chi-equal
                   past-the-wall configuration, chi verified exactly), and
                   the born cell is grabbed by exact sampling (centroid of
                   the past-wall triangle).
                 - parallel walls: every pair of pair-lines with 4 distinct
                   endpoints; same locus/cell/nudge discipline; the born far
                   between-cells are grabbed at exact far-column samples.
                 Single-point wall crossing is complete for every wall
                 reachable by a single-point motion (m*'s chi-cell is convex,
                 so chi(S with m*) = chi(S) makes the straight motion valid);
                 en-route births belong to their own walls, which are swept
                 in their own right.
  S3 CELL WALK  random in-cell single-point moves (each chi-preserving by the
                 convex-cell argument): a random walk inside the order type's
                 realization space; cells of every visited configuration are
                 grabbed (diff against S1's sign vectors).  Open connected
                 sets are axis-step connected, so in-cell walks reach the
                 whole component in principle; sampling makes it empirical.

Stages:
  --stage ot4|ot5|ot6|ot7|ot8   enumerate + certify (anchor + mirror closure)
  --stage ot8baseline           the W75 realization-diversity-only baseline
                                (cells + perturbations, no sweep) for the
                                root-cause diff report
  --stage outer                 INDEPENDENT CROSS-CHECK: re-enumerate using
                                only OUTER insertions (sample outside
                                conv(parent)); the type set must be unchanged
                                (every (n+1)-type has a hull vertex whose
                                deletion gives an outer insertion)
  --stage f5                    THE F5 CERTIFICATE: every 9-point order type
                                contains 5 in convex position — two
                                independent chirotope methods + cross-validated
                                witnesses; hull census; witness re-verify;
                                random battery.
  --verify                      the full engine contract run.

All arithmetic exact (int / Fraction).  Zero floats.
"""

import sys, os, json, pickle, time, argparse, random, itertools, math
import types as pytypes
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, "engine107f5_cache")
os.makedirs(CACHE, exist_ok=True)
RECEIPTS = os.path.join(HERE, "receipts107f5_v2.txt")

# classical anchor counts (order types of n GP points, UNLABELED, mirrors
# identified): n = 3..9.
OT_MIRROR_IDENTIFIED = {3: 1, 4: 2, 5: 3, 6: 16, 7: 135, 8: 3315, 9: 158817}

_R_LINES = []

def R(line=""):
    print(line, flush=True)
    _R_LINES.append(line)
    with open(RECEIPTS, "w") as f:
        f.write("\n".join(_R_LINES) + "\n")

# ---------------------------------------------------------------------------
# load the banked v1 engine (core geometry/chirotope/canonical functions,
# battle-tested in W75).  Its __main__ is disabled; its receipts are never
# touched (v2 writes receipts107f5_v2.txt only).
# ---------------------------------------------------------------------------

def _load_v1():
    src = open(os.path.join(HERE, "engine107f5.py")).read()
    mod = pytypes.ModuleType("engine107f5_v1")
    mod.__file__ = os.path.join(HERE, "engine107f5.py")
    exec(compile(src.replace('if __name__ == "__main__":', 'if False:'),
                 'engine107f5.py', 'exec'), mod.__dict__)
    return mod

V1 = _load_v1()

orient = V1.orient
sgn = V1.sgn
is_gp = V1.is_gp
chi_of_points = V1.chi_of_points
TRIPLES = V1.TRIPLES
rule_for = V1.rule_for
osign = V1.osign
canonical_key = V1.canonical_key
shear_distinct_x = V1.shear_distinct_x
arrangement_cell_samples = V1.arrangement_cell_samples
hull_monotone = V1.hull_monotone
two_method_agree = V1.two_method_agree
chi_hull_vertices = V1.chi_hull_vertices
chi_convex5_method_a = V1.chi_convex5_method_a
chi_convex5_method_b = V1.chi_convex5_method_b
chi_witness_is_convex_both = V1.chi_witness_is_convex_both

# ---------------------------------------------------------------------------
# v2 machinery: pair lines, sign vectors, walls, sweep, walk.
# ---------------------------------------------------------------------------

def pair_lines_of(pts):
    """(i,j) -> (A,B,C) with A x + B y = C, for all i<j.  Requires no two
    points sharing an x-coordinate (shear first) so B != 0 never needed
    here (we only need the line as such; verticals are fine for signs and
    intersections, but far-column sampling assumes B != 0 — callers shear)."""
    n = len(pts)
    out = {}
    for i in range(n):
        for j in range(i + 1, n):
            A = pts[j][1] - pts[i][1]
            B = pts[i][0] - pts[j][0]
            C = A * pts[i][0] + B * pts[i][1]
            out[(i, j)] = (A, B, C)
    return out

def line_isect(L1, L2):
    (A1, B1, C1), (A2, B2, C2) = L1, L2
    den = A1 * B2 - A2 * B1
    if den == 0:
        return None
    return (Fraction(C1 * B2 - C2 * B1, den), Fraction(A1 * C2 - A2 * C1, den))

def sv_of_point(pts, q, pairs):
    """Sign vector of q: sgn(orient(pts[i], pts[j], q)) over pairs (i<j)."""
    return tuple(sgn(orient(pts[i], pts[j], q)) for (i, j) in pairs)

def chi_insert(base_chi, n, sv, pairs, posmap):
    """Chirotope of the n-point config (base_chi) plus a new point with sign
    vector sv over its pairs, assembled in TRIPLES(n+1) order."""
    sig = dict(zip(pairs, sv))
    tri1 = TRIPLES(n + 1)
    out = []
    for (i, j, k) in tri1:
        if k == n:
            out.append(sig[(i, j)])
        else:
            out.append(base_chi[posmap[(i, j, k)]])
    return tuple(out)

def arrangement_generic(pts):
    """No 3 pair-lines concurrent at a non-configuration point, no 2
    pair-lines parallel (the arrangement is combinatorially full: the slab
    sampler then sees every tope).  NOTE: pair-lines sharing an endpoint
    always meet AT that endpoint — that is not a degeneracy; a genuine
    3-concurrency in a GP configuration can only involve 3 pairwise-disjoint
    pair-lines (6 distinct endpoints)."""
    n = len(pts)
    lines = pair_lines_of(pts)
    prs = sorted(lines.keys())
    m = len(prs)
    lvals = [lines[pr] for pr in prs]
    for a in range(m):
        A1, B1, _ = lvals[a]
        for b in range(a + 1, m):
            if A1 * lvals[b][1] - lvals[b][0] * B1 == 0:
                return False   # parallel
    seen = set()
    for a in range(m):
        i1, j1 = prs[a]
        for b in range(a + 1, m):
            i2, j2 = prs[b]
            if not ({i1, j1}.isdisjoint({i2, j2})):
                continue   # shared endpoint: meets at a config point — fine
            p = line_isect(lvals[a], lvals[b])
            if p is None:
                return False  # disjoint lines are non-parallel by now; safety
            if p in seen:
                return False   # >=3 disjoint pair-lines through one point
            seen.add(p)
    return True

def make_arrangement_generic(pts, chi, rng, tries=500):
    """Type-preserving perturbation until the pair-line arrangement is
    generic (single-point in-cell jitters; chi verified exactly)."""
    if arrangement_generic(pts):
        return [tuple(p) for p in pts], True
    n = len(pts)
    for _ in range(tries):
        m = rng.randrange(n)
        cand = list(pts)
        dx = Fraction(rng.randint(-12, 12), rng.choice([8, 16, 32, 5, 7]))
        dy = Fraction(rng.randint(-12, 12), rng.choice([8, 16, 32, 5, 7]))
        cand[m] = (cand[m][0] + dx, cand[m][1] + dy)
        if not is_gp(cand):
            continue
        if chi_of_points(cand) != chi:
            continue
        if arrangement_generic(cand):
            return [tuple(p) for p in cand], False
    return None, False

def simplify_realization(pts, chi, rng, tries=400):
    """Round-jitter to a modest rational grid, chi-verified — keeps
    denominators tame across levels (exactness never sacrificed)."""
    n = len(pts)
    for D in (16, 64, 256, 1024, 4096):
        for _ in range(max(4, tries // 5)):
            cand = []
            for (x, y) in pts:
                cand.append((Fraction(int(x * D) + rng.randint(-2, 2), D),
                             Fraction(int(y * D) + rng.randint(-2, 2), D)))
            if is_gp(cand) and chi_of_points(cand) == chi:
                return cand
    return [tuple(p) for p in pts]

# --- walls ------------------------------------------------------------------

def all_matchings3(n):
    """All 3-matchings of K_n (triples of disjoint pairs) = the concurrency
    walls (pair-lines sharing an endpoint cannot be part of a 3-line
    concurrency in a GP configuration)."""
    out = []
    for c in itertools.combinations(range(n), 6):
        def match(rem, acc):
            if not rem:
                out.append(tuple(acc))
                return
            first = rem[0]
            for k in rem[1:]:
                match([r for r in rem if r != first and r != k],
                      acc + [(first, k)])
        match(list(c), [])
    return out

def all_pairs4(n):
    """All pairs of disjoint pair-lines (4 distinct endpoints) = the
    parallel walls."""
    out = []
    for c in itertools.combinations(range(n), 4):
        a, b, c1, d = c
        out.append(((a, b), (c1, d)))
        out.append(((a, c1), (b, d)))
        out.append(((a, d), (b, c1)))
    return out

def _locus_intervals(base_pt, direction, other_pts_pairs, lines, extra_crit=()):
    """Critical parameters of the locus P(t) = base + t*direction: crossings
    with the given pair-lines, plus extras.  Returns sorted list."""
    crit = {Fraction(0)}
    crit.update(Fraction(e) for e in extra_crit)
    bx, by = base_pt
    dx, dy = direction
    for pr in other_pts_pairs:
        A, B, C = lines[pr]
        den = A * dx + B * dy
        if den != 0:
            crit.add(Fraction(C - A * bx - B * by, den))
    return sorted(crit)

def sweep_parent(pts, base_chi, current_svs, rng, log=None):
    """THE WALL SWEEP.  pts: arrangement-generic realization (no vertical
    pair-lines — shear first).  Returns dict chi_{n+1} -> realizing coords."""
    n = len(pts)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    posmap = {t: q for q, t in enumerate(TRIPLES(n))}
    lines = pair_lines_of(pts)
    rule = rule_for(n)
    m_sv = {m: tuple(osign(base_chi, rule, i, j, m)
                     for (i, j) in pairs if i != m and j != m)
            for m in range(n)}
    rest_pairs = {m: [(i, j) for (i, j) in pairs if i != m and j != m]
                  for m in range(n)}

    def chi_ok_with(m, q):
        """q is a legal position for point m (same chi-cell)."""
        return sv_of_point(pts, q, rest_pairs[m]) == m_sv[m]

    new = {}
    stats = {"conc_combos": 0, "conc_crossed": 0, "par_combos": 0,
             "par_crossed": 0, "grabs": 0}

    # ---------- concurrency walls ----------
    for prs in all_matchings3(n):
        ends = [x for pr in prs for x in pr]
        for m in ends:
            partner = [x for x in (prs[0] if m in prs[0] else
                                   prs[1] if m in prs[1] else prs[2])
                       if x != m][0]
            others = [pr for pr in prs if m not in pr]
            pm = line_isect(lines[others[0]], lines[others[1]])
            if pm is None:
                continue
            stats["conc_combos"] += 1
            base_pt = pts[partner]
            d = (pm[0] - base_pt[0], pm[1] - base_pt[1])
            ts = _locus_intervals(base_pt, d, rest_pairs[m], lines,
                                  extra_crit=(Fraction(1),))  # 1 = pm itself
            dd = d[0] * d[0] + d[1] * d[1]
            nvec = (Fraction(-d[1], 1) / 1, Fraction(d[0], 1) / 1)
            for a, b in zip(ts, ts[1:]):
                tm = (a + b) / 2
                mstar = (base_pt[0] + tm * d[0], base_pt[1] + tm * d[1])
                if not chi_ok_with(m, mstar):
                    continue
                grabbed_here = set()
                for s in (Fraction(1, 4), Fraction(-1, 4),
                          Fraction(1, 64), Fraction(-1, 64)):
                    mq = (mstar[0] + s * nvec[0] / dd, mstar[1] + s * nvec[1] / dd)
                    cfg = list(pts); cfg[m] = mq
                    if not is_gp(cfg):
                        continue
                    if chi_of_points(cfg) != base_chi:
                        continue
                    # the three wall lines in the crossed configuration
                    L1 = pair_lines_of(cfg)[(min(m, partner), max(m, partner))]
                    L2 = lines[others[0]]
                    L3 = lines[others[1]]
                    v12, v13, v23 = (line_isect(L1, L2), line_isect(L1, L3),
                                     line_isect(L2, L3))
                    if v12 is None or v13 is None or v23 is None:
                        continue
                    g = ((v12[0] + v13[0] + v23[0]) / 3,
                         (v12[1] + v13[1] + v23[1]) / 3)
                    sv = sv_of_point(cfg, g, pairs)
                    if 0 in sv:
                        continue
                    keysv = sv
                    if keysv in current_svs or keysv in grabbed_here:
                        continue
                    grabbed_here.add(keysv)
                    chi9 = chi_insert(base_chi, n, sv, pairs, posmap)
                    assert chi_of_points(cfg + [g]) == chi9, "grab chi mismatch"
                    if chi9 not in new:
                        new[chi9] = [tuple(p) for p in cfg] + [g]
                        stats["grabs"] += 1
                if grabbed_here:
                    stats["conc_crossed"] += 1

    # ---------- parallel walls ----------
    for (P, Q) in all_pairs4(n):
        for m in (P[0], P[1], Q[0], Q[1]):
            partner = P[0] if m == P[1] else P[1] if m in P else \
                      Q[0] if m == Q[1] else Q[1]
            other = Q if m in P else P
            q1, q2 = other
            dirv = (pts[q2][0] - pts[q1][0], pts[q2][1] - pts[q1][1])
            stats["par_combos"] += 1
            base_pt = pts[partner]
            crit = {Fraction(0)}
            bx, by = base_pt
            # crossings with pair-lines of S\m
            for pr in rest_pairs[m]:
                A, B, C = lines[pr]
                den = A * dirv[0] + B * dirv[1]
                if den != 0:
                    crit.add(Fraction(C - A * bx - B * by, den))
            # horizontality flips of the moved lines (far-sign walls)
            if dirv[1] != 0:
                for x in range(n):
                    if x == m:
                        continue
                    crit.add(Fraction(pts[x][1] - by, dirv[1]))
            ts = sorted(crit)
            dd = dirv[0] * dirv[0] + dirv[1] * dirv[1]
            nvec = (-dirv[1], dirv[0])
            for a, b in zip(ts, ts[1:]):
                tm = (a + b) / 2
                mstar = (bx + tm * dirv[0], by + tm * dirv[1])
                if not chi_ok_with(m, mstar):
                    continue
                grabbed_here = set()
                for s in (Fraction(1, 4), Fraction(-1, 4),
                          Fraction(1, 64), Fraction(-1, 64)):
                    mq = (mstar[0] + s * nvec[0] / dd, mstar[1] + s * nvec[1] / dd)
                    cfg = list(pts); cfg[m] = mq
                    if not is_gp(cfg):
                        continue
                    if chi_of_points(cfg) != base_chi:
                        continue
                    stats_crossed = False
                    # far-column grabs (both far sides, both between-fractions)
                    Bn = max(max(abs(p[0]), abs(p[1])) for p in cfg) + 16
                    Lp = pair_lines_of(cfg)[(min(m, partner), max(m, partner))]
                    Lo = lines[other]
                    for X in (-1024 * Bn, -64 * Bn, 64 * Bn, 1024 * Bn):
                        y1 = Fraction(Lp[2] - Lp[0] * X, Lp[1])
                        y2 = Fraction(Lo[2] - Lo[0] * X, Lo[1])
                        for fr in (Fraction(1, 2), Fraction(1, 4), Fraction(3, 4)):
                            q = (X, y1 + fr * (y2 - y1))
                            sv = sv_of_point(cfg, q, pairs)
                            if 0 in sv:
                                continue
                            if sv in current_svs or sv in grabbed_here:
                                continue
                            grabbed_here.add(sv)
                            chi9 = chi_insert(base_chi, n, sv, pairs, posmap)
                            assert chi_of_points(cfg + [q]) == chi9, \
                                "par grab chi mismatch"
                            if chi9 not in new:
                                new[chi9] = [tuple(p) for p in cfg] + [q]
                                stats["grabs"] += 1
                            stats_crossed = True
                if grabbed_here:
                    stats["par_crossed"] += 1
    return new, stats

# --- the in-cell walk --------------------------------------------------------

def walk_parent(pts, base_chi, rng, steps=6, want_new_vs=None):
    """Random in-cell single-point moves inside the realization space; grab
    cells of every visited configuration not present in the parent's cell
    set.  Returns (dict chi->coords, n_configs)."""
    n = len(pts)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    posmap = {t: q for q, t in enumerate(TRIPLES(n))}
    rule = rule_for(n)
    new = {}
    cur = [tuple(p) for p in pts]
    walked = 0
    lo = min(min(p[0], p[1]) for p in cur)
    hi = max(max(p[0], p[1]) for p in cur)
    W = (hi - lo) + Fraction(4)
    for _ in range(steps):
        m = rng.randrange(n)
        rest = [(i, j) for (i, j) in pairs if i != m and j != m]
        target_sv = tuple(osign(base_chi, rule, i, j, m) for (i, j) in rest)
        placed = False
        for _ in range(300):
            q = (Fraction(rng.randint(int((lo - W) * 16), int((hi + W) * 16)), 16),
                 Fraction(rng.randint(int((lo - W) * 16), int((hi + W) * 16)), 16))
            if sv_of_point(cur, q, rest) == target_sv:
                placed = True
                break
        if not placed:
            continue
        cand = list(cur); cand[m] = q
        if not is_gp(cand) or chi_of_points(cand) != base_chi:
            continue
        cur = cand
        walked += 1
        # grab cells of this configuration
        sh, cells = arrangement_cell_samples(cur)
        for (sx, sy) in cells:
            sv = sv_of_point(sh, (sx, sy), pairs)
            if want_new_vs is not None and sv in want_new_vs:
                continue
            chi9 = chi_insert(base_chi, n, sv, pairs, posmap)
            if chi9 not in new:
                new[chi9] = [tuple(p) for p in sh] + [(sx, sy)]
    return new, walked

# ---------------------------------------------------------------------------
# level enumeration + certification
# ---------------------------------------------------------------------------

def _parent_job_v2(arg):
    key, rec, seed, opts = arg
    rng = random.Random(seed)
    n = len(rec['pts'])
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    posmap = {t: q for q, t in enumerate(TRIPLES(n))}
    chi = rec['chi']

    pts = shear_distinct_x(rec['pts'])
    assert chi_of_points(pts) == chi, "shear must preserve chi"
    pts, was = make_arrangement_generic(pts, chi, rng)
    if pts is None:
        return key, None, "GENERIC-FAIL"

    # S1: cells
    sh, cells = arrangement_cell_samples(pts)
    current_svs = set()
    out = {}
    for (sx, sy) in cells:
        sv = sv_of_point(sh, (sx, sy), pairs)
        current_svs.add(sv)
        chi9 = chi_insert(chi, n, sv, pairs, posmap)
        if chi9 not in out:
            out[chi9] = [tuple(p) for p in sh] + [(sx, sy)]

    st = {"cells": len(current_svs), "conc_combos": 0, "conc_crossed": 0,
          "par_combos": 0, "par_crossed": 0, "sweep_grabs": 0, "walk_cfgs": 0}

    # S2: the wall sweep
    if opts.get('sweep', True):
        grabs, s2 = sweep_parent(sh, chi, current_svs, rng)
        for chi9, coords in grabs.items():
            if chi9 not in out:
                out[chi9] = coords
        for k in st:
            if k in s2:
                st[k] += s2[k]

    # S3: the in-cell walk
    if opts.get('walk', True):
        wgrabs, nwalk = walk_parent(sh, chi, rng, steps=opts.get('walk_steps', 6),
                                    want_new_vs=None)
        for chi9, coords in wgrabs.items():
            if chi9 not in out:
                out[chi9] = coords
        st['walk_cfgs'] += nwalk

    return key, out, st

def enumerate_level_v2(types_n, n, opts=None, tag=""):
    """types_n: ck -> {'chi', 'pts'} at level n; produce level n+1."""
    opts = opts or {}
    from multiprocessing import Pool, cpu_count
    t0 = time.time()
    items = [(k, v, 700000 + n * 131 + i, opts) for i, (k, v) in enumerate(types_n.items())]
    results = {}
    agg = {"cells": 0, "conc_combos": 0, "conc_crossed": 0, "par_combos": 0,
           "par_crossed": 0, "sweep_grabs": 0, "walk_cfgs": 0, "generic_fail": 0}
    insertions = 0
    def absorb(out):
        nonlocal insertions
        insertions += len(out)
        for chi9, coords in out.items():
            # realize + canonicalize (cache by chi to avoid re-canonicalizing)
            ck = canonical_key(chi9, n + 1, rule_for(n + 1))
            if ck not in results:
                results[ck] = {'chi': chi9, 'pts': coords}
    if len(items) >= 8:
        with Pool(min(2, cpu_count())) as pool:
            for key, out, st in pool.imap_unordered(_parent_job_v2, items, chunksize=1):
                if out is None:
                    agg['generic_fail'] += 1
                    continue
                absorb(out)
                for k in st: agg[k] += st[k]
    else:
        for it in items:
            key, out, st = _parent_job_v2(it)
            if out is None:
                agg['generic_fail'] += 1
                continue
            absorb(out)
            for k in st: agg[k] += st[k]
    wall = time.time() - t0
    return results, {'parents': len(items), 'insertions': insertions,
                     'wall': wall, **agg}

def certify_level(results, n1, extra=""):
    """Mirror closure + anchor certificate for a level-n1 type set
    (keys = canonical chis)."""
    rule_n1 = rule_for(n1)
    sm = 0
    closure_ok = True
    fail = []
    for ck in results:
        negk = canonical_key(tuple(-s for s in ck), n1, rule_n1)
        if negk not in results:
            closure_ok = False
            fail.append(ck)
        elif negk == ck:
            sm += 1
    N = len(results)
    identified = (N + sm) // 2 if closure_ok else None
    exp = OT_MIRROR_IDENTIFIED.get(n1)
    ok = (exp is not None and identified == exp and closure_ok)
    return {'N': N, 'self_mirror': sm, 'identified': identified,
            'anchor': exp, 'closure_ok': closure_ok, 'ok': ok,
            'fail_sample': fail[:2]}

def stage_ot(target_n, opts=None, resume=True, tag=""):
    types = None
    for n in range(3, target_n + 1):
        pn = os.path.join(CACHE, f"ot{n}.pkl")
        v2n = os.path.join(CACHE, f"ot{n}_v2.pkl")
        use = v2n if (n >= 4 and resume and os.path.exists(v2n)) else None
        if use and os.path.exists(use):
            types = pickle.load(open(use, 'rb'))
            cert = certify_level(types, n)
            R(f"[ot{tag}] n={n}: cached v2 {cert['N']} reflection-distinguished, "
              f"mirror-identified {cert['identified']} (anchor {cert['anchor']}) "
              f"{'OK' if cert['ok'] else 'MISMATCH'}")
            if not cert['ok']:
                return None
            continue
        if n == 3:
            pts = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)),
                   (Fraction(0), Fraction(1))]
            chi = chi_of_points(pts)
            ck = canonical_key(chi, 3, rule_for(3))
            types = {ck: {'chi': chi, 'pts': pts}}
            with open(v2n, 'wb') as f:
                pickle.dump(types, f, protocol=4)
            R(f"[ot{tag}] n=3: bootstrap 1 type")
            continue
        assert types is not None
        R(f"[ot{tag}] expanding n={n-1} ({len(types)} types) -> n={n} ...")
        nxt, stats = enumerate_level_v2(types, n - 1, opts=opts, tag=tag)
        # simplify realizations (denominator control) + store
        rng = random.Random(4242 + n)
        for ck, rec in nxt.items():
            rec['pts'] = simplify_realization(rec['pts'], rec['chi'], rng)
        cert = certify_level(nxt, n)
        R(f"[ot{tag}] n={n}: {cert['N']} reflection-distinguished types "
          f"({cert['self_mirror']} self-mirror + "
          f"{(cert['N']-cert['self_mirror'])//2 if cert['closure_ok'] else '?'} chiral pairs) "
          f"-> mirror-identified {cert['identified']} (anchor {cert['anchor']}) "
          f"[{'OK' if cert['ok'] else 'MISMATCH'}] | parents={stats['parents']} "
          f"insertions={stats['insertions']} cells={stats['cells']} "
          f"conc-walls: {stats['conc_crossed']}/{stats['conc_combos']} combos "
          f"par-walls: {stats['par_crossed']}/{stats['par_combos']} combos "
          f"sweep-grabbed-types={stats['sweep_grabs']} walk-cfgs={stats['walk_cfgs']} "
          f"wall={stats['wall']:.0f}s")
        if not cert['ok']:
            if not cert['closure_ok']:
                R(f"[ot{tag}] !! MIRROR-CLOSURE FAILURES: {cert['fail_sample']}")
            R(f"[ot{tag}] !! COUNT CERTIFICATE MISMATCH at n={n}: aborting.")
            return None
        with open(v2n, 'wb') as f:
            pickle.dump(nxt, f, protocol=4)
        types = nxt
    return types

# ---------------------------------------------------------------------------
# stage: the W75 baseline (cells + perturbations only) for the root-cause diff
# ---------------------------------------------------------------------------

def _parent_job_baseline(arg):
    key, rec, seed = arg
    rng = random.Random(seed)
    n = len(rec['pts'])
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    posmap = {t: q for q, t in enumerate(TRIPLES(n))}
    chi = rec['chi']
    pts = shear_distinct_x(rec['pts'])
    out = {}
    realizations = [pts]
    for _ in range(120):
        cand = []
        for (x, y) in pts:
            dx = Fraction(rng.randint(-14, 14), 10)
            dy = Fraction(rng.randint(-14, 14), 10)
            cand.append((x + dx, y + dy))
        if len(set(cand)) < len(cand):
            continue
        if not is_gp(cand) or chi_of_points(cand) != chi:
            continue
        realizations.append(cand)
    for P in realizations:
        sh, cells = arrangement_cell_samples(P)
        for (sx, sy) in cells:
            sv = sv_of_point(sh, (sx, sy), pairs)
            chi9 = chi_insert(chi, n, sv, pairs, posmap)
            if chi9 not in out:
                out[chi9] = [tuple(p) for p in sh] + [(sx, sy)]
    return key, out, len(realizations)

def stage_ot8_baseline():
    """Reproduce the W75 realization-diversification baseline (3313/3315) and
    diff against the v2 set — the root-cause receipt for the 2 missing types."""
    R("[baseline] W75-style realization-diversification-only enumeration "
      "(cells + random perturbations, NO wall sweep)")
    types7 = pickle.load(open(os.path.join(CACHE, "ot7_v2.pkl"), 'rb'))
    from multiprocessing import Pool, cpu_count
    items = [(k, v, 910000 + i) for i, (k, v) in enumerate(types7.items())]
    results = {}
    t0 = time.time()
    reals = 0
    if len(items) >= 8:
        with Pool(min(2, cpu_count())) as pool:
            for key, out, nr in pool.imap_unordered(_parent_job_baseline, items, chunksize=1):
                reals += nr
                for chi9, coords in out.items():
                    ck = canonical_key(chi9, 8, rule_for(8))
                    if ck not in results:
                        results[ck] = {'chi': chi9, 'pts': coords}
    else:
        for it in items:
            key, out, nr = _parent_job_baseline(it)
            reals += nr
            for chi9, coords in out.items():
                ck = canonical_key(chi9, 8, rule_for(8))
                if ck not in results:
                    results[ck] = {'chi': chi9, 'pts': coords}
    cert = certify_level(results, 8)
    R(f"[baseline] n=8: {cert['N']} reflection-distinguished, "
      f"mirror-identified {cert['identified']} (anchor {cert['anchor']}) "
      f"closure_ok={cert['closure_ok']} | realizations={reals} "
      f"wall={time.time()-t0:.0f}s")
    with open(os.path.join(CACHE, "ot8_baseline.pkl"), 'wb') as f:
        pickle.dump(results, f, protocol=4)
    # diff against v2
    v2 = pickle.load(open(os.path.join(CACHE, "ot8_v2.pkl"), 'rb'))
    missing = set(v2.keys()) - set(results.keys())
    R(f"[baseline] v2-only types (the ones the W75 method missed): {len(missing)}")
    for ck in list(missing)[:8]:
        chi = v2[ck]['chi']
        rule8 = rule_for(8)
        hv = chi_hull_vertices(chi, 8, rule8)
        wa = chi_convex5_method_a(chi, 8, rule8)
        R(f"[baseline]   missing type {str(ck)[:44]}... hull={len(hv)} "
          f"convex5={'YES' if wa is not None else 'NO'} "
          f"self-mirror={canonical_key(tuple(-s for s in ck),8,rule8)==ck}")
    extra = set(results.keys()) - set(v2.keys())
    R(f"[baseline] baseline-only types (must be 0 — v2 is a superset by "
      f"construction): {len(extra)}")
    return cert['ok'], missing

# ---------------------------------------------------------------------------
# stage OUTER: independent outer-insertion cross-check
# ---------------------------------------------------------------------------

def _outer_job(arg):
    key, rec, seed = arg
    rng = random.Random(seed)
    n = len(rec['pts'])
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    posmap = {t: q for q, t in enumerate(TRIPLES(n))}
    chi = rec['chi']
    pts = shear_distinct_x(rec['pts'])
    pts, _ok = make_arrangement_generic(pts, chi, rng)
    if pts is None:
        return key, None
    sh, cells = arrangement_cell_samples(pts)
    current_svs = set()
    out = {}
    for (sx, sy) in cells:
        conf = sh + [(sx, sy)]
        if len(hull_monotone(conf)) <= n:   # sample not a hull vertex: inner
            continue
        sv = sv_of_point(sh, (sx, sy), pairs)
        current_svs.add(sv)
        chi9 = chi_insert(chi, n, sv, pairs, posmap)
        if chi9 not in out:
            out[chi9] = [tuple(p) for p in sh] + [(sx, sy)]
    # outer sweep: walls with outer grabs only
    grabs, _st = sweep_parent(sh, chi, current_svs, rng)
    for chi9, coords in grabs.items():
        if len(hull_monotone(coords)) <= n:
            continue
        if chi9 not in out:
            out[chi9] = coords
    # outer walk
    wgrabs, _nw = walk_parent(sh, chi, rng, steps=6, want_new_vs=current_svs)
    for chi9, coords in wgrabs.items():
        if len(hull_monotone(coords)) <= n:
            continue
        if chi9 not in out:
            out[chi9] = coords
    return key, out

def stage_outer(n=8):
    R(f"[outer] INDEPENDENT GENERATION at n={n}: outer insertions only "
      f"(hull-vertex-deletion direction)")
    types_prev = pickle.load(open(os.path.join(CACHE, f"ot{n-1}_v2.pkl"), 'rb'))
    from multiprocessing import Pool, cpu_count
    items = [(k, v, 830000 + i) for i, (k, v) in enumerate(types_prev.items())]
    results = {}
    t0 = time.time()
    if len(items) >= 8:
        with Pool(min(2, cpu_count())) as pool:
            for key, out in pool.imap_unordered(_outer_job, items, chunksize=1):
                if out is None:
                    continue
                for chi9, coords in out.items():
                    ck = canonical_key(chi9, n, rule_for(n))
                    if ck not in results:
                        results[ck] = {'chi': chi9, 'pts': coords}
    else:
        for it in items:
            key, out = _outer_job(it)
            if out is None:
                continue
            for chi9, coords in out.items():
                ck = canonical_key(chi9, n, rule_for(n))
                if ck not in results:
                    results[ck] = {'chi': chi9, 'pts': coords}
    cert = certify_level(results, n)
    R(f"[outer] n={n}: {cert['N']} reflection-distinguished, mirror-identified "
      f"{cert['identified']} (anchor {cert['anchor']}) closure={cert['closure_ok']} "
      f"wall={time.time()-t0:.0f}s")
    ref = pickle.load(open(os.path.join(CACHE, f"ot{n}_v2.pkl"), 'rb'))
    same = set(results.keys()) == set(ref.keys())
    R(f"[outer] outer-only set == full set: {'YES — CROSS-CHECK GREEN' if same else 'NO'} "
      f"(|outer|={len(results)} |full|={len(ref)}; "
      f"outer-missing={len(set(ref)-set(results))} full-missing={len(set(results)-set(ref))})")
    return same and cert['ok']

# ---------------------------------------------------------------------------
# stage F5: the master certificate over ALL 9-point order types
# ---------------------------------------------------------------------------

def _f5_job(chi):
    n = 9
    rule = rule_for(n)
    hull = chi_hull_vertices(chi, n, rule)
    h = len(hull)
    wa = chi_convex5_method_a(chi, n, rule)
    wb = chi_convex5_method_b(chi, n, rule)
    if wa is None and wb is None:
        return h, False, "both-none", 0
    if (wa is None) != (wb is None):
        return h, False, "method-disagree", 0
    okw = (chi_witness_is_convex_both(chi, n, rule, wa) and
           chi_witness_is_convex_both(chi, n, rule, wb))
    if not okw:
        return h, False, "cross-fail", 0
    return h, True, "ok", len(set(wa) & set(hull))

def stage_f5():
    R("[f5] MASTER CERTIFICATE: every 9-point order type contains a convex 5")
    pn = os.path.join(CACHE, "ot9_v2.pkl")
    if os.path.exists(pn):
        types = pickle.load(open(pn, 'rb'))
        R(f"[f5] loaded cached ot9_v2: {len(types)} reflection-distinguished types")
    else:
        R("[f5] no cached n=9 — enumerating (this is the C-lane product in the "
          "full run; python fallback)")
        types = stage_ot(9)
        if types is None:
            return False
    total = len(types)
    rule9 = rule_for(9)
    cert = certify_level(types, 9)
    R(f"[f5] count certificate: {cert['N']} reflection-distinguished "
      f"({cert['self_mirror']} self-mirror), mirror-identified "
      f"{cert['identified']} (anchor {cert['anchor']}) "
      f"[{'OK' if cert['ok'] else 'MISMATCH'}] closure={cert['closure_ok']}")
    if not cert['ok']:
        R("[f5] !! refusing to certify with a count mismatch")
        return False
    census = {}
    wcomp = {}
    bad = []
    t0 = time.time()
    done = 0
    from multiprocessing import Pool, cpu_count
    items = [rec['chi'] for rec in types.values()]
    with Pool(min(2, cpu_count())) as pool:
        for h, ok, why, nh in pool.imap_unordered(_f5_job, items, chunksize=64):
            done += 1
            census[h] = census.get(h, 0) + 1
            if not ok:
                bad.append(why)
            else:
                wcomp[(h, nh)] = wcomp.get((h, nh), 0) + 1
            if done % 40000 == 0:
                print(f"  [f5] {done}/{total} ({time.time()-t0:.0f}s)", flush=True)
    R(f"[f5] hull census: " + ", ".join(f"h={h}:{c}" for h, c in sorted(census.items())))
    R(f"[f5] witness composition (hull, #hull-verts-in-witness): count")
    for (h, nh), c in sorted(wcomp.items()):
        R(f"[f5]   hull={h} witness-hull-vertices={nh}: {c}")
    if bad:
        R(f"[f5] !! FAILURES: {len(bad)} ({set(bad)})")
        return False
    R(f"[f5] GREEN — all {total} 9-point order types contain a convex 5 "
      f"(two independent chirotope methods, witnesses cross-validated) "
      f"({time.time()-t0:.0f}s)")
    return True

# ---------------------------------------------------------------------------
# witness + random battery
# ---------------------------------------------------------------------------

def stage_witness():
    R("[witness] banked 8-point witness re-verify (lower side f(5) >= 9)")
    wb = json.load(open(os.path.join(HERE, "engine107", "witness_best.json")))
    w8 = [(int(x), int(y)) for (x, y) in wb["pts5"]]
    assert is_gp(w8), "witness must be GP"
    ok, A5 = two_method_agree(w8)
    R(f"[witness] GP=Yes | subsets with convex 5: {len(A5)} (must be 0) | "
      f"two-method agreement: {'GREEN' if ok else 'RED'}")
    # the witness's order type must be among the certified n=8 types
    chi8 = chi_of_points(w8)
    ck8 = canonical_key(chi8, 8, rule_for(8))
    ot8 = pickle.load(open(os.path.join(CACHE, "ot8_v2.pkl"), 'rb'))
    inside = ck8 in ot8
    R(f"[witness] witness order type present in the certified 3315 "
      f"enumeration: {'YES' if inside else 'NO'}")
    # its badness confirmed at the chirotope level (both methods)
    wa = chi_convex5_method_a(chi8, 8, rule_for(8))
    wb2 = chi_convex5_method_b(chi8, 8, rule_for(8))
    R(f"[witness] chirotope-level: convex5 method A: {wa}, method B: {wb2} "
      f"(both must be None)")
    return ok and (not A5) and inside and (wa is None) and (wb2 is None)

def stage_rand(target=100000):
    R(f"[rand] random 9-point GP battery ({target} sets, exact integers)")
    rng = random.Random(107107)
    census = {}
    fails = 0
    t0 = time.time()
    done = 0
    while done < target:
        pts = [(rng.randint(-500, 500), rng.randint(-500, 500)) for _ in range(9)]
        if not is_gp(pts):
            continue
        done += 1
        h = len(hull_monotone(pts))
        census[h] = census.get(h, 0) + 1
        w = V1.convex5_witness(pts, require_both=True)
        if not w:
            fails += 1
            R(f"[rand] !! COUNTEREXAMPLE: {pts}")
        if done % 20000 == 0:
            print(f"  [rand] {done}/{target} ({time.time()-t0:.0f}s)", flush=True)
    R(f"[rand] hull census: " + ", ".join(f"{h}:{c}" for h, c in sorted(census.items())))
    if fails:
        R(f"[rand] FAILED ({fails})")
        return False
    R(f"[rand] GREEN — {target} random 9-point GP sets, every one contains a "
      f"convex 5 ({time.time()-t0:.0f}s)")
    return True

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=["ot4", "ot5", "ot6", "ot7", "ot8",
                                        "ot9", "baseline", "outer", "f5",
                                        "witness", "rand", "verify"], default=None)
    ap.add_argument("--no-sweep", action="store_true")
    ap.add_argument("--no-walk", action="store_true")
    ap.add_argument("--walk-steps", type=int, default=6)
    ap.add_argument("--rand", type=int, default=100000)
    args = ap.parse_args()
    opts = {'sweep': not args.no_sweep, 'walk': not args.no_walk,
            'walk_steps': args.walk_steps}
    t0 = time.time()
    if args.stage == "ot4":
        stage_ot(4, opts, tag="4")
    elif args.stage == "ot5":
        stage_ot(5, opts, tag="5")
    elif args.stage == "ot6":
        stage_ot(6, opts, tag="6")
    elif args.stage == "ot7":
        stage_ot(7, opts, tag="7")
    elif args.stage == "ot8":
        stage_ot(8, opts, tag="8")
    elif args.stage == "ot9":
        stage_ot(9, opts, tag="9")
    elif args.stage == "baseline":
        stage_ot8_baseline()
    elif args.stage == "outer":
        stage_outer(8)
    elif args.stage == "f5":
        stage_f5()
    elif args.stage == "witness":
        stage_witness()
    elif args.stage == "rand":
        stage_rand(args.rand)
    elif args.stage == "verify":
        R("=== engine107f5v2 --verify (the engine contract) ===")
        ok = True
        ok &= bool(stage_ot(8, opts, tag="8"))
        ok &= bool(stage_ot8_baseline()[0])
        ok &= bool(stage_outer(8))
        ok &= bool(stage_witness())
        ok &= bool(stage_rand(min(args.rand, 20000)))
        ok &= bool(stage_f5())
        R(f"=== verify: {'ALL GREEN' if ok else 'FAILURES PRESENT'} "
          f"({time.time()-t0:.0f}s) ===")
    else:
        print("no stage given")
    print(f"[wall total] {time.time()-t0:.0f}s")

if __name__ == "__main__":
    main()
