#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine107audit_w81.py — W81-107B — THE AUDITOR/DOUBLER ENGINE (fresh code paths).

Lane: W81-107B (Erdos weak-problems campaign, problem #107 Happy Ending).
Mandate: independent re-verification of the #107 package with algorithms
written from scratch for this lane — no campaign engine code is imported.

Fresh instruments (all exact arithmetic — int / Fraction; zero floats):
  OT   own order-type enumerator: per-subset sign vectors over triples,
       canonical key = min over ALL n! relabelings x {id, mirror} of the
       sign vector (mirror-identified unlabeled order type).
  CVA  convexity code A: own Andrew monotone chain (strict pops, x-sorted
       input assumed; equal-x safe — pure cross-product tests).
  CVB  convexity code B: own gift wrap (Jarvis march, orientation-driven
       candidate selection, far-point tie-break).
  DP   own longest cup/cap DP: best[i][L] = minimal last slope of an
       L-cup ending at i (dual: maximal first... no — maximal last slope
       for caps), exact Fraction slopes; validated against brute-force
       chain scans on small sets.
  E/X  own rebuild of the ES_SANDWICH_ALLN.md §1 construction
       (E(a,b;delta) recursion + cluster-arc assembly), scaled once to
       integers (orientation-sign preserving).

Checks:
  A1  f(4)=5 EXHAUSTIVE both directions via the order-type enumerator:
      4-point GP types (anchor 2) / 5-point GP types (anchor 3) on all
      grids with <= 40 points (2x2, 3x3, 4x4, 5x5, 6x6, 5x8); every GP
      5-type contains a convex 4 (both codes); a 4-point GP type with no
      convex 4 exists (both codes); the 2-1 split mechanism of the
      repaired ES_PACKAGE_PROOF.md §5 (the {a,b,p,q} extremality finish)
      re-derived in code on the hull-3 type.
  A2  the banked 8-point no-convex-5 witnesses (Erdos107.lean w5 kernel
      witness, PROOF.md interleaved witness): GP exact; all C(8,5)=56
      subsets non-convex, BOTH codes.
  A3  ES-SANDWICH lower-side rebuild at n=6,7,8: |X_n| = 2^(n-2), cluster
      sizes C(m,i), GP exact, y-band order, slope separation
      (intra in (0, s]; inter |slope| >= 1/(1+38rho) > 1/2, vertical = inf),
      Lemma M spot-check, and max-convex = n-1 (exhaustive no-convex-n at
      n=6,7 both codes at n=6 + code A full / code B sampled at n=7;
      n=8: convex-(n-1) transversal witnesses + randomized/hillclimb
      no-convex-8 search + structure census).
  A4  U-BIS closed form G(n) = C(2n-2,n-1) - 2n + 3 for n = 3..11 (two
      binomial codes vs the exact hockey-stick double sum) + instance
      checks (16-point GP sets force convex 4; 64-point GP sets force a
      5-cup or 5-cap by the own DP -> convex 5 by own codes; label census
      L-MLT(a) |P_ij| <= C(i+j-2,i-1)).
  A5  the binomial table C(2n-4,n-2)+1, n=3..30, two codes; anchors; the
      gap-law ratios of ES_SANDWICH_ALLN.md §6; U-BIS >= ES-ALLN-SHARP;
      the VANDERMONDE-DOUBLE identities of SHARP_PROOF.md §4 (inner
      hockey, the corrected outer intermediate, final) both binomial
      codes, all 3 <= a,b <= 30.
  A6  the W81-107A comparison base: 3 seeded-random n=8 parents from the
      banked ot8_v2 census re-run through the campaign python v2
      machinery (read-only import); parent realization + cell/child
      fingerprints dumped for the C-port cell comparison.
  A7  NEGATIVE CONTROLS (mandatory): planted convex 5 in the no-convex-5
      witness MUST be detected (both codes); a convex-6 hexagon MUST be
      found by the no-convex-6 scanner; collinear injection MUST fail GP;
      the corrupted U-BIS form (- 2n + 2) MUST be rejected; the
      rho-inflated construction MUST violate the slope-separation
      threshold (the checker is not vacuous); the DP MUST match brute
      force on random small sets.
  A8  the two boundary lanes named by the W81-107B audit brief: (i)
      ES_PACKAGE_PROOF.md §2 Theorem CC's three-case extension lemma at
      the k=3 / l=3 boundary — the statement at (k,l) = (3,3), (3,4),
      (4,3) on every GP x-distinct grid subset of the exact threshold
      size C(k+l-4,k-2)+1 (own DP + brute chains, two codes), the (3,3)
      X/Y-split + sigma/tau trichotomy mechanism on every GP x-distinct
      3-set, and the E(k,l) tightness (size C(k+l-4,k-2), GP, distinct x,
      no k-cup, no l-cap); (ii) ES_PACKAGE_PROOF.md §7.3 GP-ELIM at the
      N >= 2 boundary — greedy extraction at/above the exact threshold on
      planted-collinearity boards (t measured, per-stage forbidden
      census <= C(j,2)(t-2)), the degenerate lanes t=2 / m=1 / m=2, and
      the all-collinear board where m=3 needs N+1 (the +1 has teeth).

Stages:  --stage a1|a2|a3|a4|a5|a6|a8|neg|gate|verify (default: verify)
         gate  = compact battery for the comparator driver (S-AUDIT-W81)
         verify = full battery.  Exit 0 iff every executed check passes;
         every check prints exactly one PASS/FAIL line; the receipts file
         receipts107audit_w81.txt is rewritten on each run (append-mode
         sections preserved across stages within one process).

Time budget: <= 8 min for --verify (measured; guard prints per-check wall).
"""

import argparse
import hashlib
import itertools
import json
import math
import os
import random
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
RECEIPTS = os.path.join(HERE, "receipts107audit_w81.txt")
V2PARENT_DUMP = os.path.join(HERE, "audit_w81_v2parents.json")
SEED = 20261181  # W81-107B deterministic seed

_R = []
_T0 = time.time()
_TOL = 8 * 60  # the 8-minute discipline (soft guard; hard-fails a check that
# would blow the budget — every stage is measured and reported)


def R(line=""):
    print(line, flush=True)
    _R.append(line)
    with open(RECEIPTS, "w", encoding="utf-8") as f:
        f.write("\n".join(_R) + "\n")


# ===========================================================================
# SECTION 0 — FRESH GEOMETRY CORE (own implementations; nothing imported)
# ===========================================================================

def cross3(o, a, b):
    """Exact orientation determinant of (o, a, b)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def is_gp(pts):
    """General position: no 3 collinear (exact)."""
    n = len(pts)
    for a in range(n):
        xa, ya = pts[a]
        for b in range(a + 1, n):
            xb, yb = pts[b]
            for c in range(b + 1, n):
                if (xb - xa) * (pts[c][1] - ya) - (pts[c][0] - xa) * (yb - ya) == 0:
                    return False
    return True


def hull_chain(pts):
    """Convexity code A — own Andrew monotone chain.

    pts: iterable of distinct points (any order; equal x fine). Returns the
    STRICT hull vertex list in CCW order (collinear boundary points dropped
    by the <= pops — GP input has none anyway).
    """
    p = sorted(pts)
    if len(p) <= 2:
        return p
    lo = []
    for q in p:
        while len(lo) >= 2 and cross3(lo[-2], lo[-1], q) <= 0:
            lo.pop()
        lo.append(q)
    up = []
    for q in reversed(p):
        while len(up) >= 2 and cross3(up[-2], up[-1], q) <= 0:
            up.pop()
        up.append(q)
    return lo[:-1] + up[:-1]


def hull_giftwrap(pts):
    """Convexity code B — own gift wrap (Jarvis march).

    Wraps CCW from the lexicographic minimum; among collinear candidates the
    FAR one is taken (so boundary midpoints are skipped — strict hull).
    """
    pts = list(pts)
    if len(pts) <= 2:
        return pts
    start = min(pts)
    hull = [start]
    cur = start
    while True:
        nxt = None
        for cand in pts:
            if cand == cur:
                continue
            if nxt is None:
                nxt = cand
                continue
            o = cross3(cur, nxt, cand)
            if o < 0:  # cand is strictly right of cur->nxt: better (CCW wrap)
                nxt = cand
            elif o == 0:
                # collinear: keep the farther point (skip the near midpoint)
                d1 = (nxt[0] - cur[0]) ** 2 + (nxt[1] - cur[1]) ** 2
                d2 = (cand[0] - cur[0]) ** 2 + (cand[1] - cur[1]) ** 2
                if d2 > d1:
                    nxt = cand
        if nxt == start:
            break
        hull.append(nxt)
        cur = nxt
        if len(hull) > len(pts):  # safety net (cannot happen on distinct pts)
            return None
    return hull


def convex_position(pts, code="A"):
    """True iff every point is a strict hull vertex (|hull| == |pts|)."""
    if len(pts) <= 2:
        return True  # degenerate conventions never used on k>=3 in this engine
    h = hull_chain(pts) if code == "A" else hull_giftwrap(pts)
    return h is not None and len(h) == len(pts)


def has_convex_k(pts, k, code="A"):
    """Some k-subset in convex position (brute; pts small or k small)."""
    for sub in itertools.combinations(pts, k):
        if convex_position(sub, code):
            return True
    return False


def no_convex_k(pts, k, code="A"):
    """Exhaustive: NO k-subset in convex position. Returns (verdict, count)."""
    cnt = 0
    for sub in itertools.combinations(pts, k):
        cnt += 1
        if convex_position(sub, code):
            return False, cnt
    return True, cnt


# --- own order-type machinery ----------------------------------------------

_TRIPLE_CACHE = {}


def triples(n):
    t = _TRIPLE_CACHE.get(n)
    if t is None:
        t = list(itertools.combinations(range(n), 3))
        _TRIPLE_CACHE[n] = t
    return t


def sign_vector(pts):
    """Orientation signs of all label triples (a<b<c) — the raw chirotope."""
    out = []
    for a, b, c in triples(len(pts)):
        o = cross3(pts[a], pts[b], pts[c])
        out.append(1 if o > 0 else (-1 if o < 0 else 0))
    return tuple(out)


def canonical_ot(pts):
    """Mirror-identified unlabeled order type: min over all n! relabelings
    of the sign vector, and over their mirrors (negations). n <= 5 in this
    engine (120 perms x 10 triples — cheap after bucket dedupe)."""
    n = len(pts)
    best = None
    tri = triples(n)
    for perm in itertools.permutations(range(n)):
        q = [pts[i] for i in perm]
        sv = []
        for a, b, c in tri:
            o = cross3(q[a], q[b], q[c])
            sv.append(1 if o > 0 else (-1 if o < 0 else 0))
        sv = tuple(sv)
        if best is None or sv < best:
            best = sv
        mir = tuple(-x for x in sv)
        if mir < best:
            best = mir
    return best


# --- own cup/cap DP ---------------------------------------------------------

def _slopes_sorted(pts):
    """pts must have pairwise distinct x (caller shears if needed).
    Returns list of (x, y) in x-order."""
    return sorted(pts)


def cup_cap_dp(pts):
    """Own longest cup/cap DP on an x-distinct set.

    Returns (cup_len[i], cap_len[i]) per point (x-sorted order).
    best_cup[i][L] = minimal possible last slope of an L-cup ending at i
    (None if impossible); dual for caps (maximal last slope).
    Exact Fraction slopes.
    """
    p = _slopes_sorted(pts)
    n = len(p)
    if n == 1:
        return [1], [1], p
    sl = {}
    for i in range(n):
        for j in range(i + 1, n):
            sl[(i, j)] = F(p[j][1] - p[i][1], p[j][0] - p[i][0])
    INF = None
    cup = [dict() for _ in range(n)]   # L -> min last slope
    cap = [dict() for _ in range(n)]   # L -> max last slope
    for i in range(n):
        cup[i][1] = None  # slope-free singleton
        cap[i][1] = None
    for i in range(1, n):
        for j in range(i):
            sij = sl[(j, i)]
            for L, ms in cup[j].items():
                if ms is None or ms < sij:
                    cur = cup[i].get(L + 1)
                    if cur is None or sij < cur:
                        cup[i][L + 1] = sij
            for L, ms in cap[j].items():
                if ms is None or ms > sij:
                    cur = cap[i].get(L + 1)
                    if cur is None or sij > cur:
                        cap[i][L + 1] = sij
    cup_len = [max(cup[i].keys()) for i in range(n)]
    cap_len = [max(cap[i].keys()) for i in range(n)]
    return cup_len, cap_len, p


def max_cup_cap(pts):
    cl, cp, p = cup_cap_dp(pts)
    return max(cl), max(cp), cl, cp, p


def _brute_max_chain(pts, want_cup=True):
    """Brute-force longest k-cup/k-cap over all subsets (validation only)."""
    p = _slopes_sorted(pts)
    n = len(p)
    best = 1
    for size in range(n, 1, -1):
        if size <= best:
            break
        for sub in itertools.combinations(range(n), size):
            slopes = [F(p[sub[t + 1]][1] - p[sub[t]][1],
                        p[sub[t + 1]][0] - p[sub[t]][0]) for t in range(size - 1)]
            if want_cup and all(slopes[t] < slopes[t + 1] for t in range(len(slopes) - 1)):
                best = max(best, size)
                break
            if (not want_cup) and all(slopes[t] > slopes[t + 1] for t in range(len(slopes) - 1)):
                best = max(best, size)
                break
    return best


def shear_distinct_x(pts):
    """Own det-1 shear to pairwise distinct x (integer shear for integer
    input; Fraction-safe: tries s = 0,1,2,... then fractions)."""
    n = len(pts)
    best = None
    cands = [F(k) for k in range(0, 4 * n * n + 8)]
    for s in cands:
        xs = [p[0] + s * p[1] for p in pts]
        if len(set(xs)) == n:
            best = s
            break
    if best is None:
        raise RuntimeError("no shear found (impossible: <= C(n,2) bad values)")
    return [(p[0] + best * p[1], p[1]) for p in pts], best


# ===========================================================================
# SECTION 1 — THE ES-SANDWICH CONSTRUCTION (own rebuild, exact)
# ===========================================================================

def Eset(a, b, delta):
    """E(a,b;delta) per ES_SANDWICH_ALLN.md §1 spec (exact Fractions).

    E(2,b) = E(a,2) = {(0,0)};
    E(a,b) = A u B, A = (1/8)E(a-1,b;delta/3),
                        B = (1/8)E(a,b-1;delta/3) + (1, 3*delta/4).
    """
    if a <= 2 or b <= 2:
        return [(F(0), F(0))]
    A = [(x / 8, y / 8) for (x, y) in Eset(a - 1, b, delta / 3)]
    B = [(x / 8 + 1, y / 8 + 3 * delta / 4) for (x, y) in Eset(a, b - 1, delta / 3)]
    return A + B


def build_Xn(n, rho_mult=F(1)):
    """The ES_SANDWICH_ALLN.md §1 construction, exact.

    m = n-2; D = m/4; s = 1/(16(m+1)); eta = 1/(2^14 m); rho = eta/2.
    Centers c_i = (1-(m-2i)^2/(16m), (m-2i)/8) on the concave arc.
    T_i = c_i + rho*(E(n-i, i+2; s) - (19/32, 19s/48)).
    rho_mult > 1 inflates rho (negative control A7-NC6).
    Returns (clusters, pts, params dict).
    """
    m = n - 2
    D = F(m, 4)
    s = F(1, 16 * (m + 1))
    eta = F(1, (2 ** 14) * m)
    rho = eta / 2 * rho_mult
    offx, offy = F(19, 32), 19 * s / 48
    clusters = []
    for i in range(m + 1):
        yi = F(m - 2 * i, 8)
        xi = 1 - F((m - 2 * i) ** 2, 16 * m)
        E = Eset(n - i, i + 2, s)
        Ti = [(xi + rho * (ex - offx), yi + rho * (ey - offy)) for (ex, ey) in E]
        clusters.append(Ti)
    pts = [q for T in clusters for q in T]
    return clusters, pts, {"m": m, "D": D, "s": s, "eta": eta, "rho": rho, "n": n}


def scale_to_int(pts):
    """Uniform positive scaling to integers (orientation signs preserved)."""
    den = 1
    for (x, y) in pts:
        den = den * x.denominator // math.gcd(den, x.denominator)
        den = den * y.denominator // math.gcd(den, y.denominator)
    return [(int(x * den), int(y * den)) for (x, y) in pts], den


def slope_separation(clusters, params):
    """The load-bearing slope-separation law, exact.

    intra: slope in (0, s] for same-cluster pairs (distinct x guaranteed).
    inter: |slope| >= sigma = 1/(1+38*rho) (vertical pairs = +inf, satisfy).
    Returns dict with measured extremes and pass/fail booleans.
    """
    s, rho = params["s"], params["rho"]
    sigma = F(2 ** 15 * params["m"], 2 ** 15 * params["m"] + 38)  # = 1/(1+38rho)
    intra_ok = True
    intra_max = F(0)
    intra_pos_ok = True
    inter_ok = True
    inter_min = None  # min |slope| over non-vertical cross pairs
    nvert = 0
    flat = [(q, ci) for ci, T in enumerate(clusters) for q in T]
    for a in range(len(flat)):
        pa, ca = flat[a]
        for b in range(a + 1, len(flat)):
            pb, cb = flat[b]
            dx = pb[0] - pa[0]
            dy = pb[1] - pa[1]
            if ca == cb:
                if dx == 0:
                    intra_ok = False  # same-cluster equal x would break the law
                    continue
                sl = dy / dx
                if not (sl > 0):
                    intra_pos_ok = False
                if sl > intra_max:
                    intra_max = sl
                if not (F(0) < sl <= s):
                    intra_ok = False
            else:
                if dx == 0:
                    nvert += 1  # vertical cross pair: |slope| = inf >= sigma
                    continue
                sl = abs(dy / dx)
                if inter_min is None or sl < inter_min:
                    inter_min = sl
                if sl < sigma:
                    inter_ok = False
    chain_ok = (intra_max < F(1, 2) < sigma
                and (inter_min is None or sigma <= inter_min))  # None = all vertical = inf
    return {"intra_ok": intra_ok, "intra_pos_ok": intra_pos_ok,
            "intra_max": intra_max, "inter_ok": inter_ok,
            "inter_min": inter_min, "sigma": sigma, "nvert": nvert,
            "sigma_gt_half": sigma > F(1, 2),
            "s_lt_half": s < F(1, 2),
            "chain_ok": chain_ok}


# ===========================================================================
# SECTION 2 — CHECKS
# ===========================================================================

GRIDS = [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (5, 8)]
ANCHOR_OT = {4: 2, 5: 3}  # classical unlabeled GP order types (mirrors ided)

W5_KERNEL = [(14395371738365952, 14189451647385600),
             (19471918138964442, 5423598718156800),
             (19471898862300744, 5423599789082561),
             (19471821755645952, 5423615852968976),
             (19471918138964442, -5423598718156800),
             (19471841032309650, -5423582654270385),
             (19471821755645952, -5423581583344624),
             (14395371738365952, -14189451647385600)]

W5_INTERLEAVED = [(2 * t, t * t) for t in range(4)] + \
                 [(2 * t + 1, -((3 - t) ** 2) + 2) for t in range(4)]

W4_WITNESS = [(0, 0), (6, 0), (3, 9), (3, 2)]


def check_a1(mode="full"):
    """A1 — f(4)=5 exhaustively via the own order-type enumerator."""
    t0 = time.time()
    rng = random.Random(SEED)
    grids = GRIDS if mode == "full" else [(3, 3), (4, 4), (5, 5), (6, 6)]
    ot4, ot5 = {}, {}
    gp4_nonconv = 0
    gp5_total = 0
    fail_5 = 0
    split_ok = True
    split_done = 0
    raw4, raw5 = {}, {}   # raw sign vector -> representative (dedupe BEFORE
    # canonicalization: canonical_ot costs n! * C(n,3) crosses)
    for (w, h) in grids:
        grid = [(x, y) for x in range(w) for y in range(h)]
        if len(grid) > 40:
            continue
        for sub in itertools.combinations(grid, 4):
            sv = sign_vector(sub)
            if 0 in sv:
                continue  # not GP
            if sv not in raw4:
                raw4[sv] = sub
            if not has_convex_k(list(sub), 4, "A") or not has_convex_k(list(sub), 4, "B"):
                gp4_nonconv += 1  # a GP 4-set with NO convex 4 (the lower side)
        for sub in itertools.combinations(grid, 5):
            sv = sign_vector(sub)
            if 0 in sv:
                continue
            gp5_total += 1
            if sv not in raw5:
                raw5[sv] = sub
            okA = has_convex_k(list(sub), 4, "A")
            okB = has_convex_k(list(sub), 4, "B")
            if not (okA and okB):
                fail_5 += 1
        # the 2-1 split mechanism on hull-3 witnesses (sampled, in-grid):
        # the repaired ES_PACKAGE_PROOF.md §5 finish — the {a,b,p,q} 2-1-split
        # quadruple must be in convex position (both codes)
        if w * h >= 9:
            cnt = 0
            for sub in itertools.combinations(grid, 5):
                if cnt >= 25:
                    break
                sv = sign_vector(sub)
                if 0 in sv:
                    continue
                tri = hull_chain(sub)
                if len(tri) != 3:
                    continue
                hp = [q for q in sub if q not in tri]  # the 2 interior points
                # split triangle vertices by line pq (2 and 1)
                (p1, p2) = hp
                sides = [cross3(p1, p2, v) for v in tri]
                if 0 in sides:
                    continue  # GP violation guard (cannot happen)
                side_sign = [1 if x > 0 else -1 for x in sides]
                if side_sign.count(1) == 2:
                    ab = [tri[i] for i in range(3) if side_sign[i] == 1]
                elif side_sign.count(-1) == 2:
                    ab = [tri[i] for i in range(3) if side_sign[i] == -1]
                else:
                    continue
                quad = ab + [p1, p2]
                if not (convex_position(quad, "A") and convex_position(quad, "B")):
                    split_ok = False
                cnt += 1
                split_done += 1
    for sv, sub in raw4.items():
        ot4.setdefault(canonical_ot(sub), sub)
    for sv, sub in raw5.items():
        ot5.setdefault(canonical_ot(sub), sub)
    # anchors + both directions
    n4, n5 = len(ot4), len(ot5)
    ok = (n4 == ANCHOR_OT[4] and n5 == ANCHOR_OT[5] and gp4_nonconv > 0
          and fail_5 == 0 and split_ok and split_done > 0)
    # every 5-type rep: convex 4 by both codes (belt & braces on the reps)
    for k, rep in ot5.items():
        if not (has_convex_k(list(rep), 4, "A") and has_convex_k(list(rep), 4, "B")):
            ok = False
    # the banked 4-point witness: no convex 4, both codes
    w4_ok = (is_gp(W4_WITNESS) and not has_convex_k(W4_WITNESS, 4, "A")
             and not has_convex_k(W4_WITNESS, 4, "B"))
    det = (f"grids {[f'{w}x{h}({w*h})' for (w, h) in grids]}; "
           f"GP 5-sets swept: {gp5_total}; order types: n=4 -> {n4} (anchor 2), "
           f"n=5 -> {n5} (anchor 3); GP 4-sets with no convex 4: {gp4_nonconv} "
           f"(f(4) >= 5); GP 5-sets lacking a convex 4: {fail_5} (f(4) <= 5); "
           f"2-1-split quadruples convex: {split_done}/{split_done} both codes; "
           f"banked W4 witness no-convex-4 both codes: {w4_ok}")
    R(("PASS" if ok and w4_ok else "FAIL") + f" A1-OTF4 [wall {time.time()-t0:.1f}s] — {det}")
    return ok and w4_ok


def check_a2():
    """A2 — the banked 8-point no-convex-5 witnesses, both codes."""
    t0 = time.time()
    ok = True
    dets = []
    for name, W in (("kernel-w5", W5_KERNEL), ("interleaved", W5_INTERLEAVED)):
        gp = is_gp(W)
        nA, cA = no_convex_k(W, 5, "A")
        nB, cB = no_convex_k(W, 5, "B")
        # hull sizes: 4 both codes (the witness shape sanity)
        hA, hB = len(hull_chain(W)), len(hull_giftwrap(W))
        good = gp and nA and nB and cA == 56 and cB == 56 and hA == hB
        ok = ok and good
        dets.append(f"{name}: GP={gp}, no-convex-5 A={nA} ({cA}/56) B={nB} ({cB}/56), hull={hA}/{hB}")
    R(("PASS" if ok else "FAIL") + f" A2-W5WITNESS [wall {time.time()-t0:.1f}s] — " + "; ".join(dets))
    return ok


def _esandwich_n(n, mode="full"):
    """One ES-SANDWICH instance: build, certify structure, max-convex = n-1."""
    t0 = time.time()
    clusters, pts, par = build_Xn(n)
    m = par["m"]
    size_ok = len(pts) == 2 ** (n - 2)
    csize_ok = all(len(clusters[i]) == math.comb(m, i) for i in range(m + 1))
    pti, den = scale_to_int(pts)
    gp = is_gp(pti)
    # y-band order: y_i = (m-2i)/8 DECREASES in i, so cluster i+1 sits
    # strictly BELOW cluster i (disjoint ordered bands)
    yband_ok = all(max(q[1] for q in clusters[i + 1]) < min(q[1] for q in clusters[i])
                   for i in range(m))
    sep = slope_separation(clusters, par)
    pti_sorted = sorted(pti)
    # Lemma M spot check: middle-cluster points strictly right of line B-T
    lemM_ok = True
    lemM_cnt = 0
    rng = random.Random(SEED + n)
    flat = [(q, ci) for ci, T in enumerate(clusters) for q in T]
    for _ in range(400):
        k = rng.randrange(0, m)
        l = rng.randrange(k + 2, m + 1) if m >= k + 2 else None
        if l is None:
            continue
        i = rng.randrange(k + 1, l)
        Bc, Tc = clusters[l][rng.randrange(len(clusters[l]))], clusters[k][rng.randrange(len(clusters[k]))]
        for u in clusters[i]:
            # strictly RIGHT of the directed line B->T (B bottom, T top):
            # the arc bulges right, so cross3(B, T, u) < 0 must hold exactly
            if cross3(Bc, Tc, u) >= 0:
                lemM_ok = False
            lemM_cnt += 1
    # max convex = n-1
    wit_ok = False
    witB_ok = False
    # transversal = one point per cluster -> must be convex (n-1 points)
    for _ in range(200):
        tr = [T[rng.randrange(len(T))] for T in clusters]
        if convex_position(tr, "A"):
            wit_ok = True
            if convex_position(tr, "B"):
                witB_ok = True
                break
    if n <= 7:
        kA, cA = no_convex_k(pti_sorted, n, "A")
    else:
        kA, cA = True, 0
    if n == 6:
        kB, cB = no_convex_k(pti_sorted, n, "B")
    elif n == 7:
        if mode == "full":
            kB, cB = no_convex_k(pti_sorted, n, "B")
        else:
            # gate mode: systematic 1-in-59 sample (57k subsets), code B
            cnt = 0
            kB = True
            cB = 0
            for idx, sub in enumerate(itertools.combinations(pti_sorted, n)):
                if idx % 59:
                    continue
                cB += 1
                if convex_position(sub, "B"):
                    kB = False
                    break
    else:
        kB, cB = True, 0
    # n=8: randomized + hillclimb search for a convex 8 (must find none)
    hill_best = 0
    hill_hits = 0
    if n == 8:
        N = len(pti)
        best_overall = 0
        # random 8-subsets
        for _ in range(60000):
            sub = rng.sample(pti, 8)
            h = len(hull_chain(sub))
            if h == 8:
                hill_hits += 1
                break
            best_overall = max(best_overall, h)
        # hillclimb from random 8-subsets (fitness = hull count)
        for _ in range(400):
            cur = rng.sample(pti, 8)
            curset = set(cur)
            improved = True
            while improved:
                improved = False
                h0 = len(hull_chain(cur))
                best_overall = max(best_overall, h0)
                if h0 == 8:
                    hill_hits += 1
                    break
                for out_i in range(8):
                    if improved or h0 == 8:
                        break
                    for cand in pti:
                        if cand in curset:
                            continue
                        nxt = cur[:out_i] + [cand] + cur[out_i + 1:]
                        if len(hull_chain(nxt)) > h0:
                            cur = nxt
                            curset = set(cur)
                            improved = True
                            break
            best_overall = max(best_overall, len(hull_chain(cur)))
            if len(hull_chain(cur)) == 8:
                hill_hits += 1
        hill_best = best_overall
    # n<=5: full exhaustive both codes (tiny)
    ok = (size_ok and csize_ok and gp and yband_ok and sep["intra_ok"]
          and sep["inter_ok"] and sep["sigma_gt_half"] and sep["s_lt_half"]
          and sep["chain_ok"] and lemM_ok and lemM_cnt > 0 and wit_ok and witB_ok
          and kA and kB)
    if n == 8:
        ok = ok and (hill_hits == 0) and hill_best == 7
    extra = (f"n={n}: |X|={len(pts)} (want {2**(n-2)}), cluster sizes ok={csize_ok}, "
             f"GP={gp} (scale 1/{den}), y-bands ordered={yband_ok}; "
             f"slopes: intra_max={float(sep['intra_max']):.6f} <= s={float(par['s']):.6f}, "
             f"inter_min={'inf' if sep['inter_min'] is None else format(float(sep['inter_min']), '.6f')} "
             f">= sigma=1/(1+38rho)={float(sep['sigma']):.6f} > 1/2={sep['sigma_gt_half']}, "
             f"vertical pairs={sep['nvert']}, intra<1/2<sigma<=inter chain={sep['chain_ok']}; "
             f"LemmaM {lemM_cnt} checks ok={lemM_ok}; "
             + (f"no-convex-{n}: codeA {cA} subsets={kA}, codeB {cB} subsets={kB}"
                if n <= 7 else
                f"no-convex-8 search: hillclimb best={hill_best}, convex-8 hits={hill_hits}")
             + f"; convex-{n-1} transversal witness A={wit_ok} B={witB_ok}")
    R(("PASS" if ok else "FAIL") + f" A3-SANDWICH-N{n} [wall {time.time()-t0:.1f}s] — {extra}")
    return ok


def check_a3(mode="full"):
    """A3 — the ES-SANDWICH lower-side rebuild at n = 6, 7, 8 (+3,4,5 quick)."""
    ok = True
    for n in (3, 4, 5):
        clusters, pts, par = build_Xn(n)
        pti, _ = scale_to_int(pts)
        kA, cA = no_convex_k(sorted(pti), n, "A")
        kB, cB = no_convex_k(sorted(pti), n, "B")
        sep = slope_separation(clusters, par)
        good = (len(pts) == 2 ** (n - 2) and is_gp(pti) and kA and kB
                and sep["intra_ok"] and sep["inter_ok"])
        # at n=3,4 the doc's 's <= 1/64' does NOT hold (audit finding #3):
        # the load-bearing chain intra <= s < 1/2 < sigma <= |inter| does.
        s_le_64 = par["s"] <= F(1, 64)
        good = good and sep["chain_ok"]
        ok = ok and good
        R(("PASS" if good else "FAIL") +
          f" A3-SANDWICH-N{n} [wall 0s] — |X|={len(pts)}, GP={is_gp(pti)}, "
          f"no-convex-{n} A({cA})={kA} B({cB})={kB}, chain ok={sep['chain_ok']} "
          f"(s={float(par['s']):.5f} <= 1/64: {s_le_64} — holds iff n >= 5, audit finding #3)")
    for n in (6, 7, 8):
        ok = _esandwich_n(n, mode) and ok
    return ok


def _pascal_row(N):
    """Own Pascal triangle row (no math.comb)."""
    row = [1]
    for _ in range(N):
        row = [1] + [row[i] + row[i + 1] for i in range(len(row) - 1)] + [1]
    return row


def _comb2(n, k):
    """Second binomial code: memoized Pascal recursion (no math.comb)."""
    if k < 0 or k > n:
        return 0
    tab = {}
    def f(N, K):
        if K < 0 or K > N:
            return 0
        if K == 0 or K == N:
            return 1
        v = tab.get((N, K))
        if v is None:
            v = f(N - 1, K - 1) + f(N - 1, K)
            tab[(N, K)] = v
        return v
    return f(n, k)


def check_a4(mode="full"):
    """A4 — U-BIS closed form + instance checks + label census."""
    t0 = time.time()
    ok = True
    vals = {}
    for n in range(3, 12):
        dsum = sum(math.comb(u + v, u) for u in range(1, n - 1) for v in range(1, n - 1))
        dsum2 = sum(_comb2(u + v, u) for u in range(1, n - 1) for v in range(1, n - 1))
        closed = math.comb(2 * n - 2, n - 1) - 2 * n + 2
        closed2 = _comb2(2 * n - 2, n - 1) - 2 * n + 2
        G = closed + 1
        vals[n] = G + 1
        if not (dsum == dsum2 == closed == closed2):
            ok = False
        if not (G + 1 >= math.comb(2 * n - 4, n - 2) + 1):  # weaker than ES-ALLN
            ok = False
    expect = {3: 4, 4: 16, 5: 64, 6: 244, 7: 914, 8: 3420, 9: 12856, 10: 48604, 11: 184738}
    if any(vals[n] != expect[n] for n in expect):
        ok = False
    # extend to n = 12..30 with both codes
    for n in range(12, 31):
        dsum = sum(math.comb(u + v, u) for u in range(1, n - 1) for v in range(1, n - 1))
        if dsum != _comb2(2 * n - 2, n - 1) - 2 * n + 2:
            ok = False
    # instance checks (own DP + own convex codes):
    rng = random.Random(SEED + 4)

    def rand_gp(N, box=4000, tries=400000):
        for _ in range(tries):
            pts = [(rng.randrange(-box, box), rng.randrange(-box, box)) for _ in range(N)]
            if len(set(pts)) == N and is_gp(pts):
                return pts
        return None

    n16 = 0
    for _ in range(25 if mode == "full" else 10):
        S = rand_gp(16)
        if S is None:
            ok = False
            break
        if not has_convex_k(S, 4, "A"):
            ok = False
            break
        n16 += 1
    n64 = 0
    n64dp = 0
    census_ok = True
    rng2 = random.Random(SEED + 44)
    for _ in range(12 if mode == "full" else 5):
        S = rand_gp(64)
        if S is None:
            ok = False
            break
        Sh, _ = shear_distinct_x(S)
        mc, mp, cl, cp, p = max_cup_cap(Sh)
        if max(mc, mp) >= 5:
            n64dp += 1
            # exhibit an actual 5-chain by CAPPED random search (a random
            # 5-subset in x-order is a cup or cap with prob ~ 1/60), then
            # confirm convex 5 by BOTH codes
            found = False
            for _try in range(8000):
                sub = sorted(rng2.sample(p, 5))
                sl = [F(sub[t + 1][1] - sub[t][1], sub[t + 1][0] - sub[t][0]) for t in range(4)]
                if all(sl[t] < sl[t + 1] for t in range(3)) or all(sl[t] > sl[t + 1] for t in range(3)):
                    if convex_position(sub, "A") and convex_position(sub, "B"):
                        found = True
                    break
            if not found:
                ok = False
        else:
            ok = False
        # label census: |P_ij| <= C(i+j-2, i-1) (L-MLT(a), the U-BIS leg)
        lab = {}
        for i in range(len(p)):
            key = (cl[i], cp[i])
            lab[key] = lab.get(key, 0) + 1
        for (i, j), cnt in lab.items():
            if i >= 2 and j >= 2 and cnt > math.comb(i + j - 2, i - 1):
                census_ok = False
        n64 += 1
    ok = ok and census_ok and n16 >= 10 and n64dp == n64 and n64 >= 5
    det = (f"closed form G(n)+1 = C(2n-2,n-1)-2n+4 for n=3..11: "
           f"{[vals[n] for n in range(3, 12)]} (anchors 4,16,64,244,914 match ALLN_PROOF.md; "
           f"extends 8:3420 9:12856 10:48604 11:184738); double-sum == closed form "
           f"both binomial codes n=3..30; U-BIS >= ES-ALLN-SHARP every n; "
           f"instances: 16-pt GP sets with convex 4: {n16}/{n16}; 64-pt GP sets with "
           f"5-cup-or-cap by own DP: {n64dp}/{n64} (each chain convex by both codes); "
           f"label census |P_ij| <= C(i+j-2,i-1): {census_ok}")
    R(("PASS" if ok else "FAIL") + f" A4-UBIS [wall {time.time()-t0:.1f}s] — {det}")
    return ok


def check_a5():
    """A5 — the binomial table + gap law + sharpening recursion."""
    t0 = time.time()
    tbl = [math.comb(2 * n - 4, n - 2) + 1 for n in range(3, 31)]
    tbl2 = [_comb2(2 * n - 4, n - 2) + 1 for n in range(3, 31)]
    ok = tbl == tbl2
    anchors = [3, 7, 21, 71, 253, 925]
    if tbl[:6] != anchors:
        ok = False
    if not all(tbl[n - 3] >= 2 ** (n - 2) + 1 for n in range(3, 31)):
        ok = False
    # receipts107alln.txt S7 cross-check (n=3..8 fresh values)
    if tbl[:6] != [3, 7, 21, 71, 253, 925]:
        ok = False
    # gap ratios n=3..10 (ES_SANDWICH_ALLN.md §6)
    gaps = []
    for n in range(3, 11):
        g = F(math.comb(2 * n - 4, n - 2) + 1, 2 ** (n - 2) + 1)
        gaps.append(round(float(g), 2))
    if gaps != [1.0, 1.4, 2.33, 4.18, 7.67, 14.23, 26.61, 50.08]:
        ok = False
    # sharpening recursion r(n) = 2r(n-1) - 1 from r(3) = 3
    r = 3
    rec_ok = True
    for n in range(4, 31):
        r = 2 * r - 1
        if r != 2 ** (n - 2) + 1:
            rec_ok = False
    ok = ok and rec_ok
    # VANDERMONDE-DOUBLE (SHARP_PROOF.md §4, the repaired prose): the inner
    # hockey sum, the CORRECTED outer intermediate (stick to a+b-5, closes
    # at C(a+b-4,b-2)-1), and the final identity — both binomial codes
    # (math.comb vs a persistent-memo Pascal recursion), all 3<=a,b<=30
    vtab = {}

    def C2(nn, kk):
        if kk < 0 or kk > nn:
            return 0
        if kk == 0 or kk == nn:
            return 1
        v = vtab.get((nn, kk))
        if v is None:
            v = C2(nn - 1, kk - 1) + C2(nn - 1, kk)
            vtab[(nn, kk)] = v
        return v

    vd_inner = vd_outer = vd_final = True
    for a in range(3, 31):
        for b in range(3, 31):
            for u in range(0, a - 2):
                if sum(math.comb(u + v, u) for v in range(0, b - 2)) != math.comb(u + b - 2, u + 1):
                    vd_inner = False
                if sum(C2(u + v, u) for v in range(0, b - 2)) != C2(u + b - 2, u + 1):
                    vd_inner = False
            if sum(math.comb(u + b - 2, b - 3) for u in range(0, a - 2)) != math.comb(a + b - 4, b - 2) - 1:
                vd_outer = False
            if sum(C2(u + b - 2, b - 3) for u in range(0, a - 2)) != C2(a + b - 4, b - 2) - 1:
                vd_outer = False
            ff = sum(math.comb(i + j - 4, i - 2) for i in range(2, a) for j in range(2, b))
            if ff != math.comb(a + b - 4, a - 2) - 1 or ff != C2(a + b - 4, a - 2) - 1:
                vd_final = False
    ok = ok and vd_inner and vd_outer and vd_final
    det = (f"table n=3..30 two codes agree; n=3..8 = {tbl[:6]} (fresh, matches "
           f"receipts107alln S7); every value >= 2^(n-2)+1; gap ratios n=3..10 = "
           f"{gaps} (match ES_SANDWICH_ALLN.md §6); sharpening recursion "
           f"r(n)=2r(n-1)-1 telescopes to 2^(n-2)+1 for n=4..30: {rec_ok}; "
           f"VANDERMONDE-DOUBLE inner/outer-intermediate/final identities "
           f"(the repaired SHARP_PROOF.md §4 prose) both binomial codes, "
           f"all 3<=a,b<=30: {vd_inner and vd_outer and vd_final}")
    R(("PASS" if ok else "FAIL") + f" A5-BINOMTABLE [wall {time.time()-t0:.1f}s] — {det}")
    return ok


def _max_collinearity(pts):
    """t(S) = max number of points of S on one line (exact; integer pts)."""
    n = len(pts)
    if n <= 1:
        return n
    lines = {}
    for i in range(n):
        for j in range(i + 1, n):
            dx = pts[j][0] - pts[i][0]
            dy = pts[j][1] - pts[i][1]
            g = math.gcd(abs(dx), abs(dy))
            if g:
                dx //= g
                dy //= g
            if dx < 0 or (dx == 0 and dy < 0):
                dx, dy = -dx, -dy
            # canonical line key: primitive direction + the invariant
            # offset dx*y - dy*x (constant along the line)
            off = dx * pts[i][1] - dy * pts[i][0]
            lines.setdefault((dx, dy, off), set()).update((i, j))
    return max(len(v) for v in lines.values())


def _greedy_gp_extract(pts, m, order):
    """The GP-ELIM greedy (ES_PACKAGE_PROOF.md §7.3): repeatedly take the
    first point in `order` that is not forbidden (not on a line through
    two already-chosen points). Returns (chosen indices, per-stage
    forbidden-count log)."""
    chosen = []
    log = []
    for _ in range(m):
        j = len(chosen)
        cs = set(chosen)
        forb = set()
        for a in range(len(chosen)):
            for b in range(a + 1, len(chosen)):
                pa, pb = pts[chosen[a]], pts[chosen[b]]
                for ix in order:
                    if ix in cs or ix in forb:
                        continue
                    if cross3(pa, pb, pts[ix]) == 0:
                        forb.add(ix)
        log.append((j, len(forb)))
        nxt = None
        for ix in order:
            if ix not in cs and ix not in forb:
                nxt = ix
                break
        if nxt is None:
            break
        chosen.append(nxt)
    return chosen, log


def check_a8():
    """A8 — the two boundary lanes named by the W81-107B audit brief."""
    t0 = time.time()
    rng = random.Random(SEED + 8)
    ok = True
    grids = [(4, 4), (5, 5), (6, 6)]
    # ---------- (i) CC three-case extension lemma at the k=3/l=3 boundary
    stats = {}
    for (k, l) in ((3, 3), (3, 4), (4, 3)):
        N = math.comb(k + l - 4, k - 2) + 1
        n_sets = 0
        bad = 0
        for (w, h) in grids:
            grid = [(x, y) for x in range(w) for y in range(h)]
            for sub in itertools.combinations(grid, N):
                if len(set(p[0] for p in sub)) != N:  # CC premise: distinct x
                    continue
                sub = list(sub)
                if not is_gp(sub):
                    continue
                n_sets += 1
                mc, mp, _cl, _cp, _p = max_cup_cap(sub)
                bc = _brute_max_chain(sub, True)
                bp = _brute_max_chain(sub, False)
                if not (mc == bc and mp == bp):  # two codes agree
                    bad += 1
                if not (mc >= k or mp >= l):  # the CC statement at (k,l)
                    bad += 1
        stats[(k, l)] = (n_sets, bad)
        ok = ok and n_sets > 0 and bad == 0
    # the (3,3) X/Y-split + sigma/tau trichotomy mechanism on EVERY GP
    # x-distinct 3-set (the three-case lemma's moves, mechanized)
    mech_ok = True
    mech_n = 0
    for (w, h) in grids:
        grid = [(x, y) for x in range(w) for y in range(h)]
        for sub in itertools.combinations(grid, 3):
            if len(set(p[0] for p in sub)) != 3:
                continue
            sub = list(sub)
            if not is_gp(sub):
                continue
            p = sorted(sub)  # x-order p1 < p2 < p3
            cl, cp, _ps = cup_cap_dp(p)
            # Y = {cup = 1} = {leftmost}; cup(p2) = 2 (the pair (p1,p2))
            if not (cl[0] == 1 and cl[1] == 2 and cl[2] in (2, 3)):
                mech_ok = False
            tau = F(p[1][1] - p[0][1], p[1][0] - p[0][0])
            sigma = F(p[2][1] - p[1][1], p[2][0] - p[1][0])
            if tau == sigma:
                mech_ok = False  # GP forbids collinearity (must not happen)
            elif sigma > tau:
                # case 1: (p1,p2,p3) is a 3-cup (k=3 case of the lemma)
                if not (_brute_max_chain(p, True) >= 3 and cl[2] == 3):
                    mech_ok = False
            else:
                # case 2: (p1,p2,p3) is a 3-cap (l=3 case of the lemma)
                if not (_brute_max_chain(p, False) >= 3 and cp[2] == 3):
                    mech_ok = False
            # no-3-cup census: then |X| = |{cup = 2}| = 2 = C(1,1)+1 (the
            # IH trigger at (3,2)) and the 2-cap V = (p2,p3) lies in X
            if cl == [1, 2, 2] and not (sigma < tau):
                mech_ok = False
            mech_n += 1
    ok = ok and mech_ok and mech_n > 0
    # tightness: E(k,l) at the boundary (the bound is exact in both dirs)
    tight_ok = True
    for (k, l) in ((3, 3), (3, 4), (4, 3)):
        E = Eset(k, l, F(1, 64))
        if len(E) != math.comb(k + l - 4, k - 2):
            tight_ok = False
        if len(set(x for (x, _y) in E)) != len(E):
            tight_ok = False
        if not is_gp(E):
            tight_ok = False
        mc, mp, _cl, _cp, _p = max_cup_cap(E)
        bc = _brute_max_chain(E, True)
        bp = _brute_max_chain(E, False)
        if not (mc == bc and mp == bp and mc <= k - 1 and mp <= l - 1):
            tight_ok = False
    ok = ok and tight_ok
    # ---------- (ii) GP-ELIM at the N >= 2 boundary -----------------------
    gelim_ok = True
    census_ok = True
    gelim_runs = 0
    for _trial in range(24):
        board = []
        seen = set()
        for _ln in range(3):  # 3 planted lines with 4..6 integer points
            a = rng.randrange(-3, 4)
            b = rng.randrange(-40, 41)
            for x in range(rng.randrange(4, 7)):
                q = (7 * x + rng.randrange(0, 3), a * (7 * x) + b)
                if q not in seen:
                    seen.add(q)
                    board.append(q)
        while len(board) < 26:  # scattered points
            q = (rng.randrange(-200, 201), rng.randrange(-200, 201))
            if q not in seen:
                seen.add(q)
                board.append(q)
        order = list(range(len(board)))
        rng.shuffle(order)
        for m in (2, 3, 4, 5):
            # smallest prefix (in shuffle order) meeting the GP-ELIM
            # threshold with t MEASURED on that prefix
            N = None
            for take in range(m, len(board) + 1):
                prefix = [board[i] for i in order[:take]]
                t = _max_collinearity(prefix)
                if take >= (m - 1) + math.comb(m - 1, 2) * (t - 2) + 1:
                    N = take
                    tN = t
                    break
            if N is None:
                continue  # board too small for this m at its measured t
            prefix = [board[i] for i in order[:N]]
            chosen, log = _greedy_gp_extract(prefix, m, list(range(N)))
            if len(chosen) < m:
                gelim_ok = False
            for (j, nf) in log:  # Claim 2 census: forbidden <= C(j,2)(t-2)
                if nf > math.comb(j, 2) * (tN - 2):
                    census_ok = False
            gelim_runs += 1
    # degenerate lanes: t = 2 (S already GP), m = 1, m = 2 (the N >= 2 row)
    for _trial in range(6):
        S = []
        while len(S) < 12:
            q = (rng.randrange(-500, 500), rng.randrange(-500, 500))
            if q not in S and is_gp(S + [q]):
                S.append(q)
        if _max_collinearity(S) != 2:
            gelim_ok = False
        for m in (3, 4, 5):  # threshold at t=2 is exactly m
            chosen, _lg = _greedy_gp_extract(S[:m], m, list(range(m)))
            if len(chosen) < m:
                gelim_ok = False
            gelim_runs += 1
    one, _ = _greedy_gp_extract([(0, 0), (5, 7)], 1, [0, 1])
    two, _ = _greedy_gp_extract([(0, 0), (5, 7)], 2, [0, 1])
    if not (len(one) == 1 and len(two) == 2):
        gelim_ok = False
    # the all-collinear board: t = N, the m=3 threshold is N+1 — at
    # N = 8 = threshold-1 the greedy MUST stall below m (the +1 has teeth)
    line_pts = [(i, 2 * i + 1) for i in range(8)]
    tL = _max_collinearity(line_pts)
    thr3 = 2 + math.comb(2, 2) * (tL - 2) + 1
    stalled, _lg = _greedy_gp_extract(line_pts, 3, list(range(8)))
    if not (tL == 8 and thr3 == 9 and len(stalled) == 2):
        gelim_ok = False
    ok = ok and gelim_ok and census_ok and gelim_runs >= 40
    det = (f"CC at (3,3)/(3,4)/(4,3): threshold-size GP x-distinct sets "
           f"swept {stats[(3, 3)][0]}/{stats[(3, 4)][0]}/{stats[(4, 3)][0]}, "
           f"violations {stats[(3, 3)][1] + stats[(3, 4)][1] + stats[(4, 3)][1]} "
           f"(own DP + brute chains agree everywhere); the (3,3) X/Y-split + "
           f"sigma/tau trichotomy mechanism on {mech_n} 3-sets: {mech_ok}; "
           f"E(k,l) tightness (size C(k+l-4,k-2), no k-cup/l-cap, both codes): "
           f"{tight_ok}; GP-ELIM: {gelim_runs} greedy extractions at/above the "
           f"measured-t threshold all reached m: {gelim_ok}, per-stage forbidden "
           f"census <= C(j,2)(t-2): {census_ok}, degenerate lanes t=2/m=1/m=2 ok, "
           f"all-collinear board (t=8, m=3 threshold 9) stalls at 2 below "
           f"threshold (the +1 has teeth)")
    R(("PASS" if ok else "FAIL") + f" A8-BOUNDARIES [wall {time.time()-t0:.1f}s] — {det}")
    return ok


def check_a6():
    """A6 — the W81-107A comparison base: 3 seeded-random n=8 parents re-run
    through the campaign python v2 machinery (read-only import); realization
    + cell/child fingerprints dumped for the C-port comparison."""
    t0 = time.time()
    try:
        sys.path.insert(0, HERE)
        import engine107f5v2 as V2  # noqa: E402  (campaign v2; read-only)
        pkl = os.path.join(HERE, "engine107f5_cache", "ot8_v2.pkl")
        with open(pkl, "rb") as f:
            types8 = pickle_load(f)
        items = sorted(types8.items())  # deterministic order
        rng = random.Random(SEED + 6)
        picks = rng.sample(range(len(items)), 3)
        out = {"seed": SEED + 6, "parents": []}
        ok = True
        for pos in picks:
            key, rec = items[pos]
            n = len(rec["pts"])
            if n != 8:
                ok = False
                continue
            seed = 700000 + n * 131 + pos
            arg = (key, rec, seed, {"sweep": True, "walk": True, "walk_steps": 6})
            pkey, children, st = V2._parent_job_v2(arg)
            if children is None:
                ok = False
                continue
            chi = rec["chi"]
            # rebuild the exact parent realization used (shear + generic):
            prng = random.Random(seed)
            pts = V2.shear_distinct_x(rec["pts"])
            pts, _was = V2.make_arrangement_generic(pts, chi, prng)
            cellsigs = sorted(hashlib.sha256(repr(list(c)).encode()).hexdigest()[:16]
                              for c in sorted(children.values()))
            fp = hashlib.sha256(repr(cellsigs).encode()).hexdigest()[:16]
            parent_fp = hashlib.sha256(repr(sorted(children.keys())).encode()).hexdigest()[:16]
            out["parents"].append({
                "pos": pos, "key_head": str(key)[:24],
                "seed": seed, "cells": st.get("cells", 0),
                "children": len(children),
                "sweep_grabs": st.get("sweep_grabs", 0),
                "walk_cfgs": st.get("walk_cfgs", 0),
                "children_fp": parent_fp,
                "realization": [[str(c), str(d)] for (c, d) in pts],
            })
            if st.get("cells", 0) < 1 or len(children) < 1:
                ok = False
        with open(V2PARENT_DUMP, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=1)
        det = (f"3 seeded-random n=8 parents from the banked 3315-type census; "
               f"python v2 machinery re-run (cells + wall sweep + walk): " +
               "; ".join(f"pos {p['pos']}: cells={p['cells']}, children={p['children']}, "
                         f"sweep_grabs={p['sweep_grabs']}, walk_cfgs={p['walk_cfgs']}, "
                         f"fp={p['children_fp']}" for p in out["parents"]) +
               f"; realization + expectations dumped to audit_w81_v2parents.json "
               f"for the W81-107A C-port cell comparison")
        R(("PASS" if ok else "FAIL") + f" A6-V2RERUN [wall {time.time()-t0:.1f}s] — {det}")
        return ok
    except Exception as e:  # noqa: BLE001
        R(f"FAIL A6-V2RERUN [wall {time.time()-t0:.1f}s] — exception: {e!r}")
        return False


def pickle_load(f):
    import pickle
    return pickle.load(f)


def check_neg():
    """A7 — NEGATIVE CONTROLS (mandatory)."""
    t0 = time.time()
    ok = True
    dets = []
    # NC1: a planted convex 5 in a no-convex-5 witness MUST be found by both
    # codes. Deterministic single-point surgery on the interleaved witness:
    # move one cap-arc point far below the cup arc — the cup arc (4 points,
    # convex) plus the moved point and a neighbor form a convex 5.
    planted = None
    for (idx, nx, ny) in ((4, 1, -10 ** 7), (5, 3, -10 ** 7), (6, 5, -10 ** 7),
                          (4, 1, -10 ** 6), (5, 3, -10 ** 6)):
        W = list(W5_INTERLEAVED)
        W[idx] = (nx, ny)
        if not is_gp(W):
            continue
        if has_convex_k(W, 5, "A") and has_convex_k(W, 5, "B"):
            planted = (idx, nx, ny)
            break
    if planted is None:
        ok = False
        dets.append("NC1 no planted convex-5 found (build error)")
    else:
        dets.append(f"NC1 planted convex-5 (move point {planted[0]} to "
                    f"({planted[1]}, {planted[2]})) detected by BOTH codes")
    # NC2: a convex-6 hexagon MUST be found by the no-convex-6 scanner
    hexa = [(0, 0), (5, -1), (9, 3), (7, 9), (1, 10), (-3, 4)]
    if not (is_gp(hexa) and convex_position(hexa, "A") and convex_position(hexa, "B")):
        ok = False
        dets.append("NC2 hexagon build error")
    else:
        found = has_convex_k(hexa, 6, "A") and has_convex_k(hexa, 6, "B")
        if not found:
            ok = False
        dets.append(f"NC2 convex-6 hexagon detected by the subset scanner: {found}")
    # NC3: collinear injection MUST fail the GP check
    bad = [(0, 0), (1, 1), (2, 2), (3, 0)]
    if is_gp(bad):
        ok = False
    dets.append(f"NC3 collinear triple rejected by GP check: {not is_gp(bad)}")
    # NC4: the corrupted U-BIS form (- 2n + 2) MUST be rejected
    n = 7
    dsum = sum(math.comb(u + v, u) for u in range(1, n - 1) for v in range(1, n - 1))
    corrupt = math.comb(2 * n - 2, n - 1) - 2 * n + 2 - 1
    if dsum == corrupt:
        ok = False
    dets.append(f"NC4 corrupted closed form (G-1) rejected: {dsum != corrupt}")
    # NC5: a corrupted construction MUST violate the inter-separation:
    # translate the middle cluster of X_6 far right (+10, 0) — intra slopes
    # survive (translation-invariant) but cross-cluster slopes collapse
    # below sigma; the checker must FAIL (it is not vacuous)
    clusters, pts, par = build_Xn(6)
    mid = par["m"] // 2
    clusters[mid] = [(x + F(10), y) for (x, y) in clusters[mid]]
    sep = slope_separation(clusters, par)
    if sep["inter_ok"] or not sep["intra_ok"]:
        ok = False
    dets.append(f"NC5 translated-cluster corruption: inter-separation violated="
                f"{not sep['inter_ok']} while intra still ok={sep['intra_ok']} "
                f"(the slope-law checker has teeth)")
    # NC6: own DP must match brute force on random small sets
    rng = random.Random(SEED + 7)
    dp_ok = True
    for _ in range(40):
        while True:
            S = [(rng.randrange(-60, 60), rng.randrange(-60, 60)) for _ in range(8)]
            if len(set(S)) == 8 and is_gp(S):
                break
        Sh, _sh = shear_distinct_x(S)
        mc, mp, cl, cp, p = max_cup_cap(Sh)
        bc = _brute_max_chain(Sh, True)
        bp = _brute_max_chain(Sh, False)
        if mc != bc or mp != bp:
            dp_ok = False
            break
    if not dp_ok:
        ok = False
    dets.append(f"NC6 own cup/cap DP == brute-force chains on 40 random 8-sets: {dp_ok}")
    R(("PASS" if ok else "FAIL") + f" A7-NEGCONTROLS [wall {time.time()-t0:.1f}s] — " + "; ".join(dets))
    return ok


# ===========================================================================
# SECTION 3 — DRIVER
# ===========================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", default="verify",
                    choices=["a1", "a2", "a3", "a4", "a5", "a6", "a8",
                             "neg", "gate", "verify"])
    args = ap.parse_args()
    R(f"RECEIPTS — engine107audit_w81.py (W81-107B auditor/doubler engine) — "
      f"seed {SEED}; exact int/Fraction arithmetic; stage {args.stage}")
    R(f"start {time.strftime('%H:%M:%S')}; budget 8 min")
    stage = args.stage
    results = {}
    full = stage in ("verify", "a1", "a3", "a4")
    if stage in ("verify", "gate", "a1"):
        results["a1"] = check_a1("full" if full else "gate")
    if stage in ("verify", "gate", "a2"):
        results["a2"] = check_a2()
    if stage in ("verify", "gate", "a3"):
        results["a3"] = check_a3("full" if full else "gate")
    if stage in ("verify", "gate", "a4"):
        results["a4"] = check_a4("full" if full else "gate")
    if stage in ("verify", "gate", "a5"):
        results["a5"] = check_a5()
    if stage in ("verify", "gate", "a8"):
        results["a8"] = check_a8()
    if stage in ("verify", "a6"):  # gate skips the v2 re-run (cache-dependent)
        results["a6"] = check_a6()
    if stage in ("verify", "gate", "neg"):
        results["neg"] = check_neg()
    wall = time.time() - _T0
    allpass = all(results.values()) and results
    R(f"TOTAL: {sum(1 for v in results.values() if v)}/{len(results)} stage checks pass; "
      f"wall {wall:.1f}s (budget 480s: {'OK' if wall <= _TOL else 'OVER'})")
    R("AUDIT_ENGINE_GREEN=" + ("1" if allpass else "0"))
    return 0 if allpass else 1


if __name__ == "__main__":
    sys.exit(main())
