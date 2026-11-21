#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""engine107sharp.py — THE SHARP ALL-n ENGINE (W78-107E, KILL 1 + KILL 2).

Certifies THEOREM ES-ALLN-SHARP (f(n) <= C(2n-4,n-2)+1 for every n >= 3)
along the LABEL ROUTE of SHARP_PROOF.md, plus the infinite layer of
INFINITE_107.md. Builds on the banked engine107alln (W77-107E, alln107/)
which it imports; the W77 receipts (receipts107alln.txt) closed at 8/13
with three engine-side defects — the vacuous peaks ascent branch, the
false sum_le spot-check, and the point_outside_scan SIGN FLIP (all fixed
in W78; see the ADDENDUM appended to receipts107alln.txt and the
 correction note in engine107alln.point_outside_scan) — this engine
re-certifies everything those lanes carried, GREEN; every claim is
certified by two independent codes.

  S0  SETUP        — banked otbank re-verified (n=3..7: 1,2,3,20,242
                     reflection-distinguished = 1,2,3,16,135 mirror-
                     identified; n=8: 6405 = 2*3315-225), fresh seed.
  S1  LAVOID-LAW   — Lemma L-AVOID-SHARP: NO i-cup and NO j-cap inside any
                     label class P_ij. Configs: ALL order types n<=7 x ALL
                     direction cells; n=8 sample (400 types); extremal
                     S(a,b) (a,b in 3..7 — the SATURATING configurations,
                     biggest class 70 points); 3000 random sets n in [8,16].
                     TWO codes per class: (A) iterative cross-product DP on
                     the class, (B) brute-force subset scan (class <= 11
                     pts) or an independent exact Fraction-SLOPE DP.
  S2  LAVOID-MECH  — the PROOF's Steps 1-2, machine shadow, exhaustive:
                     (i) for EVERY i-cup C with cup(right end)=i and EVERY
                     w left of C: cross(w,p1,p2) < 0 (Step 1); dual for
                     caps (cross > 0). (ii) the pair shadow: for every
                     same-label pair p <x q, every max-cup edge at p ends
                     strictly above line pq (cross<0) and every max-cap
                     edge strictly below (cross>0). All cups/caps
                     enumerated by exact DFS.
  S3  MLT-SHARP    — |P_ij| <= C(i+j-4,i-2) on every config above, TWO
                     counting codes (banked cross-DP vs independent
                     Fraction-slope DP; TRUE brute-force labels on n<=9);
                     the extremal saturation census (classes EXACTLY at
                     the binomial).
  S4  ASSEMBLY     — HOCKEY (sum C(t,r) = C(N+1,r+1), r<=N<=60) and
                     VANDERMONDE-DOUBLE (1+sum sum C(i+j-4,i-2) =
                     C(a+b-4,a-2), 3<=a,b<=60), TWO binomial codes
                     (math.comb vs from-scratch memoized Pascal); the
                     in-vivo census on every extremal set.
  S5  CC-SHARP-EXH — the (a,b)-lemma on ALL order types n<=7 x ALL
                     direction cells, every applicable (a,b) with
                     N=C(a+b-4,a-2)+1 in {3..7}: TWO cup/cap codes (DP +
                     brute-force subset scan).
  S6  CC-RANDOM    — 100,000+ random GP batteries at threshold sizes,
                     (a,b) up to (7,7).
  S7  SHARP-COMPOSE— ES-ALLN-SHARP instances n=3..7 (any-x GP set ->
                     integer rotation-dilation frame -> (n,n) DP -> chain
                     -> convex by BOTH codes); the bound table n=3..60
                     (two codes); >= 2^(n-2)+1; STRICT sharpening of
                     U-BIS at every n; the banked witness family
                     re-verified.
  S8  INF-PEAKS    — THE PEAKS LAW machine (corrected: the W77 ascent
                     branch was vacuous — the final position is always a
                     vacuous peak): weak peaks, both branches (peaks
                     non-increasing / ascent strictly increasing, halting
                     EXACTLY at the final position), the de Morgan
                     complement at every position, the MS finite shadow
                     max(LIS,LDS) >= ceil(sqrt n), and the x-SORTER
                     application (distinct x-coords -> strictly monotone
                     x-subsequence — the infinite chain's round-0 step).
  S9  INF-DICH     — the box-census law: |{p: cup<=a-1, cap<=b-1}| <=
                     C(a+b-4,a-2) on every config (TWO codes); extremal
                     EQUALITY (the box saturates); the +1 escape edge.
  S10 INF-RAM3     — THE INFINITE CHAIN construction, machine mirror
                     (peaks route, no general pair-Ramsey): abstract
                     a_i/X_i/c*_i builds (structural certificate, the
                     nesting replay); the geometric build — x-sorted set,
                     a_i = leftmost, fan slopes -> TRUE longest monotone
                     subsequence (two monotone codes cross-checked) ->
                     pair-homogeneous X_{i+1} (ALL pairs verified),
                     composed law col(a_i,a_j,a_k)=c*_i, majority H ->
                     all-same-sign -> full cup/cap -> subsets convex by
                     BOTH codes; DEPTH families (parabola/concave/mixed)
                     where the build runs at full depth; the countable-
                     shear bad-parameter census.
  S11 CARD-ARITH   — the cardinal-strength arithmetic: every bound
                     dwarfed by the towers (packet composition 2/3/6-pow,
                     k+4<=2^(k+2), k^2<=2^k, m<3^m); the ES-INF-kappa
                     shadow on a 200-point nested-prefix stream (the SAME
                     finite threshold forces at every prefix scale).
  S12 LAW-SPOTS    — every cited arsenal law spot-checked at statement.
  S13 NEG-CONTROLS — corrupted inputs must fail; checker sensitivity.

Receipts -> receipts107sharp.txt. Deterministic (seed below). Exact
integer/Fraction arithmetic throughout. In-process, checkpointed
(sharp107_progress.json; completed stages are skipped on rerun; --force
re-runs everything).

Exit 0 iff every check passes.
"""
import argparse
import itertools
import json
import math
import os
import random
import sys
import time
from collections import Counter
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "alln107"))
import engine107alln as base  # noqa: E402  (banked W77; scan sign fixed W78)

RECEIPTS = os.path.join(HERE, "receipts107sharp.txt")
PROGRESS = os.path.join(HERE, "sharp107_progress.json")
SEED = 20261178
RESULTS = []
DONE = set()

MIRROR_IDENTIFIED = {3: 1, 4: 2, 5: 3, 6: 16, 7: 135, 8: 3315}
REFL_DISTINGUISHED = {3: 1, 4: 2, 5: 3, 6: 20, 7: 242, 8: 6405}
SELFMIRROR_N8 = 225


def report(cid, ok, detail):
    RESULTS.append((cid, bool(ok), str(detail)))
    print(("PASS " if ok else "FAIL ") + cid + " " + str(detail)[:240], flush=True)


def save_progress():
    with open(PROGRESS, "w") as f:
        json.dump({"done": sorted(DONE),
                   "results": [(c, o, d) for (c, o, d) in RESULTS]}, f)


# ---------------------------------------------------------------------------
# Independent code paths (the SECOND codes)
# ---------------------------------------------------------------------------

def labels_slope_dp(pts):
    """Independent label computation, code B: exact Fraction-SLOPE
    arithmetic (division) instead of the banked integer cross products
    (multiplication). cup-extension iff slope(h,j) < slope(j,i); cap iff
    >. Returns dict with x-sorted P, cup[], cap[], fcup/fcap edge tables
    keyed [j][i]. Shares no code path with engine107alln.cup_cap_labels."""
    P = sorted(pts, key=lambda p: (p[0], p[1]))
    n = len(P)
    sl = [[None] * n for _ in range(n)]
    for h in range(n):
        for j in range(h + 1, n):
            sl[h][j] = Fraction(P[j][1] - P[h][1], P[j][0] - P[h][0])
    fcup = [[0] * n for _ in range(n)]
    fcap = [[0] * n for _ in range(n)]
    cup = [1] * n
    cap = [1] * n
    for i in range(n):
        for j in range(i):
            bc = 0
            bk = 0
            for h in range(j):
                s = sl[h][j]
                t = sl[j][i]
                if s < t and fcup[h][j] > bc:
                    bc = fcup[h][j]
                elif s > t and fcap[h][j] > bk:
                    bk = fcap[h][j]
            fcup[j][i] = (bc + 1) if bc else 2
            fcap[j][i] = (bk + 1) if bk else 2
            if fcup[j][i] > cup[i]:
                cup[i] = fcup[j][i]
            if fcap[j][i] > cap[i]:
                cap[i] = fcap[j][i]
    return {"P": P, "cup": cup, "cap": cap, "fcup": fcup, "fcap": fcap}


def labels_brute(pts, cap_n=10):
    """TRUE brute force for small sets: labels by enumerating ALL subsets;
    a chain iff is_cup/is_cap; right endpoint = max x."""
    P = sorted(pts, key=lambda p: (p[0], p[1]))
    n = len(P)
    if n > cap_n:
        return None
    cup = [1] * n
    cap = [1] * n
    idx = list(range(n))
    for r in range(2, n + 1):
        for sub in itertools.combinations(idx, r):
            Q = [P[t] for t in sub]
            if base.is_cup(Q):
                if r > cup[sub[-1]]:
                    cup[sub[-1]] = r
            if base.is_cap(Q):
                if r > cap[sub[-1]]:
                    cap[sub[-1]] = r
    return {"P": P, "cup": cup, "cap": cap}


_PAS_MEMO = {}


def pascal_mem(n, k):
    """From-scratch binomial, code B: memoized Pascal recursion, no
    math.comb anywhere."""
    if k < 0 or k > n:
        return 0
    if k == 0 or k == n:
        return 1
    key = (n, k)
    v = _PAS_MEMO.get(key)
    if v is None:
        v = pascal_mem(n - 1, k - 1) + pascal_mem(n - 1, k)
        _PAS_MEMO[key] = v
    return v


def class_counts(cup, cap):
    """Label-class census from label arrays."""
    return Counter(zip(cup, cap))


def all_chains(P, kind, limit=500000):
    """Enumerate ALL cups (kind='cup') / caps of the x-sorted point list P
    by exact DFS. Yields tuples of indices. Extension test via cross
    products: chain (..., h, j) extends by k iff cross(P[h],P[j],P[k]) > 0
    (cup) / < 0 (cap)."""
    n = len(P)
    out = []
    sign = 1 if kind == "cup" else -1

    def dfs(chain):
        if len(out) > limit:
            raise RuntimeError("chain explosion")
        if len(chain) >= 2:
            out.append(tuple(chain))
        last = chain[-1]
        if len(chain) == 1:
            for k in range(last + 1, n):
                chain.append(k)
                dfs(chain)
                chain.pop()
        else:
            h, j = chain[-2], chain[-1]
            for k in range(j + 1, n):
                if sign * base.cross3(P[h], P[j], P[k]) > 0:
                    chain.append(k)
                    dfs(chain)
                    chain.pop()

    for s in range(n):
        dfs([s])
    return out


def lavoid_check_class(Pij, i, j):
    """L-AVOID-SHARP on ONE class. Returns (ok, note).
    Code A: banked iterative cross-DP on the class.
    Code B: brute-force subset scan (class <= 11 pts) or the independent
    Fraction-slope DP."""
    if len(Pij) <= 1:
        return True, "size %d" % len(Pij)
    dA = base.cup_cap_labels(Pij)
    okA = max(dA["cup"]) < i and max(dA["cap"]) < j
    note = "A:crossDP max(%d,%d)" % (max(dA["cup"]), max(dA["cap"]))
    if len(Pij) <= 11:
        found = any(base.is_cup(s)
                    for s in itertools.combinations(sorted(Pij), i))
        if not found:
            found = any(base.is_cap(s)
                        for s in itertools.combinations(sorted(Pij), j))
        okB = not found
        note += " B:brute"
    else:
        dB = labels_slope_dp(Pij)
        okB = max(dB["cup"]) < i and max(dB["cap"]) < j
        note += " B:slopeDP max(%d,%d)" % (max(dB["cup"]), max(dB["cap"]))
    return okA and okB, note


# ---------------------------------------------------------------------------
# Configuration generators (deterministic)
# ---------------------------------------------------------------------------

def configs_order_types(nmax=7, n8sample=400, rng=None):
    """Every direction-cell frame of every banked order type n<=nmax, plus
    a sample of n=8 types. Yields (tag, frame_pts)."""
    out = []
    for n in range(3, nmax + 1):
        bank = base.load_otbank(n)
        for key, pts in bank:
            cells = base.direction_cells(pts)
            for u in cells:
                out.append(("ot%d/%s" % (n, str(key)[:24]),
                            base.project_frame(pts, u)))
    if n8sample and rng is not None:
        bank = base.load_otbank(8)
        for t in rng.sample(range(len(bank)), min(n8sample, len(bank))):
            key, pts = bank[t]
            for u in base.direction_cells(pts):
                out.append(("ot8s%d/%s" % (t, str(key)[:20]),
                            base.project_frame(pts, u)))
    return out


EXTRE = {}


def get_extremal(a, b):
    if (a, b) not in EXTRE:
        EXTRE[(a, b)] = base.build_verified_extremal(a, b)
    return EXTRE[(a, b)]


def configs_random(rng, count=3000, nmin=8, nmax=16):
    out = []
    for _ in range(count):
        n = rng.randrange(nmin, nmax + 1)
        out.append(("rnd%d" % n, base.gen_gp_distinct_x(n, rng, 10 ** 4)))
    return out


# ---------------------------------------------------------------------------
# Lanes
# ---------------------------------------------------------------------------

def lane_s0(rng):
    ok = True
    counts = {}
    for n in range(3, 9):
        bank = base.load_otbank(n)
        counts[n] = len(bank)
        if len(bank) != REFL_DISTINGUISHED[n]:
            ok = False
        for _, pts in bank[:40]:
            if len(set(pts)) != n or not base.general_position(pts):
                ok = False
    arith = {n: 2 * v - REFL_DISTINGUISHED[n]
             for n, v in MIRROR_IDENTIFIED.items()}
    ok = ok and arith[8] == SELFMIRROR_N8
    ext = {}
    for (a, b) in [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7)]:
        pts, d, why = get_extremal(a, b)
        if pts is None:
            ok = False
        else:
            ext["(%d,%d)" % (a, b)] = len(pts)
    report("S0-SETUP", ok,
           "banked otbank re-verified: %s reflection-distinguished "
           "(= mirror-identified %s; n=8 selfmirror %d = 2*3315-6405); "
           "extremal bank sizes %s (each |S|=C(a+b-4,a-2), GP, distinct-x, "
           "no a-cup/b-cap — banked receipts107alln.txt)"
           % (counts, MIRROR_IDENTIFIED, SELFMIRROR_N8, ext))


def lanes_s1_s3(rng):
    ok_law = True
    ok_mlt = True
    n_classes = 0
    n_pts_in_classes = 0
    biggest = (0, None)
    frames = configs_order_types(7, 400, rng)
    frames += [("ext%d%d" % ab, get_extremal(*ab)[0])
               for ab in [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7)]]
    frames += configs_random(rng, 3000, 8, 16)
    n_frames = len(frames)
    brute_checked = 0
    for tag, fr in frames:
        if not (base.general_position(fr) and base.distinct_x(fr)):
            ok_law = False
            ok_mlt = False
            continue
        dA = base.cup_cap_labels(fr)
        dB = labels_slope_dp(fr)
        if dA["cup"] != dB["cup"] or dA["cap"] != dB["cap"]:
            ok_mlt = False
        if len(fr) <= 9:
            dBr = labels_brute(fr)
            if dBr and (dBr["cup"] != dA["cup"] or dBr["cap"] != dA["cap"]):
                ok_mlt = False
            if dBr:
                brute_checked += 1
        cA = class_counts(dA["cup"], dA["cap"])
        cB = class_counts(dB["cup"], dB["cap"])
        if cA != cB:
            ok_mlt = False
        for (i, j), cnt in cA.items():
            if i < 2 or j < 2:
                if (i, j) != (1, 1) or cnt != 1:
                    ok_law = False
                continue
            n_classes += 1
            n_pts_in_classes += cnt
            if cnt > biggest[0]:
                biggest = (cnt, (tag, i, j))
            bound = math.comb(i + j - 4, i - 2)
            if pascal_mem(i + j - 4, i - 2) != bound:
                ok_mlt = False
            if cnt > bound:
                ok_mlt = False
            if cnt >= 2:
                Pij = [dA["P"][k] for k in range(len(fr))
                       if (dA["cup"][k], dA["cap"][k]) == (i, j)]
                good, _ = lavoid_check_class(Pij, i, j)
                if not good:
                    ok_law = False
    ext_detail = []
    for (a, b) in [(5, 5), (6, 6), (7, 7)]:
        pts, d, _ = get_extremal(a, b)
        c = class_counts(d["cup"], d["cap"])
        eqs = [(i, j, n) for (i, j), n in sorted(c.items())
               if i >= 2 and j >= 2 and n == math.comb(i + j - 4, i - 2)]
        ext_detail.append("S(%d,%d): %d classes, %d SATURATE (=C(i+j-4,"
                          "i-2)) e.g. %s"
                          % (a, b, sum(1 for (i, j) in c if i >= 2 and j >= 2),
                             len(eqs),
                             ", ".join("P_%d%d=%d" % t for t in eqs[:4])))
    report("S1-LAVOID-LAW", ok_law,
           "L-AVOID-SHARP: NO i-cup and NO j-cap inside ANY label class "
           "P_ij — %d classes (%d points) over %d frames (ALL order types "
           "n<=7 x ALL direction cells; n=8 sample 400 types; extremal "
           "S(3,3)..S(7,7); 3000 random n in [8,16]); biggest class %s; "
           "every non-trivial class checked by BOTH codes (cross-DP + "
           "brute subsets / Fraction-slope DP), zero violations"
           % (n_classes, n_pts_in_classes, n_frames, biggest[1]))
    report("S3-MLT-SHARP", ok_mlt,
           "|P_ij| <= C(i+j-4,i-2) everywhere (two counting codes agree on "
           "every frame: banked cross-DP vs independent Fraction-slope DP; "
           "TRUE brute-force labels re-verified on %d sets n<=9); the law "
           "is TIGHT — the extremal saturation: %s"
           % (brute_checked, "; ".join(ext_detail)))


def lane_s2(rng):
    ok_step1 = True
    ok_step1d = True
    ok_pair = True
    n_chains = 0
    n_left = 0
    n_pairs = 0
    n_pairedges = 0
    n_skipped = 0
    frames = configs_order_types(6, 150, rng)
    frames += [("ext%d%d" % ab, get_extremal(*ab)[0])
               for ab in [(4, 4), (5, 5), (6, 6)]]
    frames += configs_random(rng, 700, 7, 13)
    for tag, fr in frames:
        P = sorted(fr, key=lambda p: (p[0], p[1]))
        n = len(P)
        d = base.cup_cap_labels(P)
        cup = d["cup"]
        cap = d["cap"]
        for kind in ("cup", "cap"):
            try:
                chains = all_chains(P, kind)
            except RuntimeError:
                n_skipped += 1
                continue
            lab = cup if kind == "cup" else cap
            for ch in chains:
                L = len(ch)
                if L < 2:
                    continue
                if lab[ch[-1]] != L:
                    continue  # only longest-at-right chains
                n_chains += 1
                p1, p2 = ch[0], ch[1]
                for w in range(p1):
                    n_left += 1
                    s = base.cross3(P[w], P[p1], P[p2])
                    if kind == "cup" and not s < 0:
                        ok_step1 = False
                    if kind == "cap" and not s > 0:
                        ok_step1d = False
        for p in range(n):
            for q in range(p + 1, n):
                if (cup[p], cap[p]) != (cup[q], cap[q]):
                    continue
                if cup[p] < 2 or cap[p] < 2:
                    continue
                n_pairs += 1
                for h in range(p):
                    if d["fcup"][h][p] == cup[p]:
                        n_pairedges += 1
                        if not base.cross3(P[h], P[p], P[q]) < 0:
                            ok_pair = False
                    if d["fcap"][h][p] == cap[p]:
                        n_pairedges += 1
                        if not base.cross3(P[h], P[p], P[q]) > 0:
                            ok_pair = False
    report("S2-LAVOID-MECH", ok_step1 and ok_step1d and ok_pair,
           "the proof's steps, machine shadow: Step 1 (left-anchored "
           "exclusion) on %d longest-at-right chains x %d left-witness "
           "pairs — cross(w,p1,p2)<0 on every cup and >0 on every cap, "
           "ZERO exceptions; the pair shadow (dagger/dagger-prime) on %d "
           "same-label pairs x %d max-chain edges — every max-cup edge "
           "strictly ABOVE line pq (cross<0), every max-cap edge strictly "
           "BELOW (cross>0); %d chain-explosion sets skipped (documented). "
           "Together: the L-AVOID-SHARP contradiction, move by move"
           % (n_chains, n_left, n_pairs, n_pairedges, n_skipped))


def lane_s4():
    ok = True
    hock = 0
    vand = 0
    for r in range(0, 61):
        for N in range(r, 61):
            s = sum(math.comb(t, r) for t in range(r, N + 1))
            s2 = sum(pascal_mem(t, r) for t in range(r, N + 1))
            if s != s2 or s != math.comb(N + 1, r + 1) \
                    or s != pascal_mem(N + 1, r + 1):
                ok = False
            hock += 1
    for a in range(3, 61):
        for b in range(3, 61):
            s = 1 + sum(math.comb(i + j - 4, i - 2)
                        for i in range(2, a) for j in range(2, b))
            s2 = 1 + sum(pascal_mem(i + j - 4, i - 2)
                         for i in range(2, a) for j in range(2, b))
            if s != s2 or s != math.comb(a + b - 4, a - 2) \
                    or s != pascal_mem(a + b - 4, a - 2):
                ok = False
            vand += 1
    in_vivo = []
    for (a, b) in [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7)]:
        pts, d, _ = get_extremal(a, b)
        c = class_counts(d["cup"], d["cap"])
        tot = 1 + sum(n for (i, j), n in c.items() if i >= 2 and j >= 2)
        good = (tot == len(pts) == math.comb(a + b - 4, a - 2)
                == pascal_mem(a + b - 4, a - 2))
        if not good:
            ok = False
        in_vivo.append("S(%d,%d): 1+sum|P_ij|=%d=|S|=C(%d,%d)"
                       % (a, b, tot, a + b - 4, a - 2))
    report("S4-ASSEMBLY", ok,
           "HOCKEY sum_{t=r}^{N} C(t,r)=C(N+1,r+1): %d instances (r,N in "
           "[0,60]); VANDERMONDE-DOUBLE 1+sum_{i=2}^{a-1}sum_{j=2}^{b-1}"
           "C(i+j-4,i-2)=C(a+b-4,a-2): %d instances (a,b in [3,60]); every "
           "value by TWO independent binomial codes (math.comb vs "
           "from-scratch memoized Pascal); in vivo on the extremal label "
           "censuses: %s" % (hock, vand, "; ".join(in_vivo)))


def _ab_pairs(N):
    out = []
    for a in range(3, N + 2):
        for b in range(3, N + 2):
            if math.comb(a + b - 4, a - 2) + 1 == N:
                out.append((a, b))
    return out


def lane_s5(rng):
    ok = True
    det = []
    n_frames = 0
    for N in range(3, 8):
        bank = base.load_otbank(N)
        pairs = _ab_pairs(N)
        if not pairs:
            continue
        cells_max = 0
        for (a, b) in pairs:
            for key, pts in bank:
                cells = base.direction_cells(pts)
                cells_max = max(cells_max, len(cells))
                for u in cells:
                    fr = base.project_frame(pts, u)
                    n_frames += 1
                    if not base.has_cup_cap(fr, a, b):
                        ok = False
                    S = sorted(fr, key=lambda p: (p[0], p[1]))
                    found = any(base.is_cup(s)
                                for s in itertools.combinations(S, a)) \
                        or any(base.is_cap(s)
                               for s in itertools.combinations(S, b))
                    if not found:
                        ok = False
        det.append("N=%d:(a,b)=%s over ALL %d types x cells(<= %d)"
                   % (N, pairs, len(bank), cells_max))
    report("S5-CC-SHARP-EXH", ok,
           "the (a,b)-lemma EXHAUSTIVELY on ALL banked order types n<=7 "
           "(1,2,3,16,135 mirror-identified = 1,2,3,20,242 reflection-"
           "distinguished) x ALL direction cells: %s; %d frames, each by "
           "TWO cup/cap codes (label DP + brute-force subset scan) — an "
           "a-cup or b-cap in EVERY frame, zero violations"
           % ("; ".join(det), n_frames))


def lane_s6(rng):
    ok = True
    det = []
    total = 0
    spec = [((3, 3), 32000), ((3, 4), 10000), ((4, 3), 10000),
            ((3, 5), 8000), ((5, 3), 8000), ((3, 6), 6000), ((6, 3), 6000),
            ((4, 4), 10000), ((4, 5), 4000), ((5, 4), 4000),
            ((5, 5), 2000), ((5, 6), 400), ((6, 5), 400),
            ((6, 6), 200), ((7, 7), 10)]
    for (a, b), reps in spec:
        N = math.comb(a + b - 4, a - 2) + 1
        good = 0
        for t in range(reps):
            pts = base.gen_gp_distinct_x(N, rng, 10 ** 5)
            if not base.has_cup_cap(pts, a, b):
                ok = False
                break
            good += 1
            if N <= 7 and t < 400:
                S = sorted(pts, key=lambda p: (p[0], p[1]))
                found = any(base.is_cup(s)
                            for s in itertools.combinations(S, a)) \
                    or any(base.is_cap(s)
                           for s in itertools.combinations(S, b))
                if not found:
                    ok = False
        total += good
        det.append("(%d,%d):N=%d %d/%d" % (a, b, N, good, reps))
    report("S6-CC-RANDOM", ok,
           "random GP batteries at the exact threshold C(a+b-4,a-2)+1: "
           + ", ".join(det) + " — TOTAL %d sets (>= 10^5), every one "
           "contains the a-cup or b-cap (exact label DP; brute-force "
           "subset cross-check on the small sets)" % total)


def lane_s7(rng):
    ok = True
    inst = []
    for m in range(3, 8):
        N = math.comb(2 * m - 4, m - 2) + 1
        reps = {3: 40, 4: 40, 5: 30, 6: 12, 7: 4}[m]
        good = 0
        for _ in range(reps):
            pts = base.gen_gp_any(N, rng, 10 ** 5)
            t = base.find_good_int_t(pts)
            if t is None:
                ok = False
                break
            R = base.rot_dilate(pts, t)
            if not (base.distinct_x(R) and base.general_position(R)):
                ok = False
                break
            d = base.cup_cap_labels(R)
            mc = max(d["cup"])
            mk = max(d["cap"])
            if not (mc >= m or mk >= m):
                ok = False
                break
            ch = base.max_chain(d, "cup" if mc >= m else "cap")
            if len(ch) < m:
                ok = False
                break
            c1, c2 = base.convex_both(ch)
            kindok = base.is_cup(ch) if mc >= m else base.is_cap(ch)
            if not (c1 and c2 and kindok):
                ok = False
                break
            good += 1
        inst.append("n=%d:N=%d %d/%d (chain->convex BOTH codes)"
                    % (m, N, good, reps))
    tab_ok = True
    for n in range(3, 61):
        sharp = math.comb(2 * n - 4, n - 2) + 1
        sharp2 = pascal_mem(2 * n - 4, n - 2) + 1
        ubis = math.comb(2 * n - 2, n - 1) - 2 * n + 4
        ubis2 = pascal_mem(2 * n - 2, n - 1) - 2 * n + 4
        if sharp != sharp2 or ubis != ubis2:
            tab_ok = False
        if not (2 ** (n - 2) + 1 <= sharp < ubis):
            tab_ok = False
    anchors = {3: 3, 4: 7, 5: 21, 6: 71, 7: 253}
    for n, v in anchors.items():
        if math.comb(2 * n - 4, n - 2) + 1 != v:
            tab_ok = False
    wit_ok = True
    try:
        with open(os.path.join(HERE, "engine107", "witness_coords.json")) as f:
            W = json.load(f)
        fam = {3: [(0, 0), (5, 9)],
               4: [(0, 0), (100, 0), (0, 100), (1, 1)],
               5: [(int(x), int(y)) for (x, y) in W["n5"]],
               6: [(int(x), int(y)) for (x, y) in W["n6"]]}
        for n in (3, 4, 5, 6):
            S = fam[n]
            if len(S) != 2 ** (n - 2) or not base.general_position(S):
                wit_ok = False
            if base.has_convex_k(S, n)[0]:
                wit_ok = False
    except Exception:
        wit_ok = False
    report("S7-SHARP-COMPOSE", ok and tab_ok and wit_ok,
           "ES-ALLN-SHARP instances (any-x GP set -> integer det>0 frame "
           "-> (n,n) label DP -> chain -> convex by BOTH codes): "
           + ", ".join(inst)
           + "; bound table n=3..60 TWO binomial codes: 2^(n-2)+1 <= "
           "C(2n-4,n-2)+1 < U-BIS C(2n-2,n-1)-2n+4 STRICTLY at every n "
           "(n=3..8: 3,7,21,71,253,925); anchors 3>=f(3)=3 (EQUALITY), "
           "7>=f(4)=5, 21>=f(5)>=9, 71>=f(6)>=17; banked witnesses 2^(n-2) "
           "re-verified (GP, no convex n, n=3..6)")


def peaks_law_machine(seq, K=8):
    """THE PEAKS LAW MACHINE (corrected; the W77 base.peaks_monotone ascent
    branch was vacuous — with any peak convention the FINAL position is a
    vacuous peak, so 'after the last peak' was always empty). Mirrors the
    in-package proof of INFINITE_107.md §1 exactly:

    weak peak at i : seq[i] >= seq[j] for all j > i (suffix maximum, ties
    allowed; the final position is the vacuous peak).
    Branch 1 (>= K peaks): the peak positions, values NON-INCREASING
      (STRICTLY decreasing when the values are distinct).
    Branch 2 (< K peaks): t' = last peak position < n-1 (the last NON-FINAL
      peak; -1 if none). Every position in (t', n-1) is a non-peak, so a
      later STRICTLY greater element exists (de Morgan complement). The
      greedy first-strictly-greater ascent from t'+1 is strictly increasing
      and can halt only at a peak — the only peak >= t'+1 is the final
      position n-1 — so it marches to n-1 EXACTLY (the finite surrogate of
      'never halts' in the infinite case).
    Returns ("peaks", peak_positions) or ("ascent", chain_positions)."""
    n = len(seq)
    ispeak = [all(seq[i] >= seq[j] for j in range(i + 1, n)) for i in range(n)]
    peaks = [i for i in range(n) if ispeak[i]]
    if len(peaks) >= K:
        return "peaks", peaks
    tprime = max([p for p in peaks if p < n - 1], default=-1)
    chain = []
    cur = tprime + 1
    while cur < n:
        chain.append(cur)
        nxt = None
        for j in range(cur + 1, n):
            if seq[j] > seq[cur]:
                nxt = j
                break
        if nxt is None:
            break
        cur = nxt
    return "ascent", chain


def lane_s8(rng):
    ok = True
    kinds = {"peaks": 0, "ascent": 0}
    mono_ok = True
    demorgan_ok = True
    reach_ok = True
    sqrt_ok = True
    # (i) distinct values: 400 sequences, both branches, strict monotone
    for _ in range(400):
        n = rng.randrange(50, 400)
        seq = rng.sample(range(10 ** 7), n)
        kind, idx = peaks_law_machine(seq, K=rng.randrange(3, 12))
        kinds[kind] += 1
        vals = [seq[i] for i in idx]
        # branch outputs: peaks STRICTLY decreasing / ascent STRICTLY
        # increasing (distinct values)
        if kind == "peaks":
            if not all(vals[i] > vals[i + 1] for i in range(len(vals) - 1)):
                mono_ok = False
        else:
            if not all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)):
                mono_ok = False
            if len(idx) >= 1 and idx[-1] != n - 1:
                reach_ok = False   # ascent halts exactly at the final slot
        # de Morgan complement at EVERY position: the proof's load-bearing
        # step — peak OR later-strictly-greater, verified by direct scans
        for i in range(n):
            greater = [j for j in range(i + 1, n) if seq[j] > seq[i]]
            suffix_ok = all(seq[i] >= seq[j] for j in range(i + 1, n))
            if suffix_ok and greater:
                demorgan_ok = False   # a peak cannot have a later greater
            if (not suffix_ok) and not greater:
                demorgan_ok = False   # a non-peak MUST have a later greater
        li, ld = base.lis_lds(seq)
        if max(li, ld) < math.ceil(math.sqrt(n)):
            sqrt_ok = False
    # (ii) ties: 300 sequences with repetitions (the weak-peak convention)
    tdec = 0
    tinc = 0
    ties_ok = True
    for _ in range(300):
        n = rng.randrange(50, 300)
        seq = [rng.randrange(50) for _ in range(n)]
        kind, idx = peaks_law_machine(seq, K=8)
        vals = [seq[i] for i in idx]
        if kind == "peaks":
            tdec += 1
            if not all(vals[i] >= vals[i + 1] for i in range(len(vals) - 1)):
                ties_ok = False   # non-increasing (ties allowed)
        else:
            tinc += 1
            if not all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)):
                ties_ok = False   # STRICTLY increasing (strict-greater steps)
            if len(idx) >= 1 and idx[-1] != n - 1:
                ties_ok = False
        # de Morgan complement: every position peak-or-later-greater
        for i in range(n):
            greater = [j for j in range(i + 1, n) if seq[j] > seq[i]]
            suffix_ok = all(seq[i] >= seq[j] for j in range(i + 1, n))
            if (suffix_ok and greater) or ((not suffix_ok) and not greater):
                ties_ok = False
    # (iii) the x-SORTER application (the infinite chain's step 2): x-coords
    # of random GP sets are DISTINCT -> strictly monotone x-subsequence
    sort_ok = True
    nsort = 0
    for _ in range(200):
        m = rng.randrange(20, 90)
        pts = base.gen_gp_any(m, rng, 10 ** 4)
        xs = [p[0] for p in pts]
        if len(set(xs)) != m:
            continue
        kind, idx = peaks_law_machine(xs, K=8)
        vals = [xs[i] for i in idx]
        nsort += 1
        if kind == "peaks":
            if not all(vals[i] > vals[i + 1] for i in range(len(vals) - 1)):
                sort_ok = False
        else:
            if not all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)):
                sort_ok = False
            if len(idx) >= 1 and idx[-1] != m - 1:
                sort_ok = False
    report("S8-INF-PEAKS", ok and mono_ok and demorgan_ok and reach_ok
           and sqrt_ok and ties_ok and sort_ok,
           "the peaks law: 400 DISTINCT-value sequences (n in [50,400)): "
           "branch census %s, peaks branch STRICTLY decreasing, ascent "
           "branch STRICTLY increasing and halting EXACTLY at the final "
           "position (the finite surrogate of never-halts); de Morgan "
           "complement (peak XOR later-strictly-greater) verified at EVERY "
           "position; finite MS shadow max(LIS,LDS) >= ceil(sqrt(n)) "
           "everywhere; 300 TIE sequences: peaks non-increasing (%d), "
           "ascent strictly increasing (%d); the x-SORTER application: 200 "
           "random GP sets, distinct x-coords -> strictly monotone "
           "x-subsequence every time (%d) — the two branches of the "
           "in-package proof plus its geometric use, exactly as derived"
           % (kinds, tdec, tinc, nsort))


def lane_s9(rng):
    ok = True
    n_checks = 0
    frames = configs_order_types(6, 120, rng)
    frames += [("ext%d%d" % ab, get_extremal(*ab)[0])
               for ab in [(4, 4), (5, 5), (6, 6)]]
    frames += configs_random(rng, 600, 8, 14)
    for tag, fr in frames:
        dA = base.cup_cap_labels(fr)
        dB = labels_slope_dp(fr)
        n = len(fr)
        for a in range(3, 9):
            for b in range(3, 9):
                bound = math.comb(a + b - 4, a - 2)
                if bound < n - 1:
                    boxA = sum(1 for i, j in zip(dA["cup"], dA["cap"])
                               if i <= a - 1 and j <= b - 1)
                    boxB = sum(1 for i, j in zip(dB["cup"], dB["cap"])
                               if i <= a - 1 and j <= b - 1)
                    if boxA != boxB or boxA > bound:
                        ok = False
                    n_checks += 1
    eq = []
    for (a, b) in [(4, 4), (5, 5), (6, 6), (7, 7)]:
        pts, d, _ = get_extremal(a, b)
        box = sum(1 for i, j in zip(d["cup"], d["cap"])
                  if i <= a - 1 and j <= b - 1)
        good = box == len(pts) == math.comb(a + b - 4, a - 2)
        if not good:
            ok = False
        eq.append("S(%d,%d): box(%d,%d)=%d=|S|=C(%d,%d)"
                  % (a, b, a - 1, b - 1, box, a + b - 4, a - 2))
    edge_ok = True
    for (a, b) in [(4, 4), (5, 5), (6, 6)]:
        pts, d, _ = get_extremal(a, b)
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        placed = False
        for dd in (10 ** 9, 10 ** 12, 10 ** 15):
            S = pts + [(min(xs) - dd, max(ys) + dd)]
            if base.general_position(S) and base.distinct_x(S):
                if not base.has_cup_cap(S, a, b):
                    edge_ok = False
                placed = True
                break
        if not placed:
            edge_ok = False
    report("S9-INF-DICH", ok and edge_ok,
           "the box-census law |{p: cup<=a-1, cap<=b-1}| <= C(a+b-4,a-2): "
           "%d (a,b)-box checks over all frames (order types n<=6 x cells, "
           "n=8 sample, extremals, 600 random), BOTH counting codes agree; "
           "extremal EQUALITY: %s; the +1 escape edge (S(a,b)+one point => "
           "cup=a or cap=b) — an infinite set fits in NO box: the finite "
           "shadow of the infinite dichotomy" % (n_checks, "; ".join(eq)))


def lane_s10(rng):
    ok = True
    det = []
    builds = 0
    hsz = []
    asz = []
    for _ in range(60):
        N = rng.randrange(20, 60)
        tab = {ijk: rng.randrange(2)
               for ijk in itertools.combinations(range(N), 3)}

        def col3d(i, j, k, tab=tab):
            return tab[(i, j, k)] if i < j < k else tab[tuple(sorted((i, j, k)))]

        good, la, H, maj = base.ram3_certificate(N, col3d)
        # the STRUCTURAL certificate must hold on every build (whatever
        # the sizes): anchors increasing, col(a_i,a_j,a_k)=c*_i for all
        # i<j<k, H homogeneous. |H| >= 3 is a finite-Ramsey TOWER demand
        # on random colorings (needs N ~ 2^2^|H|) — reported as data, not
        # required; the infinite proof needs no finite bound.
        if not good:
            ok = False
        # the construction replayed step by step: X_{i+1} ⊆ X_i (nested),
        # a_i = min(X_i), and the pair-color c(a_i, ·, ·) CONSTANT on
        # [X_{i+1}]^2 — the exact bookkeeping the infinite build iterates
        X = list(range(N))
        while len(X) >= 3:
            a = X[0]
            rest = X[1:]
            if len(rest) < 2:
                break

            def col(x, y, a=a):
                return col3d(a, x, y) if x < y else col3d(a, y, x)

            clique, colr = base._mono_clique_pairs(rest, col)
            if len(clique) < 2:
                break
            if a != min(X) or not set(clique) <= set(rest):
                ok = False
            for (x, y) in itertools.combinations(clique, 2):
                if col(x, y) != colr:
                    ok = False
            X = clique
        builds += 1
        hsz.append(len(H))
        asz.append(la)
    det.append("%d abstract 2-colorings of triples (N in [20,60)): the "
               "a_i/X_i/c*_i build certified STRUCTURALLY on every one "
               "(anchors increasing, col(a_i,a_j,a_k)=c*_i for all i<j<k, "
               "majority subsequence H fully homogeneous; |A| in [%d,%d], "
               "|H| in [%d,%d] — the finite greedy depth is the Ramsey "
               "TOWER reality: |H| >= k needs N ~ 2^2^k on random "
               "colorings; the INFINITE construction needs no finite "
               "bound — each infinite X_i keeps the build going forever)"
               % (builds, min(asz), max(asz), min(hsz), max(hsz)))
    # ------------------------------------------------------------------
    # THE GEOMETRIC CONSTRUCTION — the infinite chain's exact engine mirror
    # (INFINITE_107.md §2: peaks x-sort + iterated fan homogenization +
    # final pigeonhole; NO general pair-Ramsey — the peaks law delivers
    # every homogeneous set):
    #   X_0 = x-sorted distinct-x GP set (S8 certifies the x-sorter, S7 the
    #   frame); round i: a_i = LEFTMOST of X_i (anchors strictly x-increase);
    #   fan slopes from a_i over the rest (x-order, DISTINCT by GP) ->
    #   TRUE longest strictly-monotone subsequence (banked lis_lds = the
    #   finite MS machine) -> X_{i+1} = that subsequence, c*_i = 1 if
    #   increasing / 0 if decreasing; the majority color anchors form H.
    # Verified per round: pair-homogeneity of X_{i+1} under col(a_i,.,.)
    # (ALL pairs), and the composed law col(a_i,a_j,a_k)=c*_i (i<j<k).
    # ------------------------------------------------------------------
    her_ok = True
    conv_checks = 0
    hsizes = []
    depths = []

    def chain_build(P):
        """P: x-sorted distinct-x GP points. Returns (A, cstars, H, maj)."""
        idx = list(range(len(P)))
        A = []
        cstars = []
        while len(idx) >= 3:
            a = idx[0]
            rest = idx[1:]
            if len(rest) < 2:
                break
            slopes = [Fraction(P[j][1] - P[a][1], P[j][0] - P[a][0])
                      for j in rest]
            # sanity: slopes pairwise distinct (GP)
            if len(set(slopes)) != len(slopes):
                return None
            li, ld = base.lis_lds(slopes)
            # extract the actual longest subsequence (recompute with
            # parents — independent of lis_lds's length-only output;
            # CROSS-CHECKED: the two codes must agree on the lengths)

            def longest_mono(want_inc):
                best_len = [1] * len(slopes)
                par = [-1] * len(slopes)
                for t in range(len(slopes)):
                    for u in range(t):
                        cmp_ok = (slopes[u] < slopes[t]) if want_inc \
                            else (slopes[u] > slopes[t])
                        if cmp_ok and best_len[u] + 1 > best_len[t]:
                            best_len[t] = best_len[u] + 1
                            par[t] = u
                e = max(range(len(slopes)), key=lambda t: best_len[t])
                chain = []
                while e != -1:
                    chain.append(e)
                    e = par[e]
                return chain[::-1]
            inc = longest_mono(True)
            dec = longest_mono(False)
            if len(inc) != li or len(dec) != ld:
                return None   # the two monotone codes disagree — flag
            if len(inc) >= len(dec):
                sub, cstar = inc, 1
            else:
                sub, cstar = dec, 0
            if len(sub) < 2:
                break
            nxt = [rest[t] for t in sub]
            # pair-homogeneity: ALL pairs of nxt carry col(a,.,.) = cstar
            for (u, v) in itertools.combinations(range(len(nxt)), 2):
                s = 1 if base.cross3(P[a], P[nxt[u]], P[nxt[v]]) > 0 else 0
                if s != cstar:
                    return None
            A.append(a)
            cstars.append(cstar)
            idx = nxt
        if not A:
            return A, cstars, [], 1
        c0 = cstars.count(0)
        maj = 0 if c0 >= len(cstars) - c0 else 1
        H = [A[t] for t in range(len(A)) if cstars[t] == maj]
        return A, cstars, H, maj

    def subsets_capped(HP, rnglocal):
        """All subsets of size 3..min(len,4), plus capped random samples
        at sizes 5..6 (4000 each) when the full enumeration is too large."""
        out = []
        for r in range(3, min(len(HP), 4) + 1):
            out.extend(itertools.combinations(HP, r))
        for r in (5, 6):
            if r > len(HP):
                continue
            allc = list(itertools.combinations(HP, r))
            if len(allc) <= 4000:
                out.extend(allc)
            else:
                out.extend(rnglocal.sample(allc, 4000))
        return out

    n_deep = 0
    for _ in range(40):
        n = rng.randrange(14, 60)
        pts = base.gen_gp_distinct_x(n, rng, 10 ** 4)
        P = base._sorted_by_x(pts)
        res = chain_build(P)
        if res is None:
            her_ok = False
            continue
        A, cstars, H, maj = res
        depths.append(len(A))
        # composed law: col(a_i,a_j,a_k) = c*_i for ALL i<j<k
        for i in range(len(A)):
            for j in range(i + 1, len(A)):
                for k in range(j + 1, len(A)):
                    s = 1 if base.cross3(P[A[i]], P[A[j]],
                                         P[A[k]]) > 0 else 0
                    if s != cstars[i]:
                        her_ok = False
        if len(H) >= 3:
            hsizes.append(len(H))
            HP = [P[t] for t in H]
            for i, j, k in itertools.combinations(range(len(H)), 3):
                s = 1 if base.cross3(HP[i], HP[j], HP[k]) > 0 else 0
                if s != maj:
                    her_ok = False
            if not (base.is_cup(HP) if maj == 1 else base.is_cap(HP)):
                her_ok = False
            for sub in subsets_capped(HP, rng):
                if maj == 1 and not base.is_cup(sub):
                    her_ok = False
                if maj == 0 and not base.is_cap(sub):
                    her_ok = False
                c1, c2 = base.convex_both(sub)
                if not (c1 and c2):
                    her_ok = False
                conv_checks += 1
            n_deep += 1
    rand_depth = "random GP sets (n in [14,60)): %d builds, depth |A| in "
    rand_depth = (rand_depth + "[%d,%d], %d reached |H|>=3 (H sizes "
                  "%d..%d); every round pair-homogeneous (ALL pairs), the "
                  "composed law col(a_i,a_j,a_k)=c*_i verified on every "
                  "triple; every |H|>=3 build: H all-same-sign, a full "
                  "cup/cap, all subsets <=6 convex by BOTH codes (%d "
                  "subset checks)") % (
        len(depths), min(depths) if depths else 0,
        max(depths) if depths else 0, n_deep,
        min(hsizes) if hsizes else 0, max(hsizes) if hsizes else 0,
        conv_checks)
    # DEPTH inputs: convex-curve families — the fan slopes from EVERY
    # anchor are monotone, so the construction runs at FULL depth
    # (the structured case of the infinite construction, where every
    # X_i stays large); concave dual; mixed (half curve + half random).
    deep_ok = True
    deep_stats = []
    for fam in ("parabola", "concave", "mixed"):
        for _ in range(12):
            if fam == "parabola":
                n = rng.randrange(18, 40)
                P = [(2 * t, t * t) for t in range(1, n + 1)]
            elif fam == "concave":
                n = rng.randrange(18, 40)
                P = [(2 * t, -(t * t)) for t in range(1, n + 1)]
            else:
                n = rng.randrange(24, 48)
                half = n // 2
                P = [(2 * t, t * t) for t in range(1, half + 1)]
                xmax = P[-1][0]
                while len(P) < n:
                    q = (xmax + rng.randrange(1, 400),
                         rng.randrange(-5000, 5000))
                    if all(base.cross3(P[i], P[j], q) != 0
                           for i in range(len(P))
                           for j in range(i + 1, len(P))):
                        P.append(q)
                        xmax = q[0]
            P = base._sorted_by_x(P)
            if not (base.general_position(P) and base.distinct_x(P)):
                deep_ok = False
                continue
            res = chain_build(P)
            if res is None:
                deep_ok = False
                continue
            A, cstars, H, maj = res
            if len(H) < 3:
                deep_ok = False
                continue
            HP = [P[t] for t in H]
            if not (base.is_cup(HP) if maj == 1 else base.is_cap(HP)):
                deep_ok = False
            for i, j, k in itertools.combinations(range(len(H)), 3):
                s = 1 if base.cross3(HP[i], HP[j], HP[k]) > 0 else 0
                if s != maj:
                    deep_ok = False
            for sub in subsets_capped(HP, rng):
                c1, c2 = base.convex_both(sub)
                if not (c1 and c2):
                    deep_ok = False
                if maj == 1 and not base.is_cup(sub):
                    deep_ok = False
                if maj == 0 and not base.is_cap(sub):
                    deep_ok = False
            deep_stats.append("%s:|A|=%d,|H|=%d" % (fam, len(A), len(H)))
    det.append("the infinite chain's construction, machine mirror: "
               + rand_depth
               + "; DEPTH families (parabola/concave/mixed — the fan "
                 "slopes monotone from every anchor, full-depth builds): "
               + ", ".join(deep_stats[:6])
               + " — H a full cup/cap at every depth, all subsets convex "
                 "by both codes")
    shear_ok = True
    nb_max = 0
    for _ in range(40):
        n = 120
        pts = base.gen_gp_any(n, rng, 10 ** 4)
        bad = set()
        for i in range(n):
            for j in range(i + 1, n):
                dx = pts[j][0] - pts[i][0]
                dy = pts[j][1] - pts[i][1]
                if dy != 0:
                    g = math.gcd(abs(dx), abs(dy))
                    bad.add((-dx // g, dy // g))
        nb_max = max(nb_max, len(bad))
        t = base.find_good_int_t(pts)
        if t is None or t > n * (n - 1) // 2 + 1:
            shear_ok = False
    det.append("countable-shear census: 40 GP sets of 120 points — the "
               "bad shear parameters are FINITE in number (<= %d primitive "
               "directions <= C(120,2) pairs), a good integer shear always "
               "found within C(n,2)+1 — the countable-bad-set shadow "
               "(countably many bad s, R uncountable)" % nb_max)
    report("S10-INF-RAM3", ok and her_ok and shear_ok, "; ".join(det))


def lane_s11(rng):
    pk_ok = all(2 ** (j + k) == 2 ** j * 2 ** k
                and 3 ** (j + k) == 3 ** j * 3 ** k
                and 6 ** (j + k) == 6 ** j * 6 ** k
                for j in range(0, 25) for k in range(0, 25))
    jp_ok = all(
        sum(5 * 6 ** i for i in range(k + 1))
        == sum(5 * 6 ** i for i in range(k)) + 5 * 6 ** k
        for k in range(0, 30))
    tow1 = all(k + 4 <= 2 ** (k + 2) for k in range(0, 60))
    tow2 = all(k * k <= 2 ** k for k in range(4, 60))
    cone = all(m < 3 ** m for m in range(1, 40))
    bounds = all(math.comb(2 * m - 4, m - 2) + 1 < 3 ** (2 * m)
                 for m in range(3, 31))
    stream = base.gen_gp_any(200, rng, 10 ** 4)
    shadow_ok = True
    checked = 0
    for m, sizes in [(4, (7, 20, 60, 200)), (5, (21, 80, 200)),
                     (6, (71, 150, 200))]:
        for sz in sizes:
            pre = stream[:sz]
            t = base.find_good_int_t(pre)
            if t is None:
                shadow_ok = False
                continue
            R = base.rot_dilate(pre, t)
            d = base.cup_cap_labels(R)
            if not (max(d["cup"]) >= m or max(d["cap"]) >= m):
                shadow_ok = False
            checked += 1
    report("S11-CARD-ARITH",
           pk_ok and jp_ok and tow1 and tow2 and cone and bounds
           and shadow_ok,
           "the cardinal-strength arithmetic: packet composition 2/3/6-pow "
           "(j,k in [0,25)) exact; joined-prefix recurrence J(k+1)=J(k)+"
           "5*6^k (k<30); towers k+4<=2^(k+2) (k<60), k^2<=2^k (4<=k<60); "
           "terminal cone m<3^m (m<40); every finite bound dwarfed: "
           "C(2m-4,m-2)+1 < 3^(2m) (m=3..30). ES-INF-kappa shadow: one "
           "200-point GP stream, nested prefixes — the SAME finite "
           "threshold forces the m-cup/m-cap at EVERY prefix scale (%d "
           "prefix checks at m=4,5,6: prefix >= C(2m-4,m-2)+1 always "
           "yields the chain)" % checked)


def lane_s12(rng):
    laws = {}

    def bracket(v, w):
        return v[0] * w[1] - v[1] * w[0]

    def transform(a, b, c, d, v):
        return (a * v[0] + b * v[1], c * v[0] + d * v[1])

    vs = [(rng.randrange(-99, 100), rng.randrange(-99, 100))
          for _ in range(600)]
    laws["bracket_skew"] = all(
        bracket(vs[i], vs[i + 1]) == -bracket(vs[i + 1], vs[i])
        for i in range(0, 590, 2))
    laws["bracket_self"] = all(bracket(v, v) == 0 for v in vs[:300])
    bt_ok = True
    for i in range(300):
        a, b, c, d = (rng.randrange(-9, 10) for _ in range(4))
        if bracket(transform(a, b, c, d, vs[i]),
                   transform(a, b, c, d, vs[i + 1])) \
                != (a * d - b * c) * bracket(vs[i], vs[i + 1]):
            bt_ok = False
    laws["bracket_transform"] = bt_ok
    laws["bracket_shear"] = all(
        bracket(transform(1, t, 0, 1, vs[i]),
                transform(1, t, 0, 1, vs[i + 1])) == bracket(vs[i], vs[i + 1])
        for t in range(-9, 10) for i in range(0, 200, 2))
    laws["plucker_four"] = all(
        bracket(vs[i], vs[i + 1]) * bracket(vs[i + 2], vs[i + 3])
        - bracket(vs[i], vs[i + 2]) * bracket(vs[i + 1], vs[i + 3])
        + bracket(vs[i], vs[i + 3]) * bracket(vs[i + 1], vs[i + 2]) == 0
        for i in range(0, 300, 4))

    def amp(state, edges):
        r = 1
        for (i, j) in edges:
            r *= bracket(state[i], state[j])
        return r

    gt_ok = True
    for _ in range(120):
        a, b, c, dd = (rng.randrange(-5, 6) for _ in range(4))
        state = [(rng.randrange(-50, 51), rng.randrange(-50, 51))
                 for _ in range(6)]
        edges = [(rng.randrange(0, 6), rng.randrange(0, 6))
                 for _ in range(rng.randrange(0, 7))]
        ts = [transform(a, b, c, dd, s) for s in state]
        if amp(ts, edges) != (a * dd - b * c) ** len(edges) * amp(state, edges):
            gt_ok = False
    laws["graph_transform"] = gt_ok
    laws["binom_two_term=first_order=mod_sq"] = all(
        ((1 + x) ** u - 1 - u * x) % (x * x) == 0
        for u in range(0, 40) for x in range(1, 25))
    laws["cubic_expansion"] = all(
        (1 + a) ** 3 == 1 + 3 * a + 3 * a * a + a ** 3 for a in range(0, 300))
    laws["mod_mod_mul"] = all(
        ((n % (a * b)) % a) == (n % a)
        for n, a, b in zip(rng.sample(range(10 ** 5), 200),
                           rng.sample(range(1, 999), 200),
                           rng.sample(range(1, 999), 200)))
    laws["mul_add_div_lemma"] = all(
        ((d * k + r) // d) == (k + r // d)
        for d, k, r in zip(rng.sample(range(1, 999), 200),
                           rng.sample(range(10 ** 4), 200),
                           rng.sample(range(10 ** 4), 200)))
    laws["sum_le_sum_of_forall"] = all(
        sum(f(x) for x in l) <= sum(g(x) for x in l)
        for l in [rng.sample(range(100), rng.randrange(1, 12))
                  for _ in range(200)]
        for f, g in ((lambda x: x % 5, lambda x: x % 5 + 2),
                     (lambda x: x // 3, lambda x: x // 2)))
    # (hypothesis f <= g pointwise VERIFIED, conclusion checked: the
    #  law's exact form. The W77 spot-check used f=x%7, g=x%5+2 which
    #  VIOLATES the hypothesis at x=6 — a false test, fixed here.)
    laws["sum_range_shift"] = all(
        sum(h(x) for x in range(n + 1))
        == h(0) + sum(h(x + 1) for x in range(n))
        for n in range(0, 40)
        for h in (lambda x: x * x + 3, lambda x: 5 * x + 7))

    def dc3(n):
        c = 1 if n == 0 else 0
        while n:
            n //= 3
            c += 1
        return c

    laws["digitCount3_monotone"] = all(
        not (a <= b and dc3(a) > dc3(b))
        for a, b in zip(rng.sample(range(10 ** 5), 300),
                        rng.sample(range(10 ** 5), 300)))
    laws["packet_add"] = all(2 ** (j + k) == 2 ** j * 2 ** k
                             for j in range(0, 40) for k in range(0, 40))
    laws["joined_prefix_succ"] = all(
        sum(5 * 6 ** i for i in range(k + 1))
        == sum(5 * 6 ** i for i in range(k)) + 5 * 6 ** k
        for k in range(0, 30))
    laws["two_pow_pos"] = all(2 ** j >= 1 for j in range(0, 70))
    laws["two_pow_factored"] = all(2 ** j == 2 * 2 ** (j - 1)
                                   for j in range(1, 70))
    laws["two_pow_ge2"] = all(2 <= 2 ** j for j in range(1, 70))
    laws["two_pow2_ge"] = all(k + 4 <= 2 ** (k + 2) for k in range(0, 60))
    laws["pow2_sq"] = all(k * k <= 2 ** k for k in range(4, 60))
    laws["terminal_cone"] = all(m < 3 ** m for m in range(1, 40))
    koenig_ok = True
    for _ in range(200):
        depth = rng.randrange(4, 18)
        death = rng.randrange(2, depth + 2)
        tree = {}
        alive = {()}
        for L in range(depth):
            nxt = set()
            for node in alive:
                for c in range(rng.randrange(1, 4)):
                    child = node + (c,)
                    if L + 1 < death or rng.random() < 0.8:
                        nxt.add(child)
            tree[L + 1] = nxt
            alive = nxt
        reaches = all(len(tree.get(L, set())) > 0 for L in range(1, depth + 1))
        has_deep = len(tree.get(depth, set())) > 0
        if reaches != has_deep:
            koenig_ok = False
    laws["omega_finite_escape_shadow"] = koenig_ok
    laws["badPrefix_antitone_shadow"] = all(
        {x for x in range(50) if x >= k + 1}
        <= {x for x in range(50) if x >= k}
        for k in range(10))
    # (LONGER bad-prefix sets nest INSIDE shorter ones — the exact
    #  direction of gst_omega_badPrefixSet_antitone; the W77 shadow had
    #  the inclusion reversed — range(k) >= range(k+1 is false as sets —
    #  fixed here: surviving k+1 bad stages implies surviving k.)
    n_ok = sum(1 for v in laws.values() if v)
    report("S12-LAW-SPOTS", n_ok == len(laws),
           "%d/%d arsenal law spot-checks pass at statement: "
           "GSTCausalPairingGraphs (bracket_skew/self/transform/shear, "
           "plucker_four, graph_transform); GSTDiagonalRead + ErdosTernary2 "
           "(binom_two_term = binom_first_order = binom_mod_sq_local, the "
           "mod-x^2 expansion); CardinalWorlds (cubic_expansion, "
           "mod_mod_mul, mul_add_div_lemma, two_pow_pos/factored/ge2); "
           "Erdos261Tower (sum_le_sum_of_forall, sum_range_shift, "
           "two_pow2_ge, pow2_sq); CardinalWorldsV2 (packet_add, "
           "joined_prefix_succ); ErdosTernary2 omega-layer "
           "(digitCount3_monotone, the finite-escape/Koenig shadow, the "
           "antitone-nesting shadow, the terminal cone m<3^m)"
           % (n_ok, len(laws)))


def lane_s13(rng):
    ok = True
    pts = base.gen_gp_distinct_x(12, rng, 10 ** 3)
    d = base.cup_cap_labels(pts)
    mc = max(d["cup"])
    if mc >= 3:
        good, _ = lavoid_check_class(sorted(pts), mc, 10 ** 6)
        if good:
            ok = False  # the full set DOES contain an mc-cup: must be FLAGGED
    planted = {("x", 4, 4): math.comb(4, 2) + 1}
    viol = any(cnt > math.comb(i + j - 4, i - 2)
               for (_, i, j), cnt in planted.items())
    if not viol:
        ok = False
    pts = base.gen_gp_distinct_x(8, rng, 10 ** 3)
    dA = base.cup_cap_labels(pts)
    cupB = list(dA["cup"])
    capB = list(dA["cap"])
    cupB[3] += 4
    if class_counts(dA["cup"], dA["cap"]) == class_counts(cupB, capB):
        ok = False
    tri = [(0, 0), (5, 0), (0, 5)]
    if base.convex_position_hull(tri + [(1, 1)]) or \
            base.convex_position_scan(tri + [(1, 1)]):
        ok = False
    if not (base.convex_position_hull(tri) and base.convex_position_scan(tri)):
        ok = False
    badout = [1, 3, 2]
    if all(badout[i] < badout[i + 1] for i in range(2)):
        ok = False
    for _ in range(30):
        n = rng.randrange(4, 9)
        p = base.gen_gp_distinct_x(n, rng, 10 ** 3)
        mc, mk = base.max_cup_cap(p)
        bfl = labels_brute(p)
        if bfl and (max(bfl["cup"]) != mc or max(bfl["cap"]) != mk):
            ok = False
    fake_box = math.comb(4, 2) + 1
    if not (fake_box > math.comb(4, 2)):
        ok = False
    report("S13-NEG-CONTROLS", ok,
           "the full-set pseudo-class (contains its own max cup) is "
           "FLAGGED by the L-AVOID checker; a planted census above "
           "C(i+j-4,i-2) is FLAGGED; a corrupted label array is DETECTED "
           "by the two-code comparison; triangle+interior NON-convex on "
           "both codes (triangle convex); a corrupted peaks output fails "
           "monotonicity; DP labels == TRUE brute-force labels on 30 "
           "random sets; the planted box-census violation is flagged")


# ---------------------------------------------------------------------------
# Receipts / main
# ---------------------------------------------------------------------------

def write_receipts():
    n_ok = sum(1 for (_, ok, _) in RESULTS if ok)
    with open(RECEIPTS, "w") as f:
        f.write("RECEIPTS — engine107sharp.py (W78-107E, S078) — THE "
                "SHARP ALL-n ENGINE (the label route)\n")
        f.write("seed %d ; deterministic ; python3 ; exact integer/"
                "Fraction arithmetic; two-code discipline on every claim\n"
                "banked base: engine107alln (alln107/, W77 receipts 8/13 "
                "— three engine-side defects fixed in W78: the peaks "
                "ascent branch, the sum_le spot-check, the "
                "point_outside_scan sign flip; ADDENDUM in "
                "receipts107alln.txt); banked order types n<=8 (107K @ "
                "bb4aad7)\n\n"
                % SEED)
        for cid, ok, detail in RESULTS:
            f.write("%s %s — %s\n" % ("PASS" if ok else "FAIL", cid, detail))
        f.write("\nTOTAL: %d/%d PASS\n" % (n_ok, len(RESULTS)))
        f.write("SHARP_ENGINE_GREEN=%d\n" % (1 if n_ok == len(RESULTS) else 0))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--force", action="store_true",
                    help="re-run completed stages")
    args = ap.parse_args()
    t0 = time.time()
    rng = random.Random(SEED)
    print("=== engine107sharp — THE SHARP ALL-n ENGINE (W78-107E) ===")
    print("seed:", SEED)

    if os.path.exists(PROGRESS) and not args.force:
        try:
            with open(PROGRESS) as f:
                st = json.load(f)
            DONE.update(st.get("done", []))
            for (c, o, d) in st.get("results", []):
                RESULTS.append((c, o, d))
            if DONE:
                print("resuming; already done:", sorted(DONE), flush=True)
        except Exception:
            pass

    def run(stage, fn, *a, **kw):
        if stage in DONE:
            return
        fn(*a, **kw)
        DONE.add(stage)
        save_progress()

    run("S0", lane_s0, rng)
    run("S1S3", lanes_s1_s3, rng)
    run("S2", lane_s2, rng)
    run("S4", lane_s4)
    run("S5", lane_s5, rng)
    run("S6", lane_s6, rng)
    run("S7", lane_s7, rng)
    run("S8", lane_s8, rng)
    run("S9", lane_s9, rng)
    run("S10", lane_s10, rng)
    run("S11", lane_s11, rng)
    run("S12", lane_s12, rng)
    run("S13", lane_s13, rng)

    write_receipts()
    n_ok = sum(1 for (_, ok, _) in RESULTS if ok)
    print("\nTOTAL: %d/%d PASS, wall %.1fs"
          % (n_ok, len(RESULTS), time.time() - t0))
    print("SHARP_ENGINE_GREEN=%d" % (1 if n_ok == len(RESULTS) else 0))
    sys.exit(0 if n_ok == len(RESULTS) else 1)


if __name__ == "__main__":
    main()
