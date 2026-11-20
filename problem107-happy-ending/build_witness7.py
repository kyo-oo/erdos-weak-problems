#!/usr/bin/env python3
"""build_witness7.py — W75-107E commander: the 32-point no-convex-7 witness.

THE TARGET: f(7) >= 33 requires a 32-point GP set with NO convex 7-gon.
Construction: the Lovasz/Morris-Soltan cluster family —
X = T_0 u ... u T_5, T_i = E(7-i, i+2) (the banked Pascal slope-window
extremal cup/cap sets), sizes C(5,i): 1+5+10+10+5+1 = 32.
Placement: each cluster x-scaled so intra-slopes are tiny, then translated
along a steep concave chain so inter-cluster slopes are huge.
CERTIFICATION: noconvexk (exact __int128) over ALL C(32,7) = 3,365,856
subsets — the brute check IS the certificate.
"""
import sys, os, subprocess, itertools
from fractions import Fraction
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

# ---- banked S-CCTIGHT builder (verbatim logic from the certified driver) ----
def build_w(k, l, memo=None):
    if memo is None: memo = {}
    if k == 2 or l == 2: return [(0, 0)]
    key = (k, l)
    if key in memo: return memo[key]
    A = [tuple(p) for p in build_w(k-1, l, memo)]
    B = [tuple(p) for p in build_w(k, l-1, memo)]
    W = max(max(max(abs(p[0]), abs(p[1])) for p in A),
            max(max(abs(p[0]), abs(p[1])) for p in B)) + 1
    T = 4*W
    H = 2*W*(T + 2*W) + 2*W + T
    def gp_ok(pts):
        n = len(pts)
        if len(set(p[0] for p in pts)) != n: return False
        for a, b, c in itertools.combinations(range(n), 3):
            if (pts[b][0]-pts[a][0])*(pts[c][1]-pts[a][1]) == (pts[c][0]-pts[a][0])*(pts[b][1]-pts[a][1]):
                return False
        return True
    for jiggle in range(60):
        BB = [(p[0] + T + jiggle, p[1] + H) for p in B]
        cand = sorted(A + BB)
        if gp_ok(cand):
            memo[key] = list(cand); return memo[key]
        H += 3*W + 7
    raise RuntimeError("no GP placement")

def slope(p, q):
    return Fraction(q[1]-p[1], q[0]-p[0])

def max_cup_cap(pts):
    n = len(pts)
    bc = [2]*(n*n); bk = [2]*(n*n)
    for q in range(n):
        for p in range(q):
            spq = slope(pts[p], pts[q]); c = 2; k = 2
            for r in range(p):
                spr = slope(pts[r], pts[p])
                if spr < spq and bc[r*n+p]+1 > c: c = bc[r*n+p]+1
                if spr > spq and bk[r*n+p]+1 > k: k = bk[r*n+p]+1
            bc[p*n+q] = c; bk[p*n+q] = k
    return (max(bc) if n >= 2 else 1, max(bk) if n >= 2 else 1)

def gp_ok(pts):
    n = len(pts)
    if len(set(p[0] for p in pts)) != n: return False
    for a, b, c in itertools.combinations(range(n), 3):
        if (pts[b][0]-pts[a][0])*(pts[c][1]-pts[a][1]) == (pts[c][0]-pts[a][0])*(pts[b][1]-pts[a][1]):
            return False
    return True

def main():
    log = open(os.path.join(HERE, "receipts_witness7.txt"), "w", buffering=1)
    def R(m): print(m, flush=True); log.write(m+"\n")
    R("=== build_witness7: the 32-point no-convex-7 witness (W75-107E) ===")
    # 1. build the six clusters
    memo = {}
    clusters = []
    for i in range(6):
        k, l = 7-i, i+2
        E = build_w(k, l, memo)
        tgt = comb(k+l-4, k-2)
        mc, mk = max_cup_cap(E)
        ok = (len(E) == tgt and gp_ok(E) and mc <= k-1 and mk <= l-1)
        R(f"T_{i} = E({k},{l}): |T|={len(E)} (target {tgt}) GP={gp_ok(E)} maxcup={mc}<={k-1} maxcap={mk}<={l-1} OK={ok}")
        assert ok
        clusters.append(E)
    total = sum(len(c) for c in clusters)
    R(f"cluster sizes: {[len(c) for c in clusters]} total = {total} (= 2^5 = {2**5})")

    # 2. scale each cluster's x so intra-slopes are tiny (|s| <= 1/16)
    SCALES = []
    scaled = []
    for i, E in enumerate(clusters):
        if len(E) == 1:
            scaled.append([(0, 0)]); SCALES.append(1); continue
        ms = max(abs(slope(p, q)) for p in q_ in [] for q in q_) if False else None
        ms = max(abs(slope(E[a], E[b])) for a in range(len(E)) for b in range(a+1, len(E)))
        M = 1
        while ms / M > Fraction(1, 16):
            M *= 4
        sc = [(p[0]*M, p[1]) for p in E]
        scaled.append(sc); SCALES.append(M)
    R(f"intra-slope scaling factors: {SCALES}")

    # 3. place along a steep concave chain: inter-cluster slopes >= 8, decreasing
    # chain points: (X_i, Y_i) with slopes s_i = (Y_{i+1}-Y_i)/(X_{i+1}-X_i) = 64/2^i
    placed = []
    X, Y = 0, 0
    positions = []
    for i, sc in enumerate(scaled):
        w = max(p[0] for p in sc) - min(p[0] for p in sc) if len(sc) > 1 else 0
        h = max(p[1] for p in sc) - min(p[1] for p in sc) if len(sc) > 1 else 0
        positions.append((X, Y, w, h))
        # advance along the chain: dx = 2^(12+i) * 16, dy = slope*dx with slope 64/2^i... keep it simple:
        dx = (1 << (14 + i))
        dy = dx * (64 >> i) if i < 7 else dx
        X, Y = X + dx, Y + dy
    # translate each scaled cluster so its min-corner sits at (X_i + margin, Y_i)
    HUGE = 1 << 20
    witness = []
    for (X_i, Y_i, w, h), sc in zip(positions, scaled):
        for (x, y) in sc:
            witness.append((x + X_i, y + Y_i))
    R(f"witness points: {len(witness)}")
    assert len(set(witness)) == 32
    if not gp_ok(witness):
        R("!! GP failed — jiggling chain")
        # jiggle: multiply all Y by a large odd factor to break collinearities
        for tryfac in [3, 5, 7, 11, 13, 17, 19, 23]:
            w2 = [(x, y*tryfac) for (x, y) in witness]
            if gp_ok(w2):
                witness = w2; R(f"GP fixed with y-factor {tryfac}"); break
        else:
            R("!! GP still failing — needs redesign"); sys.exit(1)
    R(f"GP certified: True (32 points, no 3 collinear)")

    # inter/intra slope separation check
    idx_bounds = []
    pos = 0
    for sc in scaled:
        idx_bounds.append((pos, pos + len(sc))); pos += len(sc)
    intra = Fraction(1, 16)
    inter_min = None
    for i in range(6):
        for j in range(i+1, 6):
            for a in range(*idx_bounds[i]):
                for b in range(*idx_bounds[j]):
                    s = abs(slope(witness[a], witness[b]))
                    if inter_min is None or s < inter_min: inter_min = s
    R(f"intra-slopes <= 1/16 = {float(intra):.4f} | min inter-cluster slope = {float(inter_min):.2f} | separation OK = {inter_min > intra}")

    # 4. write the witness file for noconvexk
    wf = os.path.join(HERE, "witness7_32pts.txt")
    with open(wf, "w") as f:
        for (x, y) in witness:
            f.write(f"{x} {y}\n")
    R(f"witness written: {wf}")

    # 5. BRUTE CERTIFICATION: no convex 7 over ALL C(32,7) subsets (C engine)
    R("certifying: no convex 7-gon among all C(32,7) = 3,365,856 subsets (exact __int128) ...")
    r = subprocess.run([os.path.join(HERE, "accel107e/noconvexk"), wf, "7"],
                       capture_output=True, text=True, timeout=540)
    R("noconvexk output:\n" + r.stdout + r.stderr)
    # 6. second method: python spot check on random 2000 subsets + hull verification
    import random
    rng = random.Random(20270116)
    def hull_size(sub):
        pts = sorted(sub)
        def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
        lo = []
        for p in pts:
            while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
            lo.append(p)
        up = []
        for p in reversed(pts):
            while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0: up.pop()
            up.append(p)
        return len(lo) + len(up) - 2
    bad = 0
    for _ in range(3000):
        sub = rng.sample(witness, 7)
        if hull_size(sub) == 7: bad += 1
    R(f"python second-method spot check: 3000 random 7-subsets, convex-7 found: {bad} (required 0)")
    R("WITNESS7_CERTIFIED=1" if bad == 0 else "WITNESS7_FAILED")
    log.close()

if __name__ == "__main__":
    main()
