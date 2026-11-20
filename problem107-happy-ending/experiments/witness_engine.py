#!/usr/bin/env python3
"""ENGINE-107 v2 (commander-executed) — Happy Ending witness engine. EXACT integer arithmetic only.

A. f(4)=5 chirotope certificate: empirically-exact realizable 4-point pattern set
   (by exhaustive integer config enumeration), then all 2^10 5-point chirotopes:
   consistent (all 4-subsets realizable) => contains a convex 4-subset pattern.
B. Structured E_5 candidates (8 pts, no convex 5): bit-reversal rev_k, nested templates,
   pocket templates, doubling, then random.
C. E_6 (16 pts, no convex 6): structured first (rev_4, E_5-doubling), random fallback.
Every certified claim: exact integer dets, full subset scans."""
import json, itertools, random, time
from math import comb

def det3(p, q, r):
    return (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0])

def is_extreme(p, rest):
    """p is a vertex of conv({p} u rest) iff the difference vectors all fit strictly on
    one side of a line through p. Exact test: exists u among +-vecs with all w satisfying
    cross(u,w)>0 or (cross==0 and dot>0)."""
    vecs = [(q[0]-p[0], q[1]-p[1]) for q in rest]
    for (ux, uy) in vecs + [(-v[0], -v[1]) for v in vecs]:
        ok = True
        for (wx, wy) in vecs:
            c = ux*wy - uy*wx
            d = ux*wx + uy*wy
            if not (c > 0 or (c == 0 and d > 0)):
                ok = False
                break
        if ok:
            return True
    return False

def in_convex_position(pts, idxs):
    S = [pts[i] for i in idxs]
    m = len(S)
    if m <= 2:
        return True
    for a in range(m):
        if not is_extreme(S[a], [S[b] for b in range(m) if b != a]):
            return False
    return True

def convex_subset_exists(pts, m):
    n = len(pts)
    for idxs in itertools.combinations(range(n), m):
        if in_convex_position(pts, idxs):
            return list(idxs)
    return None

def max_convex_size(pts, cap=None):
    n = len(pts)
    for m in range(n, 1, -1):
        if cap and m < cap:
            break
        r = convex_subset_exists(pts, m)
        if r is not None:
            return m
    return 1

def in_general_position(pts):
    n = len(pts)
    for t in itertools.combinations(range(n), 3):
        if det3(pts[t[0]], pts[t[1]], pts[t[2]]) == 0:
            return False
    return True

# ---------- A. chirotope certificate ----------
def realizable_4patterns():
    """All realizable sign patterns of a general-position x-sorted 4-point set.
    Exhaustive over integer configs in a grid; order types of 4 points are finitely many
    and all appear in a modest grid."""
    pats = set()
    bad = 0
    for x1 in range(0, 5):
        for x2 in range(x1+1, 8):
            for y1 in range(0, 6):
                for y2 in range(0, 6):
                    for x3 in range(x2+1, 11):
                        for y3 in range(0, 6):
                            for x4 in range(x3+1, 14):
                                for y4 in range(0, 6):
                                    P = [(x1,y1),(x2,y2),(x3,y3),(x4,y4)]
                                    if any(det3(P[i],P[j],P[k])==0 for i,j,k in itertools.combinations(range(4),3)):
                                        continue
                                    s = tuple((det3(P[i],P[j],P[k])>0)-(det3(P[i],P[j],P[k])<0)
                                              for i,j,k in [(0,1,2),(0,1,3),(0,2,3),(1,2,3)])
                                    pats.add(s)
    return pats

def realizable_pattern_convexity():
    """For each realizable 4-pattern, its convex-position status, from explicit realizations."""
    REAL = realizable_4patterns()
    convex = set()
    nonconvex = set()
    for x1 in range(0, 5):
        for x2 in range(x1+1, 8):
            for y1 in range(0, 8):
                for y2 in range(0, 8):
                    for x3 in range(x2+1, 11):
                        for y3 in range(0, 8):
                            for x4 in range(x3+1, 14):
                                for y4 in range(0, 8):
                                    P = [(x1,y1),(x2,y2),(x3,y3),(x4,y4)]
                                    if any(det3(P[i],P[j],P[k])==0 for i,j,k in itertools.combinations(range(4),3)):
                                        continue
                                    s = tuple((det3(P[i],P[j],P[k])>0)-(det3(P[i],P[j],P[k])<0)
                                              for i,j,k in [(0,1,2),(0,1,3),(0,2,3),(1,2,3)])
                                    if in_convex_position(P, [0,1,2,3]):
                                        convex.add(s)
                                    else:
                                        nonconvex.add(s)
    return REAL, convex, nonconvex

def f4_certificate():
    REAL, CONVEX, NONCONVEX = realizable_pattern_convexity()
    tris = list(itertools.combinations(range(5), 3))
    consistent = 0
    bad = []
    for bits in range(1 << 10):
        chi = {tris[i]: (1 if bits >> i & 1 else -1) for i in range(10)}
        ok = True
        for quad in itertools.combinations(range(5), 4):
            pat = tuple(chi[t] for t in itertools.combinations(quad, 3))
            if pat not in REAL:
                ok = False
                break
        if not ok:
            continue
        consistent += 1
        has = False
        for quad in itertools.combinations(range(5), 4):
            pat = tuple(chi[t] for t in itertools.combinations(quad, 3))
            if pat in CONVEX:
                has = True
                break
        if not has:
            bad.append(bits)
    return REAL, CONVEX, NONCONVEX, consistent, bad

# ---------- B/C. structured candidates ----------
def revbits(i, k):
    r = 0
    for b in range(k):
        r = (r << 1) | ((i >> b) & 1)
    return r

def bitrev_set(k):
    return [(i, revbits(i, k)) for i in range(1 << k)]

def scaled_copy(pts, s, tx, ty):
    return [(x*s + tx, y*s + ty) for (x, y) in pts]

def search_E5():
    rng = random.Random(142107)
    cands = [("bitrev3", bitrev_set(3))]
    # bitrev variants: reflected versions
    base = bitrev_set(3)
    m = 8
    cands.append(("bitrev3-yflip", [(x, 7-y) for x,y in base]))
    cands.append(("bitrev3-swap", [(y, x) for x,y in base]))
    # nested square + pocket templates
    outer = [(0,0),(20,0),(20,20),(0,20)]
    for dx1 in range(1, 12, 2):
        for dy1 in range(1, 12, 2):
            inner = [(dx1,dy1),(dx1+4,dy1),(dx1+4,dy1+4),(dx1,dy1+4)]
            pts = outer + inner
            if in_general_position(pts) and convex_subset_exists(pts, 5) is None:
                cands.append((f"nested({dx1},{dy1})", pts))
    # random
    for trial in range(600000):
        pts = [(rng.randrange(0, 120), rng.randrange(0, 120)) for _ in range(8)]
        if len(set(pts)) < 8 or not in_general_position(pts):
            continue
        if convex_subset_exists(pts, 5) is None:
            return pts, f"random#{trial}", cands
    # structured only
    for name, pts in cands:
        if in_general_position(pts) and convex_subset_exists(pts, 5) is None:
            return pts, name, cands
    return None, None, cands

def search_E6(E5):
    with open("/home/z/erdos-weak-problems/problem107-happy-ending/experiments/e6_seed.txt", "w") as f:
        f.write(";".join(f"{x},{y}" for x, y in (E5 or [])))
    rng = random.Random(616)
    cands = [("bitrev4", bitrev_set(4))]
    base4 = bitrev_set(4)
    cands.append(("bitrev4-yflip", [(x, 15-y) for x,y in base4]))
    cands.append(("bitrev4-swap", [(y, x) for x,y in base4]))
    # doubling of E5 with searched placements
    if E5:
        maxc = max(x for x,y in E5) + 1
        for s in [2,3,5,7,11,13]:
            for tx in range(50, 400, 37):
                for ty in range(50, 400, 37):
                    B = scaled_copy(E5, s, tx, ty)
                    pts = E5 + B
                    if not in_general_position(pts):
                        continue
                    if convex_subset_exists(pts, 6) is None:
                        return pts, f"double(s={s},t=({tx},{ty}))"
    for name, pts in cands:
        if in_general_position(pts) and convex_subset_exists(pts, 6) is None:
            return pts, name
    # random (wide box)
    for trial in range(300000):
        pts = [(rng.randrange(0, 500), rng.randrange(0, 500)) for _ in range(16)]
        if len(set(pts)) < 16 or not in_general_position(pts):
            continue
        if convex_subset_exists(pts, 6) is None:
            return pts, f"random#{trial}"
    return None, None

def certify(pts, n_gon):
    assert in_general_position(pts), "not general position"
    assert convex_subset_exists(pts, n_gon) is None, f"has convex {n_gon}"
    w = convex_subset_exists(pts, n_gon-1)
    return {"n": len(pts), "no_convex": n_gon, "has_convex": n_gon-1, "witness": w}

def main():
    t0 = time.time()
    out = {}
    print("[A] building realizable 4-pattern set...", flush=True)
    REAL, CONVEX, NONCONVEX, consistent, bad = f4_certificate()
    print(f"[A] realizable 4-patterns: {len(REAL)} (convex: {len(CONVEX)}, nonconvex: {len(NONCONVEX)}); "
          f"consistent 5-chirotopes: {consistent}; without convex-4: {len(bad)} -> theorem {'HOLDS' if not bad else 'FAILS'} [{time.time()-t0:.0f}s]")
    out["f4"] = {"realizable_patterns": len(REAL), "convex_patterns": len(CONVEX),
                 "nonconvex_patterns": len(NONCONVEX), "consistent_chirotopes": consistent,
                 "counterexamples": len(bad), "theorem_holds": len(bad) == 0,
                 "convex_pattern_list": [list(p) for p in sorted(CONVEX)]}
    with open("/home/z/erdos-weak-problems/problem107-happy-ending/experiments/witnesses.json", "w") as f:
        json.dump(out, f, indent=1)
    print("[B] E_5 search...", flush=True)
    E5, how, cands = search_E5()
    print(f"[B] E_5: {how} [{time.time()-t0:.0f}s]")
    if E5:
        out["E5"] = {"points": E5, "found_by": how, "certificate": certify(E5, 5)}
        print(f"[B] certified: {out['E5']['certificate']}")
        with open("/home/z/erdos-weak-problems/problem107-happy-ending/experiments/witnesses.json", "w") as f:
            json.dump(out, f, indent=1)
    print("[C] E_6 search...", flush=True)
    import os
    if os.path.exists("/home/z/erdos-weak-problems/problem107-happy-ending/experiments/e6_seed.txt"):
        sd = open("/home/z/erdos-weak-problems/problem107-happy-ending/experiments/e6_seed.txt").read().strip()
        if sd:
            E5b = [tuple(map(int, p.split(","))) for p in sd.split(";")]
            E6, how6 = search_E6(E5b)
        else:
            E6, how6 = search_E6(E5)
    else:
        E6, how6 = search_E6(E5)
    print(f"[C] E_6: {how6} [{time.time()-t0:.0f}s]")
    if E6:
        out["E6"] = {"points": E6, "found_by": how6, "certificate": certify(E6, 6)}
        print(f"[C] certified: {out['E6']['certificate']}")
    with open("/home/z/erdos-weak-problems/problem107-happy-ending/experiments/witnesses.json", "w") as f:
        json.dump(out, f, indent=1)
    print("WROTE witnesses.json", time.time()-t0, "s total")

if __name__ == "__main__":
    main()
