#!/usr/bin/env python3
"""E_6 hunt: 16 points, no convex 6-gon. Families: (a) k nested quads, (b) E_5 u tiny(E_5)
at pocket/center placements, (c) E_5 u scaled/rotated copies. Exact certification only."""
import json, itertools, time

def det3(p, q, r):
    return (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0])

def is_extreme(p, rest):
    vecs = [(q[0]-p[0], q[1]-p[1]) for q in rest]
    cands = vecs + [(-a, -b) for a, b in vecs]
    for (ux, uy) in cands:
        ok = True
        for (wx, wy) in vecs:
            c = ux*wy - uy*wx
            d = ux*wx + uy*wy
            if c <= 0 and d <= 0:
                ok = False
                break
            if c < 0:
                ok = False
                break
        if ok:
            return True
    return False

def conv_pos(pts, idxs):
    S = [pts[i] for i in idxs]
    m = len(S)
    if m <= 2:
        return True
    for a in range(m):
        p = S[a]
        rest = [S[b] for b in range(m) if b != a]
        if not is_extreme(p, rest):
            return False
    return True

def has_convex(pts, m):
    for idxs in itertools.combinations(range(len(pts)), m):
        if conv_pos(pts, idxs):
            return list(idxs)
    return None

def gp(pts):
    for t in itertools.combinations(range(len(pts)), 3):
        if det3(pts[t[0]], pts[t[1]], pts[t[2]]) == 0:
            return False
    return True

d = json.load(open('witnesses.json'))
E5 = [tuple(p) for p in d['E5']['points']]

def scale_about(pts, s, cx, cy):
    return [(int(round(cx + s*(x-cx))), int(round(cy + s*(y-cy)))) for x, y in pts]

def affine(pts, a, b, c, dd, tx, ty):
    """x' = a x + b y + tx ; y' = c x + d y + ty (integers)"""
    return [(a*x + b*y + tx, c*x + dd*y + ty) for x, y in pts]

t0 = time.time()
found = None
# (b) E_5 u tiny(E_5): center-scaled and vertex-pocket placements
import statistics
cx = statistics.mean(x for x, y in E5)
cy = statistics.mean(y for x, y in E5)
cands = []
for s_num, s_den in [(1,3),(1,4),(1,5),(2,3),(1,6),(3,7),(1,8),(2,7)]:
    inner = [(int(round(cx + (x-cx)*s_num/s_den)), int(round(cy + (y-cy)*s_num/s_den))) for x, y in E5]
    pts = E5 + inner
    if len(set(pts)) == 16:
        cands.append((f"center-scale {s_num}/{s_den}", pts))
# pocket at each hull vertex: tiny copy near vertex v, scaled about v
hull = [E5[i] for i in [0, 2, 4, 7]]
for (vx, vy) in hull:
    for s_num, s_den in [(1,5),(1,7),(1,9),(1,11)]:
        inner = [(int(round(vx + (x-vx)*s_num/s_den)), int(round(vy + (y-vy)*s_num/s_den))) for x, y in E5]
        pts = E5 + inner
        if len(set(pts)) == 16:
            cands.append((f"pocket({vx},{vy}) {s_num}/{s_den}", pts))
# rotated/scaled copies (integer affine, det != 0)
for (a, b, c, dd) in [(0,1,1,0),(1,1,-1,1),(2,1,1,1),(1,2,1,1),(3,-1,1,3),(1,-1,1,1),(2,-1,1,2)]:
    for tx in range(-200, 300, 40):
        for ty in range(-200, 300, 40):
            B = affine(E5, a, b, c, dd, tx, ty)
            pts = E5 + B
            if len(set(pts)) == 16:
                cands.append((f"affine({a},{b},{c},{dd},{tx},{ty})", pts))

print(f"candidates: {len(cands)}")
for name, pts in cands:
    if not gp(pts):
        continue
    r = has_convex(pts, 6)
    if r is None:
        w5 = has_convex(pts, 5)
        print(f"E_6 FOUND: {name} [{time.time()-t0:.0f}s]; has convex 5: {w5 is not None}")
        found = (name, pts)
        json.dump({"E6": {"points": pts, "found_by": name,
                          "certificate": {"n": 16, "no_convex": 6, "has_convex": 5,
                                          "witness5": w5}}},
                  open('e6_found.json', 'w'), indent=1)
        break
if not found:
    print(f"no E_6 in family search [{time.time()-t0:.0f}s]")
