#!/usr/bin/env python3
"""THE POCKET-DOUBLING HUNT: discover the ES recursion rule R such that
E_{n+1} = E_n u R(E_n) (tiny rotated copy in a hull-vertex pocket) has no convex (n+1)-gon.
Level 1: E_4 (triangle+center) u tiny(R(E_4)) -> must have NO convex 5 (that's E_5).
Level 2: E_5 u tiny(R(E_5)) -> must have NO convex 6 (that's E_6 = THE TARGET).
Exact certification; integer coordinates (rational rotations)."""
import itertools, time, json

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
            if c < 0 or (c == 0 and d <= 0):
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
        if not is_extreme(S[a], [S[b] for b in range(m) if b != a]):
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

# rational rotations (a/b, c/b) with a^2+c^2 = b^2
ROTS = [(1,0,1),(0,1,1),(3,4,5),(4,3,5),(5,12,13),(12,5,13),(8,15,17),(15,8,17),(7,24,25),(20,21,29),(21,20,29)]

def rot_scale(pts, ra, rc, rb, s_num, s_den, cx, cy, ox, oy):
    """rotate by (ra,rc)/rb, scale by s_num/s_den about (cx,cy), translate by (ox,oy)."""
    out = []
    for x, y in pts:
        dx, dy = x - cx, y - cy
        nx = (ra*dx - rc*dy)
        ny = (rc*dx + ra*dy)
        out.append((nx*s_num + ox*(rb*s_den), ny*s_num + oy*(rb*s_den)))
    return out

def normalize(pts):
    """shift to positive coords"""
    mx = min(x for x, y in pts); my = min(y for x, y in pts)
    return [(x-mx, y-my) for x, y in pts]

t0 = time.time()
E4 = [(0, 0), (600, 0), (0, 600), (90, 90)]  # triangle + center-ish

# HUNT LEVEL 1: E_5 = E_4 u tiny(E_4) at each hull vertex pocket
level1 = []
for (vx, vy) in [(0,0), (600,0), (0,600)]:
    for (ra, rc, rb) in ROTS:
        for s_num, s_den in [(1,20),(1,30),(1,40),(1,60),(1,80),(1,120),(1,160),(1,240)]:
            # pocket offset: inward direction depends on vertex; try small inward offsets
            for (ox, oy) in [(2,2),(5,5),(10,10),(2,8),(8,2),(3,12),(12,3)]:
                copy = rot_scale(E4, ra, rc, rb, s_num, s_den, vx, vy, vx*rb*s_den//s_num + ox, vy*rb*s_den//s_num + oy)
                # the translation above re-centers the copy AT the vertex then offsets — redo cleanly:
                # simpler: work directly:
                pass
# cleaner approach: build the copy explicitly
def pocket_copy(base, vx, vy, ra, rc, rb, s_num, s_den, offx, offy):
    out = []
    for x, y in base:
        dx, dy = x - vx, y - vy
        nx = ra*dx - rc*dy
        ny = rc*dx + ra*dy
        out.append((vx + (nx*s_num)//(rb*s_den) + offx, vy + (ny*s_num)//(rb*s_den) + offy))
    return out

level1 = []
for (vx, vy) in [(0,0), (600,0), (0,600)]:
    for (ra, rc, rb) in ROTS:
        for s_num, s_den in [(1,20),(1,30),(1,40),(1,60),(1,80),(1,120),(1,160)]:
            for (offx, offy) in [(2,2),(4,4),(8,8),(16,16),(3,10),(10,3),(6,20),(20,6)]:
                copy = pocket_copy(E4, vx, vy, ra, rc, rb, s_num, s_den, offx, offy)
                pts = E4 + copy
                if len(set(pts)) < 8 or not gp(pts):
                    continue
                if has_convex(pts, 5) is None:
                    level1.append((f"v=({vx},{vy}) rot={ra},{rc}/{rb} s={s_num}/{s_den} off=({offx},{offy})", pts))
print(f"LEVEL 1 (E_5 candidates): {len(level1)} found [{time.time()-t0:.0f}s]", flush=True)

# HUNT LEVEL 2: E_6 = E_5 u pocket(E_5) — try the level-1 winners with the same/other params
level2 = []
tries = 0
for (name1, E5) in level1[:40]:
    hull5 = has_convex(E5, 4)  # some convex 4 (the outer triangle vertices etc.)
    # hull vertices of E5: compute
    def hull_vertices(pts):
        n = len(pts); h = []
        for i in range(n):
            rest = [pts[j] for j in range(n) if j != i]
            if is_extreme(pts[i], rest):
                h.append(pts[i])
        return h
    HV = hull_vertices(E5)
    for (vx, vy) in HV:
        for (ra, rc, rb) in ROTS:
            for s_num, s_den in [(1,30),(1,50),(1,80),(1,120),(1,200),(1,300)]:
                for (offx, offy) in [(2,2),(4,4),(8,8),(3,9),(9,3),(12,12)]:
                    copy = pocket_copy(E5, vx, vy, ra, rc, rb, s_num, s_den, offx, offy)
                    pts = E5 + copy
                    tries += 1
                    if len(set(pts)) < 16 or not gp(pts):
                        continue
                    if has_convex(pts, 6) is None:
                        w5 = has_convex(pts, 5)
                        level2.append((f"{name1} | v=({vx},{vy}) rot={ra},{rc}/{rb} s={s_num}/{s_den} off=({offx},{offy})", pts))
                        print(f"E_6 FOUND: {level2[-1][0]} tries={tries} [{time.time()-t0:.0f}s]", flush=True)
                        json.dump({"E6": {"points": pts, "found_by": level2[-1][0],
                                          "parent_E5": E5,
                                          "certificate": {"n": 16, "no_convex": 6,
                                                          "has_convex5": w5 is not None}}},
                                  open('e6_found.json', 'w'), indent=1)
                        break
                if level2: break
            if level2: break
        if level2: break
    if level2: break
if not level2:
    print(f"no E_6 yet (level-1 E5s: {len(level1)}, pocket tries: {tries}) [{time.time()-t0:.0f}s]")
