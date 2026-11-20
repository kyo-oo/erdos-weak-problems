#!/usr/bin/env python3
"""Battery 107: independent re-validation of the K68 kernel claims (python mirror)."""
import itertools, json

def det3(p, q, r):
    return (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0])

def is_extreme(p, rest):
    vecs = [(q[0]-p[0], q[1]-p[1]) for q in rest]
    cands = vecs + [(-a,-b) for a,b in vecs]
    for ux, uy in cands:
        if all((ux*wy-uy*wx > 0) or (ux*wy-uy*wx == 0 and ux*wx+uy*wy > 0) for wx,wy in vecs):
            return True
    return False

def convpos(S):
    return all(is_extreme(S[a], [S[b] for b in range(len(S)) if b != a]) for a in range(len(S)))

def convsubset(P, m):
    return any(convpos(list(S)) for S in itertools.combinations(P, m))

def gp(P):
    return all(det3(P[i],P[j],P[k]) != 0 for i,j,k in itertools.combinations(range(len(P)),3))

ok = True
# E_4: GP + not convex
E4 = [(0,0),(100,0),(0,100),(20,20)]
assert gp(E4) and not convpos(E4), "E4 fail"
# E_5: GP + no convex 5 + has convex 4
d = json.load(open('problem107-happy-ending/experiments/witnesses.json'))
E5 = [tuple(p) for p in d['E5']['points']]
assert gp(E5), "E5 not GP"
assert not convsubset(E5, 5), "E5 has convex 5"
assert convsubset(E5, 4), "E5 lacks convex 4"
# chiroteope certificate: all 2^20 patterns
REAL = [(-1,-1,-1,-1),(-1,-1,1,1),(1,1,-1,-1),(1,1,1,1),(-1,-1,-1,1),(-1,1,1,1),(1,-1,-1,-1),(1,1,1,-1)]
CONV = [(-1,-1,-1,-1),(-1,-1,1,1),(1,1,-1,-1),(1,1,1,1)]
QUADS = [(0,1,3,6),(0,2,4,7),(1,2,5,8),(3,4,5,9),(6,7,8,9)]
bad = 0
for bits in range(1 << 20):
    s = [1 if bits >> (2*i) & 1 else -1 for i in range(10)]
    pats = [tuple(s[i] for i in q) for q in QUADS]
    consistent = all(p in REAL for p in pats)
    has = any(p in CONV for p in pats)
    if consistent and not has:
        bad += 1
        if bad < 3: print(f"CHIRO FAIL at {bits}")
assert bad == 0, f"chirotope certificate failed: {bad}"
print("BATTERY107_ALL_GREEN" if ok else "BATTERY107_FAIL")
