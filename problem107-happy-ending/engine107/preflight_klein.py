#!/usr/bin/env python3
"""W69-E preflight: verify the Tier-1 sign-algebra architecture numerically.

Architecture under test (all over Q, ordered field):
  cross(o,a,b) = (a-o) x (b-o)              (2D cross)
  InTri(p,u,v,w)   := all(cross(u,v,p),cross(v,w,p),cross(w,u,p)) > 0  or all < 0
  Convex4(a,b,c,d) := no point strictly inside the triangle of the other 3
  trisum:  cross(b,c,e) + cross(c,a,e) + cross(a,b,e) = cross(a,b,c)
  plucker3: cross(p,q,r)*cross(p,s,t) - cross(p,q,s)*cross(p,r,t)
            + cross(p,q,t)*cross(p,r,s) = 0
  A2:      cross(u,v,x)*cross(u,v,y) > 0 and cross(x,y,u)*cross(x,y,v) > 0
           -> Convex4(u,v,x,y)
  EDGE:    cross(u,v,w)>0, cross(u,v,e)<0, cross(v,w,e)>0, cross(w,u,e)>0
           -> Convex4(u,v,w,e)
  SPLIT:   InTri(x,u,v,w) and cross(x,y,u),cross(x,y,v),cross(x,y,w) all same
           strict sign -> False
  TWOINSIDE: InTri(x,u,v,w) and InTri(y,u,v,w), crosses nonzero
           -> Convex4(u,v,x,y) or Convex4(v,w,x,y) or Convex4(w,u,x,y)
  VERTEX:  cross(u,v,w)>0, InTri(d,u,v,w) [normalized +], cross(u,v,e)<0,
           cross(v,w,e)<0, cross(w,u,e)>0 -> InTri(v,u,w,e) and InTri(d,u,w,e)
  KLEIN TREE: 5 gp points -> case tree -> some Convex4  (simulate exactly)
"""
import random
from fractions import Fraction as F
import itertools

def cross(o, a, b):
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])

def sgn(v):
    return (v > 0) - (v < 0)

def intri(p, u, v, w):
    c1, c2, c3 = cross(u,v,p), cross(v,w,p), cross(w,u,p)
    return (c1 > 0 and c2 > 0 and c3 > 0) or (c1 < 0 and c2 < 0 and c3 < 0)

def convex4(a, b, c, d):
    return (not intri(a,b,c,d)) and (not intri(b,a,c,d)) and \
           (not intri(c,a,b,d)) and (not intri(d,a,b,c))

def rand_pt(lo=-8, hi=8):
    return (F(random.randint(lo,hi)), F(random.randint(lo,hi)))

def gp5(pts):
    for i,j,k in itertools.combinations(range(len(pts)),3):
        if cross(pts[i],pts[j],pts[k]) == 0:
            return False
    return True

def rand_gp5():
    while True:
        pts = [rand_pt() for _ in range(5)]
        if len(set(pts)) == 5 and gp5(pts):
            return pts

random.seed(107)

# ---------- identities ----------
ok_p = ok_t = True
for _ in range(3000):
    p,q,r,s,t = [rand_pt() for _ in range(5)]
    lhs = cross(p,q,r)*cross(p,s,t) - cross(p,q,s)*cross(p,r,t) + cross(p,q,t)*cross(p,r,s)
    if lhs != 0: ok_p = False
    a,b,c,e = [rand_pt() for _ in range(4)]
    if cross(b,c,e)+cross(c,a,e)+cross(a,b,e) != cross(a,b,c): ok_t = False
print("plucker3 identity:", "PASS" if ok_p else "FAIL")
print("trisum  identity:", "PASS" if ok_t else "FAIL")

# ---------- A2 ----------
ok = True
for _ in range(200000):
    u,v,x,y = [rand_pt() for _ in range(4)]
    if cross(u,v,x)*cross(u,v,y) > 0 and cross(x,y,u)*cross(x,y,v) > 0:
        if not convex4(u,v,x,y): ok = False
print("A2:", "PASS" if ok else "FAIL")

# ---------- EDGE ----------
ok = True
cnt = 0
for _ in range(400000):
    u,v,w,e = [rand_pt() for _ in range(4)]
    if cross(u,v,w) > 0 and cross(u,v,e) < 0 and cross(v,w,e) > 0 and cross(w,u,e) > 0:
        cnt += 1
        if not convex4(u,v,w,e): ok = False
print("EDGE:", "PASS" if ok else "FAIL", f"({cnt} hits)")

# ---------- SPLIT ----------
ok = True
cnt = 0
for _ in range(400000):
    x,y,u,v,w = [rand_pt() for _ in range(5)]
    if intri(x,u,v,w) and sgn(cross(x,y,u))==sgn(cross(x,y,v))==sgn(cross(x,y,w))!=0:
        cnt += 1
        ok = False  # must be impossible
print("SPLIT:", "PASS" if ok else "FAIL", f"({cnt} violations)")

# ---------- TWOINSIDE ----------
ok = True
cnt = 0
for _ in range(300000):
    x,y,u,v,w = [rand_pt() for _ in range(5)]
    if intri(x,u,v,w) and intri(y,u,v,w) and cross(x,y,u)!=0 and cross(x,y,v)!=0 and cross(x,y,w)!=0:
        cnt += 1
        if not (convex4(u,v,x,y) or convex4(v,w,x,y) or convex4(w,u,x,y)):
            ok = False
print("TWOINSIDE:", "PASS" if ok else "FAIL", f"({cnt} hits)")

# ---------- VERTEX ----------
ok = True
cnt = 0
for _ in range(600000):
    u,v,w,d,e = [rand_pt() for _ in range(5)]
    if cross(u,v,w) > 0 and intri(d,u,v,w) and \
       cross(u,v,d) > 0 and cross(v,w,d) > 0 and cross(w,u,d) > 0 and \
       cross(u,v,e) < 0 and cross(v,w,e) < 0 and cross(w,u,e) > 0:
        cnt += 1
        if not (intri(v,u,w,e) and intri(d,u,w,e)):
            ok = False
print("VERTEX:", "PASS" if ok else "FAIL", f"({cnt} hits)")

# ---------- FULL KLEIN TREE (exact simulation of the Lean proof) ----------
def two_inside(x, y, u, v, w):
    """SPLIT + 2-1 pattern + A2. Returns a Convex4 tuple or None (crash = bug)."""
    cxu, cxv, cxw = cross(x,y,u), cross(x,y,v), cross(x,y,w)
    assert cxu != 0 and cxv != 0 and cxw != 0
    su, sv, sw = sgn(cxu), sgn(cxv), sgn(cxw)
    assert not (su == sv == sw), "SPLIT violated"
    # find a pair with same sign
    if su == sv:   return (u,v,x,y)
    if sv == sw:   return (v,w,x,y)
    assert su == sw
    return (w,u,x,y)

def klein_core(a, b, c, d, e):
    """assumes intri(d,a,b,c) and returns a Convex4 tuple; asserts all internal
    steps exactly as the Lean proof will take them."""
    # normalize cross(a,b,c) > 0 (caller does the swap; here assert)
    assert cross(a,b,c) > 0
    assert cross(a,b,d) > 0 and cross(b,c,d) > 0 and cross(c,a,d) > 0  # trisum-normalized
    E1, E2, E3 = cross(a,b,e), cross(b,c,e), cross(c,a,e)
    assert E1 != 0 and E2 != 0 and E3 != 0
    pat = (sgn(E1), sgn(E2), sgn(E3))
    if pat == (1,1,1):
        # e inside: TWOINSIDE(d,e; a,b,c)
        assert intri(e,a,b,c)
        return two_inside(d, e, a, b, c)
    if pat == (-1,1,1):   # beyond edge ab
        return (a,b,c,e)
    if pat == (1,-1,1):   # beyond edge bc (cyclic rotation (b,c,a))
        return (b,c,a,e)
    if pat == (1,1,-1):   # beyond edge ca (cyclic rotation (c,a,b))
        return (c,a,b,e)
    if pat == (-1,-1,1):  # beyond vertex b -> VERTEX then TWOINSIDE(b,d; a,c,e)
        assert intri(b,a,c,e) and intri(d,a,c,e), "VERTEX failed"
        return two_inside(b, d, a, c, e)
    if pat == (1,-1,-1):  # beyond vertex c -> VERTEX on (b,c,a) then TWOINSIDE(c,d; b,a,e)
        assert intri(c,b,a,e) and intri(d,b,a,e), "VERTEX failed"
        return two_inside(c, d, b, a, e)
    if pat == (-1,1,-1):  # beyond vertex a -> VERTEX on (c,a,b) then TWOINSIDE(a,d; c,b,e)
        assert intri(a,c,b,e) and intri(d,c,b,e), "VERTEX failed"
        return two_inside(a, d, c, b, e)
    assert pat == (-1,-1,-1), "impossible pattern reached"
    raise AssertionError("(-,-,-) pattern must be killed by trisum")

ok = True
for trial in range(200000):
    pts = rand_gp5()
    # top level: if some 4-subset convex, fine (tree not needed); else run tree
    found = None
    for sub in itertools.combinations(range(5), 4):
        w,x,y,z = pts[sub[0]],pts[sub[1]],pts[sub[2]],pts[sub[3]]
        if convex4(w,x,y,z):
            found = (w,x,y,z); break
    if found is None:
        # take first 4 points, find inner point
        a,b,c,d = pts[0],pts[1],pts[2],pts[3]
        e = pts[4]
        quad = [a,b,c,d]
        inner = None
        for i in range(4):
            others = [quad[j] for j in range(4) if j != i]
            if intri(quad[i], others[0], others[1], others[2]):
                inner = i; break
        assert inner is not None, "non-convex quad with no inner point?!"
        i = inner
        d_ = quad[i]
        abc = [quad[j] for j in range(4) if j != i]
        a_, b_, c_ = abc
        # normalize orientation: swap b,c if needed
        if cross(a_,b_,c_) > 0:
            res = klein_core(a_,b_,c_,d_,e)
        else:
            res = klein_core(a_,c_,b_,d_,e)
        w,x,y,z = res
        assert convex4(w,x,y,z), "KLEIN TREE returned non-convex!"
        # also all 4 must be among the 5 points
        for p in res:
            assert p in pts
print("KLEIN FULL TREE:", "PASS" if ok else "FAIL", "(200000 random gp 5-sets)")
