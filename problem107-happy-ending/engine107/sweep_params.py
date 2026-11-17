#!/usr/bin/env python3
"""Sweep ErSz61 parameters for the smallest integer coordinates."""
import sys, math, itertools
from fractions import Fraction as F
import importlib.util
spec = importlib.util.spec_from_file_location("mb", "doubter/mirror_battery.py")
mb = importlib.util.module_from_spec(spec)
sys.modules["mb"] = mb
spec.loader.exec_module(mb)

def cross(o, a, b):
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
def intri(p, u, v, w):
    c1, c2, c3 = cross(u,v,p), cross(v,w,p), cross(w,u,p)
    return (c1 > 0 and c2 > 0 and c3 > 0) or (c1 < 0 and c2 < 0 and c3 < 0)

def verify(pts, n):
    N = len(pts)
    for i,j,k in itertools.combinations(range(N),3):
        if cross(pts[i],pts[j],pts[k]) == 0: return False
    for sub in itertools.combinations(range(N), n):
        S = [pts[i] for i in sub]
        found = False
        for i in range(n):
            others = [S[j] for j in range(n) if j != i]
            for tri in itertools.combinations(others, 3):
                if intri(S[i], *tri): found = True; break
            if found: break
        if not found: return False
    return True

best = {}
for eps_e in (4, 6, 8, 10, 12):
    for w_num, w_den in ((41,100), (3,8), (2,5), (9,25)):
        for alpha, beta, gamma, c in ((F(1,4),F(1,2),F(3,4),4),
                                       (F(1,5),F(2,5),F(4,5),3),
                                       (F(1,3),F(1,2),F(2,3),3),
                                       (F(1,6),F(1,3),F(1,2),3)):
            try:
                params = dict(w=F(w_num,w_den), eps=F(1,2**eps_e),
                              alpha=alpha, beta=beta, gamma=gamma, c=c)
                pts5, _, m5 = mb.build_ersz61(5, **params)
                ok5 = verify(pts5, 5)
                if not ok5: continue
                mx5 = max(max(abs(p[0]),abs(p[1])) for p in pts5)
                pts6, _, m6 = mb.build_ersz61(6, **params)
                ok6 = verify(pts6, 6)
                mx6 = max(max(abs(p[0]),abs(p[1])) for p in pts6)
                tag = f"eps=2^-{eps_e} w={w_num}/{w_den} a={alpha} b={beta} g={gamma} c={c}"
                print(f"{tag}: n5 max={mx5:.3e} ok6={ok6} n6max={mx6:.3e}")
                if ok6 and mx5 < best.get("mx5", 10**30):
                    best = dict(mx5=mx5, mx6=mx6, params=params, tag=tag,
                                pts5=pts5, pts6=pts6)
            except Exception as ex:
                pass
print("BEST:", best.get("tag"), "mx5=%.3e mx6=%.3e" % (best.get("mx5",0), best.get("mx6",0)))
if best:
    import json
    json.dump({"params": {k: f"{v.numerator}/{v.denominator}" if isinstance(v,F) else v
                          for k,v in best["params"].items()},
               "pts5": best["pts5"], "pts6": best["pts6"]},
              open("witness_best.json","w"))
    print("saved witness_best.json")
