#!/usr/bin/env python3
from fractions import Fraction as F
"""W69-E: extract ErSz61 witness coordinates (n=5 -> 8 pts, n=6 -> 16 pts)
via the CI-green mirror_battery builder, verify gp + no-convex-n exactly,
and emit Lean literal code."""
import sys, json, math, itertools
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

default = dict(w=F(41,100), eps=F(1, 2**20),
               alpha=F(1,4), beta=F(1,2),
               gamma=F(3,4), c=4)

out = {}
for n in (5, 6):
    pts, owner, meta = mb.build_ersz61(n, **default)
    N = len(pts)
    print(f"n={n}: |X|={N} (expect 2^{n-2}={2**(n-2)}), den={meta['denominator']}, "
          f"sizes={meta['cluster_sizes']}")
    print("  coord ranges:", min(p[0] for p in pts), max(p[0] for p in pts),
          min(p[1] for p in pts), max(p[1] for p in pts))
    print("  max |coord|:", max(max(abs(p[0]),abs(p[1])) for p in pts))
    # gp check
    ncol = 0
    for i,j,k in itertools.combinations(range(N),3):
        assert cross(pts[i],pts[j],pts[k]) != 0, f"COLLINEAR {i},{j},{k}"
        ncol += 1
    print(f"  gp: all {ncol} triples non-collinear OK")
    # no convex n-gon: every n-subset has an inner point
    bad = 0; total = 0
    for sub in itertools.combinations(range(N), n):
        total += 1
        S = [pts[i] for i in sub]
        found = False
        for i in range(n):
            others = [S[j] for j in range(n) if j != i]
            for tri in itertools.combinations(others, 3):
                if intri(S[i], *tri):
                    found = True; break
            if found: break
        if not found:
            bad += 1
            print(f"  CONVEX {n}-SUBSET FOUND: {sub}")
    print(f"  no-convex-{n}: {total} subsets, {bad} convex (expect 0)")
    out[f"n{n}"] = pts

# emit Lean literal code
def lean_pt(p): return f"({p[0]}, {p[1]})"
with open("witness_coords_lean.txt","w") as f:
    for key, pts in out.items():
        name = "P8" if key=="n5" else "P16"
        f.write(f"def {name} : List (Int × Int) :=\n")
        f.write("  [" + ", ".join(lean_pt(p) for p in pts) + "]\n\n")
        f.write(f"-- {name}: {len(pts)} points, gp, no convex {5 if key=='n5' else 6}-gon\n\n")
print("wrote witness_coords_lean.txt")
json.dump({k: [list(map(str,p)) for p in v] for k,v in out.items()},
          open("witness_coords.json","w"), indent=1)
