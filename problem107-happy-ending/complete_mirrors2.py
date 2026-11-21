import json, sys, os, time
sys.path.insert(0, "/home/z/waves/w81-107a/problem107-happy-ending")
os.chdir("/home/z/waves/w81-107a/problem107-happy-ending")
from fractions import Fraction
import engine107f5v4 as V

t0 = time.time()
t9 = V.TRIPLES(9)
rule9 = V.rule_for(9)
types = {}
with open("engine107f5_cache/f9/f9_census.jsonl") as f:
    for line in f:
        d = json.loads(line)
        types[d["ck"]] = d
print(f"census: {len(types)}", flush=True)

orphans = []
for ck, d in types.items():
    chi = V.unpack_signs(d["chi"], len(t9))
    negk = V.pack_signs(V.canonical_key(tuple(-s for s in chi), 9, rule9))
    if negk not in types:
        orphans.append((ck, negk, d))
print(f"orphans: {len(orphans)}", flush=True)

added = 0
lines = []
for ck, negk, d in orphans:
    pts = [(Fraction(p[0]), Fraction(p[1])) for p in d["pts"]]
    mpts = [(x, -y) for (x, y) in pts]
    mchi = tuple(V.chi_of_points(mpts))
    ochi = tuple(-s for s in V.unpack_signs(d["chi"], len(t9)))
    assert all(s != 0 for s in mchi), "GP violation"
    assert mchi == ochi, "mirror chi mismatch"
    mck = V.pack_signs(V.canonical_key(mchi, 9, rule9))
    assert mck == negk, "canon mismatch"
    assert V.is_gp(mpts), "is_gp fail"
    hull = len(V.chi_hull_vertices(mchi, 9, rule9))
    rec = {"ck": mck, "chi": V.pack_signs(mchi),
           "pts": [[str(x), str(y)] for (x, y) in mpts], "hull": hull}
    lines.append(json.dumps(rec))
    added += 1
    print(f"  + mirror {ck[:12]} -> {mck[:12]} hull={hull}", flush=True)

with open("engine107f5_cache/f9/f9_census.jsonl", "a") as f:
    for ln in lines:
        f.write(ln + "\n")
print(f"added {added}; census now {len(types)+added}; wall {time.time()-t0:.0f}s", flush=True)
