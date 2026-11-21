import json, sys, os, time
sys.path.insert(0, "/home/z/waves/w81-107a/problem107-happy-ending")
os.chdir("/home/z/waves/w81-107a/problem107-happy-ending")
import engine107f5v4 as V

t0 = time.time()
t9 = V.TRIPLES(9); rule9 = V.rule_for(9)
types = {}
with open("engine107f5_cache/f9/f9_census.jsonl") as f:
    for line in f:
        d = json.loads(line)
        types[d["ck"]] = d
items = list(types.items())
print(f"census: {len(items)}", flush=True)

hull_census = {}
bad = []
n_le4 = 0
witness_agree = 0
for i, (ck, d) in enumerate(items):
    chi = V.unpack_signs(d["chi"], len(t9))
    h = d.get("hull")
    if h is None:
        h = len(V.chi_hull_vertices(chi, 9, rule9))
    hull_census[h] = hull_census.get(h, 0) + 1
    if h >= 5:
        continue
    n_le4 += 1
    wa = V.chi_convex5_method_a(chi, 9, rule9)
    wb = V.chi_convex5_method_b(chi, 9, rule9)
    if wa is None and wb is None:
        bad.append((ck, h, "CONVEX5-FREE"))
    elif (wa is None) != (wb is None):
        bad.append((ck, h, "method-disagreement"))
    else:
        if wa is not None and V.chi_witness_is_convex_both(chi, 9, rule9, wa):
            witness_agree += 1
    if (i + 1) % 50000 == 0:
        print(f"  {i+1}/{len(items)} ({time.time()-t0:.0f}s) le4 checked: {n_le4}, bad: {len(bad)}", flush=True)

print(f"HULL CENSUS: {dict(sorted(hull_census.items()))}", flush=True)
print(f"hull<=4 checked (two-code): {n_le4}; witness-verified: {witness_agree}", flush=True)
print(f"CONVEX-5-FREE TYPES: {len(bad)}", flush=True)
if bad:
    for b in bad[:10]:
        print("  !!", b, flush=True)
print(f"VERDICT: {'EVERY hull<=4 type in the census CONTAINS a convex 5 (two-code)' if not bad else 'FAILURES PRESENT'}", flush=True)
print(f"wall {time.time()-t0:.0f}s", flush=True)
