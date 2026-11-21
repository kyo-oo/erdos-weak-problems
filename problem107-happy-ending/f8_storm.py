import json, sys, os, time, pickle
sys.path.insert(0, "/home/z/waves/w81-107a/problem107-happy-ending")
os.chdir("/home/z/waves/w81-107a/problem107-happy-ending")
import engine107f5v4 as V

SEEDS = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [7, 13]
WALK = int(sys.argv[2]) if len(sys.argv) > 2 else 120
t0 = time.time()
t9 = V.TRIPLES(9); rule9 = V.rule_for(9)
free8 = pickle.load(open("/tmp/f8_parents.pkl", "rb"))
print(f"F8 parents: {len(free8)}", flush=True)

types = {}
with open("engine107f5_cache/f9/f9_census.jsonl") as f:
    for line in f:
        d = json.loads(line)
        types[d["ck"]] = d

bpath = "/tmp/f8_batch.txt"; opath = "/tmp/f8_out.txt"
V.write_batch(bpath, [(V.pack_signs(ck), 8, rec["chi"], rec["pts"]) for (ck, rec) in free8])

children_seen = {}   # ck -> record (all distinct children across seeds)
new_to_census = 0
convex5_free_children = []
out = open("engine107f5_cache/f9/f9_census.jsonl", "a")
for seed in SEEDS:
    V.run_engine(bpath, opath, walk_steps=WALK, seed=seed)
    children, stats, errors = V.read_engine_output(opath, 9)
    assert not errors
    fresh_child = 0
    for (ckhex, chihex, coords) in children:
        if ckhex in children_seen:
            continue
        children_seen[ckhex] = True
        fresh_child += 1
        pts = [(V.parse_frac(coords[2*i]), V.parse_frac(coords[2*i+1])) for i in range(9)]
        chi = tuple(V.chi_of_points(pts))
        ok = (all(s != 0 for s in chi)) and V.is_gp(pts)
        ck = V.pack_signs(V.canonical_key(chi, 9, rule9)) if ok else None
        certified = ok and (ck == ckhex)
        if not certified:
            print(f"  !! uncertifiable child {ckhex[:12]} — skipped", flush=True)
            continue
        hull = len(V.chi_hull_vertices(chi, 9, rule9))
        rec = {"ck": ck, "chi": V.pack_signs(chi), "pts": [[str(x), str(y)] for (x, y) in pts], "hull": hull}
        # THE DECISIVE CHECK: convex-5 two-code
        wa = V.chi_convex5_method_a(chi, 9, rule9)
        wb = V.chi_convex5_method_b(chi, 9, rule9)
        if wa is None and wb is None:
            convex5_free_children.append((ck, hull))
            print(f"  !!! CONVEX-5-FREE CHILD FOUND: {ck[:14]} hull={hull} — f(5) > 9?!", flush=True)
        if ck not in types:
            out.write(json.dumps(rec) + "\n"); out.flush()
            types[ck] = rec
            new_to_census += 1
    print(f"seed {seed}: +{fresh_child} distinct children (union {len(children_seen)}); census +{new_to_census} [{time.time()-t0:.0f}s]", flush=True)
out.close()
print(f"STORM DONE: union children of F8: {len(children_seen)}; new-to-census: {new_to_census}; CONVEX-5-FREE CHILDREN: {len(convex5_free_children)}", flush=True)
print(f"census now: {len(types)}", flush=True)
