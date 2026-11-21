import json, sys, os, time, pickle
sys.path.insert(0, "/home/z/waves/w81-107a/problem107-happy-ending")
os.chdir("/home/z/waves/w81-107a/problem107-happy-ending")
import engine107f5v4 as V

t0 = time.time()
t8 = V.TRIPLES(8); rule8 = V.rule_for(8)
bank = V._load_bank(8)
print(f"n=8 bank: {len(bank)} reflection-distinguished types", flush=True)

free8 = []
for ck, rec in bank.items():
    chi = tuple(rec["chi"])
    wa = V.chi_convex5_method_a(chi, 8, rule8)
    wb = V.chi_convex5_method_b(chi, 8, rule8)
    if wa is None and wb is None:
        free8.append((ck, rec))
    elif (wa is None) != (wb is None):
        print(f"  !! method disagreement at {str(ck)[:40]}", flush=True)
print(f"CONVEX-5-FREE 8-point types: {len(free8)}", flush=True)
for ck, rec in free8:
    hull = len(V.chi_hull_vertices(tuple(rec["chi"]), 8, rule8))
    print(f"  F8 type hull={hull} chi[:8]={rec['chi'][:8]}", flush=True)
with open("/tmp/f8_parents.pkl", "wb") as f:
    pickle.dump(free8, f)
print(f"wall {time.time()-t0:.0f}s", flush=True)
