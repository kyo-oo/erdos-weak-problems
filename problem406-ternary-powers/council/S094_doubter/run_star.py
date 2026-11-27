"""v2* curve runs: three flavors, incremental JSONL output.

  star0 : v2*_0(M) = max{v2 : S contains 0, S subseteq [0,M]}  (== v2*(M) by
          shift-invariance; computed by TargetMITM with forced {0} over [1..M])
  full  : v2*(M)  unconstrained nonempty (FullMITM, valid M <= 40)
  g     : g(m) = max{v2 : {0,m} subseteq S subseteq [0,m]}  (fresh-at-m curve;
          the TRUE cap-relevant excess is g(m) - m)

usage: run_star.py <star0|full|g> <M_lo> <M_hi>
appends records to star0.jsonl / full.jsonl / g.jsonl
"""
import sys, json, time
sys.path.insert(0, "/home/z/erdos-weak-problems/problem406-ternary-powers/council/S094_doubter")
from lib import TargetMITM, FullMITM

mode, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
OUT = f"/home/z/erdos-weak-problems/problem406-ternary-powers/council/S094_doubter/{mode}.jsonl"

for M in range(lo, hi + 1):
    t0 = time.perf_counter()
    if mode == "star0":
        mitm = TargetMITM([0], list(range(1, M + 1)))
        v, w, info = mitm.solve()
        rec = {"M": M, "v2star0": v, "witness": w,
               "popcount": len(w) if w else None, **info,
               "wall": round(time.perf_counter() - t0, 2)}
    elif mode == "full":
        mitm = FullMITM(list(range(0, M + 1)))
        v, w, info = mitm.solve()
        rec = {"M": M, "v2star_full": v, "witness": w,
               "popcount": len(w) if w else None, **info,
               "wall": round(time.perf_counter() - t0, 2)}
    elif mode == "g":
        if m0 := M:
            pass
        if M == 0:
            rec = {"m": 0, "g": 0, "witness": [0], "popcount": 1, "mode": "trivial",
                   "probes": 0, "sec": 0.0, "wall": 0.0}
        else:
            forced = [0, M] if M >= 1 else [0]
            mitm = TargetMITM(forced, list(range(1, M)))
            v, w, info = mitm.solve()
            rec = {"m": M, "g": v, "witness": w,
                   "popcount": len(w) if w else None, **info,
                   "wall": round(time.perf_counter() - t0, 2)}
    else:
        raise SystemExit("unknown mode")
    with open(OUT, "a") as f:
        f.write(json.dumps(rec) + "\n")
    print(json.dumps(rec), flush=True)
