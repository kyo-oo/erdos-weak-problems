#!/usr/bin/env python3
"""ENGINE-142 EXTENSION — extend the certified r_k tables beyond the salvage base.
k=3: N=29..38 (hard, cap 300s each); k=4: N=21..45; k=5: N=21..60; k=6: N=21..75.
Loads existing tables_rk.json, extends in place, saves continuously."""
import json, time, os
import engine_rk as E

PATH = "/home/z/erdos-weak-problems/problem142-ap-free/experiments/tables_rk.json"

def load():
    with open(PATH) as f:
        return json.load(f)

def save(d):
    with open(PATH, "w") as f:
        json.dump(d, f, indent=1)

def extend(k, N_start, N_end, cap):
    d = load()
    table = d[str(k)]
    prev = None
    for N in range(N_start, N_end + 1):
        key = str(N)
        if key in table and table[key].get("certified"):
            prev = table[key]["witness"]
            continue
        t0 = time.time()
        seed = [v for v in prev if v < N] if prev else E.greedy_lower(N, k)
        if not E.witness_valid(seed, N, k):
            seed = E.greedy_lower(N, k)
        best, opt = E.bnb(N, k, seed, time_cap=cap)
        val = len(best)
        w_sat = E.z3_rk(N, k, val)
        w_unsat = E.z3_rk(N, k, val + 1)
        agree = (w_sat is not None) and (w_unsat is None)
        certified = agree and opt
        # if bnb timed out but z3 proves val+1 impossible and val witnessed -> still certified
        if (not opt) and agree:
            certified = True  # z3 unsat at val+1 + sat witness at val = full certificate
        d = load()
        d[str(k)][key] = {
            "value": val, "bnb_optimal": opt, "z3_agree": agree,
            "certified": certified, "witness": sorted(best),
            "secs": round(time.time() - t0, 1),
        }
        save(d)
        print(f"[ext] k={k} N={N} r_k={val} bnb_opt={opt} z3_agree={agree} certified={certified} ({d[str(k)][key]['secs']}s)", flush=True)
        prev = best

if __name__ == "__main__":
    extend(3, 29, 38, 300)   # r_3 frontier: salvage got 21..28
    extend(4, 21, 45, 200)
    extend(5, 21, 60, 120)
    extend(6, 21, 75, 90)
    print("EXTENSION COMPLETE")
