#!/usr/bin/env python3
"""w66_verify.py — INDEPENDENT verification of the banked #203 states.

Ground truth to reproduce (the repo bank):
  - work/state27720.json + work/bestres27720.txt = 218,794,308 uncovered
    (28.4741%) on the L=27720 torus, 41-prime family, budget 1.0563.
  - work/state55440.json: the L=55440 greedy state (52 primes, budget 1.1628)
    — its true uncovered count was never verified to disk; we compute it.

Engine: the column-int coverage (w66_lib), pure python bigints.
"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w66_lib as W

HERE = os.path.dirname(os.path.abspath(__file__))
PD = os.path.dirname(HERE)

def load_state(path):
    rows = json.load(open(path))
    return {int(r[0]): int(r[4]) for r in rows}, [(int(r[0]), int(r[1]), int(r[2]), int(r[3]), None, None) for r in rows]

def run(L, state_path, label):
    bank = W.load_bank()
    fam = W.family(L, bank)
    assign, _ = load_state(state_path)
    fam_qs = {r[0] for r in fam}
    st_qs = set(assign)
    print(f"[{label}] L={L} family={len(fam)} budget={W.budget(fam):.4f}")
    print(f"  state primes: {len(st_qs)}; state-minus-family: {sorted(st_qs - fam_qs)}; family-minus-state: {len(fam_qs - st_qs)}")
    # build rows with U,V,o2,o3 from bank
    bk = {r[0]: r for r in bank}
    rows = []
    for q in sorted(st_qs & fam_qs):
        b = bk[q]
        rows.append((q, b[1], b[2], b[3], b[4], b[5]))
    t0 = time.time()
    total, unc = W.column_coverage(rows, assign, L)
    print(f"  UNCOVERED = {total} ({100.0 * total / (L * L):.4f}%)   [verify {time.time()-t0:.1f}s]")
    return total

if __name__ == "__main__":
    t1 = run(27720, os.path.join(PD, "work/state27720.json"), "27720")
    t2 = run(55440, os.path.join(PD, "work/state55440.json"), "55440")
    print("banked bestres27720.txt:", open(os.path.join(PD, "work/bestres27720.txt")).read().strip())
    json.dump({"L27720_uncovered": t1, "L55440_uncovered": t2},
              open(os.path.join(HERE, "w66_verify_out.json"), "w"))
