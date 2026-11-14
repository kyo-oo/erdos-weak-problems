#!/usr/bin/env python3
"""W63-D5 #306 census driver: process universe(30) in order, skipping the
known-stubborn set (handled by dedicated constructions) and everything
already done.  Checkpoints into EVIDENCE_306_W63.json after every target."""
import json, sys, time
from engine306_w63 import (universe, solve_ab, verify_full, SEED)
from fractions import Fraction

T0 = time.time()
B_HI = int(sys.argv[1]) if len(sys.argv) > 1 else 30
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 480.0
SKIP = set(sys.argv[3].split(",")) if len(sys.argv) > 3 else set()
OUT = "EVIDENCE_306_W63.json"
state = json.load(open(OUT))
targets = universe(B_HI)
print(f"universe {len(targets)} | done {len(state['done'])} | skip {sorted(SKIP)}", flush=True)
for (a, b) in targets:
    key = f"{a}/{b}"
    if key in state["done"] or key in SKIP or key in set(state["failed"]):
        continue
    if time.time() - T0 > BUDGET:
        print(f"[budget stop] done={len(state['done'])}", flush=True)
        break
    dens = solve_ab(a, b)
    if dens is not None and verify_full(a, b, dens):
        state["done"][key] = dens
        state["failed"] = [k for k in state["failed"] if k != key]
        print(f"  {a}/{b}: {len(dens)} terms, max den {dens[-1]}", flush=True)
    else:
        if key not in state["failed"]:
            state["failed"].append(key)
        print(f"  {a}/{b}: FAIL", flush=True)
    json.dump(state, open(OUT, "w"))
rem = [k for k in (f"{a}/{b}" for a, b in targets) if k not in state["done"]]
print(f"=== CENSUS: {len(state['done'])}/{len(targets)} | remaining: {rem}", flush=True)
json.dump(state, open(OUT, "w"), indent=0)
