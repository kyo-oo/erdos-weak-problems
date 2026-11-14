#!/usr/bin/env python3
"""#708 W63-D1 wide-t scan: all 4-subsets A of [2..M2] with max(A) = M in
[M1..M2], windows t = 1..T (T large) — the t-robustness extension of the
census box. Own checkpoint (resume-safe, per-batch).
Usage: widet M1 M2 T [BATCH]
"""
import sys, json, os, time
from itertools import combinations

sys.path.insert(0, "/home/z/waves/w63-d1-p708/problem708-product-divisibility")
from census2 import window_factors, minB_from_wf

CKPT = "/home/z/waves/w63-d1-p708/problem708-product-divisibility/g4_widet_ckpt.json"


def main(M1, M2, T, BATCH=100):
    state = {"done": [], "rows": [], "max": 0, "maxA": None, "hist5": []}
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            state = json.load(f)
        print(f"[widet] resume: {len(state['done'])} batches, rows="
              f"{len(state['rows'])} max={state['max']}", flush=True)
    t_start = time.time()
    for M in range(M1, M2 + 1):
        As = [sorted(S + (M,)) for S in combinations(range(2, M), 3)]
        for bi in range(0, len(As), BATCH):
            tag = f"{M}:{bi}"
            if tag in state["done"]:
                continue
            batch = As[bi:bi + BATCH]
            t0 = time.time()
            for A in batch:
                worst, wt = 0, None
                for t in range(1, T + 1):
                    s = minB_from_wf(A, window_factors(M, t))
                    if s > worst:
                        worst, wt = s, t
                state["rows"].append({"A": A, "worst": worst, "t": wt})
                if worst > state["max"]:
                    state["max"] = worst
                    state["maxA"] = [A, wt]
                if worst >= 5:
                    state["hist5"].append([A, wt, worst])
                    print(f"[widet] !!! FORCING-{worst}: A={A} t={wt}",
                          flush=True)
            state["done"].append(tag)
            with open(CKPT, "w") as f:
                json.dump(state, f)
            print(f"[widet] M={M} batch {bi}:{bi+len(batch)}: "
                  f"{time.time()-t0:.1f}s (elapsed {time.time()-t_start:.0f}s) "
                  f"rows={len(state['rows'])} max={state['max']}", flush=True)
    dist = {}
    for r in state["rows"]:
        dist[r["worst"]] = dist.get(r["worst"], 0) + 1
    print(f"[widet] DONE: {len(state['rows'])} 4-sets, t=1..{T}, "
          f"worst-dist {dict(sorted(dist.items()))}")
    print(f"[widet] GLOBAL MAX over box (max(A) in [{M1},{M2}], t=1..{T}): "
          f"{state['max']} at {state['maxA']}")
    if state["hist5"]:
        print("[widet] g(4)>=5 WITNESSES:")
        for A, wt, w in state["hist5"]:
            print(f"   A={A} t={wt}: worst = {w}")


if __name__ == "__main__":
    M1 = int(sys.argv[1]); M2 = int(sys.argv[2]); T = int(sys.argv[3])
    B = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    main(M1, M2, T, B)
