#!/usr/bin/env python3
"""ext885.py — W63-B5 / P885: the column-pair signature EXTENSION engine.

Input: the K_{k+1,2} column pairs (A, B, rows R) recorded by the hunt
(K_{5,2} for k=4 / K_{6,2} for k=5 — pairs with >= k+1 common rows).

Extension: a K_{k+1,k-1} containing the K_{k+1,2} needs further columns
C with |R(A) ^ R(B) ^ R(C)| >= k+1.  EVERY such C <= C_CAP lies in
G(r_i, r_j) for SOME row pair of R (C contains >= k+1 rows of R, so any
two of them pin C into their G-set) — and the extension enumerates
G(r_i, r_j) over ALL row pairs of R with NO tau gate on the anchors
(wider coverage than the gated direct hunt).

k=4 mode: find C with |R ^ R(C)| >= 5 -> K_{5,3} = (5 rows, {A,B,C}).
k=5 mode: pool = {C : |R ^ R(C)| >= 6}; then 4-subsets of the pool with
          common rows >= 6 -> K_{6,4}.

Usage: ext885.py k4|k5 [pairs_file] [max_pairs]
"""
import sys, time, json
from math import isqrt
from itertools import combinations
sys.path.insert(0, "/home/z/waves/w63-b5-p885/problem885-factor-difference")
import p885core as P

BASE = "/home/z/waves/w63-b5-p885/problem885-factor-difference"

def load_pairs(path):
    out = []
    try:
        with open(path) as fh:
            for line in fh:
                h = json.loads(line)
                out.append((h["A"], h["B"], h["rows"]))
    except FileNotFoundError:
        pass
    return out

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "k4"
    pairs_path = sys.argv[2] if len(sys.argv) > 2 else \
        BASE + ("/k4_pairs.jsonl" if mode == "k4" else "/k5_pairs.jsonl")
    max_pairs = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
    budget = float(sys.argv[4]) if len(sys.argv) > 4 else 480.0
    k = 4 if mode == "k4" else 5
    need = k + 1
    P.COLCAP[0] = 10 ** 8
    ce = P.ColEngine(need_rows=need)
    pairs = load_pairs(pairs_path)
    pairs.sort(key=lambda t: -len(t[2]))     # richest row sets first
    print(f"[ext-{mode}] {len(pairs)} K_({k+1},2) pairs loaded from "
          f"{pairs_path}; need {need} common rows; budget {budget}s",
          flush=True)
    t0 = time.time()
    hits = []
    nproc = 0
    for (A, B, R) in pairs:
        if nproc >= max_pairs or time.time() - t0 > budget:
            break
        nproc += 1
        Rset = set(R)
        # candidate columns: union of G(r_i, r_j) over ALL row pairs of R
        cand = set()
        for i in range(len(R)):
            for j in range(i + 1, len(R)):
                for C in P.G_candidates(R[i], R[j], P.COLCAP[0]):
                    cand.add(C)
        cand.discard(A); cand.discard(B)
        # third columns with >= need rows of R
        thirds = []
        for C in cand:
            rc = ce.rows(C)
            if rc is not None and len(Rset & set(rc)) >= need:
                thirds.append((C, sorted(Rset & set(rc))))
        if not thirds:
            continue
        if k == 4:
            for C, rows in thirds:
                if P.verify_config(rows[:5], [A, B, C]):
                    hits.append((rows[:5], [A, B, C]))
                    print(f"*** EXT HIT K_(5,3): rows={rows[:5]} "
                          f"Cs={[A, B, C]}", flush=True)
                    break
        else:
            pool = [(A, sorted(Rset))] + [(B, sorted(Rset))] + thirds
            if len(pool) >= 4:
                for combo in combinations(range(len(pool)), 4):
                    inter = set(pool[combo[0]][1])
                    for ci in combo[1:]:
                        inter &= set(pool[ci][1])
                    if len(inter) >= 6:
                        Cs = [pool[ci][0] for ci in combo]
                        rows = sorted(inter)
                        if P.verify_config(rows[:6], Cs):
                            hits.append((rows[:6], Cs))
                            print(f"*** EXT HIT K_(6,4): rows={rows[:6]} "
                                  f"Cs={Cs}", flush=True)
                            break
        if nproc % 2000 == 0:
            print(f"  [ext-{mode}] proc={nproc} hits={len(hits)} "
                  f"t={time.time()-t0:.0f}s cache={len(ce.cache)}",
                  flush=True)
    print(f"[ext-{mode}] done: proc={nproc} of {len(pairs)}; hits={len(hits)} "
          f"({time.time()-t0:.1f}s); colstats={ce.stats}", flush=True)
    if hits:
        out = BASE + (f"/ext_{mode}_hits.json" if mode == "k4" else
                      "/ext_k5_hits.json")
        with open(out, "w") as fh:
            json.dump([{"rows": r, "Cs": c} for r, c in hits], fh, indent=1)
        print(f"[ext-{mode}] hits saved -> {out}", flush=True)
        rows, Cs = hits[0]
        Ns, ds = P.build_witness(rows, Cs)
        print(f"[ext-{mode}] WITNESS: rows={rows} Cs={Cs} -> N={Ns} d={ds}",
              flush=True)

if __name__ == "__main__":
    main()
