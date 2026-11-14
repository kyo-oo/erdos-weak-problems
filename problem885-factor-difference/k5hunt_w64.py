#!/usr/bin/env python3
"""k5hunt_w64.py — W64-D / P885: the k=5 ESCALATION HUNT (K_{6,4}).

The kill path that produced the W63-B5 k=4 kill, escalated one case:
  (1) K_{6,2} harvest: column pairs (A,B) with >= 6 common rows.  Round
      W63-B5's FULL-u-window K_{5,2} hunt (engine885_r3_k4.py, u=1..501 of
      2236, tau(Delta)>=16, C<=1e8) already recorded 71715 K_{5,2} pairs on
      disk; the pairs with >= 6 common rows (12761) are K_{6,2} INSTANTLY.
  (2) extension: for each K_{6,2}, enumerate candidate columns from the
      G-sets of ALL row pairs of R, keep C with |R ^ R(C)| >= 6, then hunt
      4-subsets of the pool with >= 6 common rows -> K_{6,4} -> Theorem B
      lambda=2 -> the k=5 witness (5 N's sharing 5 d's).

W64-D upgrades over the banked ext885.py:
  * EXACT big-n factorization: trial division is only exact for n <= 1.6e9
    (40000^2); row pairs of the harvested K_{6,2}s go up to ~2e11, so
    factorize_exact is patched with a sympy.factorint fallback (exact,
    Pollard-rho + trial division) for n > 1.6e9.  Soundness: the G-set
    enumeration is exhaustive again (no missed factor pairs).
  * COLCAP configurable per run (1e8 banked default; 1e9 widening is exact
    under the same trial-division bound since 1e9 < 1.6e9, and the tau_ge
    prefilter soundness bound is stated for n <= 1e9).
  * L75 checkpoint/resume: processed-pair index + hits on disk.

Usage: k5hunt_w64.py <budget_seconds> [colcap] [pairsfile] [minrows]
"""
import sys, time, json, os
from math import isqrt
from itertools import combinations

sys.path.insert(0, "/home/z/waves/w64-b5-p885/problem885-factor-difference")
import p885core as P
from sympy import factorint as _sympy_factorint

BASE = "/home/z/waves/w64-b5-p885/problem885-factor-difference"

# ---- EXACT big-n factorization patch (soundness for Delta > 1.6e9) --------
_orig_fe = P.factorize_exact

def factorize_exact_w64(n):
    if n <= 1.6 * 10 ** 9:
        return _orig_fe(n)
    f = {}
    for p, e in _sympy_factorint(n).items():
        f[int(p)] = int(e)
    return f

P.factorize_exact = factorize_exact_w64   # G_candidates/ColEngine see the patch

def load_pairs(path, minrows):
    out = []
    with open(path) as fh:
        for line in fh:
            h = json.loads(line)
            if len(h["rows"]) >= minrows:
                out.append((h["A"], h["B"], h["rows"]))
    return out

def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
    colcap = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 8
    pairs_path = sys.argv[3] if len(sys.argv) > 3 else BASE + "/k4_pairs.jsonl"
    minrows = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    P.COLCAP[0] = colcap
    need = 6                                   # K_{6,4}: 6 rows
    ce = P.ColEngine(need_rows=need)

    pairs = load_pairs(pairs_path, minrows)
    pairs.sort(key=lambda t: -len(t[2]))       # richest first
    print(f"[k5-w64] {len(pairs)} K_(6,2) pairs (>= {minrows} rows) from "
          f"{os.path.basename(pairs_path)}; COLCAP={colcap:.1e}; "
          f"budget {budget:.0f}s", flush=True)

    ckpt = BASE + "/k5ext_ckpt_w64.json"
    hits_path = BASE + "/ext_k5_hits.json"
    done_idx = 0
    if os.path.exists(ckpt):
        prev = json.load(open(ckpt))
        done_idx = prev.get("done_idx", 0)
        if prev.get("colcap") != colcap or prev.get("pairs_path") != os.path.basename(pairs_path):
            done_idx = 0                       # config changed: restart scan
    hits = []
    if os.path.exists(hits_path):
        hits = json.load(open(hits_path))

    t0 = time.time()
    nproc = 0
    nthirds = 0
    for idx in range(done_idx, len(pairs)):
        if time.time() - t0 > budget:
            break
        A, B, R = pairs[idx]
        Rset = set(R)
        cand = set()
        for i in range(len(R)):
            for j in range(i + 1, len(R)):
                for C in P.G_candidates(R[i], R[j], colcap):
                    cand.add(C)
        cand.discard(A); cand.discard(B)
        thirds = []
        for C in cand:
            rc = ce.rows(C)
            if rc is not None and len(Rset & set(rc)) >= need:
                thirds.append((C, sorted(Rset & set(rc))))
        nthirds += len(thirds)
        if len(thirds) + 2 >= 4:
            pool = [(A, sorted(Rset)), (B, sorted(Rset))] + thirds
            for combo in combinations(range(len(pool)), 4):
                inter = set(pool[combo[0]][1])
                for ci in combo[1:]:
                    inter &= set(pool[ci][1])
                if len(inter) >= 6:
                    Cs = [pool[ci][0] for ci in combo]
                    rows = sorted(inter)
                    if P.verify_config(rows[:6], Cs):
                        hits.append({"rows": rows[:6], "Cs": Cs})
                        print(f"*** K_(6,4) HIT: rows={rows[:6]} Cs={Cs}",
                              flush=True)
                        with open(hits_path, "w") as fh:
                            json.dump(hits, fh, indent=1)
        nproc += 1
        done_idx = idx + 1
        if nproc % 500 == 0:
            print(f"  [k5-w64] proc={nproc}/{len(pairs)} thirds={nthirds} "
                  f"hits={len(hits)} t={time.time()-t0:.0f}s "
                  f"cache={len(ce.cache)} colstats={ce.stats}", flush=True)
            _save(ckpt, {"done_idx": done_idx, "nproc": nproc,
                         "nthirds": nthirds, "hits": len(hits),
                         "colcap": colcap,
                         "pairs_path": os.path.basename(pairs_path)})
    _save(ckpt, {"done_idx": done_idx, "nproc": nproc, "nthirds": nthirds,
                 "hits": len(hits), "colcap": colcap,
                 "pairs_path": os.path.basename(pairs_path)})
    print(f"[k5-w64] chunk done: proc={nproc} of {len(pairs)} (idx {done_idx}); "
          f"thirds={nthirds}; hits={len(hits)} ({time.time()-t0:.1f}s); "
          f"colstats={ce.stats}", flush=True)
    if hits:
        rows, Cs = hits[0]["rows"], hits[0]["Cs"]
        Ns, ds = P.build_witness(rows, Cs)
        print(f"[k5-w64] WITNESS: rows={rows} Cs={Cs} -> N={Ns} d={ds}",
              flush=True)

def _save(path, st):
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(st, fh)
    os.replace(tmp, path)

if __name__ == "__main__":
    main()
