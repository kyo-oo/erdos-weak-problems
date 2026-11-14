#!/usr/bin/env python3
"""engine885_r3_k4.py — W63-B5 / P885: the k=4 (K_{5,3}) witness hunt.

Round-1/2 hunted k=5 only; the k=4 row (in-house) is UNHIT (old N-indexed
engine, zero below 5e5).  This lane hunts K_{5,3} — 5 rows, 3 columns —
with the rich-column-funnel engine over the FULL anchor box rows <= 2236
(Delta = s1^2-s0^2 <= 5e6, u-window COMPLETE — round 1 stopped at u=500).

Gates (honestly reported): tau(Delta) >= 16 (tau_sieve prefilter 8),
C <= 1e8, row-degree cap 40.  Any K_{5,3} hit => a complete unconditional
#885(4) case theorem with in-house witness (new row: k=4 was unhit
in-house).  Chunked L75: budget seconds, then checkpoint+exit cleanly.

Usage: engine885_r3_k4.py <budget_seconds> [tau_exact] [s1_max]
"""
import sys, time, json
sys.path.insert(0, "/home/z/waves/w63-b5-p885/problem885-factor-difference")
import p885core as P

BASE = "/home/z/waves/w63-b5-p885/problem885-factor-difference"

def k3_validation(ce3):
    """Re-derive the in-house K_{4,2} (rows {2,22,46,134}, C {1365,3360})
    through the FULL engine path (anchor enumeration + rich funnel)."""
    t0 = time.time()
    found, nhits = False, 0
    for u in range(1, 201):
        for v in range(u + 2, 400 - u + 1, 2):
            D = u * v
            if P.exact_tau(D) < 12:
                continue
            s0, s1 = (v - u) // 2, (u + v) // 2
            best, hh, g, ph = P.process_pair(s0, s1, 3, ce3)
            for rows, Cs in hh:
                nhits += 1
                if sorted(rows)[:4] == [2, 22, 46, 134] and \
                        sorted(Cs) == [1365, 3360]:
                    found = True
    print(f"[k4r3] k3 VALIDATION: in-house K_(4,2) re-derived = {found}; "
          f"k3 configs in window = {nhits} ({time.time()-t0:.1f}s)",
          flush=True)
    return found

def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
    tau_exact = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    s1_max = int(sys.argv[3]) if len(sys.argv) > 3 else 2236
    P.COLCAP[0] = 10 ** 8

    # ---------- self-test: core exactness on the in-house K_{4,2} ----------
    ce3 = P.ColEngine(need_rows=4)
    rA, rB = ce3.rows(1365), ce3.rows(3360)
    inter = sorted(set(rA) & set(rB))
    assert rA == (2, 22, 38, 46, 94, 134, 226, 682), rA
    assert 3360 % 4 == 0 and len(rB) == 16, rB
    assert inter == [2, 22, 46, 134], inter
    g22 = P.G_candidates(2, 22, 10 ** 8)
    assert set([1365, 3360]) <= set(g22), g22
    print("[k4r3] core self-test PASS: R(1365)^R(3360) = {2,22,46,134}; "
          f"G(2,22) = {sorted(g22)}", flush=True)
    assert k3_validation(ce3), "k3 validation FAILED — engine unsound"

    # ---------- the k=4 hunt ----------
    print(f"[k4r3] PASS 2: k=4 hunt — K_(5,3), full u-window, "
          f"rows <= {s1_max}, tau >= {tau_exact}", flush=True)
    ce4 = P.ColEngine(need_rows=5)
    tau_sieve = P.build_tau_sieve(s1_max * s1_max)
    tag = f"k4t{tau_exact}"
    st, done = P.hunt_chunk(4, s1_max, max(4, tau_exact // 2), tau_exact,
                            budget, tag, BASE + "/k4_ckpt.json",
                            BASE + "/k4_hits.jsonl",
                            BASE + "/k4_pairs.jsonl",
                            ce4, tau_sieve)
    print(f"[k4r3] chunk done={done} stats={st} colstats={ce4.stats}",
          flush=True)
    if st["hits"] > 0:
        print("[k4r3] *** K=4 WITNESS LANDED *** first hit:", flush=True)
        with open(BASE + "/k4_hits.jsonl") as fh:
            line = fh.readline()
            h = json.loads(line)
            rows, Cs = h["rows"], h["Cs"]
            Ns, ds = P.build_witness(rows, Cs)
            print(f"  rows={rows} Cs={Cs} -> N={Ns} d={ds}", flush=True)

if __name__ == "__main__":
    main()
