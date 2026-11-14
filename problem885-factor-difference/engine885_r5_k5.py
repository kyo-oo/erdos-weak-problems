#!/usr/bin/env python3
"""engine885_r5_k5.py — W64-D / P885: the k=5 (K_{6,4}) FULL-u-window hunt.

The banked escalation (W63-B5's engine885_r3_k4.py lane) completed only
u <= 501 of 2236 before landing the k=4 kill.  This engine finishes the
anchor box rows <= 2236 (Delta = s1^2-s0^2 <= 5e6) in k=5 mode:
need_rows = 6, harvesting K_{6,2} column pairs (2 columns, >= 6 common
rows) into k5_pairs.jsonl for the extension pass (k5hunt_w64.py).

W64-D upgrades: exact big-n factorization patch (sympy fallback for
Delta > 1.6e9 — irrelevant inside this window but uniform); seeded
resume at u_next = 501 with the 12761 K_{6,2}s already harvested by the
W63-B5 k=4 hunt (k4_pairs.jsonl rows >= 6 — COMPLETE for that window:
the k=4-mode pair recorder kept every pair with >= 5 common rows).

Gates (honest census register): tau(Delta) >= 16 (sieve prefilter 8),
C <= COLCAP (default 1e8), row-degree cap 40.

Usage: engine885_r5_k5.py <budget_seconds> [colcap] [s1_max] [tau_exact]
"""
import sys, time, json, os

sys.path.insert(0, "/home/z/waves/w64-b5-p885/problem885-factor-difference")
import p885core as P
from sympy import factorint as _sympy_factorint

BASE = "/home/z/waves/w64-b5-p885/problem885-factor-difference"

_orig_fe = P.factorize_exact

def factorize_exact_w64(n):
    if n <= 1.6 * 10 ** 9:
        return _orig_fe(n)
    return {int(p): int(e) for p, e in _sympy_factorint(n).items()}

P.factorize_exact = factorize_exact_w64

def seed_from_k4(pairs_path, ckpt_path):
    """Seed the k5 pair file + checkpoint from the W63-B5 K_{5,2} harvest."""
    if os.path.exists(ckpt_path):
        return                                   # already seeded/started
    seen = set()
    n = 0
    with open(pairs_path, "a") as out:
        if os.path.exists(BASE + "/k4_pairs.jsonl"):
            for line in open(BASE + "/k4_pairs.jsonl"):
                try:
                    h = json.loads(line)
                except Exception:
                    continue
                if len(h["rows"]) >= 6 and (h["A"], h["B"]) not in seen:
                    seen.add((h["A"], h["B"]))
                    out.write(json.dumps({"A": h["A"], "B": h["B"],
                                          "rows": h["rows"]}) + "\n")
                    n += 1
    st = {"pairs": 0, "rich": 0, "proc": 0, "maxG": 0, "best": 0,
          "hits": 0, "pairhits": n, "maxrich": 0, "u_next": 501,
          "seeded": n}
    tmp = ckpt_path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(st, fh)
    os.replace(tmp, ckpt_path)
    print(f"[k5r5] seeded {n} K_(6,2) pairs from the W63-B5 u<=501 harvest",
          flush=True)

def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
    colcap = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 8
    s1_max = int(sys.argv[3]) if len(sys.argv) > 3 else 2236
    tau_exact = int(sys.argv[4]) if len(sys.argv) > 4 else 16
    P.COLCAP[0] = colcap

    ce = P.ColEngine(need_rows=6)
    ckpt = BASE + "/k5_ckpt.json"
    pairs_path = BASE + "/k5_pairs.jsonl"
    seed_from_k4(pairs_path, ckpt)

    # ---------- self-test: the k4 witness pair config through this engine --
    rA = ce.rows(24135111); rB = ce.rows(2514375); rC = ce.rows(15992775)
    assert rA is not None and rB is not None and rC is not None
    inter = set(rA) & set(rB) & set(rC)
    assert {267, 1525, 3165, 5475, 27915} <= set(inter), sorted(inter)
    print(f"[k5r5] core self-test PASS: R(24135111)^R(2514375)^R(15992775) "
          f"contains the k4 witness rows (|inter|={len(inter)})", flush=True)

    print(f"[k5r5] hunt: K_(6,2) harvest, u=501..{s1_max}, tau>={tau_exact}, "
          f"C<={colcap:.1e}, budget {budget:.0f}s", flush=True)
    tau_sieve = P.build_tau_sieve(s1_max * s1_max)
    st, done = P.hunt_chunk(5, s1_max, max(4, tau_exact // 2), tau_exact,
                            budget, "k5r5", ckpt,
                            BASE + "/k5_hits.jsonl", pairs_path,
                            ce, tau_sieve)
    print(f"[k5r5] chunk done={done} stats={st} colstats={ce.stats}",
          flush=True)

if __name__ == "__main__":
    main()
