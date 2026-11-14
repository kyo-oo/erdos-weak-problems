#!/usr/bin/env python3
"""W66-P203-D A4 — THE NO-FRAME: can the CURRENT palette provably NOT close?

Three independent analyses on the live hunt families
(L=27720: 41 members, budget 1.0563; L=55440: 52 members, budget 1.1628):

  N1  Density budget Sigma 1/h (uniform 2-D LP-dual bound): a cover needs
      Sigma 1/h >= 1. Both families pass -> density does NOT kill them.

  N2  LP-BLINDNESS THEOREM (rigorous, constructive): whenever Sigma 1/h >= 1
      the uniform fractional assignment x_{p,coset} = 1/h covers every
      cell to depth Sigma 1/h >= 1, so the fractional covering LP is
      FEASIBLE; by LP duality NO certificate of the form
      (exists y>=0 on cells: sum y > sum_p max_coset y) can exist -- in
      particular no 1-D column/row LP-dual certificate. Verified
      numerically by solving both 1-D LPs (HiGHS): min sum z_p >= 1.

  N3  BONFERRONI-E3 COMBINATORIAL NO-GO (LP-invisible, beyond N2):
      For ANY choice of one coset per prime,
        |union| <= S1 - S2 + S3   (Bonferroni, odd truncation)
      with S2 >= sum over FORCED pairs (joint map surjective: every coset
      pair intersects in exactly L^2/(h_p h_q) cells) and S3 <= sum over
      triples of L^2/J_{pqr} (J = joint image order, exact via gcd of
      maximal minors of the dlog relation matrix). Hence
        max_union/L^2 <= Sigma 1/h - Sigma_{forced pairs} 1/(h_p h_q)
                        + Sigma_{triples} 1/J_{pqr}.
      If this bound is < 1 the family CANNOT close -- a rigorous
      combinatorial infeasibility certificate that kills every subset of
      the palette at once (extra primes only enlarge the union).

  Also: the random-placement baseline, the containment-degenerate pair
  census (where coset choice actually matters), and the honest status.
"""
import json, math, os, sys, time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
PDIR = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from a1_palette_audit import my_order

def load_family(L):
    pal = json.load(open(os.path.join(PDIR, "pal_dlog_full.json")))
    fam = []
    for r in pal:
        q, h, U, V, o2, o3 = (int(x) for x in r)
        if L % h == 0:
            fam.append({"q": q, "h": h, "U": U, "V": V, "o2": o2, "o3": o3})
    return fam

def pair_J(a, b):
    """joint image order J_{pq} for the (k,l)->(2^k3^l mod p, mod q) map,
    exact via gcd of maximal minors of the dlog relation matrix."""
    hp, hq = a["h"], b["h"]
    Up, Vp, Uq, Vq = a["U"], a["V"], b["U"], b["V"]
    minors = [hp * hq, hp * Uq, hp * Vq, hq * Up, hq * Vp,
              abs(Up * Vq - Uq * Vp)]
    g = 0
    for m in minors:
        g = math.gcd(g, m)
    return (hp * hq) // g, g

def triple_J(a, b, c):
    """joint image order J_{pqr}, exact via gcd of the 3x3 minors of
    [[h_p,0,0],[0,h_q,0],[0,0,h_r],[U_p,U_q,U_r],[V_p,V_q,V_r]]."""
    hs = [a["h"], b["h"], c["h"]]
    Us = [a["U"], b["U"], c["U"]]
    Vs = [a["V"], b["V"], c["V"]]
    rows = [[hs[0], 0, 0], [0, hs[1], 0], [0, 0, hs[2]], Us, Vs]
    g = 0
    for tri in combinations(range(5), 3):
        m = [[rows[i][0], rows[i][1], rows[i][2]] for i in tri]
        d = (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
             - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
             + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
        g = math.gcd(g, abs(d))
    prod = hs[0] * hs[1] * hs[2]
    return prod // g if g else prod

def no_frame(L):
    print(f"=== NO-FRAME at L={L} ===", flush=True)
    fam = load_family(L)
    S1 = sum(1.0 / f["h"] for f in fam)
    print(f"N1 family: {len(fam)} primes; Sigma 1/h = {S1:.6f} "
          f"(>= 1: {'YES — density does not kill' if S1 >= 1 else 'NO — RIGOROUS DENSITY NO-GO'})", flush=True)
    print(f"N1 strongest members: " + ", ".join(f"q={f['q']}(h={f['h']},1/h={1.0/f['h']:.4f})"
          for f in sorted(fam, key=lambda f: f['h'])[:8]), flush=True)

    # N2 the uniform fractional witness (constructive)
    print(f"N2 LP-blindness witness: x_(p,coset)=1/h for each of the h cosets of each prime; "
          f"every cell covered to depth exactly {S1:.6f} >= 1 -> fractional cover FEASIBLE -> "
          f"NO LP-dual certificate of any kind can exist for this family.", flush=True)
    # numerical confirmation via the 1-D column LP
    run_1d_lp(L, fam, axis="k")
    run_1d_lp(L, fam, axis="l")

    # N3 Bonferroni-E3
    t0 = time.time()
    forced_pairs = []
    avoid_pairs = []
    S2f = 0.0
    for a, b in combinations(fam, 2):
        J, g = pair_J(a, b)
        if g == 1:
            forced_pairs.append((a["q"], b["q"]))
            S2f += 1.0 / (a["h"] * b["h"])
        else:
            avoid_pairs.append((a["q"], b["q"], J))
    print(f"N3 pairs: {len(forced_pairs)} forced (joint surjective, intersection "
          f"L^2/(h_p h_q) always), {len(avoid_pairs)} avoidable/degenerate; "
          f"S2_forced = {S2f:.6f}", flush=True)
    S3cap = 0.0
    Jstats = {}
    for a, b, c in combinations(fam, 3):
        J = triple_J(a, b, c)
        S3cap += 1.0 / J
    print(f"N3 triples: {len(list(combinations(fam,3)))} evaluated; S3_cap = {S3cap:.6f} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    B = S1 - S2f + S3cap
    print(f"N3 BONFERRONI-E3 BOUND: max_union/L^2 <= S1 - S2_forced + S3_cap "
          f"= {S1:.6f} - {S2f:.6f} + {S3cap:.6f} = {B:.6f}", flush=True)
    if B < 1.0:
        print(f"N3 VERDICT: B < 1 — RIGOROUS COMBINATORIAL NO-GO: the family CANNOT "
              f"cover Z_{L}^2 (any subset, any coset choice). Palette growth is FORCED.", flush=True)
    else:
        print(f"N3 VERDICT: B >= 1 — the E3 bound does not kill the family "
              f"(headroom {B-1:.6f}); the hunt is not provably doomed at this level.", flush=True)

    # honest status numbers
    prod = 1.0
    for f in fam:
        prod *= (1.0 - 1.0 / f["h"])
    print(f"status: random-placement baseline union = {1-prod:.6f}; "
          f"integral best (A2-verified, L=27720 state) = 0.715259; "
          f"gap to random = {0.715259-(1-prod):+.6f}", flush=True)
    # degenerate pair census (where choice matters)
    if avoid_pairs:
        print(f"choice-matters pairs (J < h_p h_q): {len(avoid_pairs)}: "
              f"{[(q1, q2, J) for (q1, q2, J) in avoid_pairs[:12]]}", flush=True)
    return {"L": L, "n": len(fam), "S1": S1, "S2_forced": S2f, "S3_cap": S3cap, "B": B,
            "forced_pairs": len(forced_pairs), "avoid_pairs": len(avoid_pairs)}

def run_1d_lp(L, fam, axis="k"):
    """1-D LP (column k-axis or row l-axis) min sum z_p s.t. sum y = 1,
    y >= 0, w_p * y(AP_{p,a}) <= z_p for every position a.
    Certificate iff min < 1. Theorem says min >= 1 here; run to confirm."""
    import numpy as np
    import scipy.sparse as sp
    from scipy.optimize import linprog
    n = len(fam)
    ms = []; ws = []
    for f in fam:
        if axis == "k":
            m = f["h"] // f["o3"]; w = 1.0 / f["o3"]
        else:
            m = f["h"] // f["o2"]; w = 1.0 / f["o2"]
        ms.append(m); ws.append(w)
    nvar = L + n
    c = np.zeros(nvar); c[L:] = 1.0
    # equality: sum y = 1
    A_eq = sp.csr_matrix((np.ones(L), (np.zeros(L, dtype=int), np.arange(L))),
                          shape=(1, nvar))
    b_eq = np.array([1.0])
    # inequalities: w_p * sum_{k = a mod m} y_k - z_p <= 0  (sparse)
    data = []; rowi = []; coli = []
    nrow = 0
    for i in range(n):
        m = ms[i]
        idxs = np.arange(L)
        if m == 1:
            for k in range(L):
                data.append(ws[i]); rowi.append(nrow); coli.append(k)
            data.append(-1.0); rowi.append(nrow); coli.append(L + i)
            nrow += 1
        else:
            for a in range(m):
                ks = idxs[a::m]
                for k in ks:
                    data.append(ws[i]); rowi.append(nrow); coli.append(int(k))
                data.append(-1.0); rowi.append(nrow); coli.append(L + i)
                nrow += 1
    A_ub = sp.csr_matrix((data, (rowi, coli)), shape=(nrow, nvar))
    b_ub = np.zeros(nrow)
    t0 = time.time()
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, None)] * nvar, method="highs")
    val = res.fun if res.success else None
    print(f"N2 1-D {axis}-axis LP ({'column' if axis == 'k' else 'row'}): "
          f"{nrow} constraints, {nvar} vars; min sum z_p = "
          f"{val if val is None else round(val, 6)} "
          f"({'NO certificate (>= 1) — LP-blindness theorem CONFIRMED' if val is not None and val >= 1 - 1e-6 else 'CERTIFICATE EXISTS?!' if val is not None else 'LP FAILED: ' + str(res.message)}) "
          f"[{time.time()-t0:.0f}s]", flush=True)
    return val

def main():
    out = {}
    out["L27720"] = no_frame(27720)
    out["L55440"] = no_frame(55440)
    json.dump(out, open(os.path.join(HERE, "no_frame.json"), "w"), indent=1)
    print("A4 DONE", flush=True)

if __name__ == "__main__":
    main()
