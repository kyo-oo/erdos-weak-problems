#!/usr/bin/env python3
"""W66-P203-D A5 — deeper no-frame: E5 Bonferroni truncation + budget
concentration curve for the L=27720 family (41 primes).

  E5 bound: max_union/L^2 <= S1 - S2_forced + S3_cap - S4_forced + S5_cap
  (odd Bonferroni partial; forced 4-ways always intersect at exactly
   L^2/(h_i h_j h_k h_l); 5-way intersections capped by L^2/J_quint).
  Joint orders via closed-form maximal minors (validated in A4b).

  Budget curve: cumulative Sigma 1/h over the density-sorted family —
  how deep into the weak tail any closed cover is forced to reach.
"""
import json, math, os, sys, time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
PDIR = os.path.dirname(HERE)

def load_family(L):
    pal = json.load(open(os.path.join(PDIR, "pal_dlog_full.json")))
    return [{"q": int(r[0]), "h": int(r[1]), "U": int(r[2]), "V": int(r[3]),
             "o2": int(r[4]), "o3": int(r[5])} for r in pal if L % int(r[1]) == 0]

def pair_g(a, b):
    hp, hq = a["h"], b["h"]
    minors = [hp * hq, hp * b["U"], hp * b["V"], hq * a["U"], hq * a["V"],
              abs(a["U"] * b["V"] - b["U"] * a["V"])]
    g = 0
    for m in minors:
        g = math.gcd(g, m)
    return g

def quad_forced_and_J(a, b, c, d):
    """forced? J = prod(h)/g, g = gcd of the 4x4 maximal minors of the
    6x4 relation matrix [4 h-rows; U-row; V-row]. Closed forms:
    (a) 4 h-rows: prod h
    (b) 3 h-rows + U: (prod of 3 h) * U_j   (j = missing axis)
    (c) 3 h-rows + V: (prod of 3 h) * V_j
    (d) 2 h-rows + U + V: (prod 2 h) * (U_i V_j - U_j V_i)  {i,j}=complement
    """
    fs = [a, b, c, d]
    hs = [f["h"] for f in fs]
    Us = [f["U"] for f in fs]
    Vs = [f["V"] for f in fs]
    prod = hs[0] * hs[1] * hs[2] * hs[3]
    g = prod
    for j in range(4):
        pj = 1
        for t in range(4):
            if t != j:
                pj *= hs[t]
        g = math.gcd(g, pj * Us[j])
        g = math.gcd(g, pj * Vs[j])
    for i, j in combinations(range(4), 2):
        pj = 1
        for t in range(4):
            if t != i and t != j:
                pj *= hs[t]
        g = math.gcd(g, pj * abs(Us[i] * Vs[j] - Us[j] * Vs[i]))
    return (g == 1), prod // g

def quint_J(a, b, c, d, e):
    fs = [a, b, c, d, e]
    hs = [f["h"] for f in fs]
    Us = [f["U"] for f in fs]
    Vs = [f["V"] for f in fs]
    prod = 1
    for h in hs:
        prod *= h
    g = prod
    for j in range(5):
        pj = 1
        for t in range(5):
            if t != j:
                pj *= hs[t]
        g = math.gcd(g, pj * Us[j])
        g = math.gcd(g, pj * Vs[j])
    for i, j in combinations(range(5), 2):
        pj = 1
        for t in range(5):
            if t != i and t != j:
                pj *= hs[t]
        g = math.gcd(g, pj * abs(Us[i] * Vs[j] - Us[j] * Vs[i]))
    return prod // g if g else prod

def main():
    fam = sorted(load_family(27720), key=lambda f: f["h"])
    S1 = sum(1.0 / f["h"] for f in fam)
    print(f"L=27720 family: {len(fam)} primes, S1 = {S1:.6f}", flush=True)

    # budget concentration
    cum = 0.0
    print("budget concentration (density-sorted):", flush=True)
    for i, f in enumerate(fam):
        cum += 1.0 / f["h"]
        if (i + 1) in (8, 12, 16, 20, 24, 28, 32, 36, 41) or f is fam[-1]:
            print(f"   top {i+1:2d} primes: cumulative budget {cum:.4f}", flush=True)
    for i, f in enumerate(fam):
        cum2 = sum(1.0 / g["h"] for g in fam[:i+1])
        if cum2 >= 1.0:
            print(f"   budget reaches 1.0 at the top-{i+1} prime (q={f['q']}, h={f['h']})", flush=True)
            break

    # pair data (reuse a4 numbers computed fresh here)
    t0 = time.time()
    S2f = 0.0
    for a, b in combinations(fam, 2):
        if pair_g(a, b) == 1:
            S2f += 1.0 / (a["h"] * b["h"])
    print(f"S2_forced = {S2f:.6f} [{time.time()-t0:.0f}s]", flush=True)

    # triples
    t0 = time.time()
    S3cap = 0.0
    for a, b, c in combinations(fam, 3):
        hs = [a["h"], b["h"], c["h"]]
        Us = [a["U"], b["U"], c["U"]]
        Vs = [a["V"], b["V"], c["V"]]
        prod = hs[0] * hs[1] * hs[2]
        g = prod
        for j in range(3):
            pj = 1
            for t in range(3):
                if t != j:
                    pj *= hs[t]
            g = math.gcd(g, pj * Us[j])
            g = math.gcd(g, pj * Vs[j])
        g = math.gcd(g, hs[0] * abs(Us[1] * Vs[2] - Us[2] * Vs[1]))
        g = math.gcd(g, hs[1] * abs(Us[0] * Vs[2] - Us[2] * Vs[0]))
        g = math.gcd(g, hs[2] * abs(Us[0] * Vs[1] - Us[1] * Vs[0]))
        J = prod // g if g else prod
        S3cap += 1.0 / J
    print(f"S3_cap = {S3cap:.6f} [{time.time()-t0:.0f}s]", flush=True)

    # quads (forced 4-ways)
    t0 = time.time()
    S4f = 0.0; nforced4 = 0
    for quad in combinations(fam, 4):
        forced, J = quad_forced_and_J(*quad)
        if forced:
            nforced4 += 1
            S4f += 1.0 / J
    print(f"S4_forced = {S4f:.6f} over {nforced4} forced quads [{time.time()-t0:.0f}s]", flush=True)

    # quints
    t0 = time.time()
    S5cap = 0.0
    for quint in combinations(fam, 5):
        S5cap += 1.0 / quint_J(*quint)
    print(f"S5_cap = {S5cap:.6f} [{time.time()-t0:.0f}s]", flush=True)

    B3 = S1 - S2f + S3cap
    B5 = S1 - S2f + S3cap - S4f + S5cap
    print(f"E3 bound = {B3:.6f}; E5 bound = {B5:.6f}", flush=True)
    for name, B in (("E3", B3), ("E5", B5)):
        if B < 1:
            print(f"{name} < 1: RIGOROUS COMBINATORIAL NO-GO — the palette cannot close.", flush=True)
        else:
            print(f"{name} >= 1: no kill (headroom {B-1:.6f}).", flush=True)
    json.dump({"S1": S1, "S2f": S2f, "S3cap": S3cap, "S4f": S4f, "S5cap": S5cap,
               "B3": B3, "B5": B5},
              open(os.path.join(HERE, "no_frame_deep.json"), "w"), indent=1)
    print("A5 DONE", flush=True)

if __name__ == "__main__":
    main()
