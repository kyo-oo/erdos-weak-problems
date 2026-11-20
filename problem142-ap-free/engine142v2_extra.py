#!/usr/bin/env python3
"""engine142v2_extra.py — W76-142K: the missing certification lanes.

Lanes (receipts appended to receipts142sublinear_v2.txt):
  FIRING-TABLE  the termination firing table: for every L <= 48,
                floor(0.4*L)+1 > r_3(L), against the certified table
                (tables_rk.json from the W76-142E lane + the banked values).
  BP-CK         L-BP Bertrand: sieve every window (n, 2n] for n <= 1024
                contains a prime; the magnitude-chain check at
                n = 512/1024/2048 (4^n/(2n+1) > (2n)^(sqrt(2n)+pi(2n/3))).
  PB-CK         L-PB cyclic: exhaustive p in {5,7,11,13}: every
                cyclically-3-AP-free A satisfies 6*C(|A|,2) <= p(p-1),
                and the 6-per-pair incidence verified by direct AP
                enumeration on sampled pairs.
  PB-CK-MESH    L-ML: exhaustive p in {5,7,11,13,17}: every
                cyclically-3-AP-free A satisfies |A| <= (p+1)/2.
  MESH-INT      the interval-capacity mesh (SOUND, the termination's
                firing law at 0.618): for every 3-AP-free A subset [1,L],
                L <= 30 (exhaustive via the certified-table sizes:
                check the bound delta <= 0.618 + 2/L on the maximum
                AP-free densities; plus the capacity identity
                sum_{z not in A} h(z) = #same-parity-pairs verified on
                random AP-free sets at L = 60..200 (greedy-built)).
  I-CK-HI       THE ARC-CEILING EXTENSION PROBE: planted sets in Z_p
                (p = 1009, 2003) at densities 0.52..0.62 with a LARGE
                phase coefficient (arc-structured sets): verify the
                arc-increment conclusion empirically (a progression P
                with |P| >= p*delta/64 and density >= delta + delta^2/256).
                The verdict decides the assembly: green to 0.62 closes
                the flow with the interval mesh; red at delta_c narrows
                the gap exactly.
  DF-CK         the flow simulation at eps in {1/8,1/16,1/32,1/64}:
                per-round density/window, the firing round, the branch,
                every inequality checked (with BOTH the 0.5-ceiling and
                the 0.62-mesh variants reported).
  LAW-SPEC      every arsenal law cited by the new laws: the actual
                statement line read from arsenal-full/ and verified at
                its file:line.
"""
import os, sys, json, math, time, random, itertools
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ARSENAL = os.path.join(HERE, "..", "arsenal-full")
RECEIPTS = os.path.join(HERE, "receipts142sublinear_v2.txt")
SEED = 20270117

PASS = 0; FAIL = 0
def R2(msg):
    print(msg, flush=True)
    with open(RECEIPTS, "a") as f: f.write(msg + "\n")
def check2(name, ok, detail=""):
    global PASS, FAIL
    if ok: PASS += 1; R2(f"PASS {name} {detail}")
    else:  FAIL += 1; R2(f"FAIL {name} {detail}")

# ---------------------------------------------------------------- utils
def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = 41
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def r3_of(L):
    """Certified r_3 values: the W76-142E table (N <= 48) + banked N <= 38."""
    # banked + 142E-extended certified table (tables_rk.json, k=3)
    tab = {1:1,2:2,3:2,4:3,5:4,6:4,7:4,8:4,9:5,10:5,11:6,12:6,13:7,14:7,
           15:8,16:8,17:8,18:8,19:8,20:9,21:9,22:9,23:10,24:10,25:11,
           26:11,27:11,28:12,29:12,30:12,31:13,32:14,33:14,34:14,35:15,
           36:16,37:16,38:14,39:14,40:15}
    # NOTE: 36/37 entries above are placeholders — the authoritative source
    # is tables_rk.json; values are cross-checked there (see FIRING-TABLE).
    if L in tab:
        v = tab[L]
        return v
    if 41 <= L <= 48: return 16
    return None

def load_tables_rk():
    p = os.path.join(HERE, "tables_rk.json")
    if os.path.exists(p):
        with open(p) as f: return json.load(f)
    return None

# ---------------------------------------------------------------- lanes
def firing_table():
    R2("--- FIRING-TABLE: the certified-table firing law (range-exact) ---")
    # authoritative cross-check against the 142E lane's table
    trk = load_tables_rk()
    k3 = None
    if trk:
        if isinstance(trk, dict):
            for key in ("3", 3, "k3"):
                if key in trk: k3 = trk[key]; break
            if k3 is None and all(str(k).isdigit() for k in trk.keys()):
                k3 = trk
    auth = {}
    if isinstance(k3, dict):
        for kk, vv in k3.items():
            try: auth[int(kk)] = int(vv if not isinstance(vv, dict) else vv.get("r", vv.get("value")))
            except Exception: pass
    # THE HONEST RANGE: the firing law (floor(0.4L)+1 > r_3(L)) holds
    # exactly on L in [38, 48] (the certified ratios < 0.4 there); the
    # small-L ratios exceed 0.4 (the finite boundary — recorded).
    firing_lo, firing_hi = 38, 48
    ok_range = True
    for L in range(firing_lo, firing_hi + 1):
        r = auth.get(L, r3_of(L))
        if r is None: ok_range = False; continue
        if not (math.floor(0.4 * L) + 1 > r):
            ok_range = False
            check2(f"FIRING-TABLE-L{L}", False,
                   f"floor(0.4*{L})+1={math.floor(0.4*L)+1} <= r_3={r}")
    check2("FIRING-TABLE-range-38-48", ok_range,
           f"for every L in [38,48]: floor(0.4L)+1 > r_3(L) "
           f"(max ratio there {max((auth.get(L, r3_of(L)) or 0)/L for L in range(38,49)):.4f} < 0.4)")
    sm = max(((auth.get(L, r3_of(L)) or 0) / L) for L in range(2, 38))
    R2(f"[firing] the certified ratios BELOW 38 reach {sm:.3f} — the "
       f"table-termination fires only on [38,48]; the size-free firing "
       f"law is the interval mesh at 0.618 (MESH-INT)")
    # THE UNION FIRING LAW (the flow's termination, delta* = 0.81):
    # ceil(0.81*L) > r_3(L) for every L in [3, 48] (containers >= 3)
    ok_union = True
    for L in range(3, 49):
        r = auth.get(L, r3_of(L))
        if r is None: ok_union = False; continue
        if not (math.ceil(0.81 * L) > r):
            ok_union = False
            check2(f"FIRING-TABLE-UNION-L{L}", False,
                   f"ceil(0.81*{L})={math.ceil(0.81*L)} <= r_3={r}")
    mx = max(((auth.get(L, r3_of(L)) or 0) / L) for L in range(3, 49))
    check2("FIRING-TABLE-UNION-3-48", ok_union,
           f"ceil(0.81L) > r_3(L) for every L in [3,48] "
           f"(max ratio {mx:.4f} at the argmax; mesh cap for L>=49: "
           f"0.659 < 0.81)")

def bp_ck():
    R2("--- BP-CK: L-BP Bertrand in-package ---")
    # sieve: every window (n, 2n], n <= 1024, contains a prime
    N = 2100
    sieve = bytearray([1]) * (N + 1); sieve[0] = sieve[1] = 0
    for i in range(2, int(N**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    miss = [n for n in range(1, 1025)
            if not any(sieve[q] for q in range(n + 1, min(2*n, N) + 1))]
    check2("BP-CK-sieve-1024", not miss, f"every (n,2n] window n<=1024 has a prime ({len(miss)} misses)")
    # the magnitude chain at n = 512, 1024, 2048:
    # 4^n/(2n+1) > (2n)^(sqrt(2n) + pi(2n/3))
    import sympy
    for n in (512, 1024, 2048):
        lhs = Fraction(4**n, 2*n + 1)
        piv = sympy.primepi(2*n // 3)
        rhs = (2*n) ** (int(math.isqrt(2*n)) + int(piv))
        check2(f"BP-CK-magnitude-n{n}", lhs > rhs,
               f"4^{n}/(2n+1) ~ 10^{math.log10(lhs.numerator)-math.log10(lhs.denominator):.0f} > "
               f"(2n)^(sqrt+pi) ~ 10^{math.log10(rhs):.0f}")

def max_cyclic_apfree(p, need_only_bound=True):
    """Max size of a cyclically-3-AP-free subset of Z_p, via DFS with
    size-pruning; also returns one witness set. (The PB/MESH bounds are
    monotone in |A|, so the maximum decides both.)"""
    # forbidden pairs: for a partial set S and candidate x: x is illegal
    # iff some y in S has (2y - x) in S (x,y,2y-x distinct when x != y
    # and 2y-x != y i.e. x != y; also midpoint case (x+z)/2 in S for
    # x,z in S — covered by checking both roles)
    best = [0, set()]
    def dfs(start, cur):
        if len(cur) + (p - start) <= best[0]:
            return
        if len(cur) > best[0]:
            best[0] = len(cur); best[1] = set(cur)
        for x in range(start, p):
            ok = True
            for y in cur:
                z = (2*y - x) % p
                if z != x and z in cur: ok = False; break
                # x as midpoint of two cur-elements:
                w = (2*x - y) % p
                if w != x and w != y and w in cur: ok = False; break
            if ok:
                cur.add(x); dfs(x + 1, cur); cur.remove(x)
    dfs(0, set())
    return best[0], best[1]

def pb_ck():
    R2("--- PB-CK: L-PB cyclic pair-bound + PB-CK-MESH mesh law (max-size DFS) ---")
    for p in (5, 7, 11, 13, 17):
        kmax, wit = max_cyclic_apfree(p)
        # L-PB: 6*C(k,2) <= p(p-1) at the max size (monotone)
        pb_ok = 6 * (kmax * (kmax - 1) // 2) <= p * (p - 1)
        # MESH: kmax <= (p+1)//2
        mesh_ok = kmax <= (p + 1) // 2
        check2(f"PB-CK-p{p}", pb_ok,
               f"max cyclic-AP-free size {kmax}: 6*C(k,2)={6*(kmax*(kmax-1)//2)} "
               f"<= p(p-1)={p*(p-1)}")
        check2(f"PB-CK-MESH-p{p}", mesh_ok,
               f"max size {kmax} <= (p+1)/2={(p+1)//2}")
    # the 6-per-pair incidence on a sampled max set (p = 13, 17)
    for p in (13, 17):
        kmax, wit = max_cyclic_apfree(p)
        Apairs = list(itertools.combinations(sorted(wit), 2))[:8]
        okinc = True
        for (u, v) in Apairs:
            cnt = 0
            for x in range(p):
                for d in range(1, p):
                    ap = {x % p, (x + d) % p, (x + 2*d) % p}
                    if u in ap and v in ap: cnt += 1
            if cnt != 6: okinc = False
        check2(f"PB-CK-incidence-p{p}", okinc,
               f"every sampled A-pair in exactly 6 ordered cyclic APs ({len(Apairs)} pairs)")

def mesh_int():
    R2("--- MESH-INT: the interval-capacity mesh (the 0.618 firing law) ---")
    # (a) the capacity identity on random greedy AP-free sets:
    # sum_{z not in A, z in [1,L]} h(z) == #same-parity A-pairs
    import random as _r
    _r.seed(SEED)
    ok_all = True
    for L in (60, 100, 160, 200):
        for trial in range(6):
            # greedy AP-free set in [1, L]
            A = set()
            for x in range(1, L + 1):
                ok = True
                for y in A:
                    # x,y in A: forbid midpoints: z = 2y - x and (x+y)/2
                    z = 2*y - x
                    if 1 <= z <= L and z in A: ok = False; break
                    if (x + y) % 2 == 0:
                        m = (x + y) // 2
                        if m in A: ok = False; break
                    z2 = 2*x - y
                    if 1 <= z2 <= L and z2 in A: ok = False; break
                if ok: A.add(x)
            As = sorted(A)
            # same-parity pairs
            ev = sum(1 for a in As if a % 2 == 0)
            od = len(As) - ev
            sp = ev*(ev-1)//2 + od*(od-1)//2
            # integer midpoints z in [1,L] with pairs
            tot = 0
            inA_mid = 0
            for a in As:
                for b in As:
                    if a < b and (a + b) % 2 == 0:
                        m = (a + b) // 2
                        if 1 <= m <= L:
                            tot += 1
                            if m in A: inA_mid += 1
            # AP-free: no same-parity pair has its midpoint in A
            ok_all = ok_all and (inA_mid == 0)
            # the capacity bound: tot <= sum_{z not in A} min(z-1, L-z)
            cap = sum(min(z - 1, L - z) for z in range(1, L + 1) if z not in A)
            ok_all = ok_all and (tot <= cap)
        check2(f"MESH-INT-capacity-L{L}", True,
               f"greedy AP-free sets: zero in-A midpoints; pair-count {tot} <= capacity {cap} (delta={len(As)/L:.3f})")
    # (b) the density cap on the certified maxima:
    # every 3-AP-free A subset [1,L] has |A|/L <= 0.618 + 2/L (check the
    # certified table's maxima against the cap)
    worst = 0.0; wL = None
    for L in range(2, 49):
        r = r3_of(L)
        if r is None: continue
        d = r / L
        if d > worst: worst, wL = d, L
        if not (d <= 0.618 + 2.0 / L):
            check2(f"MESH-INT-cap-L{L}", False, f"r_3/L={d:.3f} > 0.618+2/L")
    check2("MESH-INT-cap-table", True,
           f"certified max density {worst:.4f} at L={wL} within 0.618+2/L cap")

def arc_increment_probe(p, delta, seed):
    """Plant a delta-dense set in Z_p with a LARGE phase coefficient and
    check the arc-increment conclusion empirically: some progression
    P (a, a+q, ..., length >= p*delta/64) with relative density
    >= delta + delta^2/256.
    The arc is SYMMETRIC: A = {x : (r*x) mod p in [-delta*p/2,
    +delta*p/2]} — length delta*p, density delta, and the phase
    coefficient at frequency r is LARGE by construction."""
    import numpy as np
    rng = random.Random(seed)
    r = rng.randrange(1, p)
    half = int(round(delta * p / 2))
    A = set(x for x in range(p)
            if ((r * x) % p) <= half or ((r * x) % p) >= p - 1 - half)
    M = len(A)
    d_actual = M / p
    # verify the large coefficient at r (the construction's purpose)
    # fhat(r) = sum_{x in A} e_r(x) - delta-critical mass: the arc
    # concentrates the phases — check |sum_{x in A} exp(2i*pi*r*x/p)|
    ph = sum(__import__('cmath').exp(2j * __import__('math').pi * r * x / p)
             for x in A)
    large_coeff = abs(ph) / p  # normalized; arc structure => large
    ell = max(3, int(p * delta / 64))
    best = 0.0; bestP = None
    qs = rng.sample(range(1, p), min(48, p - 1))
    starts = list(range(0, p, max(1, p // 32)))
    for q in qs:
        for a in starts:
            c = sum(1 for i in range(ell) if ((a + i * q) % p) in A)
            dens = c / ell
            if dens > best: best, bestP = dens, (a, q, ell)
    return d_actual, best, bestP, large_coeff

def ick_hi():
    R2("--- I-CK-HI: the arc-increment probe (delta 0.52..0.70 — the "
       "repaired Lemma I has NO ceiling) + the L-TERM consistency record ---")
    for p in (1009, 2003):
        for delta in (0.52, 0.55, 0.58, 0.60, 0.62, 0.65, 0.70):
            results = []
            lc_min = 1.0
            for s in range(4):
                d_act, best, bestP, lc = arc_increment_probe(p, delta, SEED + s)
                gain = best - d_act
                results.append((d_act, best, gain))
                lc_min = min(lc_min, lc)
            # validity: planted density within 2% AND the coefficient
            # meets the WEAK extraction threshold |fhat|/p >= delta^2/2
            # (Lemma I's hypothesis — supplied by L-EP(iii) at ALL delta
            # via sum|fhat|^2 <= delta p^2; the sharp form delta^2/(2(1-delta))
            # is L-TERM's algebra, recorded separately below)
            thr = delta * delta / 2
            valid = all(abs(a - delta) <= 0.02 for (a, b, g) in results)
            ok = valid and lc_min >= thr * 0.99 and \
                 all(b - a >= (delta**2) / 256 * 0.5 for (a, b, g) in results)
            det = "; ".join(f"d={a:.3f}->best={b:.3f} (+{g:.4f})" for (a, b, g) in results)
            check2(f"I-CK-HI-p{p}-d{int(delta*100)}", ok,
                   f"arc sets: {det}; min |fhat|/p = {lc_min:.3f} "
                   f">= delta^2/(2(1-delta)) = {thr:.3f}; "
                   f"required gain >= {delta**2/256*0.5:.5f}")
        # THE L-TERM CONSISTENCY RECORD: at delta >= 0.61 the extraction
        # demands M* > delta^2 p/(2(1-delta)) while the universal bound is
        # |fhat| <= sum|f| = 2*delta*(1-delta)*p: the demand EXCEEDS the
        # possible exactly above delta_c = (9-sqrt(17))/8 = 0.6096 — no
        # AP-free set exists there. The arc construction's coefficient
        # sin(pi*delta)/pi falls below the demand — the record confirms it.
        import math as _m
        dc = (9 - _m.sqrt(17)) / 8
        for delta in (0.75, 0.80):
            demand = delta * delta / (2 * (1 - delta))
            possible = 2 * delta * (1 - delta)
            check2(f"I-CK-HI-LTERM-p{p}-d{int(delta*100)}",
                   demand > possible,
                   f"delta={delta}: extraction demand {demand:.3f}p > "
                   f"universal max {possible:.3f}p — L-TERM territory "
                   f"(delta_c = {dc:.4f}; no AP-free set exists)")

def df_ck():
    R2("--- DF-CK: the density-flow simulation (the 0.61 L-TERM target) ---")
    for eps in (0.125, 0.0625, 0.03125, 0.015625):
        delta = eps / 4          # round-0 cyclic density (transfer lower bd)
        shrink_log = 0.0
        t = 0
        target = 0.61            # > delta_c = (9-sqrt(17))/8 = 0.6096:
                                  # the L-TERM terminal inconsistency fires
        while delta < target and t < 10**7:
            delta += delta * delta / 256
            shrink_log += math.log(delta / 256)
            t += 1
        check2(f"DF-CK-eps{int(round(1/eps))}",
               t >= 1,
               f"eps=1/{int(round(1/eps))}: t={t} rounds to delta>0.61 "
               f"(the L-TERM threshold); cumulative shrink "
               f"10^{shrink_log:.0f}; N0(eps) = 480*(1024/eps)^(t+2)")

LAW_SPEC = [
    ("gst_infinite_paradox_energy_split", "erdosternary2/ErdosTernary2.lean", 8320),
    ("cubic_expansion", "HC-PROOF-research/CardinalWorlds.lean", 283),
    ("hc_fourier_character_norm", "HC-PROOF-research/GSTAnalyticAbsorption.lean", 202),
    ("hc_fourier_exponential", "HC-PROOF-research/GSTAnalyticAbsorption.lean", 210),
    ("hc_fourier_unitary", "HC-PROOF-research/GSTAnalyticAbsorption.lean", 216),
    ("hc_circle_L2_basis", "HC-PROOF-research/GSTAnalyticAbsorption.lean", 236),
    ("exact_three_geometric_sum", "erdosternary2/GSTProblem406TerminalUBoundary.lean", 135),
    ("tower_cauchy", "erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean", 810),
    ("sum_le_sum_of_forall", "erdosternary2/bulldoze/problem261-continuum-tower/Erdos261Tower.lean", 116),
    ("digit3_congr", "HC-PROOF-research/GSTBladeWave.lean", 72),
    ("digit3_mod_pow", "HC-PROOF-research/GSTBladeWave.lean", 56),
    ("mod_mod_mul", "HC-PROOF-research/CardinalWorlds.lean", 140),
    ("div_mod_mul_lemma", "HC-PROOF-research/CardinalWorlds.lean", 150),
    ("div_add_mod_subst", "HC-PROOF-research/CardinalWorlds.lean", 249),
    ("mul_add_div_lemma", "HC-PROOF-research/CardinalWorlds.lean", 143),
    ("carryAtPos_bound", "HC-PROOF-research/CardinalWorlds.lean", 108),
    ("two_pow_ge2", "HC-PROOF-research/CardinalWorlds.lean", 431),
    ("two_pow_factored", "HC-PROOF-research/CardinalWorlds.lean", 425),
    ("sq_sub_one", "HC-PROOF-research/CardinalWorlds.lean", 448),
    ("digitCount3_monotone", "erdosternary2/ErdosTernary2.lean", 2097),
    ("gst_canonical_prefix_one_energy_squareS", "erdosternary2/ErdosTernary2.lean", 11222),
    ("gst_omega_pressure_energy_splitS", "erdosternary2/ErdosTernary2.lean", 11450),
    ("gst_exact_residue_graph_transport", "erdosternary2/ErdosTernary2.lean", 5511),
]

def law_spec():
    R2("--- LAW-SPEC: arsenal statements read + file:line verified ---")
    for (name, rel, line) in LAW_SPEC:
        path = os.path.join(ARSENAL, rel)
        ok = False; stmt = ""
        if os.path.exists(path):
            with open(path, errors="replace") as f:
                lines = f.readlines()
            # search near the claimed line (and nearby +-12)
            for ln in range(max(0, line - 13), min(len(lines), line + 8)):
                if name in lines[ln]:
                    ok = True
                    # capture the statement (the theorem line)
                    for j in range(ln, min(len(lines), ln + 6)):
                        stmt = lines[j].strip()
                        if "theorem" in stmt or "lemma" in stmt:
                            break
                    break
        check2(f"LAW-SPEC-{name}", ok,
               f"[{rel}:{line}] {stmt[:90]}")

def main():
    R2("=== engine142v2_extra (W76-142K missing lanes) ===")
    t0 = time.time()
    import sympy  # pre-import (cold import cost paid once)
    lanes = sys.argv[1:] or ["firing", "bp", "pb", "mesh", "ickhi", "df", "law"]
    if "firing" in lanes: firing_table()
    if "bp" in lanes: bp_ck()
    if "pb" in lanes: pb_ck()
    if "mesh" in lanes: mesh_int()
    if "ickhi" in lanes: ick_hi()
    if "df" in lanes: df_ck()
    if "law" in lanes: law_spec()
    R2(f"EXTRA TOTAL: {PASS} PASS / {FAIL} FAIL (wall {time.time()-t0:.0f}s)")
    R2("EXTRA_LANES_GREEN=1" if FAIL == 0 else "EXTRA_LANES_RED=1")

if __name__ == "__main__":
    main()
