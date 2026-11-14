#!/usr/bin/env python3
"""W66-P203-D A4b — VALIDATION of the joint-order machinery behind the
Bonferroni-E3 no-go bound (the audit of the audit).

The bound uses J_{S} = |image of (k,l) -> (2^k 3^l mod p)_{p in S}| for
pairs/triples, computed via gcd of maximal minors of the dlog relation
matrix. Validated here by BRUTE FORCE:

  V1  pair_J / triple_J vs brute-force subgroup order (samples).
  V2  forced pair (g=1): every coset pair intersects in exactly
      (Lk*Ll)/J cells (brute force on the small common torus).
  V3  avoidable pair (g>1): some coset pair has EMPTY intersection.
  V4  Bonferroni E3 inequality: brute-force union of random coset
      systems vs S1 - S2 + S3 computed exactly.
"""
import json, math, os, sys, random
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
PDIR = os.path.dirname(HERE)
sys.path.insert(0, HERE)

def brute_joint_order(Us, Vs, hs):
    gens = [tuple(U % h for U, h in zip(Us, hs)), tuple(V % h for V, h in zip(Vs, hs))]
    seen = {(0,) * len(hs)}
    frontier = list(seen)
    while frontier:
        newf = []
        for x in frontier:
            for g in gens:
                y = tuple((a + b) % h for a, b, h in zip(x, g, hs))
                if y not in seen:
                    seen.add(y); newf.append(y)
        frontier = newf
    return len(seen)

def pair_J_formula(a, b):
    hp, hq = a["h"], b["h"]
    Up, Vp, Uq, Vq = a["U"], a["V"], b["U"], b["V"]
    minors = [hp * hq, hp * Uq, hp * Vq, hq * Up, hq * Vp, abs(Up * Vq - Uq * Vp)]
    g = 0
    for m in minors:
        g = math.gcd(g, m)
    return (hp * hq) // g, g

def triple_J_formula(a, b, c):
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

def load_family(L):
    pal = json.load(open(os.path.join(PDIR, "pal_dlog_full.json")))
    return [{"q": int(r[0]), "h": int(r[1]), "U": int(r[2]), "V": int(r[3]),
             "o2": int(r[4]), "o3": int(r[5])} for r in pal if L % int(r[1]) == 0]

def coset_cells(q, t, o2, o3, Lk, Ll):
    """cells (k,l), k<Lk, l<Ll, with 2^k 3^l = t mod q (brute enumeration)."""
    cells = set()
    p3 = {pow(3, l, q): l for l in range(o3)}
    pw2 = 1
    for k in range(o2):
        need = t * pow(pw2, -1, q) % q
        if need in p3:
            l0 = p3[need]
            for kk in range(k, Lk, o2):
                for ll in range(l0, Ll, o3):
                    cells.add((kk, ll))
        pw2 = pw2 * 2 % q
    return cells

def main():
    fam = load_family(27720)
    print(f"family: {len(fam)} primes", flush=True)

    # V1 pairs (first 25 family members, all pairs) and triples (first 14)
    bad = 0; tested = 0
    for a, b in combinations(fam[:25], 2):
        Jf, g = pair_J_formula(a, b)
        Jb = brute_joint_order([a["U"], b["U"]], [a["V"], b["V"]], [a["h"], b["h"]])
        tested += 1
        if Jf != Jb:
            bad += 1
            print(f"   V1 PAIR MISMATCH q={a['q']},{b['q']}: formula {Jf} brute {Jb}", flush=True)
    print(f"V1 pair formula vs brute force: {tested} pairs, mismatches {bad}", flush=True)

    badt = 0; testedt = 0
    for a, b, c in combinations(fam[:14], 3):
        Jf = triple_J_formula(a, b, c)
        Jb = brute_joint_order([a["U"], b["U"], c["U"]], [a["V"], b["V"], c["V"]],
                               [a["h"], b["h"], c["h"]])
        testedt += 1
        if Jf != Jb:
            badt += 1
            print(f"   V1 TRIPLE MISMATCH {a['q']},{b['q']},{c['q']}: formula {Jf} brute {Jb}", flush=True)
    print(f"V1 triple formula vs brute force: {testedt} triples, mismatches {badt}", flush=True)

    # V2/V3 pair intersection structure on the minimal common torus
    checks = 0; bad2 = 0; empty_found = 0
    for a, b in combinations(fam[:14], 2):
        Jf, g = pair_J_formula(a, b)
        Lk = a["o2"] * b["o2"] // math.gcd(a["o2"], b["o2"])
        Ll = a["o3"] * b["o3"] // math.gcd(a["o3"], b["o3"])
        if Lk * Ll > 600000:
            continue
        Ha = sorted({pow(2, k, a["q"]) * pow(3, l, a["q"]) % a["q"]
                     for k in range(a["o2"]) for l in range(a["o3"])})
        Hb = sorted({pow(2, k, b["q"]) * pow(3, l, b["q"]) % b["q"]
                     for k in range(b["o2"]) for l in range(b["o3"])})
        assert len(Ha) == a["h"] and len(Hb) == b["h"]
        if g == 1:  # forced: EVERY coset pair intersects in exactly Lk*Ll/J cells
            for ta in (Ha[0], Ha[len(Ha)//2], Ha[-1]):
                for tb in (Hb[0], Hb[len(Hb)//2], Hb[-1]):
                    ca = coset_cells(a["q"], ta, a["o2"], a["o3"], Lk, Ll)
                    cb = coset_cells(b["q"], tb, b["o2"], b["o3"], Lk, Ll)
                    inter = len(ca & cb)
                    if inter != (Lk * Ll) // Jf:
                        bad2 += 1
                        print(f"   V2 VIOLATION {a['q']},{b['q']} t={ta},{tb}: "
                              f"inter {inter} != {(Lk*Ll)//Jf}", flush=True)
                    checks += 1
        else:
            for ta in Ha:
                ca = coset_cells(a["q"], ta, a["o2"], a["o3"], Lk, Ll)
                for tb in Hb:
                    cb = coset_cells(b["q"], tb, b["o2"], b["o3"], Lk, Ll)
                    if not (ca & cb):
                        empty_found += 1
                        break
                else:
                    continue
                break
            checks += 1
    print(f"V2/V3 forced/avoidable structure: {checks} pairs checked, violations {bad2}, "
          f"empty intersections found for {empty_found}/{sum(1 for a,b in combinations(fam[:14],2) if pair_J_formula(a,b)[1]>1 and (a['o2']*b['o2']//math.gcd(a['o2'],b['o2']))*(a['o3']*b['o3']//math.gcd(a['o3'],b['o3']))<=600000)} avoidable pairs", flush=True)

    # V4 Bonferroni E3 on random coset systems (small family, exact)
    rng = random.Random(99)
    sub = [f for f in fam if f["q"] in (5, 7, 11, 13, 17, 43)]
    o2l = 1; o3l = 1
    for f in sub:
        o2l = o2l * f["o2"] // math.gcd(o2l, f["o2"])
        o3l = o3l * f["o3"] // math.gcd(o3l, f["o3"])
    Lk, Ll = o2l, o3l
    print(f"V4 Bonferroni E3 exact test on family {[f['q'] for f in sub]} at torus {Lk}x{Ll}", flush=True)
    viol = 0
    for trial in range(40):
        cosets = []
        for f in sub:
            H = sorted({pow(2, k, f["q"]) * pow(3, l, f["q"]) % f["q"]
                        for k in range(f["o2"]) for l in range(f["o3"])})
            t = rng.choice(H)
            cosets.append((f, t, coset_cells(f["q"], t, f["o2"], f["o3"], Lk, Ll)))
        uni = set().union(*(c[2] for c in cosets))
        S1 = sum(len(c[2]) for c in cosets)
        S2 = sum(len(ca & cb) for ca, cb in combinations([c[2] for c in cosets], 2))
        S3 = sum(len(ca & cb & cc) for ca, cb, cc in combinations([c[2] for c in cosets], 3))
        E3 = S1 - S2 + S3
        if E3 < len(uni):
            viol += 1
            print(f"   V4 VIOLATION: E3={E3} < |union|={len(uni)}", flush=True)
    print(f"V4 Bonferroni E3 >= |union| on 40 random systems: violations {viol}", flush=True)
    print("A4b DONE", flush=True)

if __name__ == "__main__":
    main()
