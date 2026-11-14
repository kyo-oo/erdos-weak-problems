#!/usr/bin/env python3
"""
lc203.py — W63-B3: the LINE/COLUMN necessary-condition audit for the #203
torus covering (the S063 structural cell law made quantitative).

For a prime q (o2 = ord_q 2, o3 = ord_q 3, h = lcm(o2,o3), U = dlog 2,
V = dlog 3 w.r.t. a generator of <2,3>_q ~ Z/h):
  psi_q(k,l) = U k + V l mod h;  q | m 2^k 3^l + 1  <=>  psi_q(k,l) = w_q,
  w_q a FREE choice in Z/h (bijection with residues m mod q, m coprime q).

On the LINE l = l0: k must satisfy U k = w - V l0 (mod h); solvable iff
g_q := gcd(U, h) = h/o2 divides w - V l0; then it is ONE class k mod o2.
Hence line l0 is covered by 1D residue classes and the CLASSIC bound
  sum_{q live on l0} 1/o2(q) >= 1
is necessary for EVERY l0 (similarly columns: sum 1/o3 >= 1).

Live-set of q on the l-axis: l0 = lambda mod m_q, m_q = g_q/gcd(V, g_q),
a free choice of lambda (absorbed into w_q).  Total line mass:
  sum_q gcd(V_q, g_q)/h_q  >= min-line-budget-average ... >= 1 necessary.

This script: (1) computes exact (U,V) for the complete 42-prime L=27720
family (dual-method cross-check vs the banked pal_dlog_full.json),
(2) the aggregate line/column masses, (3) the OPTIMIZED per-line budget
profile (greedy load balancing of the live-classes), (4) verdict.
"""
import json, math, os, sys
from collections import defaultdict
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
L = 27720

def factor_small(x):
    fs = set(); d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    return fs

def dlogs(p, o2, o3, h):
    """generator of <2,3>_q and (U, V) dlogs of 2 and 3 (BSGS)."""
    # BFS the subgroup <2,3>
    sub = {1: None}
    frontier = [1]
    while frontier:
        nf = []
        for v in frontier:
            for m, tag in ((2, 0), (3, 1)):
                w = v * m % p
                if w not in sub:
                    sub[w] = (v, tag); nf.append(w)
        frontier = nf
    assert len(sub) == h, (p, len(sub), h)
    fs = factor_small(h)
    # find a generator: element of order h
    for g in sorted(sub):
        if g == 1: continue
        o = h
        for q in fs:
            while o % q == 0 and pow(g, o // q, p) == 1:
                o //= q
        if o == h:
            # BSGS for dlogs of 2 and 3
            m = int(math.isqrt(h)) + 1
            table = {}
            cur = 1
            for j in range(m):
                if cur not in table: table[cur] = j
                cur = cur * g % p
            ginv_m = pow(pow(g, m, p), -1, p)
            def bsgs(t):
                gamma = t % p
                for i in range(m + 2):
                    j = table.get(gamma)
                    if j is not None: return (i * m + j) % h
                    gamma = gamma * ginv_m % p
                return None
            U = bsgs(2); V = bsgs(3)
            assert U is not None and V is not None
            assert pow(g, U, p) == 2 % p and pow(g, V, p) == 3 % p
            return g, U, V
    raise RuntimeError("no generator found for p=%d" % p)

def main():
    fam = json.load(open(os.path.join(HERE, "fam27720.json")))["family"]
    dlbank = {r[0]: r for r in json.load(open(os.path.join(HERE, "pal_dlog_full.json")))}
    rows = []
    for (p, h, o2, o3) in fam:
        g, U, V = dlogs(p, o2, o3, h)
        # dual-method cross-check vs banked dlogs (generator may differ:
        # U,V both scale by a unit mod h; verify 2,3 reconstruction + kernel)
        b = dlbank.get(p)
        note = ""
        if b is not None:
            # reconstruct: find t with g^t = banked generator... simpler:
            # check that (U,V) and (bU,bV) generate the same kernel map:
            # same subgroup, both valid dlog pairs <=> exists unit t:
            # U = t*bU, V = t*bV mod h.  Solve t from U = t*bU (bU unit?).
            bU, bV = b[2], b[3]
            ok = False
            # try to solve t via both equations
            for (x, bx) in ((U, bU), (V, bV)):
                gg = math.gcd(bx, h)
                if math.gcd(x, h) != gg: continue
                if gg == 1:
                    t = x * pow(bx, -1, h) % h
                    if math.gcd(t, h) == 1 and (t * bU - U) % h == 0 and (t * bV - V) % h == 0:
                        ok = True; break
            note = "banked-OK" if ok else "BANKED-MISMATCH"
        else:
            note = "new-prime(no bank)"
        rows.append((p, h, o2, o3, U, V, g, note))
        print(f"p={p:6d} h={h:5d} o2={o2:5d} o3={o3:5d} U={U:5d} V={V:5d} g={g:5d} {note}")
    mism = [r for r in rows if r[7] == "BANKED-MISMATCH"]
    print(f"dlog dual-check: {len(rows)-len(mism)-sum(1 for r in rows if r[7]=='new-prime(no bank)')}/{sum(1 for r in rows if r[7]!='new-prime(no bank)')} consistent with banked file" if True else "")
    if mism:
        print("MISMATCHES:", mism)

    # ---- aggregate line/column masses --------------------------------
    lm = sum(Fraction(math.gcd(V, h // o2), h) for (_, h, o2, o3, U, V, _, _) in rows)
    cm = sum(Fraction(math.gcd(U, h // o3), h) for (_, h, o2, o3, U, V, _, _) in rows)
    print(f"AGGREGATE LINE mass  = {float(lm):.6f}  ({lm})")
    print(f"AGGREGATE COLUMN mass= {float(cm):.6f}  ({cm})")
    print(f"budget sum 1/h = {float(sum(Fraction(1,h) for (_,h,_,_,_,_,_,_) in rows)):.6f}")

    # ---- optimized per-line budget profile ---------------------------
    # each prime: live on l = lambda mod m_q (m_q = g/gcd(V,g)), weight 1/o2,
    # lambda free.  Greedy load balancing over the L lines.
    items = []
    for (p, h, o2, o3, U, V, _, _) in rows:
        g = h // o2
        m = g // math.gcd(V, g)
        items.append((p, m, o2))
    load = [Fraction(0)] * L
    for (p, m, o2) in sorted(items, key=lambda t: -1.0 / t[2]):
        w = Fraction(1, o2)
        # choose lambda minimizing the max load over its live lines
        bestlam, bestcost = None, None
        # live lines for lambda: l0 in [lambda + j*m for j in range(L/m)]
        nrep = L // m
        # cost of adding weight to the max-loaded line among live ones
        # precompute sums lazily: for each lambda track max load
        # efficient: lines l0 ≡ lambda (mod m); load depends only on l0
        cands = []
        for lam in range(m):
            mx = max(load[lam + j * m] for j in range(nrep))
            cands.append((mx, lam))
        cands.sort()
        lam = cands[0][1]
        for j in range(nrep):
            load[lam + j * m] += w
    mn = min(load); mx = max(load)
    print(f"OPTIMIZED per-line budget: min = {float(mn):.6f} ({mn}), max = {float(mx):.6f}")
    if mn >= 1:
        print("LINE CONDITION: PASS (with slack %.4f)" % float(mn - 1))
    else:
        print("LINE CONDITION: FAIL — deficit %.6f" % float(1 - mn))
    json.dump({"rows": [[p,h,o2,o3,U,V] for (p,h,o2,o3,U,V,_,_) in rows],
               "line_min": [float(mn)], "agg_line": float(lm), "agg_col": float(cm)},
              open(os.path.join(HERE, "lc203.json"), "w"))

if __name__ == "__main__":
    main()
