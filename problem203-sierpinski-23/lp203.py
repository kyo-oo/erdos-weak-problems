#!/usr/bin/env python3
"""
lp203.py — W63-B3: exact FRACTIONAL max-min line/column budget LP for the
#203 torus covering necessary conditions (scipy HiGHS).

NECESSARY CONDITIONS for a covering of the torus (Z/L2)x(Z/L3) by the family
(here L2 = L3 = 27720, the complete 42-prime census):
  for EVERY line l0:   sum_{q live on l0} 1/o2(q) >= 1
  for EVERY column k0: sum_{q live on k0} 1/o3(q) >= 1
(live on line l0 iff gcd(U,h) | w - V l0; the live l-classes are ONE class
lambda mod g_q, g_q = h/o2, lambda free via w_q; symmetric for columns.)

This LP computes the exact FRACTIONAL optimum of the max-min budget (an
upper bound for every integer placement).  Optimum < 1  ==>  the covering is
PROVABLY IMPOSSIBLE on this family (the axis is the bottleneck).
Dual-method: greedy integer placement (lower bound) + LP (upper bound).
"""
import json, math, os, sys
import numpy as np
from scipy import sparse
from scipy.optimize import linprog
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
L = 27720

def load_rows():
    d = json.load(open(os.path.join(HERE, "lc203.json")))["rows"]
    return [(p, h, o2, o3, U, V) for (p, h, o2, o3, U, V) in d]

def solve_axis(rows, axis, Lmod):
    """axis='line': weights 1/o2, moduli g=h/o2, live classes mod g over l in Z/Lmod.
       axis='col':  weights 1/o3, moduli g=h/o3, live classes mod g over k in Z/Lmod."""
    qs, ws, gs = [], [], []
    for (p, h, o2, o3, U, V) in rows:
        if axis == "line":
            w_num, g = 1, h // o2
            o = o2
        else:
            w_num, g = 1, h // o3
            o = o3
        qs.append(p); ws.append(Fraction(1, o)); gs.append(g)
    nq = len(qs)
    nvar = sum(gs) + 1   # x_{q,lambda} + t
    # constraint rows: Lmod line-budget rows + nq simplex rows
    rows_i, cols_i, vals = [], [], []
    colbase = {}
    c = 0
    for i in range(nq):
        colbase[i] = c
        c += gs[i]
    tcol = c
    # build sparse A_ub for line rows: -sum w*x[...] + t <= 0
    # and A_eq for simplex: sum_lambda x = 1
    r = 0
    for ell in range(Lmod):
        for i in range(nq):
            lam = ell % gs[i]
            # column index (i, lam)
            rows_i.append(ell); cols_i.append(colbase[i] + lam)
            vals.append(-float(ws[i]))
        rows_i.append(ell); cols_i.append(tcol); vals.append(1.0)
    A_ub = sparse.csr_matrix((vals, (rows_i, cols_i)), shape=(Lmod, nvar))
    b_ub = np.zeros(Lmod)
    er, ec, ev = [], [], []
    for i in range(nq):
        for lam in range(gs[i]):
            er.append(i); ec.append(colbase[i] + lam); ev.append(1.0)
    A_eq = sparse.csr_matrix((ev, (er, ec)), shape=(nq, nvar))
    b_eq = np.ones(nq)
    obj = np.zeros(nvar); obj[tcol] = -1.0
    bounds = [(0, None)] * nvar
    res = linprog(obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=bounds, method="highs")
    return res, ws, gs, qs

def greedy_min(rows, axis, Lmod):
    qs, ws, gs = [], [], []
    for (p, h, o2, o3, U, V) in rows:
        o = o2 if axis == "line" else o3
        qs.append(p); ws.append(Fraction(1, o)); gs.append(h // o)
    order = sorted(range(len(qs)), key=lambda i: -float(ws[i]))
    load = [Fraction(0)] * Lmod
    for i in order:
        g, w = gs[i], ws[i]
        best = None
        for lam in range(g):
            mx = max(load[lam + j * g] for j in range(Lmod // g))
            if best is None or mx < best[0]:
                best = (mx, lam)
        lam = best[1]
        for j in range(Lmod // g):
            load[lam + j * g] += w
    return min(load), max(load)

def main():
    rows = load_rows()
    for axis in ("line", "col"):
        t0 = time.time() if (time := __import__("time")) else 0
        res, ws, gs, qs = solve_axis(rows, axis, L)
        frac = -res.fun if res.success else None
        gmin, gmax = greedy_min(rows, axis, L)
        print(f"[{axis}] LP fractional max-min = {frac:.6f}   "
              f"(greedy integer min = {float(gmin):.6f}, max = {float(gmax):.6f})")
        verdict = "PASS (necessary cond satisfied fractionally)" if frac is not None and frac >= 1.0 else \
                  "FAIL — covering PROVABLY impossible on this family" if frac is not None else "LP FAILED"
        print(f"[{axis}] verdict: {verdict}")
        # per-parity diagnostic
        if axis == "line":
            base = sum(Fraction(1, o2) for (_, _, o2, _, _, _) in rows if (lambda h, o2: h // o2)(rows[0][1], rows[0][2]) == 1)
        print()

if __name__ == "__main__":
    main()
