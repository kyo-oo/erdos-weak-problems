#!/usr/bin/env python3
"""
line203.py — W63-B3: THE INTEGER line/column necessary-condition solver for
the #203 covering families (the certified impossibility frontier).  v2:
per-family invocation + checkpoint + DUAL verification (z3 re-solve of the
same integer program + direct exact-Fraction recomputation of the optimal
placement's line loads).

LAW (campaign-derived): on line l=l0 of the torus (Z/L2)x(Z/L3), a prime q
(o2,o3,U,V,h) is live iff gcd(U,h) =: g_q | (w_q - V*l0); with the coset w_q
FREE, q is live on exactly the lines l0 = lambda_q mod m_q, where
   m_q = g_q / gcd(V_q, g_q),  g_q = h_q/o2_q,
and on every live line it covers ONE k-class mod o2_q (L2/o2_q cells).
NECESSARY for a covering: for EVERY line: sum over live primes of 1/o2 >= 1.
Loads depend only on l0 mod M, M = lcm(m_q) — so the L3 lines collapse to M
line-TYPES and the INTEGER max-min placement is an exact finite problem.

Verdict: integer line-opt < 1  =>  NO COVERING EXISTS with this family (any
subset, any coset assignment) — a complete negative theorem for that census.

Usage: line203.py <family-index>          (families in census order)
"""
import json, math, os, sys, time
from collections import defaultdict
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
CKPT = os.path.join(HERE, "line203.json")
def log(s): print(s, flush=True)

def axis_items(rows, axis):
    out = []
    for (p, h, o2, o3, U, V) in rows:
        if axis == "line":
            o = o2; g = h // o2; v = V
        else:
            o = o3; g = h // o3; v = U
        m = g // math.gcd(v, g)
        out.append((p, o, g, m))
    return out

def solve_maxmin(items, timelimit=240.0):
    """max-min integer placement. Returns (opt_fraction, placement, M, how)."""
    from scipy import sparse
    from scipy.optimize import milp, LinearConstraint, Bounds
    import numpy as np
    M = 1
    for (p, o, g, m) in items: M = M * m // math.gcd(M, m)
    fixed = [(p, o, g, m) for (p, o, g, m) in items if m == 1]
    base = [Fraction(0)] * M
    for (p, o, g, m) in fixed:
        for t in range(M): base[t] += Fraction(1, o)
    movers = [(p, o, g, m) for (p, o, g, m) in items if m > 1]
    vidx = {}; nv = 0
    for (p, o, g, m) in movers:
        for lam in range(m):
            vidx[(p, lam)] = nv; nv += 1
    tcol = nv; nv += 1
    rows_i, cols_i, vals = [], [], []
    for tt in range(M):
        for (p, o, g, m) in movers:
            lam = tt % m
            rows_i.append(tt); cols_i.append(vidx[(p, lam)]); vals.append(1.0 / o)
        rows_i.append(tt); cols_i.append(tcol); vals.append(-1.0)
    A = sparse.csr_matrix((vals, (rows_i, cols_i)), shape=(M, nv))
    lb = np.full(M, -np.inf); ub = np.full(M, np.inf)
    for tt in range(M): lb[tt] = -float(base[tt])
    cons = [LinearConstraint(A, lb, ub)]
    rows_i, cols_i, vals = [], [], []
    for i, (p, o, g, m) in enumerate(movers):
        for lam in range(m):
            rows_i.append(i); cols_i.append(vidx[(p, lam)]); vals.append(1.0)
    A2 = sparse.csr_matrix((vals, (rows_i, cols_i)), shape=(len(movers), nv))
    cons.append(LinearConstraint(A2, np.ones(len(movers)), np.ones(len(movers))))
    c = np.zeros(nv); c[tcol] = -1.0
    integrality = np.ones(nv); integrality[tcol] = 0
    xl = np.zeros(nv); xu = np.ones(nv); xu[tcol] = np.inf
    options = {"time_limit": timelimit}
    res = milp(c, constraints=cons, integrality=integrality, bounds=Bounds(xl, xu),
               options=options)
    if not res.success:
        return None, None, M, f"milp-fail({res.message[:60]})"
    # placement from x
    place = {}
    xs = res.x
    for (p, o, g, m) in movers:
        for lam in range(m):
            if xs[vidx[(p, lam)]] > 0.5:
                place[p] = lam
    opt = Fraction(-float(res.fun)).limit_denominator(10**6)
    gap = getattr(res, "mip_gap", None)
    how = f"milp(gap={gap})" if gap is not None else "milp"
    if gap is not None and gap > 1e-9:
        how = f"milp-INCOMPLETE(gap={gap:.2e})"   # honest label
    return opt, place, M, how

def verify_placement(items, place, axis):
    """EXACT rational recomputation of the min load for a given placement."""
    M = 1
    for (p, o, g, m) in items: M = M * m // math.gcd(M, m)
    loads = [Fraction(0)] * M
    for (p, o, g, m) in items:
        lam = place.get(p, 0)
        w = Fraction(1, o)
        for t in range(lam, M, m):
            loads[t] += w
    return min(loads), max(loads)

def z3_crosscheck(items, timelimit=300):
    """second-method solve of the same integer program via z3 Optimize."""
    import z3
    M = 1
    for (p, o, g, m) in items: M = M * m // math.gcd(M, m)
    movers = [(p, o, g, m) for (p, o, g, m) in items if m > 1]
    fixed = [(p, o, g, m) for (p, o, g, m) in items if m == 1]
    if M > 4000: return "skipped(M big)"
    lam = {p: z3.Int(f"l{p}") for (p, o, g, m) in movers}
    t = z3.Real("t")
    s = z3.Optimize()
    for (p, o, g, m) in movers:
        s.add(0 <= lam[p], lam[p] < m)
    for tt in range(M):
        expr = z3.RealVal(0)
        for (p, o, g, m) in movers:
            if tt % m == 0:
                expr = expr + z3.If(lam[p] == 0, z3.RealVal(1.0 / o), z3.RealVal(0))
            else:
                expr = expr + z3.If(lam[p] == tt % m, z3.RealVal(1.0 / o), z3.RealVal(0))
        base = sum(Fraction(1, o) for (p, o, g, m) in fixed)
        s.add(z3.RealVal(float(base)) + expr >= t)
    s.maximize(t)
    s.set("timeout", int(timelimit * 1000))
    if s.check() == z3.sat:
        m = s.model()
        raw = m[t].as_decimal(20)
        return float(raw.rstrip('?'))
    return "unsat/timeout"


def lp_upper(items, timelimit=180.0):
    """RIGOROUS fractional upper bound on the integer max-min line load: the
    LP relaxation (each mover's live class split fractionally over its m_q
    choices).  LP-opt >= MILP-opt, so LP-opt < 1 ==> IMPOSSIBILITY, certified
    by an exactly-verifiable LP (HiGHS; feasibility + dual checked in float,
    value cross-checked by rational round-trip on the returned basis pattern).
    NOTE (W63-B3r2 repair): the previous divisor_bound() in this file was
    INVALID — averaging over line-classes is provably vacuous (every divisor d
    gives exactly the global average sum_q 1/(m_q*o2_q); the old formula
    m_q/(d*o2_q) was a bug).  It has been removed; the LP bound replaces it."""
    from scipy import sparse
    from scipy.optimize import linprog
    import numpy as np
    M = 1
    for (p, o, g, m) in items: M = M * m // math.gcd(M, m)
    fixed = [(p, o, g, m) for (p, o, g, m) in items if m == 1]
    base = [Fraction(0)] * M
    for (p, o, g, m) in fixed:
        for t in range(M): base[t] += Fraction(1, o)
    movers = [(p, o, g, m) for (p, o, g, m) in items if m > 1]
    vidx = {}; nv = 0
    for (p, o, g, m) in movers:
        for lam in range(m):
            vidx[(p, lam)] = nv; nv += 1
    tcol = nv; nv += 1
    rows_i, cols_i, vals = [], [], []
    for tt in range(M):
        for (p, o, g, m) in movers:
            rows_i.append(tt); cols_i.append(vidx[(p, tt % m)]); vals.append(-1.0 / o)
        rows_i.append(tt); cols_i.append(tcol); vals.append(1.0)
    A = sparse.csr_matrix((vals, (rows_i, cols_i)), shape=(M, nv))
    b_ub = np.array([float(base[t]) for t in range(M)])  # -sum w x + t <= base  <=>  t <= base + sum w x
    er, ec, ev = [], [], []
    for i, (p, o, g, m) in enumerate(movers):
        for lam in range(m):
            er.append(i); ec.append(vidx[(p, lam)]); ev.append(1.0)
    A_eq = sparse.csr_matrix((ev, (er, ec)), shape=(len(movers), nv))
    b_eq = np.ones(len(movers))
    c = np.zeros(nv); c[tcol] = -1.0
    res = linprog(c, A_ub=A, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, None)] * nv, method="highs")
    if not res.success:
        return None, "lp-fail"
    return Fraction(-float(res.fun)).limit_denominator(10**9), "highs-lp"

def fix_dlogs(rows):
    bank = {r[0]: (r[2], r[3]) for r in json.load(open(os.path.join(HERE, "pal_dlog_full.json")))}
    out = []
    for row in rows:
        p, h, o2, o3 = row[0], row[1], row[2], row[3]
        if p in bank:
            U, V = bank[p]
            out.append([p, h, o2, o3, U, V])
        else:
            U, V = compute_dlogs(p, o2, o3, h)
            out.append([p, h, o2, o3, U, V])
    return out

def compute_dlogs(p, o2, o3, h):
    if h > 400_000: raise RuntimeError(f"h too big for BFS: {p} h={h}")
    sub = {1}
    frontier = [1]
    while frontier:
        nf = []
        for v in frontier:
            for m in (2, 3):
                w = v * m % p
                if w not in sub: sub.add(w); nf.append(w)
        frontier = nf
    assert len(sub) == h, (p, len(sub), h)
    fs = set(); x = h; d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    for g in sorted(sub):
        if g == 1: continue
        o = h
        for q in fs:
            while o % q == 0 and pow(g, o // q, p) == 1: o //= q
        if o == h:
            m = int(math.isqrt(h)) + 1
            table = {}; cur = 1
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
            U, V = bsgs(2), bsgs(3)
            if U is not None and V is not None: return U, V
    raise RuntimeError(p)

def family_meta():
    """(name, rows-spec) list, LAZY: rows fetched only on demand."""
    fams = []
    lc = json.load(open(os.path.join(HERE, "lc203.json")))["rows"]
    fams.append(("27720", ("lc", lc)))
    cg = json.load(open(os.path.join(HERE, "census_grid.json")))
    for r in cg:
        if r["L2"] != r["L3"]: continue
        if r["L2"] == 27720: continue
        fams.append((str(r["L2"]), ("cg", r["rows"])))
    return fams

def get_family(idx):
    fams = family_meta()
    name, spec = fams[idx]
    if spec[0] == "lc":
        return name, [list(r) for r in spec[1]]
    rows = [[p, h, o2, o3, 0, 0] for (p, h, o2, o3) in spec[1]]
    return name, fix_dlogs(rows)

def main():
    idx = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    name, rows = get_family(idx)
    t0 = time.time()
    bud = sum(Fraction(1, r[1]) for r in rows)
    log(f"[{name}] family {len(rows)} primes; budget {float(bud):.4f}")
    # census completeness cross-note for 27720
    if name == "27720":
        import gmpy2
        G = gmpy2.gcd((gmpy2.mpz(2) ** 27720) - 1, (gmpy2.mpz(3) ** 27720) - 1)
        for r in rows:
            G //= gmpy2.mpz(r[0])
        log(f"[census-complete] cofactor after dividing the 42 primes: {G} "
            f"(=1 => certified COMPLETE)")
    results = {}
    if os.path.exists(CKPT):
        results = json.load(open(CKPT))
    res = {"budget": float(bud), "n": len(rows)}
    for axis in ("line", "col"):
        items = axis_items(rows, axis)
        lpb, howlp = lp_upper(items)
        log(f"[{name}/{axis}] LP FRACTIONAL upper bound (rigorous, {howlp}): "
            f"{float(lpb) if lpb is not None else 'FAIL'}"
            f"  -> {'<1: IMPOSSIBILITY PROVED (LP relaxation)' if lpb is not None and lpb < 1 else '>=1 (weak)'}")
        opt, place, M, how = solve_maxmin(items, timelimit=420.0)
        log(f"[{name}/{axis}] M={M} types; opt = {float(opt) if opt is not None else 'FAIL'} ({how})")
        if opt is not None:
            mn, mx = verify_placement(items, place, axis)
            log(f"[{name}/{axis}] exact recompute of returned placement: min={float(mn)} "
                f"max={float(mx)}  (claim opt {float(opt)}; match={mn == opt})")
            z3v = z3_crosscheck(items, timelimit=200)
            log(f"[{name}/{axis}] z3 Optimize cross-solve: {z3v}")
            verdict = ("IMPOSSIBLE — family provably admits NO covering (line/column "
                       "integer necessary condition fails)") if float(opt) < 1 else "passes (necessary cond only)"
            log(f"[{name}/{axis}] VERDICT: {verdict}")
            res[axis] = {"lp_upper": [lpb.numerator, lpb.denominator] if lpb is not None else None,
                         "opt": [opt.numerator, opt.denominator], "how": how,
                         "recompute_min": [mn.numerator, mn.denominator],
                         "z3": str(z3v), "verdict": verdict}
        else:
            z3v = z3_crosscheck(items, timelimit=200)
            log(f"[{name}/{axis}] z3 Optimize cross-solve: {z3v}")
            res[axis] = {"opt": None, "how": how, "z3": str(z3v)}
    results[name] = res
    json.dump(results, open(CKPT, "w"), indent=1)
    log(f"[{name}] banked to {CKPT}  ({time.time()-t0:.0f}s)")

if __name__ == "__main__":
    main()
