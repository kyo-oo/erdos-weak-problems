#!/usr/bin/env python3
"""engine289_round4.py — W63-D3 r4: THE PELL CASCADE CERT + THE TERMINAL WAR.

THE MACHINE (all identities exact; dual-method where stated):

  Split law: 1/d = f(m) + 1/D  ⟺  D*num = d*m*(m+1), num = m^2-(2d-1)m-d
  (f(m) = 1/m + 1/(m+1)). Universal edge: m = 2d always gives D = 2d(2d+1).

  THE PELL CASCADE (the r4 discovery): with (d_0, m_0) = (1, 2),
      d_{n+1} = 6*d_n - d_{n-1},   m_n = 2*d_n + m_{n-1},
  the split 1/d_n = f(m_n) + 1/d_{n+1} holds EXACTLY for every n >= 1
  (verified exactly here for n <= 12 + the sympy propagation check).
  Telescoped: for every k >= 1 the k pair-blocks [m_0,m_0+1]..[m_{k-1},m_{k-1}+1]
  are pairwise non-adjacent (length 2) and sum to exactly 1 - 1/d_k.

  THE TERMINAL WAR: a total-1 #289 family with k blocks exists iff SOME
  reachable leftover d has a "d-family": legal blocks summing to exactly 1/d.
  Shapes hunted here (for the reachable node set):
    (s1) 1/d = f(x) + f(y): x scan + perfect-square root test (gmpy2);
          global numpy scan (any d) for x,y <= 30000.
    (s2) 1/d = sigma(a, a+L-1): tight candidate range a in [Ld-L+1, Ld].
    (s3) 1/d = f(x)+f(y)+f(z): (x,y) scan + quadratic root test.
    (s4) 1/d = f(x) + sigma(W): x scan + window-for-r range test.
    (s5) 1/d = sigma(W1) + sigma(W2): W1 scan + window-for-r range test.

  Checkpoints -> engine289_round4_state.json after every stage (L75 law).
"""
import json, math, time, sys
from fractions import Fraction

T0 = time.time()
BUDGET = 480.0
STATE = {"cascade": [], "cascade_sympy": None, "nodes": [],
         "s1_global": [], "s1": [], "s2": [], "s3": [], "s4": [], "s5": [],
         "tree": {}, "notes": []}

def _load_state():
    """Merge previous checkpoints (the engine is re-run per chunk; never lose
    banked stages)."""
    import os
    path = __file__.replace(".py", "_state.json")
    if os.path.exists(path):
        try:
            prev = json.load(open(path))
            for k, v in prev.items():
                if isinstance(v, list) and isinstance(STATE.get(k), list):
                    STATE[k] = v
                elif isinstance(v, dict) and isinstance(STATE.get(k), dict):
                    STATE[k].update(v)
                elif v is not None:
                    STATE[k] = v
        except Exception as e:
            print("STATE LOAD WARN:", e, flush=True)

_load_state()

def elapsed():
    return time.time() - T0

def over():
    return elapsed() > BUDGET

def out(*xs):
    print(" ".join(str(x) for x in xs), flush=True)

def save():
    with open(__file__.replace(".py", "_state.json"), "w") as fh:
        json.dump(STATE, fh)

def f(n):
    return Fraction(2 * n + 1, n * (n + 1))

def sigma(a, b):
    s = Fraction(0)
    for i in range(a, b + 1):
        s += Fraction(1, i)
    return s

def check_family(blocks):
    """#289 shape + total 1, TWO methods (Fraction + integer product)."""
    assert blocks
    for (a, b) in blocks:
        assert 2 <= a and a + 1 <= b
    for i in range(len(blocks) - 1):
        assert blocks[i][1] + 2 <= blocks[i + 1][0]
    S = Fraction(0)
    D = 1
    for (a, b) in blocks:
        for n in range(a, b + 1):
            S += Fraction(1, n)
            D *= n
    assert S == 1, ("frac total", S)
    N = sum(D // n for (a, b) in blocks for n in range(a, b + 1))
    assert N == D, ("int total", N, D)
    return True

# ---------------------------------------------------------------------------
# S1 — THE PELL CASCADE CERTIFICATION
# ---------------------------------------------------------------------------

def cascade_sequences(N):
    d = [1, 6]
    m = [2, 14]
    for n in range(1, N):
        d.append(6 * d[-1] - d[-2])
        m.append(2 * d[-1] + m[-1])
    return d, m   # d[0]=1, d[1]=6, ...; m[0]=2 (block of d0=1), m[n] block of d_n

def stage_S1(N=13):
    out("=== S1 THE PELL CASCADE (recurrences d_{n+1}=6d_n-d_{n-1}, m_n=2d_n+m_{n-1}) ===")
    d, m = cascade_sequences(N)
    rows = []
    allok = True
    for n in range(1, N):
        lhs = Fraction(1, d[n])
        rhs = f(m[n]) + Fraction(1, d[n + 1])
        ok = (lhs == rhs)
        allok = allok and ok
        rows.append([d[n], m[n], d[n + 1], ok])
        out(f"  n={n}: 1/{d[n]} = f({m[n]}) + 1/{d[n+1]}   {'OK' if ok else 'FAIL'}")
    # telescoped family totals, dual-method (Fraction + integer cross-mult)
    for k in range(1, 8):
        blocks = [(m[i], m[i] + 1) for i in range(k)]
        tot = Fraction(0)
        D = 1
        for (a, b) in blocks:
            for n in range(a, b + 1):
                tot += Fraction(1, n)
                D *= n
        NN = sum(D // n for (a, b) in blocks for n in range(a, b + 1))
        target = Fraction(1) - Fraction(1, d[k])
        okF = (tot == target)
        okI = (NN * d[k] == (d[k] - 1) * D)
        # placement: pairwise non-adjacent, lengths 2
        okP = all(blocks[i][1] + 2 <= blocks[i + 1][0] for i in range(k - 1))
        out(f"  k={k}: blocks {[a for (a, b) in blocks]} total=1-1/{d[k]} "
            f"frac={okF} int={okI} place={okP}")
        allok = allok and okF and okI and okP
    STATE["cascade"] = rows
    STATE["cascade_sequences"] = {"d": d, "m": m}
    STATE["cascade_allok"] = allok
    out("S1 CASCADE CERT:", "ALL OK" if allok else "FAIL")
    save()

def stage_S1_sympy():
    """THE CLEAN SYMBOLIC LAWS of the cascade (all sympy-exact):
    (L1) PELL PRESERVATION (zero hypotheses): with d_{n+1} = 6*d_n - d_{n-1},
         d_{n+1}^2 - 6*d_n*d_{n+1} + d_n^2 = d_n^2 - 6*d_{n-1}*d_n + d_{n-1}^2.
         [So by induction from the base 6^2-6*1*6+1^2 = 1, the Pell relation
          P(d_n, d_{n+1}) := d_{n+1}^2 - 6 d_n d_{n+1} + d_n^2 = 1 holds for ALL n.]
    (L2) SPLIT-FROM-PELL: with s = d_{n+1} - d_n = 2*m_n + 1 (the m-definition),
         P(d_n, d_{n+1}) = 1  ⟺  s^2 = 4 d_n d_{n+1} + 1  ⟺  the cross-multiplied
         split identity (d_{n+1}-d_n) m (m+1) = d_n d_{n+1} (2m+1).
    (L3) The m-recurrence m_n = 2 d_n + m_{n-1} is equivalent to the d-recurrence
         given 2 m_{n-1} = d_n - d_{n-1} - 1 (the invariant)."""
    import sympy as sp
    dp, dn, m = sp.symbols("dp dn m", integer=True)
    dnext = 6 * dn - dp
    L1 = sp.expand(dnext**2 - 6 * dn * dnext + dn**2
                   - (dn**2 - 6 * dp * dn + dp**2))
    l1ok = (sp.simplify(L1) == 0)
    # L2: substitute dnext = s + dn, s = 2m+1 in the Pell form minus 1:
    s = sp.symbols("s", integer=True)
    dD = sp.symbols("dD", integer=True)  # d_n * d_{n+1}
    pell_minus_1 = (dn + s)**2 - 6 * dn * (dn + s) + dn**2 - 1
    # claim: pell_minus_1 = 4*(m*(m+1) - d_n*d_{n+1}) when s = 2m+1 (so
    # Pell=1 ⟺ m(m+1) = d_n*d_{n+1} ⟺ the split identity, both directions)
    split_core = m * (m + 1) - dn * (dn + 2 * m + 1)
    e1 = sp.expand(pell_minus_1.subs(s, 2 * m + 1) - 4 * split_core)
    l2ok = (sp.simplify(e1) == 0)
    out("S1-SYMPY L1 Pell-preservation (0 hyps):", l1ok,
        "| L2 split ⟺ Pell:", l2ok)
    STATE["cascade_sympy"] = {"L1_pell_preservation": l1ok,
                              "L2_split_iff_pell": l2ok}
    save()

# ---------------------------------------------------------------------------
# Terminal-shape solvers
# ---------------------------------------------------------------------------

def solve_pair_for_target(r):
    """All integer y with f(y) = r (r = P/Q > 0). Quadratic root test."""
    from gmpy2 import isqrt as gisqrt
    P, Q = r.numerator, r.denominator
    if P <= 0:
        return []
    D = P * P + 4 * Q * Q
    S = gisqrt(D)
    if S * S != D:
        return []
    num = 2 * Q - P + int(S)
    den = 2 * P
    if num % den:
        return []
    y = num // den
    return [y] if y >= 2 else []

def term_s1(d):
    """(s1): 1/d = f(x) + f(y), x < y, x in [2d+1, 4d+8] (the smaller block)."""
    from gmpy2 import isqrt as gisqrt
    res = []
    fd = Fraction(1, d)
    for x in range(2 * d + 1, 4 * d + 9):
        P = x * (x + 1) - d * (2 * x + 1)
        if P <= 0:
            continue
        Q = d * x * (x + 1)
        Dsq = P * P + 4 * Q * Q
        S = gisqrt(Dsq)
        if S * S != Dsq:
            continue
        num = 2 * Q - P + int(S)
        den = 2 * P
        if num % den:
            continue
        y = num // den
        if y >= x + 3 and f(x) + f(y) == fd:
            res.append((x, y))
    return res

def term_s2(d):
    """(s2): 1/d = sigma(a, a+L-1) for L >= 3 (L=2 impossible: 4d^2+1)."""
    res = []
    fd = Fraction(1, d)
    for L in range(3, 61):
        lo = L * d - L + 1
        for a in range(max(2, lo), L * d + 1):
            if sigma(a, a + L - 1) == fd:
                res.append((a, L))
    return res

def windows_for_target(r, L_hi=12):
    """All (a, L) with sigma(a, a+L-1) = r, 2 <= L <= L_hi (range test)."""
    res = []
    if r <= 0:
        return res
    P, Q = r.numerator, r.denominator
    for L in range(2, L_hi + 1):
        # a in [L*Q/P - L + 1, L*Q/P]
        hi_a = (L * Q) // P
        lo_a = hi_a - L + 1 - 1  # floor slack
        for a in range(max(2, lo_a), hi_a + 2):
            if a + L - 1 >= a + 1 and sigma(a, a + L - 1) == r:
                res.append((a, L))
    return res

def term_s4(d):
    """(s4): 1/d = f(x) + sigma(W): x in [2d, 12d], window-for-r test."""
    res = []
    fd = Fraction(1, d)
    for x in range(2 * d, 12 * d + 1):
        r = fd - f(x)
        if r <= 0:
            break
        for (a, L) in windows_for_target(r):
            if a >= x + 3:
                res.append((x, a, a + L - 1))
    return res

def term_s5(d):
    """(s5): 1/d = sigma(W1) + sigma(W2): W1 scan + window-for-r test."""
    res = []
    fd = Fraction(1, d)
    # W1 with sigma(W1) < 1/d: a >= L(d-1)+1; cap a <= 14d
    for L1 in range(2, 9):
        a1 = max(2, L1 * (d - 1) + 1)
        s = None
        for a in range(a1, 14 * d + 1):
            if s is None:
                s = sigma(a, a + L1 - 1)
            else:
                s = s - Fraction(1, a - 1) + Fraction(1, a + L1 - 1) if a > a1 else s
            if s >= fd:
                break
            r = fd - s
            for (a2, L2) in windows_for_target(r):
                if a2 >= a + L1 + 1:  # non-adjacent after W1
                    res.append(((a, a + L1 - 1), (a2, a2 + L2 - 1)))
            if over():
                return res, True
    return res, False

def term_s3(d):
    """(s3): 1/d = f(x)+f(y)+f(z): (x,y) scan + quadratic root test."""
    from gmpy2 import isqrt as gisqrt
    res = []
    fd = Fraction(1, d)
    lo = 2 * d + 1
    hi = 6 * d + 1
    for x in range(lo, hi):
        fx = f(x)
        if fx >= fd:
            continue
        for y in range(x + 3, hi):
            r = fd - fx - f(y)
            if r <= 0:
                break
            P, Q = r.numerator, r.denominator
            Dsq = P * P + 4 * Q * Q
            S = gisqrt(Dsq)
            if S * S != Dsq:
                continue
            num = 2 * Q - P + int(S)
            den = 2 * P
            if num % den:
                continue
            z = num // den
            if z >= y + 3 and fx + f(y) + f(z) == fd:
                res.append((x, y, z))
    return res

# ---------------------------------------------------------------------------
# S2 — global (s1) scan (any d): f(x)+f(y) = 1/d, x<y<=M (numpy int64)
# ---------------------------------------------------------------------------

def stage_S2(M=30000):
    out("=== S2 GLOBAL (s1): all x<y<=", M, "with numerator(f(x)+f(y))==1 ===")
    import numpy as np
    hits = []
    x = 2
    while x <= M:
        y = np.arange(x + 1, M + 1, dtype=np.int64)
        xi = np.int64(x)
        N = (xi + y + 1) * (2 * xi * y + xi + y)
        D = xi * (xi + 1) * y * (y + 1)
        mask = (D % N) == 0
        if mask.any():
            ys = y[mask]
            Ns = N[mask]
            Ds = D[mask]
            for yy, nn, dd in zip(ys.tolist(), Ns.tolist(), Ds.tolist()):
                hits.append((x, yy, dd // nn))
        x += 1
        if x % 5000 == 0:
            out(f"  S2 progress x={x} hits={len(hits)} [{elapsed():.0f}s]")
            STATE["s1_global"] = hits
            save()
        if over():
            STATE["s1_global"] = hits
            save()
            out("S2 BUDGET STOP at x =", x)
            return
    STATE["s1_global"] = hits
    out("S2 DONE: ", len(hits), "hits (x,y,d):", hits[:20], f"[{elapsed():.0f}s]")
    save()

# ---------------------------------------------------------------------------
# S3 — the reachable node set + targeted terminal hunts
# ---------------------------------------------------------------------------

def m_split_edges(d, m_hi):
    """All (m, D): 1/d = f(m) + 1/D, m in [2d, m_hi]."""
    res = []
    for m in range(2 * d, m_hi + 1):
        num = m * m - (2 * d - 1) * m - d
        if num <= 0:
            continue
        t = d * m * (m + 1)
        if t % num:
            continue
        res.append((m, t // num))
    return res

def node_set():
    """The reachable leftover set (tree from 1): Pell chain, universal chain,
    20-chain, 156-branch, 4970-branch + entry nodes."""
    d, m = cascade_sequences(13)
    nodes = []
    nodes.append(("pell", 1))     # entry root
    for i in range(1, 13):
        nodes.append((f"pell_d{i}", d[i]))
    # universal chain from 6: 6 -> 156 -> 97656 ( -> too big )
    u = 6
    for i in range(3):
        nodes.append((f"univ_{i}", u))
        u = 2 * u * (2 * u + 1)
    # 20-chain (entry sigma(3,6) = 19/20)
    nodes.append(("w20", 20))
    dd = [2, 20, 198, 1960, 19402, 192020]  # hypothesized 10d - d_prev chain
    for i, v in enumerate(dd[1:]):
        nodes.append((f"w20_{i}", v))
    # 156-branch (26-chain?) and 4970-branch
    for v in [156, 4050]:
        nodes.append(("br156", v))
    nodes.append(("br4970", 4970))
    nodes.append(("br4970b", 705705))
    nodes.append(("br820", 820))
    # dedupe
    seen = set()
    res = []
    for name, v in nodes:
        if v not in seen:
            seen.add(v)
            res.append((name, v))
    return res

def stage_S3():
    out("=== S3 TARGETED TERMINAL WAR (reachable nodes) ===")
    nodes = node_set()
    STATE["s1"] = []
    out("nodes:", nodes)
    STATE["nodes"] = nodes
    save()
    for name, d in nodes:
        if over():
            out("S3 BUDGET STOP")
            return
        t = time.time()
        r1 = term_s1(d)
        if r1:
            out(f"  !!! (s1) TERMINAL FOUND at d={d} ({name}):", r1)
        STATE["s1"].append([name, d, r1])
        save()
        out(f"  (s1) d={d} [{name}]: {len(r1)} hits [{time.time()-t:.1f}s, tot {elapsed():.0f}s]")
    out("S3 (s1) DONE")

def stage_S4():
    out("=== S4 (s2) window terminals (all nodes) ===")
    STATE["s2"] = []
    for name, d in STATE.get("nodes", node_set()):
        if over():
            return
        t = time.time()
        r = term_s2(d)
        if r:
            out(f"  !!! (s2) TERMINAL FOUND at d={d} ({name}):", r)
        STATE["s2"].append([name, d, r])
        save()
        out(f"  (s2) d={d}: {len(r)} hits [{time.time()-t:.1f}s]")

def stage_S5():
    out("=== S5 (s3) triple terminals (small nodes) ===")
    STATE["s3"] = []
    small = [(n, d) for (n, d) in STATE.get("nodes", node_set()) if d <= 2200]
    for name, d in small:
        if over():
            return
        t = time.time()
        r = term_s3(d)
        if r:
            out(f"  !!! (s3) TERMINAL FOUND at d={d} ({name}):", r)
        STATE["s3"].append([name, d, r])
        save()
        out(f"  (s3) d={d} [{name}]: {len(r)} hits [{time.time()-t:.1f}s, tot {elapsed():.0f}s]")

def stage_S6():
    out("=== S6 (s4)+(s5) mixed/two-window terminals (small nodes) ===")
    STATE["s4"] = []
    STATE["s5"] = []
    small = [(n, d) for (n, d) in STATE.get("nodes", node_set()) if d <= 600]
    for name, d in small:
        if over():
            return
        t = time.time()
        r4 = term_s4(d)
        if r4:
            out(f"  !!! (s4) TERMINAL FOUND at d={d} ({name}):", r4)
        STATE["s4"].append([name, d, r4])
        save()
        out(f"  (s4) d={d}: {len(r4)} hits [{time.time()-t:.1f}s]")
        t = time.time()
        r5, stopped = term_s5(d)
        if r5:
            out(f"  !!! (s5) TERMINAL FOUND at d={d} ({name}):", r5)
        STATE["s5"].append([name, d, r5])
        save()
        out(f"  (s5) d={d}: {len(r5)} hits [{time.time()-t:.1f}s, tot {elapsed():.0f}s]")

# ---------------------------------------------------------------------------
# S7 — tree growth: window-split edges (1/d = sigma(a,b) + 1/d')
# ---------------------------------------------------------------------------

def stage_S7():
    out("=== S7 WINDOW-SPLIT TREE EDGES (nodes d <= 30000) ===")
    from fractions import Fraction as Fr
    for name, d in STATE.get("nodes", node_set()):
        if d > 30000 or over():
            continue
        t = time.time()
        edges = []
        fd = Fr(1, d)
        for L in range(2, 13):
            a1 = max(2, L * (d - 1) + 1)
            for a in range(a1, 14 * d + 1):
                s = sigma(a, a + L - 1)
                if s >= fd:
                    break
                P, Q = s.numerator, s.denominator
                numr = Q - d * P
                if numr > 0 and (d * Q) % numr == 0:
                    d2 = d * Q // numr
                    edges.append(((a, a + L - 1), d2))
                if over():
                    STATE["tree"][name + "_" + str(d)] = edges
                    save()
                    return
        STATE["tree"][name + "_" + str(d)] = edges
        save()
        out(f"  d={d} [{name}]: {len(edges)} window-split edges [{time.time()-t:.1f}s]")

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    out("=== engine289_round4.py —", which, "===")
    if which in ("all", "S1"):
        stage_S1()
        stage_S1_sympy()
    if which in ("all", "S2"):
        stage_S2()
    if which in ("all", "S3"):
        stage_S3()
    if which in ("all", "S4"):
        stage_S4()
    if which in ("all", "S5"):
        stage_S5()
    if which in ("all", "S6"):
        stage_S6()
    if which in ("all", "S7"):
        stage_S7()
    save()
    out("CHUNK COMPLETE elapsed", f"{elapsed():.0f}s")
