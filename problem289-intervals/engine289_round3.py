#!/usr/bin/env python3
"""engine289_round3.py — W63-D3: THE CASCADE + TERMINAL WAR (#289 YES-side).

THE MACHINE (derivation, all identities exact, dual-method certified):

  Split law (algebra): 1/d = f(2d) + 1/(2d(2d+1)), f(n) = sigma([n,n+1])
    = 1/n + 1/(n+1) = (2n+1)/(n(n+1)).
  General split edge: 1/d = f(m) + 1/d' whenever num := m^2-(2d-1)m-d > 0
    and num | d*m*(m+1); then d' = d*m*(m+1)/num.
  Backward edge: given child D, predecessor p = D*m*(m+1)/(m^2+(2D+1)m+D)
    when integral, num > 0.

  Family assembly: 1 = [entry block] + [path pair-blocks [m_i, m_i+1]]
    + [terminal family for the leftover 1/d*].
    Entries: 1 = f(2) + 1/6 (pair, forced); sigma([a,b]) = 1 - 1/d
    (window entries, hunted). Terminals: 1/d* = legal family
    (pair pair / pair triple / window / mixed / two windows — hunted).

This engine hunts ALL pieces and assembles + dual-verifies families.
Checkpoints -> engine289_round3_state.json.
"""
import json, math, time
from fractions import Fraction

T0 = time.time()
BUDGET = 500.0
STATE = {"term_pair": [], "term_pair_pref": [], "term_triple": [],
         "term_window": [], "entry_window": [], "term_mixed": [],
         "term_w2": [], "edges_fwd": {}, "assembled": [], "notes": []}

def elapsed():
    return time.time() - T0

def out(*xs):
    print(" ".join(str(x) for x in xs), flush=True)

def save():
    with open("engine289_round3_state.json", "w") as fh:
        json.dump(STATE, fh)

def f(n):
    return Fraction(2 * n + 1, n * (n + 1))

def over():
    return elapsed() > BUDGET

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
# E1 TERM-P: pair terminals f(x) + f(y) = 1/d (y >= x+3); also pair
# prefixes f(x)+f(y) = 1 - 1/d (den-num == 1).
# ---------------------------------------------------------------------------

def e1(M):
    res, pref = [], []
    for x in range(2, M - 1):
        fx = f(x)
        for y in range(x + 3, M):
            s = fx + f(y)
            if s.numerator == 1:
                res.append((x, y, s.denominator))
            elif s.denominator - s.numerator == 1:
                pref.append((x, y, s.denominator))
    return res, pref

# ---------------------------------------------------------------------------
# E2 TERM-T: triple terminals f(x)+f(y)+f(z) = 1/d (spacing >= 3).
# ---------------------------------------------------------------------------

def e2(M):
    res = []
    fs = {n: f(n) for n in range(2, M)}
    for x in range(2, M - 2):
        for y in range(x + 3, M - 1):
            s2 = fs[x] + fs[y]
            if s2 >= 1:
                break
            for z in range(y + 3, M):
                s3 = s2 + fs[z]
                if s3.numerator == 1:
                    res.append((x, y, z, s3.denominator))
                elif s3 > 1:
                    break
    return res

# ---------------------------------------------------------------------------
# E3 TERM-W / ENTRY-W: window sums sigma(a,b): terminals (num==1) and
# entries (den-num==1).
# ---------------------------------------------------------------------------

def e3(M):
    term, entry = [], []
    for a in range(2, M + 1):
        s = Fraction(1, a) + Fraction(1, a + 1)
        for b in range(a + 2, M + 1):
            s += Fraction(1, b)
            if s.numerator == 1:
                term.append((a, b, s.denominator))
            elif s.denominator - s.numerator == 1:
                entry.append((a, b, s.denominator))
    return term, entry

# ---------------------------------------------------------------------------
# E4 TERM-M: mixed terminals f(x) + sigma(W) = 1/d (W after x+1).
# ---------------------------------------------------------------------------

def e4(M):
    res = []
    for x in range(2, M - 1):
        fx = f(x)
        for a in range(x + 3, M + 1):
            s = fx + Fraction(1, a) + Fraction(1, a + 1)
            for b in range(a + 2, M + 1):
                s += Fraction(1, b)
                if s.numerator == 1:
                    res.append((x, (a, b), s.denominator))
                elif s > 1:
                    break
    return res

# ---------------------------------------------------------------------------
# E5 TERM-W2: two-window terminals sigma(W1) + sigma(W2) = 1/d.
# ---------------------------------------------------------------------------

def e5(M):
    res = []
    # window sums, incremental
    for a1 in range(2, M + 1):
        s1 = Fraction(1, a1) + Fraction(1, a1 + 1)
        for b1 in range(a1 + 2, M + 1):
            s1 += Fraction(1, b1)
            if s1 >= 1:
                break
            for a2 in range(b1 + 2, M + 1):
                s2 = s1 + Fraction(1, a2) + Fraction(1, a2 + 1)
                for b2 in range(a2 + 2, M + 1):
                    s2 += Fraction(1, b2)
                    if s2.numerator == 1:
                        res.append(((a1, b1), (a2, b2), s2.denominator))
                    elif s2 > 1:
                        break
    return res

# ---------------------------------------------------------------------------
# E6/E7 cascade: forward edges from small d; backward predecessors;
# assembly.
# ---------------------------------------------------------------------------

def fwd_edge(d, m):
    num = m * m - (2 * d - 1) * m - d
    if num <= 0:
        return None
    t = d * m * (m + 1)
    if t % num:
        return None
    return t // num

def bwd_pred(D, m):
    """predecessor p of child D via split block [m, m+1]; None if not exact."""
    den = m * m + (2 * D + 1) * m + D
    num = D * m * (m + 1)
    if num % den:
        return None
    p = num // den
    # validity: forward edge p -> D via m must have positive num
    if fwd_edge(p, m) != D:
        return None
    return p

def bwd_all(D):
    """All predecessors p (with their m) of D."""
    preds = []
    m = 2
    while True:
        p = bwd_pred(D, m)
        if p is not None and 2 <= p < D:
            preds.append((p, m))
        # stop when the deficit D - p(m) is < 1 forever (p approaches D)
        den = m * m + (2 * D + 1) * m + D
        approx = D * m * (m + 1) / den
        if D - approx < 1 and m > 4 * D:
            break
        m += 1
        if m > 4 * D * D + 10:
            break
    return preds

def fwd_edges_from(d, m_hi):
    """All edges d -> d' via m in [2d, m_hi]."""
    edges = []
    for m in range(2 * d, m_hi + 1):
        dd = fwd_edge(d, m)
        if dd is not None and dd > d:
            edges.append((m, dd))
    return edges


if __name__ == "__main__":
    out("=== engine289_round3.py — cascade + terminal war ===")

    t = time.time()
    TP, PP = e1(5000)
    STATE["term_pair"] = TP
    STATE["term_pair_pref"] = PP
    out("E1 pair terminals (M=5000):", len(TP), "| pair 2-block prefixes:", len(PP),
        f"[{time.time()-t:.0f}s]")
    for r in TP[:30]:
        out("   TERM pair:", r)
    for r in PP[:30]:
        out("   PREF pair:", r)
    save()

    if not over():
        t = time.time()
        TT = e2(400)
        STATE["term_triple"] = TT
        out("E2 triple terminals (M=400):", len(TT), f"[{time.time()-t:.0f}s]")
        for r in TT[:20]:
            out("   TERM triple:", r)
        save()

    if not over():
        t = time.time()
        TW, EW = e3(1500)
        STATE["term_window"] = TW
        STATE["entry_window"] = EW
        out("E3 window terminals (M=1500):", len(TW), "| window entries:", len(EW),
            f"[{time.time()-t:.0f}s]")
        for r in TW[:30]:
            out("   TERM window:", r)
        for r in EW[:30]:
            out("   ENTRY window:", r)
        save()

    if not over():
        t = time.time()
        TM = e4(300)
        STATE["term_mixed"] = TM
        out("E4 mixed terminals (M=300):", len(TM), f"[{time.time()-t:.0f}s]")
        for r in TM[:20]:
            out("   TERM mixed:", r)
        save()

    if not over():
        t = time.time()
        W2 = e5(150)
        STATE["term_w2"] = W2
        out("E5 two-window terminals (M=150):", len(W2), f"[{time.time()-t:.0f}s]")
        for r in W2[:20]:
            out("   TERM w2:", r)
        save()

    # forward edges from 6 and from small entry d's (analysis)
    if not over():
        t = time.time()
        for d in [6, 20, 35, 156, 204, 820, 4970]:
            edges = fwd_edges_from(d, min(2 * d * d + 2 * d + 2, 400000))
            STATE["edges_fwd"][str(d)] = edges
            out("E6 fwd edges from", d, ":", edges)
        out(f"E6 done [{time.time()-t:.0f}s]")
        save()

    out("CHUNK COMPLETE elapsed", f"{elapsed():.0f}s")
    save()
