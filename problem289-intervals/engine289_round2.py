#!/usr/bin/env python3
"""engine289_round2.py — W63-D3: THE LARGE-k CONSTRUCTION WAR (#289).

Round-2 engine (the YES-side hunt): total-1 k-interval Egyptian families
(Erdos #289: intervals I_1..I_k disjoint, NON-ADJACENT, |I_i| >= 2,
sum_i sum_{n in I_i} 1/n = 1) + the RE-HOMING/SPLITTING census
(the k -> k+1 pump primitives).

Models hunted:
  (P) pair-block family: blocks [n_i, n_i+1] (length exactly 2), n_1 >= 2,
      n_{i+1} >= n_i + 3 (non-adjacency), sum_i f(n_i) = 1, f(n)=1/n+1/(n+1).
  (H) head+pair family: one general window [a,b] (a >= 2, b >= a+1) +
      j pair-blocks after it (non-adjacent), total 1.

Methods: exact Fraction arithmetic; meet-in-the-middle hashing on exact sums
(the full model (P)/(H) census at the given M — exhaustive over the model);
EVERY reported family re-verified by a SECOND method: integer cross-
multiplication over the product of ALL denominators in the union.

Re-homing census (Engine A): f(n) = f(x) + f(y) — the pair-block split law
(a pair-block re-homed as two pair-blocks): for fixed (n, x), r = f(n)-f(x)
must satisfy the quadratic r*y^2+(r-2)*y-1 = 0; integer root iff
P^2 + 4*Q^2 = S^2 (P=r reduced numerator, Q denominator) and
(2Q - P + S) divisible by 2P. Exhaustive over n, x <= M.

Stage checkpoints -> engine289_round2_state.json after every stage.
"""
import json, math, sys, time
from fractions import Fraction

T0 = time.time()
BUDGET = 480.0  # seconds per chunk (L75 reaper law)
STATE = {"stages": {}, "families": {}, "rehome": []}


def elapsed():
    return time.time() - T0


def f(n):
    return Fraction(2 * n + 1, n * (n + 1))


def window_sum(a, b):
    s = Fraction(0)
    for i in range(a, b + 1):
        s += Fraction(1, i)
    return s


def check_family(blocks):
    """Full #289 shape + total 1; verified by TWO methods.
    blocks: list of (a, b), sorted by a."""
    assert blocks, "empty family"
    for (a, b) in blocks:
        assert 2 <= a and a + 1 <= b, ("length", (a, b))
    for i in range(len(blocks) - 1):
        assert blocks[i][1] + 2 <= blocks[i + 1][0], ("adjacency", blocks[i], blocks[i + 1])
    # method 1: exact Fractions
    S = Fraction(0)
    for (a, b) in blocks:
        for n in range(a, b + 1):
            S += Fraction(1, n)
    assert S == 1, ("fraction total", S)
    # method 2: integer cross-multiplication over the full denominator product
    D = 1
    for (a, b) in blocks:
        for n in range(a, b + 1):
            D *= n
    N = 0
    for (a, b) in blocks:
        for n in range(a, b + 1):
            N += D // n
    assert N == D, ("integer total", N, D)
    return True


def out(*xs):
    line = " ".join(str(x) for x in xs)
    print(line, flush=True)


def save():
    with open("engine289_round2_state.json", "w") as fh:
        json.dump(STATE, fh)


def over_budget():
    return elapsed() > BUDGET


# ---------------------------------------------------------------------------
# Layer construction: all j-tuples of pair-block starts, spacing >= 3,
# within [start_lo, M]; returns dict sum -> list of tuples (witnesses).
# ---------------------------------------------------------------------------

def build_layer(M, j, start_lo=2):
    """sum -> list of tuples (n_1 < n_2 < ... < n_j), n_{i+1} >= n_i + 3,
    n_1 >= start_lo, n_j + 1 <= M (block [n, n+1] inside [2, M])."""
    cur = {Fraction(0): [()]}
    for depth in range(1, j + 1):
        nxt = {}
        for s, tups in cur.items():
            for t in tups:
                lo = (t[-1] + 3) if t else start_lo
                for n in range(lo, M):  # need n+1 <= M
                    ns = s + f(n)
                    lst = nxt.get(ns)
                    if lst is None:
                        nxt[ns] = [t + (n,)]
                    else:
                        lst.append(t + (n,))
        cur = nxt
    return cur


def layer_size(layer):
    return sum(len(v) for v in layer.values())


def count_tuples(M, j, start_lo=2):
    """C(M - start_lo - 3*(j-1) + 1, j) roughly (spacing-3 sequences)."""
    top = M - 1  # largest allowed start (n+1 <= M)
    if top - start_lo - 3 * (j - 1) + 1 < j:
        return 0
    n = top - start_lo - 3 * (j - 1) + 1
    return math.comb(n, j)


# ---------------------------------------------------------------------------
# Hunt (P): pair-only families, MITM a + b.
# ---------------------------------------------------------------------------

def hunt_pairs(k, M, cap=12):
    """Find pair-block families with k blocks within [2, M], total 1.
    MITM: left a-tuples + right b-tuples, a = k//2 <= b."""
    a = k // 2
    b = k - a
    if count_tuples(M, a) == 0 or count_tuples(M, b) == 0:
        return []
    left = build_layer(M, a)
    right = build_layer(M, b)
    found = []
    for s, tups in left.items():
        comp = Fraction(1) - s
        cands = right.get(comp)
        if not cands:
            continue
        for t in tups:
            for u in cands:
                if not u:
                    continue
                if u[0] >= t[-1] + 3:
                    blocks = [(n, n + 1) for n in t + u]
                    found.append(blocks)
                    if len(found) >= cap:
                        return found
    return found


# ---------------------------------------------------------------------------
# Hunt (H): head window + j pair-blocks.
# ---------------------------------------------------------------------------

def hunt_head(j, M_head, M_pairs, cap=12):
    """Find families: head window [a, b] within [2, M_head] + j pair-blocks
    within [2, M_pairs] after the head, total 1."""
    layer = build_layer(M_pairs, j) if j >= 1 else {Fraction(0): [()]}
    found = []
    for a in range(2, M_head + 1):
        for b in range(a + 1, M_head + 1):
            comp = Fraction(1) - window_sum(a, b)
            if comp <= 0:
                break  # window sums grow in b; once past 1, stop
            cands = layer.get(comp)
            if not cands:
                continue
            for u in cands:
                if u and u[0] >= b + 2:
                    blocks = [(a, b)] + [(n, n + 1) for n in u]
                    found.append(blocks)
                    if len(found) >= cap:
                        return found
    return found


# ---------------------------------------------------------------------------
# Engine A: micro re-homing census f(n) = f(x) + f(y).
# ---------------------------------------------------------------------------

def rehome_census(M, cap=200):
    """All (n, x, y): f(n) = f(x) + f(y), x >= n+3, y >= x+3, n+1 <= M."""
    res = []
    fn = {}
    for n in range(2, M):
        fn[n] = Fraction(2 * n + 1, n * (n + 1))
    for n in range(2, M - 3):
        for x in range(n + 3, M - 3):
            r = fn[n] - fn[x]
            if r <= 0:
                break
            P, Q = r.numerator, r.denominator
            D = P * P + 4 * Q * Q
            S = math.isqrt(D)
            if S * S != D:
                continue
            num = 2 * Q - P + S
            den = 2 * P
            if num % den:
                continue
            y = num // den
            if y >= x + 3 and y + 1 <= M:
                res.append((n, x, y))
                if len(res) >= cap:
                    return res
    return res


# ---------------------------------------------------------------------------
# Engine B: window re-homing census sigma(W) = sigma(V) + sigma(Z)
# variants: (i) W pair-block, V any window, Z any window;
#          (ii) W any window, V pair-block, Z any window.
# ---------------------------------------------------------------------------

def window_table(M):
    """sum -> list of (a, b) windows with a >= 2, a+1 <= b <= M."""
    tab = {}
    for a in range(2, M + 1):
        s = Fraction(1, a)
        # length >= 2: start b at a+1
        s += Fraction(1, a + 1)
        for b in range(a + 1, M + 1):
            if b > a + 1:
                s += Fraction(1, b)
            tab.setdefault(s, []).append((a, b))
    return tab


def rehome_window_pairW(M, cap=100):
    """f(n) = sigma(V) + sigma(Z): W = pair-block [n, n+1]; V, Z windows."""
    tab = window_table(M)
    res = []
    for n in range(2, M - 1):
        T = f(n)
        for a in range(2, M + 1):
            s = Fraction(0)
            for b in range(a + 1, M + 1):
                s += Fraction(1, b)
                r = T - s
                if r <= 0:
                    break
                cands = tab.get(r)
                if not cands:
                    continue
                for (c, d) in cands:
                    if c >= b + 2:
                        res.append((n, (a, b), (c, d)))
                        if len(res) >= cap:
                            return res
    return res


def rehome_window_headW(M, cap=100):
    """sigma(W) = f(n) + sigma(Z): W any window; V = pair-block."""
    tab = window_table(M)
    res = []
    for a in range(2, M + 1):
        s = Fraction(1, a)
        for b in range(a + 1, M + 1):
            s += Fraction(1, b)
            T = s  # sigma(a, b)
            for n in range(2, M - 1):
                r = T - f(n)
                if r <= 0:
                    break
                cands = tab.get(r)
                if not cands:
                    continue
                for (c, d) in cands:
                    if c >= n + 3:  # Z after the pair-block, non-adjacent
                        res.append(((a, b), n, (c, d)))
                        if len(res) >= cap:
                            return res
    return res


# ---------------------------------------------------------------------------
# STAGES
# ---------------------------------------------------------------------------

def stage_P(name, k, M):
    if over_budget():
        out("STAGE", name, "SKIPPED (budget)")
        return
    t = time.time()
    res = hunt_pairs(k, M)
    ok = []
    for blocks in res:
        try:
            check_family(blocks)
            ok.append(blocks)
        except AssertionError as e:
            out("  VERIFY FAIL", blocks, e)
    STATE["families"][name] = ok
    out("STAGE", name, f"(k={k}, M={M}):", len(res), "raw,", len(ok),
        "verified", f"[{time.time()-t:.1f}s, tot {elapsed():.0f}s]")
    save()


def stage_H(name, j, Mh, Mp):
    if over_budget():
        out("STAGE", name, "SKIPPED (budget)")
        return
    t = time.time()
    res = hunt_head(j, Mh, Mp)
    ok = []
    for blocks in res:
        try:
            check_family(blocks)
            ok.append(blocks)
        except AssertionError as e:
            out("  VERIFY FAIL", blocks, e)
    STATE["families"][name] = ok
    out("STAGE", name, f"(head<= {Mh}, pairs<= {Mp}, k={j+1}):", len(res), "raw,",
        len(ok), "verified", f"[{time.time()-t:.1f}s, tot {elapsed():.0f}s]")
    save()


if __name__ == "__main__":
    out("=== engine289_round2.py — W63-D3 large-k construction war ===")
    out("models: (P) pair-blocks only; (H) head window + pair-blocks")

    # ---- chunk 1: pair-only hunts, k = 3..8, moderate M ----
    stage_P("P_k3_M2000", 3, 2000)
    stage_P("P_k4_M600", 4, 600)
    stage_P("P_k5_M200", 5, 200)
    stage_P("P_k6_M150", 6, 150)
    stage_P("P_k7_M90", 7, 90)
    stage_P("P_k8_M70", 8, 70)

    # ---- head+pair hunts ----
    if not over_budget():
        stage_H("H_k3_M240", 2, 240, 240)
        stage_H("H_k4_M200", 3, 200, 200)
        stage_H("H_k5_M80", 4, 80, 80)

    # ---- Engine A: micro re-homing census ----
    if not over_budget():
        t = time.time()
        res = rehome_census(2000)
        STATE["rehome"] = res
        out("STAGE A (f(n)=f(x)+f(y), M=2000):", len(res), "solutions",
            f"[{time.time()-t:.1f}s, tot {elapsed():.0f}s]")
        for r in res[:40]:
            out("   rehome:", r, "-> f-check:",
                f(r[0]) == f(r[1]) + f(r[2]))
        save()

    save()
    out("CHUNK COMPLETE. elapsed", f"{elapsed():.0f}s")
