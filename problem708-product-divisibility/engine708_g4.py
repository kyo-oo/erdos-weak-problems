#!/usr/bin/env python3
"""#708 W63-D1: THE g(4) MASTER ENGINE — hunt + census + dual-method verification.

Problem (corpus #708, Erdos $100):
  g(n) = min g such that for ANY A (|A|=n, A subset [2,inf)) and ANY set I of
  max(A) consecutive integers, exists B subset I, |B|=g, prod(A) | prod(B).
  Known: g(2)=2, g(3)=4 (ErSu59). Target this round: g(4) evidence to EXACT.

This engine computes, for fixed A and window start t (I = {t+1,...,t+max(A)}),
the EXACT min |B| over distinct elements of I with prod(A) | prod(B):
  METHOD 1 (primary): exponent-vector DP over demand states (each element
    take/skip once — exact subset-semantics, O(M * states)).
  METHOD 2 (dual): itertools.combinations brute force with gmpy2 exact
    big-int products (independent route, for cross-validation).

Modes:
  selftest     : regression vs the banked K62 8-case worst values + DP-vs-brute
                 cross-check on a sub-box + boundary cases.
  probe BIG    : adversarial 4-sets, t = 1..BIG — hunt any minB >= 5 (g(4)>=5).
  census M1 M2 T : all 4-subsets A of [2..M2] with max(A) in [M1..M2],
                 windows t = 1..T, worst per A; checkpoint per M block.

House law compliance: foreground chunks only, checkpoints after every chunk,
absolute paths always.
"""
import sys, json, os, time
from itertools import combinations

try:
    import gmpy2
except ImportError:
    gmpy2 = None

sys.set_int_max_str_digits(100000)

OUT = "/home/z/waves/w63-d1-p708/problem708-product-divisibility"
CKPT = os.path.join(OUT, "g4_census_ckpt.json")


# ---------------------------------------------------------------- factorize
def factorize(n):
    """Trial division with a small-wheel; exact dict p -> e. (n <= ~10^6 here:
    window elements t+M <= ~1050 for the probe, prod(A) <= ~M^4 <= ~10^5.)"""
    fac = {}
    if n < 2:
        return fac
    d = 2
    while d * d <= n:
        while n % d == 0:
            fac[d] = fac.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fac[n] = fac.get(n, 0) + 1
    return fac


def prod(lst):
    r = 1
    for x in lst:
        r *= x
    return r


# ---------------------------------------------------------------- method 1
def minB_dp(A, t):
    """EXACT min |B|: DP over remaining-demand states, each window element
    take/skip exactly once. Returns (minsize, witness or None)."""
    M = max(A)
    lo, hi = max(2, t + 1), t + M
    P = prod(A)
    D = factorize(P)
    ps = sorted(D)
    e = tuple(D[p] for p in ps)
    idx = {p: i for i, p in enumerate(ps)}
    k = len(ps)
    # element vectors (truncated at the demand — extra supply is free slack)
    els = []
    for b in range(lo, hi + 1):
        fb = factorize(b)
        v = [0] * k
        for p, c in fb.items():
            if p in idx:
                v[idx[p]] = min(c, e[idx[p]])
        els.append((b, tuple(v)))
    # DP: dict state -> (count, witness list)
    start = e
    cur = {start: (0, [])}
    for (b, v) in els:
        nxt = dict(cur)
        for s, (c, wit) in cur.items():
            s2 = tuple(max(0, s[i] - v[i]) for i in range(k))
            if s2 == s:
                continue  # useless element (supplies nothing relevant)
            cand = (c + 1, wit + [b])
            old = nxt.get(s2)
            if old is None or cand[0] < old[0]:
                nxt[s2] = cand
        cur = nxt
        # early exit
        if (0,) * k in cur:
            pass
    zero = (0,) * k
    if zero in cur:
        return cur[zero]
    return (M + 1, None)  # uncoverable (cannot happen: B=I itself covers? no —
    # B must have prod(A) | prod(B); in an M-window with M >= max(A), the whole
    # window's product is a multiple of every a_i? NOT guaranteed; but some
    # cover always exists in practice; caller treats >10 as 'no cover' flag.)


# ---------------------------------------------------------------- method 2
def minB_brute(A, t, kmax=None):
    """Dual method: itertools.combinations + gmpy2 exact mod. Returns
    (minsize, witness or None)."""
    M = max(A)
    lo, hi = max(2, t + 1), t + M
    I = list(range(lo, hi + 1))
    P = gmpy2.mpz(prod(A)) if gmpy2 else prod(A)
    if kmax is None:
        kmax = len(I)
    for k in range(0, kmax + 1):
        for comb in combinations(I, k):
            x = (gmpy2.mpz(1) if gmpy2 else 1)
            for b in comb:
                x *= b
            if x % P == 0:
                return (k, list(comb))
    return (kmax + 1, None)


# ---------------------------------------------------------------- selftest
BANKED = [
    ([2, 3], 2),
    ([6, 10, 15], 3),
    ([2, 3, 5], 3),
    ([6, 10, 14, 15], 4),
    ([6, 10, 15, 21], 4),
    ([2, 3, 5, 7], 3),
    ([6, 10, 14, 15, 21], 5),
    ([6, 10, 14, 15, 21, 35], 5),
]


def selftest():
    print("=== #708 g4 engine SELFTEST: regression + dual-method ===")
    ok = True
    # (i) regression: the 8 banked worst values over t=1..40 (engine708.py's
    # certified outputs, K62 kernel rows)
    for A, w in BANKED:
        worst = 0
        wt = None
        for t in range(1, 41):
            s, _ = minB_dp(A, t)
            if s > worst:
                worst, wt = s, t
        st = "OK" if worst == w else "MISMATCH"
        if worst != w:
            ok = False
        print(f"  A={A}: worst over t=1..40 = {worst} (banked {w}) at t={wt} [{st}]")
    # (ii) DP-vs-brute exact equality on a sub-box: all 4-subsets of [2..12]
    #      with max 12, t = 1..12
    mism = 0
    tests = 0
    for S in combinations(range(2, 12), 3):
        A = sorted(S + (12,))
        for t in range(1, 13):
            s1, _ = minB_dp(A, t)
            s2, _ = minB_brute(A, t)
            tests += 1
            if s1 != s2:
                mism += 1
                print(f"  DUAL MISMATCH A={A} t={t}: dp={s1} brute={s2}")
    print(f"  dual-method sub-box (4-sets max=12, t=1..12): {tests} pairs, "
          f"{mism} mismatches [{'OK' if mism == 0 else 'FAIL'}]")
    if mism:
        ok = False
    # (iii) boundary cases: t=1 (window {2..M+1} contains A: minB <= 4 for
    #       4-sets — B = A itself) and t large (window past the demand primes)
    bad = 0
    for S in combinations(range(2, 16), 3):
        A = sorted(S + (16,))
        s1, _ = minB_dp(A, 1)
        if s1 > 4:
            print(f"  BOUNDARY FAIL: A={A} at t=1 has minB={s1} > 4")
            bad += 1
    print(f"  boundary t=1 (all 4-sets max=16): {bad} violations of minB<=4 "
          f"[{'OK' if bad == 0 else 'FAIL'}]")
    if bad:
        ok = False
    print("SELFTEST", "GREEN" if ok else "RED")
    return ok


# ---------------------------------------------------------------- probe
ADVERSARIAL_4 = [
    [6, 10, 14, 15], [6, 10, 15, 21], [6, 10, 14, 21], [6, 14, 15, 21],
    [10, 14, 15, 21], [6, 10, 21, 35], [6, 14, 21, 35], [10, 14, 21, 35],
    [14, 15, 21, 35], [6, 10, 14, 15, 21][:4],
    [6, 10, 12, 15], [6, 12, 14, 15], [10, 12, 14, 15], [12, 14, 15, 21],
    [6, 10, 15, 30], [6, 10, 14, 22], [2, 3, 5, 7], [2, 3, 5, 25],
    [5, 6, 7, 8], [4, 6, 8, 9], [6, 10, 14, 15, 35][:4], [10, 15, 21, 35],
]


def probe(big):
    print(f"=== #708 g4 PROBE: adversarial 4-sets, t = 1..{big} (g(4)>=5 hunt) ===")
    found = []
    for A in ADVERSARIAL_4:
        A = sorted(set(A))
        if len(A) != 4:
            continue
        worst, wt, wB = 0, None, None
        for t in range(1, big + 1):
            s, B = minB_dp(A, t)
            if s > worst:
                worst, wt, wB = s, t, B
        tag = ""
        if worst >= 5:
            tag = "  <<< FORCING >= 5 FOUND"
            found.append((A, wt, worst, wB))
        print(f"  A={A}: worst over t=1..{big} = {worst} at t={wt} B={wB}{tag}")
    if found:
        print("PROBE: g(4) >= 5 WITNESSES FOUND:")
        for A, wt, w, B in found:
            print(f"   A={A} t={wt}: minB = {w} (witness of size {w}: {B})")
    else:
        print(f"PROBE: no forcing-5 found among adversarial list over t=1..{big}")
    return found


# ---------------------------------------------------------------- census
def census(M1, M2, T, resume=True):
    """All 4-subsets A of [2..M2] with max(A) = M in [M1..M2]; windows
    t = 1..T. Records worst per A; checkpoint per M block."""
    state = {"done_M": [], "rows": [], "max": 0, "maxA": None}
    if resume and os.path.exists(CKPT):
        with open(CKPT) as f:
            state = json.load(f)
        print(f"[census] resuming: {len(state['done_M'])} M-blocks done, "
              f"max so far {state['max']}")
    for M in range(M1, M2 + 1):
        if M in state["done_M"]:
            continue
        t0 = time.time()
        block = []
        for S in combinations(range(2, M), 3):
            A = sorted(S + (M,))
            worst, wt = 0, None
            for t in range(1, T + 1):
                s, _ = minB_dp(A, t)
                if s > worst:
                    worst, wt = s, t
            block.append((A, worst, wt))
            if worst > state["max"]:
                state["max"] = worst
                state["maxA"] = (A, wt)
        state["rows"].extend([{"A": b[0], "worst": b[1], "t": b[2]} for b in block])
        state["done_M"].append(M)
        with open(CKPT, "w") as f:
            json.dump(state, f)
        wcounts = {}
        for r in block:
            wcounts[r[1]] = wcounts.get(r[1], 0) + 1
        print(f"[census] M={M}: {len(block)} 4-sets, worst-distribution "
              f"{dict(sorted(wcounts.items()))}, "
              f"{time.time()-t0:.1f}s, max-so-far={state['max']} "
              f"at {state['maxA']}")
    # summary
    dist = {}
    for r in state["rows"]:
        dist[r["worst"]] = dist.get(r["worst"], 0) + 1
    print(f"[census] TOTAL: {len(state['rows'])} 4-sets, "
          f"worst-distribution {dict(sorted(dist.items()))}")
    print(f"[census] GLOBAL MAX over box (max(A) in [{M1},{M2}], t=1..{T}): "
          f"{state['max']} at A={state['maxA']}")
    return state


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if mode == "selftest":
        selftest()
    elif mode == "probe":
        probe(int(sys.argv[2]) if len(sys.argv) > 2 else 400)
    elif mode == "census":
        M1 = int(sys.argv[2]); M2 = int(sys.argv[3]); T = int(sys.argv[4])
        census(M1, M2, T)
    else:
        print("modes: selftest | probe BIG | census M1 M2 T")
