#!/usr/bin/env python3
"""W66-P306-K THE CLOSER v2: the decomposition ladder + direct flips.

THE LADDER (the disjoint-window machinery, STATUS.md round-2 path):
  target t = HEAD (a certified rep h with prime footprint P_h) + RESIDUAL
  r = t - h hunted over the TAIL window (primes <= 67 not in P_h) by
  subset-sum with complement-flip. Disjoint prime windows => all
  denominators distinct across the stages (CRT-compose for distinctness).

Direct flips (the near-unit regime, t > 0.83): full-window subset-sum with
complement-flip + memoized DFS over windows up to 67.

Chunked + checkpointed to EVIDENCE_306_W66K.json after every target.
"""
import sys, os, time, json
sys.setrecursionlimit(300000)
from fractions import Fraction
from math import gcd
from sympy import primerange

T0 = time.time()
CHUNK = int(os.environ.get("CHUNK", "14"))
BUDGET = float(os.environ.get("BUDGET", "470"))

BOX = []
for b in [2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30]:
    for a in range(1, b):
        if gcd(a, b) == 1:
            BOX.append(Fraction(a, b))
BOX.sort()

REPS = {}
CKPT = "EVIDENCE_306_W66K.json"
with open(CKPT) as f:
    old = json.load(f)
for k, v in old["reps"].items():
    t = Fraction(k)
    if t in BOX:
        REPS[t] = v

# kernel r1 heads
KERNEL_R1 = {
    Fraction(1, 2): [6,10,15,21,26,35,39,65,91],
    Fraction(2, 3): [6,10,14,21,22,26,33,35,38,51,57,77,91,95,119,133,143,187,209,247,323],
    Fraction(3, 5): [6,10,14,15,22,26,34,35,51,77,119,143,187],
    Fraction(4, 5): [6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,69,77,85,115,143,299,323,391],
    Fraction(5, 6): [6,10,14,15,21,22,33,34,35,38,39,46,51,55,57,65,69,77,85,91,95,115,119,133,143,221,299,391],
    Fraction(3, 10): [10,21,22,26,33,55,77,143],
    Fraction(2, 5): [6,15,21,26,35,39,65,91],
    Fraction(3, 7): [6,10,14,26,39,65,91],
    Fraction(4, 7): [6,10,14,15,21,26,35,39,65,91],
    Fraction(1, 3): [6,10,15],
    Fraction(1, 5): [10,14,35],
    Fraction(1, 7): [15,21,35],
    Fraction(2, 7): [6,14,21],
    Fraction(3, 13): [6,26,39],
    Fraction(3, 11): [6,21,22,77],
    Fraction(8, 21): [6,10,15,21],
    Fraction(3, 14): [6,21],
    Fraction(2, 21): [15,35],
    Fraction(1, 6): [6],
}
for t, dens in KERNEL_R1.items():
    assert sum(Fraction(1, n) for n in dens) == t, t
    REPS.setdefault(t, dens)

PRIMES = list(primerange(2, 100))
ALLP = set(PRIMES)

def prime_set(dens):
    S = set()
    for n in dens:
        d = 2
        m = n
        while d * d <= m:
            while m % d == 0:
                S.add(d)
                m //= d
            d += 1
        if m > 1:
            S.add(m)
    return S

def build_pairs(P):
    L = 1
    for p in P:
        L *= p
    pairs = []
    ps = sorted(P)
    n = len(ps)
    for i in range(n):
        for j in range(i + 1, n):
            d = ps[i] * ps[j]
            pairs.append((d, L // d))
    return L, pairs

WCACHE = {}
def window_pairs(P):
    key = tuple(sorted(P))
    if key not in WCACHE:
        WCACHE[key] = build_pairs(set(P))
    return WCACHE[key]

def solve(pairs, T, tmo, node_cap):
    total = sum(v for _, v in pairs)
    if T > total or T < 0:
        return None
    flip = (2 * T > total)
    if flip:
        T = total - T
    ps = sorted(pairs, key=lambda t: -t[1])
    vals = [v for _, v in ps]
    dens = [d for d, _ in ps]
    m = len(vals)
    suf = [0] * (m + 1)
    mnv = [0] * (m + 1)
    for k in range(m - 1, -1, -1):
        suf[k] = suf[k + 1] + vals[k]
        mnv[k] = vals[k] if mnv[k + 1] == 0 else min(vals[k], mnv[k + 1])
    res = [None]
    nodes = [0]
    t0 = time.time()
    failmemo = set()
    def dfs(k, rem, acc):
        if res[0] is not None:
            return
        nodes[0] += 1
        if (nodes[0] & 4095) == 0 and time.time() - t0 > tmo:
            return
        if nodes[0] > node_cap:
            return
        if rem == 0:
            res[0] = acc[:]
            return
        if k >= m or rem > suf[k] or rem < mnv[k]:
            return
        key = (k, rem)
        if key in failmemo:
            return
        v = vals[k]
        if v <= rem:
            acc.append(dens[k])
            dfs(k + 1, rem - v, acc)
            if res[0] is not None:
                return
            acc.pop()
        if rem <= suf[k + 1]:
            dfs(k + 1, rem, acc)
            if res[0] is not None:
                return
        failmemo.add(key)
    dfs(0, T, [])
    if res[0] is None:
        return None
    if flip:
        chosen = set(res[0])
        return [d for d, _ in pairs if d not in chosen]
    return res[0]

def verify(dens, t):
    s = sum(Fraction(1, n) for n in dens)
    assert s == t, (str(t), s, dens[:6])
    assert len(set(dens)) == len(dens)
    import sympy
    for n in dens:
        f = sympy.factorint(n)
        assert len(f) == 2 and all(e == 1 for e in f.values()), (n, f)

# ---------- the ladder ----------
TAILCAP = {}  # frozenset(excluded primes) -> (cap Fraction, tail pairs, tailL)

def tail_ctx(excl):
    key = frozenset(excl)
    if key not in TAILCAP:
        tp = [p for p in PRIMES if p <= 67 and p not in excl]
        L, pairs = window_pairs(tp)
        tot = Fraction(sum(v for _, v in pairs), L)
        TAILCAP[key] = (tot, L, pairs)
    return TAILCAP[key]

def hunt_fraction(t, P_excl, tmo=12.0, cap=3_000_000):
    """Hunt rep of t over pairs of primes <= 67 minus P_excl."""
    tot, L, pairs = tail_ctx(P_excl)
    if t > tot or t <= 0:
        return None
    r = t
    # common denominator D = lcm(L, r.denominator)
    d = r.denominator
    D = L * (d // gcd(L, d))
    T = r.numerator * (D // d)
    vals_ok = all(D % n == 0 for n, _ in pairs[:1])  # sanity: D divisible by pair dens
    scaled = [(n, D // n) for n, _ in pairs]
    res = solve(scaled, T, tmo, cap)
    if res is None:
        return None
    return sorted(res)

def ladder(t):
    """Try t = head + residual over tail (head prime-disjoint)."""
    cands = []
    for h, hdens in sorted(REPS.items(), key=lambda kv: -kv[0]):
        if h >= t:
            continue
        r = t - h
        if r <= 0:
            continue
        Ph = prime_set(hdens)
        tot, L, pairs = tail_ctx(Ph)
        if r > tot:
            continue
        cands.append((h, hdens, Ph, r))
    # prefer heads leaving the largest tail slack (r far below cap => easier)
    cands.sort(key=lambda c: (c[3] / tail_ctx(c[2])[0]))
    for h, hdens, Ph, r in cands[:10]:
        res = hunt_fraction(r, Ph, tmo=10.0, cap=2_000_000)
        if res is not None:
            dens = sorted(hdens + res)
            ok = True
            try:
                verify(dens, t)
            except AssertionError:
                ok = False
            if ok:
                return dens
    return None

# ---------- the direct flip ----------
WINDOWS = [23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]

def direct(t):
    a, b = t.numerator, t.denominator
    for w in WINDOWS:
        P = [p for p in PRIMES if p <= w]
        L, pairs = window_pairs(P)
        if L % b != 0:
            continue
        T = a * (L // b)
        total = sum(v for _, v in pairs)
        if T > total:
            continue
        r = solve(pairs, T, 8.0, 1_500_000)
        if r is not None:
            dens = sorted(r)
            ok = True
            try:
                verify(dens, t)
            except AssertionError:
                ok = False
            if ok:
                return dens
    return None

todo = [t for t in BOX if t not in REPS]
print(f"state: {len(REPS)}/181; closing {min(CHUNK, len(todo))} of {len(todo)}", flush=True)
done_ct = 0
for t in todo:
    if done_ct >= CHUNK or time.time() - T0 > BUDGET:
        break
    got = ladder(t)
    tag = "LADDER"
    if got is None:
        got = direct(t)
        tag = "DIRECT"
    if got is not None:
        REPS[t] = got
        print(f"  HIT {t} [{tag}]: {len(got)} terms, max den {got[-1]} [{time.time()-T0:.0f}s]", flush=True)
    else:
        print(f"  MISS {t} [{time.time()-T0:.0f}s]", flush=True)
    done_ct += 1
    with open(CKPT, "w") as f:
        json.dump({"box_size": len(BOX), "represented": len(REPS),
                   "reps": {str(t): REPS[t] for t in sorted(REPS)},
                   "remaining": [str(x) for x in BOX if x not in REPS]},
                  f, indent=1)

rem_now = [x for x in BOX if x not in REPS]
print(f"\n=== CENSUS: {len(REPS)}/181; REMAINING ({len(rem_now)}): "
      f"{[str(x) for x in rem_now]} [{time.time()-T0:.0f}s]", flush=True)
