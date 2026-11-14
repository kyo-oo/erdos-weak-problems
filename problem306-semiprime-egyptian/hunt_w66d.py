#!/usr/bin/env python3
"""W66-P306-D INDEPENDENT HUNT ENGINE v2 (pure python + sympy primes only).

Adversarial census continuation: repo-verifiable state = 105/181; attacks the
76-target remainder (12 near-unit family + 64 budget-stopped).

Machinery (exact integer arithmetic over the window primorial L):
  * lane A — direct window subset-sums with complement flip; MITM exhaustive
    for <= 45 items (2^22 halves), randomized-restart DFS otherwise
  * lane B — split-peel: a/b = sum of pieces (ai, b) on pairwise-disjoint
    denominator sets, each piece an exact subset-sum over primes(b) + a fresh
    prime chunk (distinctness via the avoid set; final independent verify)

Every banked receipt passes INDEPENDENT verification (Fraction sum + trial
division factorization + pairwise distinctness + lcm integer dual).
Checkpoint: EVIDENCE_306_W66D.json after every target.
"""
import json, sys, time, random
from bisect import bisect_left
from fractions import Fraction
from math import gcd, isqrt

T0 = time.time()
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 900.0
OUT = "EVIDENCE_306_W66D.json"
LOGF = open("hunt_w66d.log", "a", buffering=1)

def log(*a):
    print(*a, file=LOGF, flush=True)
    print(*a, flush=True)

from sympy import primerange
PRIMES = list(primerange(2, 600))
PR_SET = set(PRIMES)

def trial_factors(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f.append(n)
    return f

def is_prime_indep(n):
    if n < 2:
        return False
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return False
    return True

def dclass(n):
    f = trial_factors(n)
    return len(f) == 2 and f[0] != f[1] and is_prime_indep(f[0]) and is_prime_indep(f[1])

def verify(a, b, dens):
    if not dens or len(set(dens)) != len(dens):
        return False
    if any(d <= 1 for d in dens) or not all(dclass(d) for d in dens):
        return False
    if sum(Fraction(1, n) for n in dens) != Fraction(a, b):
        return False
    L = b
    for n in dens:
        L = L * n // gcd(L, n)
    if L % b or sum(L // n for n in dens) != a * (L // b):
        return False
    return True

def box(B=30):
    t = []
    for b in range(2, B + 1):
        f = trial_factors(b)
        if len(f) != len(set(f)):
            continue
        for a in range(1, b):
            if gcd(a, b) == 1:
                t.append((a, b))
    return t

BOX = box(30)

def window_items(W, avoid):
    L = 1
    for p in W:
        L *= p
    items = []
    n = len(W)
    for i in range(n):
        for j in range(i + 1, n):
            d = W[i] * W[j]
            if d in avoid:
                continue
            items.append((L // d, d))
    items.sort(key=lambda t: -t[0])
    return L, items

# ---------------- exact subset-sum solvers ----------------
def dfs_solve(items, T, cap_nodes=3_000_000, tmo=20.0, seed=None):
    vals = [v for v, _ in items]
    m = len(vals)
    order = list(range(m))
    if seed is not None:
        random.Random(seed).shuffle(order)      # diversify exploration order
        # (suffix pruning still valid: sums recomputed on this order)
    vlist = [vals[i] for i in order]
    ilist = [items[i] for i in order]
    suf = [0] * (m + 1)
    for k in range(m - 1, -1, -1):
        suf[k] = suf[k + 1] + vlist[k]
    if T < 0 or T > suf[0]:
        return None
    nv = [-v for v in vlist]
    is_sorted = seed is None                  # unseeded: descending order
    res, nodes, t0 = [None], [0], time.time()
    sys.setrecursionlimit(20000)
    def dfs(k, rem, acc):
        if res[0] is not None or nodes[0] > cap_nodes:
            return
        if time.time() - t0 > tmo:
            return
        if rem == 0:
            res[0] = [d for v, d in acc]
            return
        if k >= m or rem > suf[k]:
            return
        if is_sorted:
            j = bisect_left(nv, -rem, k, m)
            if j >= m or suf[j] < rem:
                return
            rng_i = range(j, m)
        else:
            rng_i = range(k, m)
        for i in rng_i:
            v = vlist[i]
            if v > rem:
                if is_sorted:
                    break
                continue
            nodes[0] += 1
            acc.append(ilist[i])
            dfs(i + 1, rem - v, acc)
            acc.pop()
            if res[0] is not None:
                return
    dfs(0, T, [])
    return res[0]

def mitm_feasible(items, half_cap=1 << 22):
    m = len(items)
    if m == 0 or m > 46:
        return False
    h = min(m // 2, 22)
    while h > 0 and (1 << (m - h)) > 4 * half_cap:
        h -= 1
    if (1 << h) > half_cap:
        return False
    return True

def mitm_solve(items, T, half_cap=1 << 22, tmo=240.0):
    """exhaustive MITM, table side <= half_cap sums (RAM-bounded), probe side
    streamed as a generator. Returns dens list or None."""
    m = len(items)
    if m == 0 or m > 46 or not mitm_feasible(items, half_cap):
        return None
    h = min(m // 2, 22)
    while h > 0 and (1 << (m - h)) > 4 * half_cap:
        h -= 1
    A, B = items[:h], items[h:]
    try:
        sa = [0]
        for v, _ in A:
            sa = sa + [x + v for x in sa]
        table = {}
        for idx, s in enumerate(sa):
            if s not in table:
                table[s] = idx
        valsB = [v for v, _ in B]
        mB = len(B)
        t0 = time.time()
        def gen(i, s, mask):
            if i == mB:
                yield s, mask
                return
            yield from gen(i + 1, s, mask)
            yield from gen(i + 1, s + valsB[i], mask | (1 << i))
        cnt = 0
        for s, mask in gen(0, 0, 0):
            cnt += 1
            if not (cnt & 0xFFFFF) and time.time() - t0 > tmo:
                return None
            need = T - s
            hit = table.get(need)
            if hit is not None:
                dens = []
                for i in range(len(A)):
                    if (hit >> i) & 1:
                        dens.append(A[i][1])
                for i in range(mB):
                    if (mask >> i) & 1:
                        dens.append(B[i][1])
                return dens
    except MemoryError:
        return None
    return None

def solve_window(W, a, b, avoid, cap=3_000_000, tmo=20.0, use_mitm=True):
    L, items = window_items(W, avoid)
    if not items or L % b != 0:
        return None
    T = a * (L // b)
    total = sum(v for v, _ in items)
    if T > total or T < 0:
        return None
    if 2 * T > total:
        C = total - T
        if use_mitm and mitm_feasible(items):
            sub = mitm_solve(items, C)          # EXHAUSTIVE for this window
        else:
            sub = dfs_solve(items, C, cap, tmo)
            if sub is None:
                for sd in (1, 2, 3, 4):
                    sub = dfs_solve(items, C, cap // 3, tmo, seed=sd)
                    if sub is not None:
                        break
        if sub is not None:
            chosen = set(sub)
            return sorted({d for v, d in items if d not in chosen})
        return None
    if use_mitm and mitm_feasible(items):
        sub = mitm_solve(items, T)              # EXHAUSTIVE for this window
    else:
        sub = dfs_solve(items, T, cap, tmo)
        if sub is None:
            for sd in (1, 2, 3, 4):
                sub = dfs_solve(items, T, cap // 3, tmo, seed=sd)
                if sub is not None:
                    break
    if sub is not None:
        return sorted(set(sub))
    return None

# ---------------- split-peel (disjoint-window composition) ----------------
CHUNKS = []
pool = [p for p in PRIMES if 3 <= p]
# rich chunks first (small primes), then fresh blocks
rich = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
CHUNKS.append(rich[0:6])          # [3,5,7,11,13,17]
CHUNKS.append(rich[6:10])         # [19,23,29,31]
CHUNKS.append(rich[10:14])        # [37,41,43,47]
i = 0
rest = [p for p in PRIMES if p >= 53]
while i + 6 <= len(rest) and len(CHUNKS) < 40:
    CHUNKS.append(rest[i:i + 6])
    i += 6

def split_pieces(a):
    """binary split of the numerator a into pieces (few, balanced)."""
    out = []
    stack = [a]
    while stack:
        x = stack.pop()
        if x <= 3:
            out.append(x)
        else:
            h = x // 2
            stack.append(h)
            stack.append(x - h)
    return sorted(out, reverse=True)

def chunk_richness(W):
    """fast density ESTIMATE for a window: (sum 1/p)^2 / 2 — feasibility
    pre-filter (upper-ish bound ignoring the 1/p^2 subtraction)."""
    s = sum(Fraction(1, p) for p in W)
    return s * s / 2

def solve_peel(a, b, tmo_piece=15.0):
    bs = sorted(set(trial_factors(b)))
    pieces = split_pieces(a)
    witness, avoid = [], set()
    for ai in pieces:
        if ai == 0:
            continue
        got = None
        tgt = Fraction(ai, b)
        # windows: primes(b) + each chunk; density-infeasible chunks skipped
        for ci in range(len(CHUNKS)):
            W = sorted(set(bs) | set(CHUNKS[ci]))
            if chunk_richness(W) < tgt * Fraction(11, 10):
                continue
            got = solve_window(W, ai, b, avoid, cap=1_500_000, tmo=tmo_piece)
            if got:
                break
        if not got:
            # wider custom windows: primes(b) + chunk + next chunk (8-14 primes)
            for ci in range(0, len(CHUNKS) - 1, 2):
                W = sorted(set(bs) | set(CHUNKS[ci]) | set(CHUNKS[ci + 1]))
                got = solve_window(W, ai, b, avoid, cap=1_500_000, tmo=tmo_piece,
                                   use_mitm=False)
                if got:
                    break
        if not got:
            return None
        if set(got) & avoid:
            return None
        witness += got
        avoid |= set(got)
    if len(set(witness)) != len(witness):
        return None
    return sorted(witness)

# ---------------- driver ----------------
try:
    state = json.load(open(OUT))
except Exception:
    state = {"done": {}, "failed": [], "source": "W66-P306-D independent hunt"}
done = state["done"]
for k in list(done):
    a, b = map(int, k.split("/"))
    if not verify(a, b, done[k]):
        log(f"[GUARD] existing receipt {k} failed re-verification — dropped")
        del done[k]

XS = [23, 29, 31, 37, 41, 47, 53, 61]
WINS = [[p for p in PRIMES if p <= x] for x in XS]

targets = [t for t in BOX if f"{t[0]}/{t[1]}" not in done]
# attack order: small targets first (fast MITM wins), near-units last
targets.sort(key=lambda ab: Fraction(ab[0], ab[1]))
NEAR = [t for t in targets if Fraction(t[0], t[1]) >= Fraction(5, 6)]
MID = [t for t in targets if Fraction(1, 2) <= Fraction(t[0], t[1]) < Fraction(5, 6)]
EASY = [t for t in targets if Fraction(t[0], t[1]) < Fraction(1, 2)]
targets = EASY + MID + NEAR
log(f"[HUNT v2] {len(done)}/181 banked; attacking {len(targets)} "
    f"(easy {len(EASY)}, mid {len(MID)}, near-unit {len(NEAR)}; budget {BUDGET:.0f}s)")

for (a, b) in targets:
    key = f"{a}/{b}"
    if time.time() - T0 > BUDGET:
        log(f"[budget stop] banked total {len(done)}")
        break
    t = Fraction(a, b)
    got = None
    bs = sorted(set(trial_factors(b)))
    # lane A: direct windows, biggest sensible first
    if t < Fraction(1, 2):
        for xi, X in enumerate(XS):
            if X < bs[-1]:
                continue
            got = solve_window(WINS[xi], a, b, set(), tmo=10.0)
            if got:
                break
    elif t < Fraction(5, 6):
        # mid targets: window first, peel fallback
        for xi, X in enumerate(XS):
            if X < bs[-1]:
                continue
            got = solve_window(WINS[xi], a, b, set(), tmo=12.0)
            if got:
                break
    else:
        # near-unit: PEEL FIRST (the disjoint-window route is the high
        # probability path); complement-flip windows only as fallback
        got = solve_peel(a, b, tmo_piece=10.0)
        if got is None:
            for xi, X in enumerate(XS):
                if X < bs[-1] or X < 29:
                    continue
                got = solve_window(WINS[xi], a, b, set(), tmo=12.0)
                if got:
                    break
    # lane B: split-peel with disjoint windows
    if got is None and t < Fraction(5, 6):
        got = solve_peel(a, b, tmo_piece=12.0)
    if got is not None and verify(a, b, got):
        done[key] = got
        state["failed"] = [k for k in state.get("failed", []) if k != key]
        log(f"  {key}: {len(got)} terms, max den {got[-1]}")
    else:
        if got is not None:
            log(f"  {key}: candidate FAILED verification (bug!)")
        if key not in state.get("failed", []):
            state["failed"].append(key)
        log(f"  {key}: FAIL")
    json.dump(state, open(OUT, "w"))

rem = [f"{a}/{b}" for a, b in BOX if f"{a}/{b}" not in done]
log(f"=== W66D CENSUS: {len(done)}/181 | remaining: {rem}")
json.dump(state, open(OUT, "w"), indent=1)
