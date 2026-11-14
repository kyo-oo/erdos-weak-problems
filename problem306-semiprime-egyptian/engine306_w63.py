#!/usr/bin/env python3
"""W63-D5 #306: THE GENERAL BEG INDUCTION ENGINE v2 — full-closure census.

Universe U_B: all reduced rationals a/b with b squarefree, 2 <= b <= B,
0 < a/b < 1.  Represent EVERY member as a finite sum of DISTINCT reciprocals
of distinct-prime semiprimes (n = p*q, p < q primes).

MACHINERY (the BEG induction):
  * DIRECT prime-window pair subset-sums: window W = all primes <= X (plus
    primes of b); items = the semiprimes p*q (p<q in W); exact subset-sum
    to T = a*L/b, L = prod(W).  Complement-flip when the target density
    exceeds 1/2 (solve total-T, take the complement).
  * DFS: descending values, include-first, suffix-sum pruning, jump-skip
    past values > rem.  MITM: <= 40 items.
  * PEEL fallback: a/b = (a-1)/b + 1/b on DISJOINT fresh windows (the
    induction step; each 1/b piece over primes(b) + a disjoint fresh-pool
    slice -> denominators automatically distinct).
  * AMICABLE-TRIPLE SEED BANK (CRT prime-pair splitting): primes u<v<w,
    u*v*w = x*(u+v+w) => 1/(uv)+1/(uw)+1/(vw) = 1/x; twin family (2,q,q+2)
    and u-family (u,v,uv-u-v).  These are exactly the small-window hits.

DUAL VERIFICATION per witness: exact Fraction arithmetic AND gmpy2 integer
arithmetic over D = lcm(b, denominators), plus factorization by sympy
factorint AND independent trial division.

State: EVIDENCE_306_W63.json (checkpoint after each target; resumable).
"""
import json, sys, time
from fractions import Fraction
from math import gcd, isqrt
import gmpy2
from sympy import primerange, factorint

T_START = time.time()
B_HI = int(sys.argv[1]) if len(sys.argv) > 1 else 30
BUDGET_S = float(sys.argv[2]) if len(sys.argv) > 2 else 420.0
OUT = "EVIDENCE_306_W63.json"

PRIMES = list(primerange(2, 400))
PR_SET = set(PRIMES)

def factor_primes(n):
    f = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f

def squarefree(b):
    f = factor_primes(b)
    return len(f) == len(set(f))

# ---------------- amicable-triple seed bank ----------------
SEED = {}
def build_seed():
    for x in PRIMES:
        if x > 97:
            continue
        for i, u in enumerate(PRIMES):
            if u > 60:
                break
            if u * u <= x:
                continue
            for v in PRIMES[i + 1:]:
                if v > 200:
                    break
                den = u * v - x
                if den <= 0:
                    continue
                num = x * (u + v)
                if num % den:
                    continue
                w = num // den
                if w <= v or w not in PR_SET:
                    continue
                SEED.setdefault(x, []).append([u * v, u * w, v * w])
build_seed()

# ---------------- exact subset-sum solvers ----------------
def dfs_solve(items, T, cap_nodes=2_500_000, tmo=5.0):
    """items: (value, den); descending include-first DFS with suffix pruning
    and jump-skip.  Returns dens list or None."""
    items = sorted(items, key=lambda t: -t[0])
    vals = [v for v, _ in items]
    m = len(vals)
    suf = [0] * (m + 1)
    for k in range(m - 1, -1, -1):
        suf[k] = suf[k + 1] + vals[k]
    if T < 0 or T > suf[0]:
        return None
    # negated vals for bisect: vals desc; find first index with vals[idx] <= rem
    nvals = [-v for v in vals]
    res, nodes, t0 = [None], [0], time.time()
    sys.setrecursionlimit(300000)

    from bisect import bisect_left

    def dfs(k, rem, acc):
        if res[0] is not None or nodes[0] > cap_nodes:
            return
        if rem == 0:
            res[0] = acc[:]
            return
        if time.time() - t0 > tmo:
            return
        if k >= m or rem > suf[k]:
            return
        # jump to first item with value <= rem
        j = bisect_left(nvals, -rem, k, m)  # nvals desc in -v => asc; -rem pos
        if j >= m:
            return
        if suf[j] < rem:
            return
        v = vals[j]
        acc.append(items[j][1])
        dfs(j + 1, rem - v, acc)
        acc.pop()
        if res[0] is not None:
            return
        dfs(j + 1, rem, acc)

    dfs(0, T, [])
    return res[0]

def mitm_solve(items, T):
    """meet-in-the-middle exact subset-sum; items <= 40."""
    m = len(items)
    if m == 0 or m > 40:
        return None
    h1, h2 = items[: m // 2], items[m // 2:]
    def gen(lst):
        sums = [0]
        dens = [[]]
        for v, d in lst:
            n = len(sums)
            for i in range(n):
                sums.append(sums[i] + v)
                dens.append(dens[i] + [d])
        return sums, dens
    a_sums, a_dens = gen(h1)
    table = {}
    for s, dd in zip(a_sums, a_dens):
        if s not in table:
            table[s] = dd
    # stream half-B
    b_sums = [0]
    b_dens = [[]]
    for v, d in h2:
        n = len(b_sums)
        for i in range(n):
            b_sums.append(b_sums[i] + v)
            b_dens.append(b_dens[i] + [d])
    for s, dd in zip(b_sums, b_dens):
        need = T - s
        hit = table.get(need)
        if hit is not None:
            return hit + dd
    return None

# ---------------- window machinery ----------------
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
    return L, items

# prefix windows and their pair-density
XS = [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
WINS = [[p for p in PRIMES if p <= x] for x in XS]
def pair_density(W):
    s = Fraction(0)
    n = len(W)
    for i in range(n):
        for j in range(i + 1, n):
            s += Fraction(1, W[i] * W[j])
    return s
DENS = [pair_density(W) for W in WINS]

def solve_window(W, a, b, avoid, cap=2_500_000, tmo=5.0):
    """exact subset-sum for a/b over window W (primes(b) must be in W).
    Complement-flip when beneficial.  Returns dens or None."""
    L, items = window_items(W, avoid)
    if not items:
        return None
    if L % b != 0:
        return None
    T = a * (L // b)
    total = sum(v for v, _ in items)
    if T > total or T < 0:
        return None
    sub = None
    if T * 2 > total:
        C = total - T
        sub = dfs_solve(items, C, cap, tmo)
        if sub is None and len(items) <= 40:
            sub = mitm_solve(items, C)
        if sub is not None:
            chosen = set(sub)
            return sorted(d for v, d in items if d not in chosen)
        return None
    sub = dfs_solve(items, T, cap, tmo)
    if sub is None and len(items) <= 40:
        sub = mitm_solve(items, T)
    if sub is not None:
        return sorted(sub)
    return None

# ---------------- peel machinery (the induction step) ----------------
def solve_peel(a, b, avoid0=frozenset()):
    """a/b = (a-1)/b (+) 1/b (+) ... — each 1/b on a DISJOINT fresh window.
    Fresh slices: consecutive prime blocks past the previous window."""
    bs = factor_primes(b)
    blocks = [[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47],
              [53, 59, 61, 67], [71, 73, 79, 83], [89, 97, 101, 103],
              [107, 113, 127, 131]]
    witness = []
    avoid = set(avoid0)
    for piece_idx in range(a, 0, -1):
        if piece_idx == 1:
            # last piece: 1/b over a window
            got = None
            for bi in range(len(blocks)):
                W = sorted(set(bs) | set(blocks[bi]))
                got = solve_window(W, 1, b, avoid)
                if got:
                    break
            if not got:
                return None
            witness += got
            avoid |= set(got)
            break
        else:
            got = None
            for bi in range(len(blocks)):
                W = sorted(set(bs) | set(blocks[bi]))
                got = solve_window(W, 1, b, avoid)
                if got:
                    break
            if not got:
                return None
            witness += got
            avoid |= set(got)
    if len(set(witness)) != len(witness):
        return None
    return sorted(witness)

# ---------------- the target solver ----------------
def solve_ab(a, b, deep=True):
    bs = factor_primes(b)
    # lane A: direct windows (primes(b) always included since b<=B<=30 < 13?? ensure)
    for xi, X in enumerate(XS):
        if X < max(bs):
            continue
        W = WINS[xi]
        d = DENS[xi]
        if Fraction(a, b) > d + Fraction(1, 100):
            continue
        got = solve_window(W, a, b, set())
        if got:
            return got
        # one extra prime appended
        for extra in [PRIMES[len(W)], PRIMES[len(W) + 1]]:
            W2 = sorted(W + [extra])
            got = solve_window(W2, a, b, set())
            if got:
                return got
    # lane B: seed triple bank for 1/x pieces (only b prime, a small)
    if len(bs) == 1 and a <= 3:
        trs = SEED.get(b, [])
        cnt = 0
        dens = []
        for tr in trs:
            if cnt + 1 > a:
                break
            if all(d not in dens for d in tr):
                dens += tr
                cnt += 1
        if cnt == a and len(set(dens)) == len(dens):
            if verify_pair(a, b, dens):
                return sorted(dens)
    # lane C: peel induction
    if deep:
        got = solve_peel(a, b)
        if got:
            return got
    return None

# ---------------- verification (dual method) ----------------
def verify_pair(a, b, dens):
    if not dens or len(set(dens)) != len(dens):
        return False
    if any(d in (0, 1) for d in dens):
        return False
    s = sum(Fraction(1, n) for n in dens)
    if s != Fraction(a, b):
        return False
    D = gmpy2.mpz(b)
    for n in dens:
        D = gmpy2.lcm(D, gmpy2.mpz(n))
    acc = gmpy2.mpz(0)
    for n in dens:
        if D % n != 0:
            return False
        acc += D // n
    if D % b != 0 or acc != gmpy2.mpz(a) * (D // b):
        return False
    for n in dens:
        f = factor_primes(n)
        if len(f) != 2 or f[0] == f[1] or f[0] * f[1] != n:
            return False
    return True

def verify_full(a, b, dens):
    if not verify_pair(a, b, dens):
        return False
    for n in dens:
        fi = factorint(n)
        if len(fi) != 2 or max(fi.values()) != 1:
            return False
    return True

# ---------------- universe + driver ----------------
def universe(B):
    targets = []
    for b in range(2, B + 1):
        if not squarefree(b):
            continue
        for a in range(1, b):
            if gcd(a, b) == 1:
                targets.append((a, b))
    return targets

def main():
    try:
        state = json.load(open(OUT))
        if state.get("B") != B_HI:
            state = {"done": {}, "failed": [], "B": B_HI}
    except Exception:
        state = {"done": {}, "failed": [], "B": B_HI}
    targets = universe(B_HI)
    print(f"universe: {len(targets)} rationals (b squarefree <= {B_HI}, 0<a/b<1)", flush=True)
    print(f"seed bank: {sum(len(v) for v in SEED.values())} triples / {len(SEED)} targets", flush=True)
    for (a, b) in targets:
        key = f"{a}/{b}"
        if key in state["done"]:
            continue
        if time.time() - T_START > BUDGET_S:
            print(f"[budget stop] done={len(state['done'])}", flush=True)
            break
        dens = solve_ab(a, b)
        if dens is not None and verify_full(a, b, dens):
            state["done"][key] = dens
            if key in state["failed"]:
                state["failed"].remove(key)
            print(f"  {a}/{b}: {len(dens)} terms, max den {dens[-1]}", flush=True)
        else:
            if key not in state["failed"]:
                state["failed"].append(key)
            print(f"  {a}/{b}: FAIL", flush=True)
        json.dump(state, open(OUT, "w"))
    print(f"\n=== #306 W63 CENSUS: {len(state['done'])}/{len(targets)} (b<={B_HI}) ===", flush=True)
    if state.get("failed"):
        print(f"residue: {state['failed']}", flush=True)
    json.dump(state, open(OUT, "w"), indent=0)

if __name__ == "__main__":
    main()
