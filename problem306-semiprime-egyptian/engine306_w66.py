#!/usr/bin/env python3
"""W66-P306-E — THE CLOSING ENGINE v2: MITM/LP staged disjoint-window composer.

Mission: land the remaining census-box rationals a/b (b squarefree <= 30,
0 < a/b < 1) as sums of DISTINCT reciprocals of distinct-prime semiprimes
(n = p*q, p < q, primes certified by trial division).

MACHINERY (the STATUS.md round-2 path — staged disjoint windows):

  * WINDOWS: W = CORE_k U primes(b) U FRESH_i; CORE_k = primes <= c_k with
    escalation c_k in {7, 11, 13, 17, 23}; FRESH_i = disjoint blocks of
    primes past 47 (the fresh stream, rotating cursor).  Windows share only
    CORE primes; FRESH blocks are disjoint, so cross-window denominator
    collisions are confined to CORE-internal pairs — excluded via `avoid`.
  * MITM (meet-in-the-middle over term-subsets of a window): exact
    subset-sum to T = a*L/b, halves hash-joined; pools <= 36 items.
  * DFS-RESTARTS: for pools beyond the MITM cap (the 45-136-item big
    windows) — descending include-first DFS with suffix pruning, bisect
    jump-skip, node cap, deadline, plus randomized tie-perturbation
    restarts (the near-unit regime's workhorse).
  * COMPLEMENT-FLIP: when the target exceeds half the window total, solve
    total - T (the small complement — for near-units r = 1 - small this is
    the small side) and keep the complement subset.
  * LP/density bound: window skipped unless 0 <= T <= total (the LP
    relaxation feasibility bound).
  * STAGED COMPOSITION: a/b = sum of pieces; pieces are existing receipts
    used literally when disjoint, else re-landed on fresh windows with
    avoid = all used denominators; same-denominator splits from the done
    bank (a = c1 + c2 + ... with each ci/b reduced into the bank).

State: EVIDENCE_306_W66E.json (checkpoint after every target; the full
represented-set list).  Receipts: one file per rational under rep306_w66/
with the exact term list + verification transcript.

Pure python + sympy primerange ONLY.  Long hunts: background + checkpoints.
"""
import json
import os
import random
import sys
import time
from bisect import bisect_left
from fractions import Fraction
from math import gcd

from sympy import primerange

HERE = os.path.dirname(os.path.abspath(__file__))
STATE = os.path.join(HERE, "EVIDENCE_306_W66E.json")
RECEIPTS = os.path.join(HERE, "rep306_w66")
B_HI = 30
T_START = time.time()
BUDGET_S = float(os.environ.get("E306_BUDGET", "7200"))
TARGET_CAP_S = float(os.environ.get("E306_TARGET_CAP", "210"))

PRIMES = list(primerange(2, 1200))
FRESH_POOL = [p for p in PRIMES if p > 47]
CORE_STOPS = [7, 11, 13, 17, 23]
CORES = [[p for p in PRIMES if p <= c] for c in CORE_STOPS]
FRESH_CURSOR = 0


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    if n % 3 == 0:
        return n == 3
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def prime_factors(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f


def squarefree(b):
    f = prime_factors(b)
    return len(f) == len(set(f))


def certify(n):
    """n = p*q, p < q distinct primes (trial division) -> (p, q) else None."""
    if n < 6:
        return None
    d = 2
    while d * d <= n:
        if n % d == 0:
            p, q = d, n // d
            if p < q and is_prime_trial(p) and is_prime_trial(q):
                return (p, q)
            return None
        d += 1
    return None


def verify_receipt(a, b, dens, loud=False):
    problems = []
    if not dens:
        problems.append("empty")
    if len(dens) != len(set(dens)):
        problems.append("duplicates")
    for n in dens:
        if certify(n) is None:
            problems.append(f"non-semiprime {n}")
    if sum(Fraction(1, n) for n in dens) != Fraction(a, b):
        problems.append("sum mismatch")
    if problems and loud:
        print(f"    !! VERIFY FAIL {a}/{b}: {problems}", flush=True)
    return not problems


def integer_crosscheck(a, b, dens):
    D = b
    for n in dens:
        D = D * n // gcd(D, n)
    return D % b == 0 and sum(D // n for n in dens) == a * (D // b)

# ---------------------------------------------------------------- solvers
sys.setrecursionlimit(200000)


def _dfs_core(vals, dens, T, cap_nodes, tmo):
    """Descending include-first DFS with suffix pruning + jump-skip."""
    m = len(vals)
    suf = [0] * (m + 1)
    for k in range(m - 1, -1, -1):
        suf[k] = suf[k + 1] + vals[k]
    if T < 0 or T > suf[0]:
        return None
    nvals = [-v for v in vals]
    res, nodes, t0 = [None], [0], time.time()

    def dfs(k, rem, acc):
        if res[0] is not None or nodes[0] > cap_nodes:
            return
        nodes[0] += 1
        if rem == 0:
            res[0] = acc[:]
            return
        if time.time() - t0 > tmo:
            return
        if k >= m or rem > suf[k]:
            return
        j = bisect_left(nvals, -rem, k, m)
        if j >= m or suf[j] < rem:
            return
        acc.append(dens[j])
        dfs(j + 1, rem - vals[j], acc)
        acc.pop()
        if res[0] is not None:
            return
        dfs(j + 1, rem, acc)

    dfs(0, T, [])
    return res[0]


def dfs_solve(items, T, cap_nodes=1_000_000, tmo=6.0):
    items = sorted(items, key=lambda t: -t[0])
    return _dfs_core([v for v, _ in items], [d for _, d in items],
                     T, cap_nodes, tmo)


def dfs_restarts(items, T, restarts=6, tmo=3.5, cap_nodes=300_000):
    """The big-pool weapon: deterministic pass + randomized-perturbation
    restarts (random re-ordering multiplier on values)."""
    r = dfs_solve(items, T, cap_nodes, tmo)
    if r is not None:
        return r
    rng = random.Random(0x306)
    for k in range(restarts):
        jitter = 1.0 + rng.random() * 0.5
        order = sorted(items, key=lambda t: -(t[0] * (jitter + rng.random() * 0.2)))
        r = _dfs_core([v for v, _ in order], [d for _, d in order],
                      T, cap_nodes // 2, tmo)
        if r is not None:
            return r
    return None


def mitm_solve(items, T, cap=36):
    """Meet-in-the-middle exact subset-sum (hash-join of the two halves)."""
    m = len(items)
    if m == 0 or m > cap:
        return None
    h1, h2 = items[: m // 2], items[m // 2:]
    sums, masks = [0], [0]
    for i, (v, d) in enumerate(h1):
        bit = 1 << i
        n = len(sums)
        for s_i in range(n):
            s = sums[s_i] + v
            if s <= T:
                sums.append(s)
                masks.append(masks[s_i] | bit)
    table = {}
    for s, mk in zip(sums, masks):
        if s not in table:
            table[s] = mk
    sums2, masks2 = [0], [0]
    for i, (v, d) in enumerate(h2):
        bit = 1 << i
        n = len(sums2)
        for s_i in range(n):
            s = sums2[s_i] + v
            if s <= T:
                sums2.append(s)
                masks2.append(masks2[s_i] | bit)
    for s, mk in zip(sums2, masks2):
        need = T - s
        hit = table.get(need)
        if hit is not None:
            dens = []
            for i, (v, d) in enumerate(h1):
                if (hit >> i) & 1:
                    dens.append(d)
            for i, (v, d) in enumerate(h2):
                if (mk >> i) & 1:
                    dens.append(d)
            return dens
    return None


def window(W, avoid):
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


def solve_window(W, a, b, avoid, deadline=None):
    """Exact a/b over window W: LP bound + complement-flip + MITM/DFS."""
    L, items = window(W, avoid)
    if not items or L % b:
        return None
    T = a * (L // b)
    total = sum(v for v, _ in items)
    if T < 0 or T > total:
        return None
    pool = [(v, d) for v, d in items if v <= T]  # eligible items only
    if not pool:
        return None
    if 2 * T > total:
        C = total - T                       # complement-flip: solve small side
        cpool = [(v, d) for v, d in items if v <= C]
        sub = None
        if len(cpool) <= 36:
            sub = mitm_solve(cpool, C)
        if sub is None:
            sub = dfs_restarts(cpool, C)
        if sub is None:
            return None
        chosen = set(sub)
        return sorted(d for v, d in items if d not in chosen)
    sub = None
    if len(pool) <= 36:
        sub = mitm_solve(pool, T)
    if sub is None:
        sub = dfs_restarts(pool, T)
    if sub is not None:
        return sorted(sub)
    return None

# ------------------------------------------------- fresh stream / landing
def fresh_block(k):
    global FRESH_CURSOR
    if FRESH_CURSOR + k > len(FRESH_POOL):
        return None
    blk = FRESH_POOL[FRESH_CURSOR: FRESH_CURSOR + k]
    FRESH_CURSOR += k
    return blk


def fresh_cursor():
    return FRESH_CURSOR


def set_fresh_cursor(c):
    global FRESH_CURSOR
    FRESH_CURSOR = c


def land_piece(a, b, avoid, deadline=None, passes=2):
    """Land a/b on fresh windows: CORE escalation x fresh-size x rotation.
    MITM for <=36-item pools, DFS-restarts beyond.  Small targets get a
    fast rotation sweep (each 15-36-item MITM costs well under a second)."""
    bs = sorted(set(prime_factors(b)))
    r = a / b
    # fast sweep for small targets: small windows, many rotations
    if r <= 0.42:
        for attempt in range(10):
            for core_stop in (7, 11, 13, 17):
                core = [p for p in PRIMES if p <= core_stop]
                for fsize in (1, 2):
                    if deadline is not None and time.time() > deadline:
                        return None
                    blk = fresh_block(fsize)
                    if blk is None:
                        return None
                    W = sorted(set(core) | set(bs) | set(blk))
                    if len(W) * (len(W) - 1) // 2 > 36:
                        continue
                    got = solve_window(W, a, b, avoid, deadline)
                    if got is not None:
                        return got
    # general ladder (bigger windows, DFS-restarts beyond the MITM cap)
    for attempt in range(passes):
        for core in CORES:
            for fsize in (1, 2, 4, 6):
                blk = fresh_block(fsize)
                if blk is None:
                    return None
                W = sorted(set(core) | set(bs) | set(blk))
                if deadline is not None and time.time() > deadline:
                    return None
                got = solve_window(W, a, b, avoid, deadline)
                if got is not None:
                    return got
    return None

# ------------------------------------------------- universe / state
def universe(B):
    targets = []
    for b in range(2, B + 1):
        if not squarefree(b):
            continue
        for a in range(1, b):
            if gcd(a, b) == 1:
                targets.append((a, b))
    return targets


def load_state():
    try:
        st = json.load(open(STATE))
        if st.get("B") == B_HI:
            for k in list(st["done"]):
                a, b = map(int, k.split("/"))
                if not verify_receipt(a, b, st["done"][k]):
                    print(f"  !! loaded receipt {k} FAILED reverification — dropped", flush=True)
                    del st["done"][k]
            return st
    except Exception:
        pass
    done = {}
    srcA = json.load(open(os.path.join(HERE, "EVIDENCE_306_W63.json")))["done"]
    for k, v in srcA.items():
        a, b = map(int, k.split("/"))
        if verify_receipt(a, b, v):
            done[k] = v
    import re
    for line in open(os.path.join(os.path.dirname(HERE), "EVIDENCE_306.txt")):
        m = re.match(r"^(\d+)/(\d+)\s*=\s*(.*)$", line.strip())
        if not m:
            continue
        a, b = int(m.group(1)), int(m.group(2))
        dens = [int(x) for x in re.findall(r"1/(\d+)", m.group(3))]
        k = f"{a}/{b}"
        if k not in done and verify_receipt(a, b, dens):
            done[k] = dens
    return {"done": done, "failed": [], "B": B_HI, "landed_w66": []}


def save_state(st):
    tmp = STATE + ".tmp"
    json.dump(st, open(tmp, "w"), indent=0)
    os.replace(tmp, STATE)

# ------------------------------------------------- receipts
def emit_receipt(a, b, dens, method):
    os.makedirs(RECEIPTS, exist_ok=True)
    name = f"r{a}_{b}.txt"
    sd = sorted(dens)
    D = b
    for n in sd:
        D = D * n // gcd(D, n)
    acc = sum(D // n for n in sd)
    lines = []
    W = lines.append
    W("#306 semiprime Egyptian representation receipt — W66-P306-E")
    W(f"rational: {a}/{b}   (b squarefree, b <= 30 census box)")
    W(f"method:   {method}")
    W(f"terms:    {len(sd)} distinct semiprime denominators n = p*q, p < q")
    W("")
    W(f"{a}/{b} = " + " + ".join(f"1/{n}" for n in sd))
    W("")
    W("term table (n = p*q, p < q, primes certified by trial division):")
    for n in sd:
        p, q = certify(n)
        W(f"  {n:6d} = {p} * {q}")
    W("")
    W("verification transcript (python /home/z/.venv/bin/python3, Fraction arithmetic):")
    W("  >>> from fractions import Fraction")
    W(f"  >>> dens = {sd}")
    W(f"  >>> sum(Fraction(1, n) for n in dens) == Fraction({a}, {b})")
    W("  True")
    W("  >>> len(set(dens)) == len(dens)")
    W("  True")
    W("  >>> all(certify(n) is not None for n in dens)   # p<q semiprime, trial division")
    W("  True")
    W(f"  integer cross-check over D = lcm(b, dens) = {D}:")
    W(f"  >>> sum(D // n for n in dens) == {a} * (D // {b})")
    W(f"  True   (acc = {acc}, a*(D//b) = {a * (D // b)})")
    W("")
    W("engine: engine306_w66.py (MITM/LP staged disjoint-window composer v2)")
    W("state:  EVIDENCE_306_W66E.json  (census checkpoint)")
    assert verify_receipt(a, b, sd) and integer_crosscheck(a, b, sd)
    open(os.path.join(RECEIPTS, name), "w").write("\n".join(lines) + "\n")
    return name

# ------------------------------------------------- composition driver
USED_MASS_CAP = 0.82   # CORE<=17 + fresh-pair window density (36 items)


def core_mass(dens):
    """Mass of the CORE<=23-internal denominators (the shared resource:
    fresh-cross pairs live in per-piece disjoint fresh space)."""
    s = Fraction(0)
    for n in dens:
        if all(p <= 23 for p in prime_factors(n)):
            s += Fraction(1, n)
    return float(s)


def solve_ab(a, b, st, deadline=None):
    done = st["done"]

    def red_key(a1, b1):
        g = gcd(a1, b1)
        return f"{a1 // g}/{b1 // g}"

    def mass(dens):
        return float(sum(Fraction(1, n) for n in dens))
    # ---- A: direct fresh-window ladder (density-feasible only)
    if a / b <= 0.83:
        set_fresh_cursor(0)
        got = land_piece(a, b, set(), deadline)
        if got is not None and verify_receipt(a, b, got):
            return got, "A:direct-fresh-window"

    # ---- B: split-2 from the done bank: literal + fresh piece (fall
    #      through the split list; piece must fit the remaining density)
    for c in range(a - 1, 0, -1):
        if deadline is not None and time.time() > deadline:
            break
        k1, k2 = red_key(c, b), red_key(a - c, b)
        if k1 not in done or k2 not in done:
            continue
        g2 = gcd(a - c, b)
        p1 = done[k1]
        if (a - c) / b > USED_MASS_CAP - core_mass(p1) + 0.06:
            continue
        used = set(p1)
        set_fresh_cursor(0)
        p2 = land_piece((a - c) // g2, b // g2, used, deadline)
        if p2 is not None and verify_receipt(a, b, sorted(p1 + p2)):
            return sorted(p1 + p2), f"B:split-2[{k1} literal + {k2} fresh-window]"

    # ---- C: greedy done-peel chain: literals while disjoint, else fresh
    #      pieces; fall through smaller peels when a piece fails; final
    #      direct fresh land of the remainder.
    rem, used, witness, pieces = a, set(), [], []
    core_used = 0.0
    guard = 0
    while rem > 0 and guard < 14:
        guard += 1
        if deadline is not None and time.time() > deadline:
            break
        landed = False
        for c in range(rem, 0, -1):
            if deadline is not None and time.time() > deadline:
                break
            key = red_key(c, b)
            if key not in done:
                continue
            if c / b > USED_MASS_CAP - core_used + 0.06:
                continue
            lit = done[key]
            g = gcd(c, b)
            if set(lit).isdisjoint(used):
                witness += lit
                used |= set(lit)
                core_used += core_mass(lit)
                pieces.append(f"{key} literal")
                rem -= c
                landed = True
                break
            got = land_piece(c // g, b // g, used, deadline)
            if got is not None:
                witness += got
                used |= set(got)
                core_used += core_mass(got)
                pieces.append(f"{key} fresh-window")
                rem -= c
                landed = True
                break
        if not landed:
            break
    if rem > 0 and (witness or rem == a):
        got = land_piece(rem, b, used, deadline)
        if got is not None:
            witness += got
            used |= set(got)
            pieces.append(f"{rem}/{b} fresh-window")
            rem = 0
    if rem == 0 and witness and verify_receipt(a, b, sorted(witness)):
        return sorted(witness), "C:done-peel-chain[" + " + ".join(pieces) + "]"

    # ---- D: pure peel: a x 1/b over disjoint fresh windows
    set_fresh_cursor(0)
    witness, used = [], set()
    ok = True
    for piece in range(a, 0, -1):
        if deadline is not None and time.time() > deadline:
            ok = False
            break
        got = land_piece(1, b, used, deadline)
        if got is None:
            ok = False
            break
        witness += got
        used |= set(got)
        if not verify_receipt(a - piece + 1, b, sorted(witness)):
            ok = False
            break
    if ok and verify_receipt(a, b, sorted(witness)):
        return sorted(witness), f"D:pure-peel[{a} x 1/{b} disjoint fresh windows]"
    return None, "E:all-strategies-exhausted"

# ------------------------------------------------- main
def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    st = load_state()
    targets = universe(B_HI)
    if which != "all":
        keys = set(which.split(","))
        targets = [(a, b) for a, b in targets if f"{a}/{b}" in keys]
    print(f"=== W66-P306-E CLOSING ENGINE v2 ===", flush=True)
    print(f"bootstrap: {len(st['done'])} verified receipts in state; "
          f"{len(targets)} targets queued", flush=True)
    for (a, b) in targets:
        key = f"{a}/{b}"
        if key in st["done"]:
            continue
        if time.time() - T_START > BUDGET_S:
            print(f"[budget stop] done={len(st['done'])}", flush=True)
            break
        t0 = time.time()
        deadline = t0 + TARGET_CAP_S
        dens, method = solve_ab(a, b, st, deadline)
        if dens is not None and verify_receipt(a, b, dens, loud=True) \
                and integer_crosscheck(a, b, dens):
            st["done"][key] = dens
            if key in st["failed"]:
                st["failed"].remove(key)
            st.setdefault("landed_w66", []).append(key)
            fname = emit_receipt(a, b, dens, method)
            print(f"  LANDED {key}: {len(dens)} terms, max den {dens[-1]}, "
                  f"{method}, receipt {fname} [{time.time() - t0:.1f}s]", flush=True)
        else:
            if key not in st["failed"]:
                st["failed"].append(key)
            print(f"  RESIST {key}: {method} [{time.time() - t0:.1f}s]", flush=True)
        save_state(st)
    print(f"\n=== #306 W66E CENSUS: {len(st['done'])}/{len(universe(B_HI))} "
          f"(b squarefree <= {B_HI}) ===", flush=True)
    if st.get("failed"):
        print(f"resisted: {st['failed']}", flush=True)
    save_state(st)


if __name__ == "__main__":
    main()
