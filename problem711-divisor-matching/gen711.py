#!/usr/bin/env python3
"""Witness-table generator for the P711 Lean extension (task 1-a).

Generates:
  (1) wit4/wit5/wit6 : per-residue OFFSET tables for THEOREM U at n = 4,5,6
      (window (m, m+2n-1): offsets c_k with 1 <= c <= 2n-2, distinct,
       (r + c_k) % k == 0 for r = m % L, L = lcm(1..n)).
  (2) witN : per-n VALUE tables for THEOREM N at n = 2..24
      (window (n, n+3n/2+1): values a_k with n < a_k < n+F, k | a_k,
       distinct).
Matching: descending-greatest greedy (engine_round3.py port) + exact Kuhn
augmenting fallback. Independent re-verification of every table afterwards.

Output: gen711_out.txt with ready-to-paste Lean defs + verification log.
"""
import sys
from math import gcd

BASE = "/home/z/erdos-weak-problems/problem711-divisor-matching"
OUT = open(f"{BASE}/gen711_out.txt", "w", buffering=1)


def log(s=""):
    print(s)
    OUT.write(s + "\n")


def lcm_upto(n):
    L = 1
    for k in range(1, n + 1):
        L = L * k // gcd(L, k)
    return L


def greedy_desc(n, lo, hi, mod_of):
    """Descending-greatest greedy on keys n..2 (engine port).
    mod_of(k) -> residue constraint: values v with v % k == mod_of(k).
    Returns dict k->v or None. Key 1: any free slot."""
    used = set()
    assign = {}

    def largest_mult(k):
        r = mod_of(k)
        v = hi - ((hi - r) % k)
        while v >= lo and v in used:
            v -= k
        return v if v >= lo else None

    for k in range(n, 1, -1):
        v = largest_mult(k)
        if v is None:
            return None
        used.add(v)
        assign[k] = v
    for v in range(lo, hi + 1):
        if v not in used:
            assign[1] = v
            return assign
    return None


def kuhn(n, lo, hi, mod_of):
    """Exact bipartite matching keys n..1 vs values in [lo,hi] (Kuhn)."""
    matchR = {}  # value -> key

    def try_k(k, seen):
        r = mod_of(k)
        v = lo + (r - lo) % k
        while v <= hi:
            if v not in seen:
                seen[v] = True
                if v not in matchR or try_k(matchR[v], seen):
                    matchR[v] = k
                    return True
            v += k
        return False

    for k in range(n, 1, -1):
        if not try_k(k, {}):
            return None
    assign = {vk[1]: vk[0] for vk in matchR.items()}
    for v in range(lo, hi + 1):
        if v not in matchR:
            assign[1] = v
            return assign
    return None


def matchable(n, lo, hi, mod_of):
    g = greedy_desc(n, lo, hi, mod_of)
    if g is not None:
        return g, "greedy"
    k = kuhn(n, lo, hi, mod_of)
    if k is not None:
        return k, "kuhn"
    return None, "FAIL"


# ================= (1) THEOREM U tables n = 4,5,6 =================
def gen_u(n):
    L = lcm_upto(n)
    rows = []
    methods = {}
    for r in range(L):
        # offsets c in [1, 2n-2] with c % k == (-r) % k, i.e. (r + c) % k == 0
        def mod_of(k, r=r):
            return (-(r)) % k
        lo, hi = 1, 2 * n - 2
        got, method = matchable(n, lo, hi, mod_of)
        if got is None:
            log(f"  !!! U-FAIL n={n} r={r}")
            return None
        methods[method] = methods.get(method, 0) + 1
        cs = [got[k] for k in range(1, n + 1)]
        rows.append(cs)
    return rows, methods


def verify_u(n, rows):
    L = lcm_upto(n)
    assert len(rows) == L
    for r, cs in enumerate(rows):
        assert len(cs) == n, (n, r)
        for k in range(1, n + 1):
            c = cs[k - 1]
            assert 1 <= c <= 2 * n - 2, (n, r, k, c)
            assert (r + c) % k == 0, (n, r, k, c)
        assert len(set(cs)) == n, (n, r, cs)
    return True


# ================= (2) THEOREM N tables n = 2..24 =================
def gen_n():
    rows = {}
    for n in range(2, 25):
        F = (3 * n) // 2 + 1
        lo, hi = n + 1, n + F - 1  # open window (n, n+F)

        def mod_of(k, n=n):
            return 0  # value itself must be divisible by k

        got, method = matchable(n, lo, hi, mod_of)
        if got is None:
            log(f"  !!! N-FAIL n={n}")
            return None
        rows[n] = [got[k] for k in range(1, n + 1)]
    return rows


def verify_n(rows):
    for n, vals in rows.items():
        F = (3 * n) // 2 + 1
        assert len(vals) == n
        for k in range(1, n + 1):
            a = vals[k - 1]
            assert n < a < n + F, (n, k, a, F)
            assert a % k == 0, (n, k, a)
        assert len(set(vals)) == n, (n, vals)
    return True


# ================= Lean emitters =================
def lean_list(l):
    return "[" + ", ".join(str(x) for x in l) + "]"


def emit_u(name, n, rows):
    lines = [f"def {name} : Nat → List Nat := fun r =>",
             "  ["]
    for r, cs in enumerate(rows):
        lines.append(f"   {lean_list(cs)},")
    lines.append("  ].getD r []")
    return "\n".join(lines)


def emit_n(name, rows):
    lines = [f"def {name} : Nat → List Nat := fun n =>",
             "  ["]
    # index n: entries 0..24
    for n in range(0, 25):
        v = rows.get(n, [])
        lines.append(f"   {lean_list(v)},")
    lines.append("  ].getD n []")
    return "\n".join(lines)


log("=" * 78)
log("P711 WITNESS TABLE GENERATOR (task 1-a): THEOREM U n<=6 + THEOREM N n<=24")
log("=" * 78)

alldefs = []
for n in (4, 5, 6):
    log(f"generating U-table n={n} ...")
    rows, methods = gen_u(n)
    if rows is None:
        log(f"n={n}: FAILED")
        sys.exit(1)
    verify_u(n, rows)
    log(f"  n={n}: {len(rows)} residue rows, methods={methods}, verified OK")
    alldefs.append(emit_u(f"wit{n}", n, rows))

log("generating N-table n=2..24 ...")
nrows = gen_n()
if nrows is None:
    log("N FAILED")
    sys.exit(1)
verify_n(nrows)
log(f"  N-table: verified OK for n=2..24 (f(n,n) witnesses in window 3n/2+1)")
alldefs.append(emit_n("witN", nrows))

log("")
log("============ LEAN DEF BLOCK (paste into Erdos711.lean) ============")
for d in alldefs:
    log(d)
    log("")
log("============ END LEAN DEF BLOCK ============")
OUT.close()
print("DONE")
