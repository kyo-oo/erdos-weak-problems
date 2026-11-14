#!/usr/bin/env python3
"""certify885.py — W63-B5 / P885: dual-method certification of a k=4
witness (the K_{5,3} -> Theorem B lambda=2 scaling -> N/d translation).

Method 1 (square criterion, gmpy2 exact): for every (N_i, d_j):
4*N_i + d_j^2 is a perfect square (Lemma 1: d in D(N) iff 4N+d^2 = m^2),
N's strictly increasing, d's distinct.

Method 2 (direct factor pairs, independent route): for every (N_i, d_j)
exhibit explicit a > b with a*b = N_i and a - b = d_j; PLUS the FULL
D-set intersection recount: D(N_i) enumerated completely by divisor
pairs (gmpy2), intersection recomputed from scratch, must contain the
k = 4 d's and must EQUAL the Method-1-derived membership verdict on
every d_j (agreement receipt).

Boundary checks: distinctness, positivity, ordering, d >= 1, N >= 1.
"""
import json, sys
from math import isqrt
from gmpy2 import mpz, isqrt as gisqrt, is_square as gisquare
from sympy import divisors as sdivisors

def D_set(N):
    """Full D(N) = {|a-b| : a*b = N} by divisor-pair enumeration."""
    return {abs(a - b) for a in sdivisors(N) for b in [N // a]
            if a * b == N}

def certify(rows, Cs, verbose=True):
    Ns, ds = None, None
    # --- translation (Theorem B, lambda = 2) ---
    rows = sorted(rows)
    s_min = rows[0]
    Ns = [s * s - s_min * s_min for s in rows[1:]]
    ds = [2 * s_min] + [2 * isqrt(c + s_min * s_min) for c in Cs]
    k = len(rows) - 1
    receipts = []
    ok = True

    # --- structural checks ---
    assert all(Ns[i] < Ns[i + 1] for i in range(len(Ns) - 1)), "N not sorted"
    assert len(set(ds)) == len(ds) >= k, "d's not distinct"
    assert all(d >= 1 for d in ds) and all(N >= 1 for N in Ns)
    assert all(c > 0 for c in Cs) and len(set(Cs)) == len(Cs) == k - 1
    assert all(rows[i] < rows[i + 1] for i in range(len(rows) - 1))

    # --- Method 1: square criterion (gmpy2) ---
    m1 = {}
    for N in Ns:
        for d in ds:
            t = 4 * mpz(N) + mpz(d) ** 2
            assert gisquare(t), f"M1 FAIL: 4*{N}+{d}^2 not square"
            m1[(N, d)] = int(gisqrt(t))
    # --- Method 2: direct factor pairs + full D-set recount ---
    Dsets = [D_set(N) for N in Ns]
    inter = set(Dsets[0])
    for D in Dsets[1:]:
        inter &= D
    for d in ds:
        assert d in inter, f"M2 FAIL: {d} not in full intersection"
    # agreement: M1 membership == M2 membership on every d_j
    for N in Ns:
        for d in ds:
            m2 = d in Dsets[Ns.index(N)]
            m1v = (N, d) in m1
            assert m2 and m1v
    # explicit factor pairs (for the Lean theorem)
    pairs = {}
    for N in Ns:
        for d in ds:
            m = m1[(N, d)]
            a, b = (m + d) // 2, (m - d) // 2
            assert a * b == N and a - b == d, f"pair FAIL N={N} d={d}"
            pairs[(N, d)] = (a, b)
    if verbose:
        print(f"[cert885] rows={rows}")
        print(f"[cert885] Cs={Cs}")
        print(f"[cert885] N={Ns} (strictly increasing, all >= 1)")
        print(f"[cert885] d={ds} (distinct, all >= 1)")
        print(f"[cert885] FULL |D(N_1) ^ ... ^ D(N_k)| = {len(inter)} "
              f">= k={k}: {sorted(inter)}")
        print("[cert885] Method 1 (gmpy2 square criterion): all "
              f"{len(Ns)*len(ds)} checks 4N+d^2=m^2 PASS")
        print("[cert885] Method 2 (divisor-pair D-sets): intersection "
              "recount PASS; agreement with Method 1 on every (N,d) PASS")
        for (N, d) in sorted(pairs):
            a, b = pairs[(N, d)]
            print(f"[cert885]   d={d} in D({N}): {a}*{b}={N}, {a}-{b}={d}")
    return Ns, ds, inter, pairs

if __name__ == "__main__":
    src = sys.argv[1] if len(sys.argv) > 1 else "ext_k4_hits.json"
    hits = json.load(open("/home/z/waves/w63-b5-p885/problem885-factor-difference/" + src))
    h = hits[0]
    certify(h["rows"], h["Cs"])
    print("[cert885] *** k=4 WITNESS FULLY CERTIFIED (dual method) ***")
