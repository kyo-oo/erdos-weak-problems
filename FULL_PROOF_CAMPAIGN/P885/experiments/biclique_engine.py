#!/usr/bin/env python3
"""P885 factor-difference sets — biclique square-grid engine.

Core reduction (PROOF.md §1):
  #885(k) TRUE  <=>  exists K_{k+1, k-1}: (k+1) distinct ints s_0..s_k and
  (k-1) distinct positive ints C_2..C_k with ALL (k+1)(k-1) sums
  s_i^2 + C_j perfect squares  (then d_1 = min s, d_j = sqrt(C_j + s_min^2),
  N_i = (s_i^2 - s_min^2)/4, scaled by lambda=2 if parities mixed).

Engine: row-pair indexing.  For any two rows (s0,s1) of a config, every C of
the config lies in G(s0,s1) = {m0^2 - s0^2 : (p,q) factor pair of
Delta = s1^2 - s0^2, m0 = (q-p)/2 > s0}.  Enumerate (u,v) = (s1-s0, s1+s0),
keep pairs with tau(u*v) >= tau_min, build G, then pairwise common-row
structure via factor pairs of delta = |C_a - C_b| (EXACT, no range cuts),
then (k-1)-subset scan for >= k+1 common rows.
"""
import sys, time, math
from math import isqrt, gcd
from itertools import combinations
from collections import defaultdict

import numpy as np

# ---------- SPF sieve ----------
def build_spf(limit):
    spf = np.zeros(limit + 1, dtype=np.int32)
    spf[1] = 1
    for i in range(2, isqrt(limit) + 1):
        if spf[i] == 0:
            spf[i*i::i] = np.where(spf[i*i::i] == 0, i, spf[i*i::i])
    # remaining zeros are primes
    mask = spf == 0
    idx = np.nonzero(mask)[0]
    spf[idx] = idx
    return spf

SPF_LIMIT = 30_000_000
print(f"[engine] building SPF sieve to {SPF_LIMIT} ...", flush=True)
_t0 = time.time()
SPF = build_spf(SPF_LIMIT)
print(f"[engine] SPF ready ({time.time()-_t0:.1f}s)", flush=True)

from sympy import factorint as _sympy_factorint

# ---- fast general factorizer: trial + Pollard-Brent rho ----
_SMALL_PRIMES = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

def _brent_rho(n):
    if n % 2 == 0: return 2
    import random
    for c in [1,3,5,7,11,13,17]:
        x = y = 2; d = 1; r = 1; q = 1; m = 128
        while d == 1:
            x = y
            for _ in range(r):
                y = (y*y + c) % n
            k = 0
            while k < r and d == 1:
                ys = y
                for _ in range(min(m, r-k)):
                    y = (y*y + c) % n
                    q = q * abs(x-y) % n
                d = math.gcd(q, n)
                k += m
            r <<= 1
        if d == n:
            d = 1; y = ys
            while d == 1:
                y = (y*y + c) % n
                d = math.gcd(abs(x-y), n)
        if 1 < d < n:
            return d
    return n

def _factor_general(n, out):
    for p in _SMALL_PRIMES:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1: continue
        if m <= SPF_LIMIT:
            f = factorize(m)
            for p, e in f.items(): out[p] = out.get(p, 0) + e
            continue
        if _is_prime(m):
            out[m] = out.get(m, 0) + 1
            continue
        d = _brent_rho(m)
        stack.append(d); stack.append(m//d)

def _is_prime(n):
    if n < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def factorize(n):
    """Return dict prime->exp (SPF if in range, else rho)."""
    if n <= SPF_LIMIT:
        f = {}
        while n > 1:
            p = int(SPF[n])
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            f[p] = e
        return f
    out = {}
    _factor_general(n, out)
    return out

def divisors(n):
    """All divisors of n (n <= SPF_LIMIT)."""
    f = factorize(n)
    divs = [1]
    for p, e in f.items():
        divs = [d * p**k for d in divs for k in range(e + 1)]
    return divs

def factor_pairs_parity(n):
    """Yield (p, q), p*q = n, p < q, p == q (mod 2) — the pairs usable for
    difference-of-squares.  Returns [] if n % 4 == 2.  For n odd: odd pairs
    (halved differences).  For n % 4 == 0: even pairs (p=2p', q=2q')."""
    if n % 2 == 1:
        out = []
        for p in divisors(n):
            q = n // p
            if p < q:
                out.append((p, q))
        return out
    if n % 4 == 2:
        return []
    m = n // 4
    out = []
    for p in divisors(m):
        q = m // p
        if p < q:
            out.append((p, q))   # actual pair (2p, 2q); caller uses (q-p), (q+p)
    return out

C_CAP = 10**13   # skip absurd C candidates (unbalanced factor pairs)

def G_candidates(s0, s1):
    """All C with 0 < C <= C_CAP, s0^2 + C = m0^2 and s1^2 + C = m1^2.
    Returns list of (C, m0, m1)."""
    Delta = s1 * s1 - s0 * s0
    out = []
    if Delta % 2 == 1:
        for p, q in factor_pairs_parity(Delta):
            m0 = (q - p) // 2
            m1 = (q + p) // 2
            if m0 > s0:
                C = m0 * m0 - s0 * s0
                if C <= C_CAP:
                    out.append((C, m0, m1))
    elif Delta % 4 == 0:
        for p, q in factor_pairs_parity(Delta):
            m0 = q - p
            m1 = q + p
            if m0 > s0:
                C = m0 * m0 - s0 * s0
                if C <= C_CAP:
                    out.append((C, m0, m1))
    # Delta % 4 == 2 impossible for squares
    return out

def common_rows(C_lo, C_hi):
    """All s >= 1 with s^2 + C_lo = y^2 and s^2 + C_hi = z^2 (C_lo < C_hi).
    Exact: via factor pairs of delta = C_hi - C_lo."""
    delta = C_hi - C_lo
    rows = []
    if delta % 2 == 1:
        for p, q in factor_pairs_parity(delta):
            y = (q - p) // 2
            s2 = y * y - C_lo
            if s2 > 0:
                s = isqrt(s2)
                if s * s == s2:
                    rows.append(s)
    elif delta % 4 == 0:
        for p, q in factor_pairs_parity(delta):
            y = q - p
            s2 = y * y - C_lo
            if s2 > 0:
                s = isqrt(s2)
                if s * s == s2:
                    rows.append(s)
    return rows

def verify_config(rows, Cs, quiet=True):
    """Full verification: all |rows|*|Cs| sums squares; rows/Cs distinct."""
    assert len(set(rows)) == len(rows) and len(set(Cs)) == len(Cs)
    assert all(c > 0 for c in Cs)
    M = {}
    for s in rows:
        for c in Cs:
            t = s * s + c
            m = isqrt(t)
            if m * m != t:
                return None
            M[(s, c)] = m
    return M

def build_witness(rows, Cs):
    """From a verified config build the #885 witness (lambda=2 scaling).
    Returns (Ns, ds, a_matrix, cert_text) with N_i = a*(a+d_j) certificates."""
    rows = sorted(rows)
    s_min = rows[0]
    Ns = [s * s - s_min * s_min for s in rows[1:]]          # lambda=2 -> /1
    ds = [2 * s_min] + [2 * isqrt(c + s_min * s_min) for c in Cs]
    # note: with lambda=2: N'_i = s_i^2 - s_min^2, d'_1 = 2 s_min,
    # d'_j = 2*sqrt(C_j + s_min^2);  a'_{ij} = m_{ij} - m_{min,j}
    a = {}
    for s in rows[1:]:
        for j, c in enumerate(Cs):
            a[(s, j)] = isqrt(s * s + c) - isqrt(s_min * s_min + c)
    return Ns, ds, a

def hunt(k, s1_max, tau_min, u_max=None, report_every=20000, time_budget=None):
    """Hunt K_{k+1, k-1}: (k+1) rows, (k-1) positive C's, all sums squares.
    Enumerate (u,v) = (s1-s0, s1+s0) with s1 <= s1_max, tau(u*v) >= tau_min."""
    need_rows = k + 1
    need_Cs = k - 1
    u_max = u_max or s1_max
    # tau sieve up to s1_max^2 (numpy, int32)
    LIM = s1_max * s1_max
    print(f"[hunt k={k}] tau-sieve to {LIM} ...", flush=True)
    _t = time.time()
    tau = np.zeros(LIM + 1, dtype=np.int32)
    for d in range(1, isqrt(LIM) + 1):
        tau[d::d] += 1     # tau[n] = # divisors <= sqrt(n); *2 - [square] approx
    print(f"[hunt k={k}] tau-sieve done ({time.time()-_t:.1f}s)", flush=True)
    # note: tau[n] here = #{d | n : d <= sqrt(n)}; true divisor count ~ 2*tau[n]

    n_pairs = 0
    t0 = time.time()
    hits = []
    for u in range(1, u_max + 1):
        # v > u, v == u (mod 2), s1 = (u+v)/2 <= s1_max -> v <= 2*s1_max - u
        vstart = u + 2
        vend = min(2 * s1_max - u, u + 2 * (s1_max - u))
        for v in range(vstart, vend + 1, 2):
            D = u * v
            if 2 * int(tau[D]) < tau_min:
                continue
            s0 = (v - u) // 2
            s1 = (u + v) // 2
            n_pairs += 1
            G = G_candidates(s0, s1)
            g = len(G)
            if g < need_Cs:
                continue
            # pairwise common rows
            adj = defaultdict(set)
            pairrows = {}
            for a in range(g):
                Ca = G[a][0]
                for b in range(a + 1, g):
                    Cb = G[b][0]
                    lo, hi = (Ca, Cb) if Ca < Cb else (Cb, Ca)
                    rr = common_rows(lo, hi)
                    if len(rr) >= need_rows:
                        pairrows[(a, b)] = rr
                        for s in rr:
                            adj[s].add(a)
                            adj[s].add(b)
            if not pairrows:
                continue
            # (k-1)-subset scan
            cnt = defaultdict(int)
            for s, nb in adj.items():
                if len(nb) >= need_Cs:
                    for combo in combinations(sorted(nb), need_Cs):
                        cnt[combo] += 1
            for combo, c in cnt.items():
                if c >= need_rows:
                    Cs = [G[i][0] for i in combo]
                    rows = sorted(s for s, nb in adj.items() if set(combo) <= nb)
                    # verify exact
                    M = verify_config(rows, Cs)
                    if M is not None and len(rows) >= need_rows:
                        rows6 = rows[:need_rows]
                        M = verify_config(rows6, Cs)
                        if M is not None:
                            hits.append((rows6, Cs))
                            print(f"*** HIT k={k}: rows={rows6} Cs={Cs}", flush=True)
        if u % 100 == 0:
            print(f"  [hunt] u={u} pairs={n_pairs} t={time.time()-t0:.0f}s hits={len(hits)}", flush=True)
            if time_budget and time.time() - t0 > time_budget:
                print("  [hunt] time budget reached"); break
    print(f"[hunt k={k}] done: pairs={n_pairs} hits={len(hits)} time={time.time()-t0:.0f}s")
    return hits

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "k3"
    if mode == "k3":
        # validation: K_{4,2} — must refind in-house (rows 2,22,46,134 / C 1365,3360)
        hits = hunt(3, 200, 12)
        for rows, Cs in hits[:10]:
            print(rows, Cs)
    elif mode == "k4":
        hits = hunt(4, int(sys.argv[2]), int(sys.argv[3]))
    elif mode == "k5":
        hits = hunt(5, int(sys.argv[2]), int(sys.argv[3]))
