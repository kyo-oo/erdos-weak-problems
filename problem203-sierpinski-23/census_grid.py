#!/usr/bin/env python3
"""
census_grid.py — W63-B3: the TORUS CENSUS GRID + the covering-budget ceiling
curve for Erdős #203.

METHOD (complete + certified): the primes compatible with the torus
(Z/L2)x(Z/L3) are EXACTLY the prime factors of G(L2,L3) := gcd(2^L2-1,
3^L3-1) (ord_q(2) | L2 <=> q | 2^L2-1).  Each contributes density
1/h, h = lcm(o2,o3) | lcm(L2,L3).  Census: G -> trial division by all
primes <= 1e8 (complete for that range) -> Brent-rho on the residual
(time-capped, honest residual bound banked).

Outputs:
  census_grid.json  — per torus: family size, budget, residual bits
  (the strategic map: where does the density lane actually live?)
"""
import sys, os, json, math, time
import numpy as np
import gmpy2

HERE = os.path.dirname(os.path.abspath(__file__))
SWEEP = 100_000_000
TORI = [
    # (L2, L3) candidates: symmetric growth of the divisor lattice
    (27720, 27720),      # 2^3 3^2 5 7 11      (the certified 42-prime census)
    (55440, 55440),      # 2^4 3^2 5 7 11
    (83160, 83160),      # 2^3 3^3 5 7 11
    (110880, 110880),    # 2^5 3^2 5 7 11
    (166320, 166320),    # 2^4 3^3 5 7 11
    (221760, 221760),    # 2^6 3^2 5 7 11
    (360360, 360360),    # 2^3 3^2 5 7 11 13
    (720720, 720720),    # 2^4 3^2 5 7 11 13
    (12252240, 12252240),# lcm(1..18) = 2^4 3^2 5 7 11 13 17
]

def log(s): print(s, flush=True)

def sieve_np(n):
    flags = np.ones(n + 1, dtype=bool); flags[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if flags[p]: flags[p * p::p] = False
    return np.nonzero(flags)[0].astype(np.int64)

def order_of(a, p, fs_p1):
    o = p - 1
    for q in fs_p1:
        while o % q == 0 and pow(a, o // q, p) == 1: o //= q
    return o

def factor_small(x):
    fs = set(); d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    return fs

def brent_rho(n, seed, max_iters=1_500_000):
    if n % 2 == 0: return 2
    if n % 3 == 0: return 3
    c = gmpy2.mpz(seed)
    y = gmpy2.mpz(2) if seed % 3 == 0 else gmpy2.mpz(seed)
    x = y; q = gmpy2.mpz(1); it = 0
    while it < max_iters:
        y = (y * y + c) % n
        q = q * abs(x - y) % n
        it += 1
        if it % 96 == 0:
            d = gmpy2.gcd(q, n)
            if d != 1:
                if d != n: return int(d)
                return None
            x = y; q = gmpy2.mpz(1)
    return None

def census(L2, L3, P, tcap=90):
    t0 = time.time()
    G = gmpy2.gcd((gmpy2.mpz(2) ** L2) - 1, (gmpy2.mpz(3) ** L3) - 1)
    gbits = G.bit_length()
    found = []
    for pv in P:
        p = int(pv)
        if p < 5: continue
        if G % p == 0:
            found.append(p)
            while G % p == 0: G //= p
    resid_bits = G.bit_length()
    # rho phase on residual (time-capped)
    rho_peeled = []
    R = G
    seed = 3
    while R.bit_length() > 2 and time.time() - t0 < tcap:
        if gmpy2.is_prime(R):
            rho_peeled.append(int(R)); R = gmpy2.mpz(1); break
        d = brent_rho(int(R), seed)
        if d is None:
            seed += 2
            if seed > 400: break
            continue
        stack = [gmpy2.mpz(d)]
        while stack:
            u = stack.pop()
            if u == 1: continue
            if gmpy2.is_prime(u):
                while R % u == 0: R //= u
                rho_peeled.append(int(u))
            else:
                d2 = brent_rho(int(u), seed)
                if d2 is None: seed += 2; stack.append(u)
                else: stack.append(gmpy2.mpz(d2)); stack.append(u // gmpy2.mpz(d2))
        seed += 2
    allp = sorted(set(found + rho_peeled))
    fam = []
    for p in allp:
        if p < 5: continue
        fs = factor_small(p - 1)
        o2 = order_of(2, p, fs); o3 = order_of(3, p, fs)
        if L2 % o2 == 0 and L3 % o3 == 0:
            fam.append([p, o2 * o3 // math.gcd(o2, o3), o2, o3])
    fam.sort(key=lambda r: (r[1], r[0]))
    budget = sum(1.0 / r[1] for r in fam)
    return {"L2": L2, "L3": L3, "G_bits": gbits, "n_le_1e8": len(found),
            "rho_extra": len(rho_peeled), "resid_bits": int(R.bit_length()),
            "family": len(fam), "budget": budget,
            "rows": fam, "wall": time.time() - t0}

def main():
    t0 = time.time()
    log(f"[sieve] primes <= {SWEEP} ...")
    P = sieve_np(SWEEP)
    log(f"[sieve] {len(P)} primes ({time.time()-t0:.1f}s)")
    out_path = os.path.join(HERE, "census_grid.json")
    results = []
    for (L2, L3) in TORI:
        r = census(L2, L3, P)
        results.append(r)
        log(f"[torus {L2}x{L3}] family={r['family']} budget={r['budget']:.4f} "
            f"(G {r['G_bits']} bits; <=1e8: {r['n_le_1e8']}; rho+{r['rho_extra']}; "
            f"residual {r['resid_bits']} bits) [{r['wall']:.0f}s]")
        # incremental save
        json.dump(results, open(out_path, "w"))
    log(f"[done] {time.time()-t0:.0f}s total")

if __name__ == "__main__":
    main()
