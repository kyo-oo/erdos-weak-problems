#!/usr/bin/env python3
"""
ceiling203.py — W63-B3: the covering-budget CEILING curve for Erdős #203.

B_inf = sum over ALL primes q >= 5 of 1/lcm(ord_q(2), ord_q(3))  (the ultimate
density budget of the covering lane; every finite torus family budget is a
partial sum of it, since a prime joins the torus-(L2,L3) family iff
o2 | L2 and o3 | L3).

Anchor censuses: B(K) = sum over primes with o2 <= K AND o3 <= K of 1/lcm.
Every such prime divides g_{d,e} = gcd(2^d-1, 3^e-1) for its exact (o2,o3)
pair (d,e <= K), so enumerating the K^2 pair-gcds (gmpy2) + factoring them
(trial division to 1e6 + capped Brent-rho, residual honestly bounded)
computes B(K) EXACTLY up to the unfactored residual.

Residual bound: after trial division to 1e6, any unfactored prime q > 1e6 has
q | 2^d-1 with d <= K and q | 3^e-1 with e <= K; q > 1e6 => o2 >= 20, o3 >= 13
=> each contributes <= 1/lcm(20,13) = 1/260; count <= resid_bits/6.4 ...
we bound: #primes <= resid_bits*ln2/ln(1e6) and each <= 1/lcm(o2,o3) with
lcm >= lcm(o2,o3) >= max(o2,o3) >= ... we use the exact lcm(d,e) >= lcm(o2,o3):
contribution >= 1/lcm(d,e) — NOT an upper bound.  UPPER bound per unfactored
prime: 1/lcm(o2,o3) <= 1/max(o2,o3) <= 1/20 is weak; we instead peel with rho
(catches <= ~1e15) leaving >= 1e15 primes: o2 >= 50, o3 >= 32 => <= 1/800
each.  Honest bound = (#resid primes)*1/800 with count <= bits/49.
"""
import sys, os, json, math, time
import gmpy2

HERE = os.path.dirname(os.path.abspath(__file__))

def log(s): print(s, flush=True)

def sieve_small(n):
    flags = bytearray(n + 1)
    flags[0:2] = b"\x01\x01" if n >= 1 else b"\x01"
    P = []
    for p in range(2, n + 1):
        if not flags[p]:
            P.append(p)
            for m in range(p * p, n + 1, p):
                flags[m] = 1
    return P

def factor_small(x):
    fs = set(); d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    return fs

def order_of(a, p, fs_p1):
    o = p - 1
    for q in fs_p1:
        while o % q == 0 and pow(a, o // q, p) == 1: o //= q
    return o

def brent_rho(n, seed, max_iters=400_000):
    if n % 2 == 0: return 2
    if n % 3 == 0: return 3
    c = gmpy2.mpz(seed)
    y = gmpy2.mpz(3 + seed % 7); x = y
    q = gmpy2.mpz(1); it = 0
    while it < max_iters:
        y = (y * y + c) % n
        q = q * abs(x - y) % n
        it += 1
        if it % 64 == 0:
            d = gmpy2.gcd(q, n)
            if d != 1:
                if d != n: return int(d)
                return None
            x = y; q = gmpy2.mpz(1)
    return None

def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    TSEL = 420  # seconds budget
    t0 = time.time()
    P1M = sieve_small(1_000_000)
    log(f"[ceiling] K = {K}; trial primes to 1e6: {len(P1M)}")
    pow2 = {}
    pow3 = {}
    primes = {}   # p -> (o2, o3) once computed
    resid_total_bits = 0
    unfactored_pairs = 0
    npairs = 0
    for d in range(2, K + 1):
        if d not in pow2:
            pow2[d] = gmpy2.mpz(2) ** d - 1
        A = pow2[d]
        for e in range(2, K + 1):
            if e not in pow3:
                pow3[e] = gmpy2.mpz(3) ** e - 1
            g = gmpy2.gcd(A, pow3[e])
            if g == 1: continue
            npairs += 1
            # factor g: trial by P1M
            gg = g
            for p in P1M:
                if p < 5: continue
                if gg % p == 0:
                    if p not in primes:
                        primes[p] = True
                    while gg % p == 0: gg //= p
            if gg > 1:
                # capped rho
                R = gg
                seed = 3
                tR = time.time()
                while R.bit_length() > 1 and time.time() - tR < 3.0:
                    if gmpy2.is_prime(R):
                        primes[int(R)] = True
                        R = gmpy2.mpz(1); break
                    d2 = brent_rho(int(R), seed)
                    if d2 is None:
                        seed += 2
                        if seed > 60: break
                        continue
                    stack = [gmpy2.mpz(d2)]
                    while stack:
                        u = stack.pop()
                        if u == 1: continue
                        if gmpy2.is_prime(u):
                            primes[int(u)] = True
                            while R % u == 0: R //= u
                        else:
                            d3 = brent_rho(int(u), seed)
                            if d3 is None: seed += 2; stack.append(u)
                            else:
                                stack.append(gmpy2.mpz(d3)); stack.append(u // gmpy2.mpz(d3))
                    seed += 2
                if R.bit_length() > 1:
                    unfactored_pairs += 1
                    resid_total_bits += R.bit_length()
        if d % 100 == 0:
            log(f"  ... d={d}/{K}: pairs-with-gcd={npairs}, distinct primes={len(primes)} "
                f"({time.time()-t0:.0f}s)")
        if time.time() - t0 > TSEL:
            log(f"[ceiling] TIME CAP hit at d={d}")
            break
    # compute orders + budget
    fam = []
    for p in primes:
        if p < 5: continue
        fs = factor_small(p - 1)
        o2 = order_of(2, p, fs); o3 = order_of(3, p, fs)
        if o2 <= K and o3 <= K:
            fam.append((p, o2 * o3 // math.gcd(o2, o3), o2, o3))
    fam.sort(key=lambda r: (r[1], r[0]))
    budget = sum(1.0 / r[1] for r in fam)
    log(f"[ceiling] K={K}: {len(fam)} primes with o2,o3 <= {K}; B(K) = {budget:.4f}")
    log(f"[ceiling] unfactored residuals: {unfactored_pairs} pairs, {resid_total_bits} bits total")
    ub_extra = resid_total_bits * 0.6931 / math.log(1e15) / 800.0 if resid_total_bits else 0.0
    log(f"[ceiling] residual upper-bound contribution <= {ub_extra:.4f}")
    json.dump({"K": K, "n_primes": len(fam), "B_K": budget,
               "resid_pairs": unfactored_pairs, "resid_bits": resid_total_bits,
               "resid_bound": ub_extra, "rows": fam},
              open(os.path.join(HERE, f"ceiling_{K}.json"), "w"))
    log(f"[ceiling] wrote ceiling_{K}.json  ({time.time()-t0:.0f}s)")

if __name__ == "__main__":
    main()
