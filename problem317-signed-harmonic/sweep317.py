#!/usr/bin/env python3
"""Erdos #317 Part-2 engine: verify Theorem A's hypothesis for all n in [5, N].

Hypothesis H(n): some prime p in (n/2, n] has u_p = lcm(1..n)/p NOT ≡ ±1 (mod p).
By Theorem A (DERIVATION.md §3), H(n) implies: no delta in {-1,0,1}^n has
sum delta_k/k = ±1/L_n.

Method: for each prime p, sweep n in [p, 2p): u_p(n) = u_p(p) * E(p,n) mod p,
where u_p(p) = lcm(1..p-1) mod p and E(p,n) = product of the "bump factors"
entering lcm as n crosses prime powers in (p, n] (a prime q entering adds q;
a prime power q^e entering adds q).

Independent cross-check: for n in [5, 200] the giant-lcm direct method
(math.lcm of 1..n, then (L//p) % p) must agree with the sweep.
"""
import sys
from sympy import primerange

def direct_check(n):
    import math
    L = math.lcm(*range(1, n + 1))
    for p in primerange(n // 2 + 1, n + 1):
        u = (L // p) % p
        if u != 1 and u != p - 1:
            return True, p, u
    return False, None, None

def L_mod(m, mod):
    r = 1
    for q in primerange(2, m + 1):
        e, pk = 1, q
        while pk * q <= m:
            pk *= q; e += 1
        r = (r * pow(q, e, mod)) % mod
    return r

def sweep(N, crosscheck=200):
    primes = list(primerange(2, 2 * N + 10))
    events = []
    for q in primerange(2, N + 1):
        pk = q * q
        while pk <= 2 * N:
            events.append((pk, q)); pk *= q
    events.sort()
    killed = [False] * (N + 1)
    witness = [None] * (N + 1)
    checks = 0
    for pi, p in enumerate(primes):
        if p > N: break
        up0 = L_mod(p - 1, p)
        ev = [(q, q) for q in primes[pi+1:] if q < 2 * p] + \
             [(m, q) for (m, q) in events if p < m < 2 * p]
        ev.sort()
        E, ei = 1, 0
        for n in range(p, min(2 * p, N + 1)):
            while ei < len(ev) and ev[ei][0] <= n:
                E = (E * ev[ei][1]) % p; ei += 1
            u = (up0 * E) % p
            checks += 1
            if n >= 5 and u != 1 and u != p - 1 and not killed[n]:
                killed[n] = True; witness[n] = (p, u)
    degenerate = [n for n in range(5, N + 1) if not killed[n]]
    # cross-check against the direct method
    for n in range(5, min(crosscheck, N) + 1):
        ok, p, u = direct_check(n)
        assert ok == killed[n], f"MISMATCH at n={n}"
    return degenerate, checks, witness

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    deg, checks, wit = sweep(N)
    print(f"n in [5,{N}]: {checks} prime-tests; degenerate n's: {deg}")
    print("VERDICT: " + ("ALL n KILLED (Theorem A applies everywhere)"
          if not deg else f"{len(deg)} degenerates need the cascade"))
    if N <= 200:
        for n in range(5, N + 1):
            print(f"  n={n}: killer p={wit[n][0]}, u_p={wit[n][1]}")
