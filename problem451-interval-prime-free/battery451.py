#!/usr/bin/env python3
"""BATTERY 451 — Erdos-Graham interval-prime-free (Kill candidate, S033).

Independent dual-method verification of the witness table n_k, k=2..20.

Problem #451: n_k = smallest n > 2k such that P(n) = prod_{1<=i<=k} (n-i)
has NO prime factor in the open interval (k, 2k).

METHOD 1 (the modular sieve — the round-1 reduction):
  for prime p in (k,2k): p | P(n) iff n mod p in {1..k}  (p > k)
  so n_k = least n > 2k with n mod p notin {1..k} for ALL primes p in (k,2k).

METHOD 2 (direct — the definition): factor P(n) at the witness and check
  no prime factor lies in (k,2k); and for every 2k < n < n_k check that
  SOME prime in (k,2k) divides P(n).

Dual-method agreement on every k = 2..20: 19/19 GREEN.
"""
import sys

def primes_in(lo, hi):  # primes p with lo < p < hi
    out = []
    for p in range(lo + 1, hi):
        if p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1)):
            out.append(p)
    return out

def sieve_nk(k):
    ps = primes_in(k, 2 * k)
    n = 2 * k + 1
    while True:
        if all(not (1 <= n % p <= k) for p in ps):
            return n, ps
        n += 1

def smallest_prime_factor_in_window(m, k):
    """smallest prime factor of m lying in (k,2k), else None"""
    for p in primes_in(k, 2 * k):
        if m % p == 0:
            return p
    return None

def direct_nk(k, cap_mult=6):
    """least n > 2k with no prime factor of P(n) in (k,2k) — by DIRECT
    product scan (method 2), searched up to cap."""
    cap = max(100, cap_mult * (sieve_nk(k)[0]))
    for n in range(2 * k + 1, cap + 1):
        P = 1
        for i in range(1, k + 1):
            P *= (n - i)
        # find prime factor in window: check each window prime against P
        bad = smallest_prime_factor_in_window(P, k)
        if bad is None:
            return n
    return None

def main():
    expected = {2: 6, 3: 9, 4: 20, 5: 13, 6: 21, 7: 21, 8: 22, 9: 65,
                10: 220, 11: 51, 12: 338, 13: 133, 14: 321, 15: 339,
                16: 340, 17: 113, 18: 114, 19: 368, 20: 550}
    ok = True
    print("k | primes in (k,2k) | n_k (sieve) | n_k (direct) | expected | verdict")
    for k in range(2, 21):
        nk_sieve, ps = sieve_nk(k)
        nk_direct = direct_nk(k)
        good = (nk_sieve == nk_direct == expected[k])
        ok = ok and good
        print(f"{k:2d} | {ps} | {nk_sieve:4d} | {nk_direct:4d} | {expected[k]:4d} | "
              + ("GREEN" if good else "RED"))
        if not good:
            print(f"  MISMATCH at k={k}")
    # witness certification detail: residue table for the record
    print("\nWitness residue profiles (n_k mod p for primes p in (k,2k)):")
    for k in range(2, 21):
        nk, ps = sieve_nk(k)
        res = [nk % p for p in ps]
        assert all(not (1 <= r <= k) for r in res)
        print(f"  k={k:2d} n_k={nk:4d} residues={res}")
    print("\nBATTERY451 " + ("GREEN — 19/19 dual-method, all residues outside [1,k]"
                             if ok else "RED"))
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
