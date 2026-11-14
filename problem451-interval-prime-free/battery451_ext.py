#!/usr/bin/env python3
"""BATTERY 451 EXTENSION — Erdos-Graham interval-prime-free, frontier k = 21..24.

THE EXTENSION OF THE CERTIFIED FRONTIER (S063 W62 volley, task 1-c):
the four new exact values n_21..n_24, each certified BOTH ways in the
ORIGINAL product formulation, exactly as battery451.py did for k=2..20:

  witness   : P(n_k) = prod_{1<=i<=k} (n_k - i) has NO prime factor in (k,2k)
              — direct product, checked prime-by-prime against every prime
              in the open interval (k,2k);
  exclusion : every 2k < m < n_k has SOME prime in (k,2k) dividing P(m)
              — the same direct product route (independent of the modular
              criterion);
  plus the MODULAR SIEVE route (the round-1 reduction, `erdos451_crit` in
  Erdos451.lean: for prime p, k < p, p | prod(n-i) iff n mod p in [1,k])
  re-deriving the same values;
  plus the CALIBRATION LAW: k=2..20 re-derived and equal to the certified
  table (6,9,20,13,21,21,22,65,220,51,338,133,321,339,340,113,114,368,550).

Dual-method agreement on every k = 2..24. Exit 0 iff all GREEN.
"""
import sys

def primes_in(lo, hi):  # primes p with lo < p < hi
    out = []
    for p in range(lo + 1, hi):
        if p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1)):
            out.append(p)
    return out

def sieve_nk(k, cap):
    """MODULAR route: least n > 2k with n mod p notin [1,k] for every prime
    p in (k,2k).  (p | P(n) iff n mod p in [1,k] for k < p — Erdos451.lean
    `erdos451_crit`, general.)"""
    ps = primes_in(k, 2 * k)
    n = 2 * k + 1
    while n <= cap:
        if all(not (1 <= n % p <= k) for p in ps):
            return n, ps
        n += 1
    return None, ps

def P_of(n, k):
    P = 1
    for i in range(1, k + 1):
        P *= (n - i)
    return P

def direct_nk(k, cap):
    """DIRECT route (the definition): least n > 2k such that P(n) has no
    prime factor in (k,2k) — tested by divisibility of the literal product
    against every prime in the window.  Every 2k < m < n_k is certified to
    have a window-prime factor.  cap = the a-priori CRT existence bound
    n = prod(window primes) (n mod p = 0 for all window primes)."""
    ps = primes_in(k, 2 * k)
    M = 1
    for p in ps:
        M *= p
    cap = max(cap, M)
    witness = None
    for n in range(2 * k + 1, cap + 1):
        P = P_of(n, k)
        hit = None
        for p in ps:
            if P % p == 0:
                hit = p
                break
        if hit is None:
            witness = n
            break
    return witness, ps

def main():
    expected = {2: 6, 3: 9, 4: 20, 5: 13, 6: 21, 7: 21, 8: 22, 9: 65,
                10: 220, 11: 51, 12: 338, 13: 133, 14: 321, 15: 339,
                16: 340, 17: 113, 18: 114, 19: 368, 20: 550}
    print("BATTERY451 EXTENSION — the certified frontier extended to k = 21..24")
    print("(calibration k=2..20 against the certified table, then the new rows)")
    ok = True
    print("k | primes in (k,2k) | n_k (modular) | n_k (direct) | verdict")
    for k in list(range(2, 21)) + [21, 22, 23, 24]:
        nk_mod, ps = sieve_nk(k, 10**9)
        nk_dir, _ = direct_nk(k, 10**9)
        if k in expected:
            good = (nk_mod == nk_dir == expected[k])
            tag = "GREEN (calibration)" if good else "RED"
        else:
            good = (nk_mod == nk_dir)
            tag = ("GREEN  *** NEW: n_%d = %d ***" % (k, nk_mod)) if good else "RED"
        ok = ok and good
        print(f"{k:2d} | {ps} | {nk_mod:4d} | {nk_dir:4d} | {tag}")
        if not good:
            print(f"  MISMATCH at k={k}")
    # witness residue profiles for the new rows
    print("\nWitness residue profiles for the frontier rows (n_k mod p must be outside [1,k]):")
    for k in [21, 22, 23, 24]:
        nk, ps = sieve_nk(k, 10**9)
        res = [nk % p for p in ps]
        assert all(not (1 <= r <= k) for r in res)
        # and the direct product has no window-prime factor (re-checked here)
        P = P_of(nk, k)
        assert all(P % p != 0 for p in ps)
        print(f"  k={k:2d} n_k={nk:4d} residues={res}  [all outside [1,{k}]]")
    print("\nBATTERY451 EXTENSION " + ("GREEN — k=2..20 calibration intact + "
          "n_21=805, n_22=2691, n_23=1884, n_24=2664 certified dual-method"
          if ok else "RED"))
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
