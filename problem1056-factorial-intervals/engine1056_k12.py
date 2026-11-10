#!/usr/bin/env python3
"""
#1056 k=12 witness hunt (S043): scan primes beyond 52163 for a value
visited 13 times in the j! mod p chain (the structure law: k consecutive
intervals with products = 1 mod p  <=>  the j! chain visits one value k+1
times). The frontier stands at k=11 (p=52163, S030-S031 war).

Per prime p: build the chain f_j = j! mod p (j = 1..p-1), count the max
value frequency; report any value with >= 13 visits (candidate k=12), and
any with 12 visits (candidate k=11 new witness / structure data).
Tight loop: local vars, precomputed range, dict frequency.
"""
import sys

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    q = 3
    while q * q <= n:
        if n % q == 0: return False
        q += 2
    return True

def scan(p):
    """max frequency of any value in the j! mod p chain, j=1..p-1"""
    freq = {}
    f = 1
    best = 0; bestv = 0
    for j in range(2, p):
        f = (f * j) % p
        c = freq.get(f, 0) + 1
        freq[f] = c
        if c > best:
            best = c; bestv = f
            if c >= 13:
                return best, bestv
    return best, bestv

if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 52164
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    best_overall = 0
    for p in range(lo, hi):
        if p % 6 not in (1, 5):
            continue
        if not is_prime(p):
            continue
        b, v = scan(p)
        if b >= 12:
            print(f"#1056 CANDIDATE: p={p} maxfreq={b} value={v}", flush=True)
        if b > best_overall:
            best_overall = b
            print(f"  new best: p={p} freq={b}", flush=True)
    print(f"#1056 scan [{lo},{hi}): best frequency = {best_overall}")
