#!/usr/bin/env python3
"""BATTERY 1072 — Erdos-Hardy-Subbarao factorial chain / Wilson-pair law
(Kill candidate, S033).

Problem #1072: f(p) = least n with n! == -1 (mod p). Open: infinitude of
f(p) = p-1 primes (Wilson-only); f(p)/p -> 0 a.e.

THE KILL CONTENT — THE WILSON-PAIR LAW:
  If n! == -1 (mod p) and 1 <= n <= p-2, then (p-1-n)! == (-1)^(p-1-n) (mod p).

Wilson-free pairing identity behind it (proved generally in the kernel):
  n! * (p-1-n)! == (-1)^(p-1-n) * (p-1)!  (mod p)

Battery: full census over primes 5 <= p < 10^4 —
  (a) every solution instance satisfies the pairing law;
  (b) Wilson-only prime count (f(p) = p-1, i.e. NO smaller n works);
  (c) the named first extra-solution primes;
  (d) census histogram matches S032 round 1.
"""
import sys

def primes_below(n):
    sieve = [True] * n
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, n, i):
                sieve[j] = False
    return [i for i in range(n) if sieve[i]]

def fact_chain_solutions(p):
    """all n in [1, p-1] with n! == -1 (mod p) — n = p-1 is the Wilson
    instance ((p-1)! == -1 mod p, always present for prime p)."""
    sols = []
    f = 1
    for n in range(1, p):
        f = (f * n) % p
        if f == p - 1:
            sols.append(n)
    return sols

def main():
    ok = True
    primes = [p for p in primes_below(10000) if p >= 5]
    total_instances = 0
    wilson_only = []
    hist = {}
    first_extra = []  # (p, n) for primes whose smallest solution n < p-1... 
    pair_violations = 0
    for p in primes:
        sols = fact_chain_solutions(p)
        total_instances += len(sols)
        hist[len(sols)] = hist.get(len(sols), 0) + 1
        if sols:
            if sols == [p - 1]:
                wilson_only.append(p)
            else:
                first_extra.append((p, sols[0], len(sols)))
        # (a) pairing law on every instance
        for n in sols:
            if not (1 <= n <= p - 2):
                continue
            lhs = 1
            for j in range(1, p - n):  # (p-1-n)!
                lhs = (lhs * j) % p
            want = 1 if (p - 1 - n) % 2 == 0 else p - 1
            if lhs != want:
                pair_violations += 1
                print(f"PAIR-LAW VIOLATION p={p} n={n}")
    # (d) S032 round-1 census claims
    claims = [
        ("primes 5 <= p < 10^4 count", len(primes), 1227),
        ("total solution instances", total_instances, 2694),
        ("Wilson-only primes", len(wilson_only), 465),
        ("pair-law violations", pair_violations, 0),
        ("first Wilson-only primes", wilson_only[:8],
         [5, 13, 17, 31, 37, 41, 53, 73]),
        ("max f(p)/p", None, None),  # informational
    ]
    for name, got, want in claims:
        if want is None:
            continue
        good = (got == want)
        ok = ok and good
        print(f"{name}: got {got} expected {want} -> " + ("GREEN" if good else "RED"))
    print("solution-count histogram:", dict(sorted(hist.items())))
    print("first extra-solution primes (p, smallest n, count):", first_extra[:12])
    # (c) named instances
    named = [(7, 3), (11, 5), (19, 9), (23, 14), (29, 18), (43, 21),
             (47, 23), (59, 15), (61, 8), (67, 18), (71, 7)]
    named_ok = True
    for p, n in named:
        f = 1
        for j in range(1, n + 1):
            f = (f * j) % p
        good = f == p - 1
        named_ok = named_ok and good
        print(f"  named instance p={p} n={n}: {n}! mod {p} = {f} "
              + ("(-1 OK)" if good else "FAIL"))
    ok = ok and named_ok
    # max ratio record
    best = max(((p, (p - 1), 1.0 * (p - 1) / p) for p in wilson_only),
               key=lambda t: t[2], default=None)
    if best is not None:
        print(f"max f(p)/p among Wilson-only: {best[2]:.4f} at p={best[0]}")
    else:
        print("no Wilson-only primes found")
        ok = False
    print("\nBATTERY1072 " + ("GREEN — full census + pairing law + named instances"
                              if ok else "RED"))
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
