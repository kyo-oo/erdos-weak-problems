#!/usr/bin/env python3
"""
battery396k3.py — BATTERY FOR KERNEL 39 (Erdős #396 k=3 witness n=8178).
Dual-method full-exclusion evidence for 4 <= n < 8178 + witness verification.

Method 1 (Kummer/Legendre carries): v_p(C(2n,n)) = (2 s_p(n) - s_p(2n))/(p-1)
  for every prime p | n(n-1)(n-2)(n-3); exclusion iff some p^e || product
  with e > v_p.  Every excluded n gets its WITNESS PRIME recorded.
Method 2 (direct): exact big-integer C(2n,n) % product on a dense sample
  (every 37th n + all n in [8100, 8178) + the witness neighborhood).
"""
import sys, math

def sp(m, p):
    s = 0
    while m:
        s += m % p; m //= p
    return s

def vp_central(n, p):
    return (2 * sp(n, p) - sp(2 * n, p)) // (p - 1)

def factorize(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def witness_prime(n):
    """return (p, e, c) with p^e || product, e > v_p(C(2n,n)), or None"""
    P = n * (n - 1) * (n - 2) * (n - 3)
    for p, e in factorize(P).items():
        c = vp_central(n, p)
        if c < e:
            return (p, e, c)
    return None

def main():
    ok = True
    witness_primes = {}
    for n in range(4, 8178):
        w = witness_prime(n)
        if w is None:
            print(f"FAIL: n={n} is a k=3 solution below 8178 (exclusion broken)")
            ok = False
        else:
            witness_primes[w[0]] = witness_primes.get(w[0], 0) + 1
    print(f"M1 carry-formula exclusion 4..8177: {'COMPLETE' if ok else 'FAIL'}")
    top = sorted(witness_primes.items(), key=lambda kv: -kv[1])[:10]
    print(f"   witness-prime census (top 10): {top}")

    # the witness itself, direct
    n = 8178
    P = n * (n - 1) * (n - 2) * (n - 3)
    C = math.comb(2 * n, n)
    w_ok = (C % P == 0)
    print(f"M2 witness n=8178 direct: P | C(16356,8178): {w_ok}")
    ok &= w_ok

    # direct sample
    sample = list(range(4, 8178, 37)) + list(range(8100, 8178))
    s_ok = True
    for m in sample:
        Pm = m * (m - 1) * (m - 2) * (m - 3)
        if math.comb(2 * m, m) % Pm == 0:
            print(f"FAIL: direct check finds n={m} works below 8178")
            s_ok = False
    print(f"M2 direct sample ({len(sample)} values incl. [8100,8178)): {'ALL EXCLUDED' if s_ok else 'FAIL'}")
    ok &= s_ok

    # agreement: carry-method == direct on the sample
    a_ok = all(witness_prime(m) is not None for m in sample)
    print(f"M1/M2 agreement on sample: {a_ok}")
    ok &= a_ok

    print("BATTERY396K3_GREEN=1" if ok else "BATTERY396K3_FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
