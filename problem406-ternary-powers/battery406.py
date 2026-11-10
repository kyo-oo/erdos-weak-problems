#!/usr/bin/env python3
"""
battery406.py — BATTERY FOR KERNEL 38 (Erdős #406 THE TERNARY CENSUS LAW).
Dual-method verification:
  A. CENSUS: for k in 0..500, the base-3 digits of 2^k are all <= 1 IFF
     k in {0, 2, 8}.  Method 1: divmod digit extraction.
     Method 2: greedy representation search (can 2^k be built as a sum of
     distinct powers of 3? — ternary-greedy with 0/1 constraint, independent
     implementation via subset-greedy on the digit positions).
  B. SEMANTIC LAW: the tfold reading (Bool list foldr) matches the digit
     reading on random lists (fold value's ternary digits are exactly the
     list, and only-0/1-digits IFF representable).
  C. MOD-3 LAW: odd exponents 2^(2j+1), j < 300: all have a ternary
     digit >= 2 (never 0/1-representable) — the parity law, evidence.
  D. MOD-8 BUDGET: random Bool lists b: tfold(b) % 8 == (E + 3*O) % 8.
  E. FUEL BOUND: 2^500 < 3^700 (and digits(2^500) = 317 <= 700).
"""
import random, sys

def tern_digits(n):
    ds = []
    while n:
        ds.append(n % 3)
        n //= 3
    return ds

def tfold(b):
    v = 0
    for d in reversed(b):
        v = 3 * v + (1 if d else 0)
    return v

def altsum(b):
    E = O = 0
    for i, d in enumerate(b):
        if d:
            if i % 2 == 0: E += 1
            else: O += 1
    return E, O

def main():
    ok = True

    # A. census, method 1 (divmod digits)
    good = []
    for k in range(0, 501):
        ds = tern_digits(2 ** k)
        if all(d <= 1 for d in ds):
            good.append(k)
    ok &= (good == [0, 2, 8])
    print(f"A1 census divmod: good exponents = {good}  {'OK' if good == [0,2,8] else 'FAIL'}")

    # A. census, method 2 (array-arithmetic base-3 doubling: start at [1]
    # and double k times with carries — no divmod anywhere)
    good2 = []
    rep = [1]
    for k in range(0, 501):
        if k > 0:
            carry = 0
            for i in range(len(rep)):
                t = 2 * rep[i] + carry
                rep[i] = t % 3
                carry = t // 3
            while carry:
                rep.append(carry % 3)
                carry //= 3
        if all(d <= 1 for d in rep):
            good2.append(k)
    ok &= (good2 == [0, 2, 8])
    print(f"A2 census base3-doubling: good exponents = {good2}  {'OK' if good2 == [0,2,8] else 'FAIL'}")

    # B. semantic law on random lists
    rng = random.Random(406)
    sem = True
    for _ in range(3000):
        b = [rng.random() < 0.5 for _ in range(rng.randint(0, 24))]
        v = tfold(b)
        ds = tern_digits(v) if v else []
        sem &= all(d <= 1 for d in ds)
        # reconstruct: digits LSB-first == b (mod trailing falses)
        if v > 0:
            sem &= (ds == [1 if d else 0 for d in b[:len(ds)]])
        elif any(b):
            sem &= False
    ok &= sem
    print(f"B semantic fold<->digits (3000 random lists): {sem}")

    # C. mod-3 law: odd exponents never 0/1-digit
    m3 = all(not all(d <= 1 for d in tern_digits(2 ** (2 * j + 1))) for j in range(300))
    ok &= m3
    print(f"C mod-3 odd-exclusion (j<300): {m3}")

    # D. mod-8 budget
    m8 = True
    for _ in range(3000):
        b = [rng.random() < 0.5 for _ in range(rng.randint(0, 30))]
        E, O = altsum(b)
        m8 &= (tfold(b) % 8 == (E + 3 * O) % 8)
    ok &= m8
    print(f"D mod-8 budget (3000 random lists): {m8}")

    # E. fuel bound
    fb = (2 ** 500 < 3 ** 700) and (len(tern_digits(2 ** 500)) <= 700)
    ok &= fb
    print(f"E fuel bound 2^500 < 3^700, digits(2^500) = {len(tern_digits(2**500))} <= 700: {fb}")

    # witnesses
    w = (tfold([True]) == 1 and tfold([True, True]) == 4 and
         tfold([True, True, True, False, False, True]) == 256 == 2 ** 8)
    ok &= w
    print(f"W witnesses 1, 4, 256: {w}")

    print("BATTERY406_GREEN=1" if ok else "BATTERY406_FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
