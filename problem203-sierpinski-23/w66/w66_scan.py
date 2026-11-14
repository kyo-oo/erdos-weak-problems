#!/usr/bin/env python3
"""w66_scan.py — THE DEEP PALETTE SCAN for Erdos #203 (W66 strategist).

Mission 2 (alternative tori): enumerate ALL primes p (any size) with
ord_p(2) | L2 and ord_p(3) | L3 for the candidate frames, beyond the bank
(pal_dlog_full.json: q <= 3e5, h <= 5000).  Two passes:

  PASS A (sieve to 1e7): p in [5, 1e7] with 2^L2A = 1 and 3^L3A = 1 mod p,
  exact (o2,o3) via an SPF sieve of p-1.
  PASS B (gcd scan, any size): p | gcd(2^d-1, 3^e-1) for divisor pairs
  (d | L2, e | L3) — the gcd values are empirically small; trial-divided to
  1e7 (+ sympy for small cofactors).

Output: w66_deep.json — entries [q, o2, o3, h, source], deduped.
Pure python/numpy/sympy; bounded runtime; intermediate cache.
"""
import json, math, os, sys, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
PD = os.path.dirname(HERE)
BANK = os.path.join(PD, "pal_dlog_full.json")

SIEVE_N = 10 ** 7
L2A = 784089600            # 2^10 * 3^2 * 5 * 7 * 11 * 13 * 17
L3A = 2801007360           # 2^8 * 3^7 * 5 * 7 * 11 * 13

def build_spf(n):
    spf = np.arange(n + 1, dtype=np.int64)
    spf[0] = 0
    spf[1] = 1
    i = 2
    while i * i <= n:
        if spf[i] == i:
            idx = np.arange(i * i, n + 1, i, dtype=np.int64)
            m = spf[idx] == idx
            spf[idx[m]] = i
        i += 1
    return spf

def factor_with_spf(n, spf):
    f = {}
    while n > 1:
        if n > len(spf) - 1:
            from sympy import factorint
            for p, e in factorint(n).items():
                f[int(p)] = f.get(int(p), 0) + int(e)
            return f
        p = int(spf[n])
        if p == 1 or p == 0:
            break
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        f[p] = e
    return f

def order_from(a, p, fac_pm1):
    o = p - 1
    for q in fac_pm1:
        while o % q == 0 and pow(a, o // q, p) == 1:
            o //= q
    return o

def main():
    t0 = time.time()
    out = {}
    bank = json.load(open(BANK))
    for r in bank:
        q, h, o2, o3 = int(r[0]), int(r[1]), int(r[4]), int(r[5])
        out[q] = [q, o2, o3, h, "bank"]
    print(f"[bank] {len(out)} primes", flush=True)

    sieved = os.path.join(HERE, "w66_deep_sieve.json")
    if os.path.exists(sieved):
        for k, v in json.load(open(sieved)).items():
            out[int(k)] = v
        print(f"[cache] loaded sieve pass: {len(out)} total", flush=True)
    else:
        spf = build_spf(SIEVE_N)
        primes = np.nonzero(spf[2:] == np.arange(2, SIEVE_N + 1, dtype=np.int64))[0] + 2
        primes = primes[primes >= 5].tolist()
        print(f"[sieve] {len(primes)} primes in [5,1e7] ({time.time()-t0:.0f}s)", flush=True)
        cnt = 0
        for p in primes:
            if pow(2, L2A, p) != 1 or pow(3, L3A, p) != 1:
                continue
            f = factor_with_spf(p - 1, spf)
            o2 = order_from(2, p, f)
            o3 = order_from(3, p, f)
            if L2A % o2 or L3A % o3:
                continue
            h = o2 * o3 // math.gcd(o2, o3)
            if p not in out:
                out[p] = [p, o2, o3, h, "sieve"]
                cnt += 1
            if cnt and cnt % 200 == 0:
                print(f"  [A] +{cnt} ({time.time()-t0:.0f}s)", flush=True)
        print(f"[pass A] +{cnt} new primes (total {len(out)}) ({time.time()-t0:.0f}s)", flush=True)
        json.dump({str(k): v for k, v in out.items()}, open(sieved, "w"))

    # ---------- PASS B: gcd scan for p > 1e7 ----------
    from sympy import factorint
    def divs(n):
        ds = [1]
        f = {}
        x = n
        d = 2
        while d * d <= x:
            while x % d == 0:
                f[d] = f.get(d, 0) + 1
                x //= d
            d += 1 if d == 2 else 2
        if x > 1:
            f[x] = f.get(x, 0) + 1
        for p, e in f.items():
            ds = [d * p ** i for d in ds for i in range(e + 1)]
        return sorted(set(ds))
    DSET = sorted(set(d for d in divs(12252240) if d <= 24000)
                  | set(2 ** i for i in range(1, 11))
                  | set(3 ** i for i in range(1, 8)))
    ESET = sorted((set(e for e in divs(L3A) if e <= 4200)
                   | set(e for e in divs(55440) if 4200 < e <= 50400)
                   | set(e for e in divs(720720) if 4200 < e <= 50400)))
    ESET = sorted(e for e in ESET if e <= 50400)
    print(f"[pass B] d-set {len(DSET)} (max {DSET[-1]}), e-set {len(ESET)} (max {ESET[-1]})", flush=True)
    small_primes = None
    # small primes to 1e5 for trial division of gcds (big gcds give up beyond)
    TD = 10 ** 5
    spf5 = build_spf(TD)
    small_primes = np.nonzero(spf5[2:] == np.arange(2, TD + 1, dtype=np.int64))[0] + 2
    small_primes = small_primes[small_primes >= 5].tolist()
    found = 0
    maxg = 0
    pairs = [(d, e) for d in DSET for e in ESET if (d * e) // math.gcd(d, e) <= 50000]
    print(f"[pass B] {len(pairs)} gcd pairs", flush=True)
    for i, (d, e) in enumerate(pairs):
        M = 3 ** e - 1
        x = (pow(2, d, M) - 1) % M
        G = math.gcd(x, M)
        if G <= 1:
            continue
        if G > maxg:
            maxg = G
        g = G
        fac = {}
        for p in small_primes:
            if p * p > g:
                break
            if g % p == 0:
                ee = 0
                while g % p == 0:
                    g //= p
                    ee += 1
                fac[p] = ee
        if g > 1 and g < 10 ** 16:
            try:
                for p, ee in factorint(g).items():
                    fac[int(p)] = fac.get(int(p), 0) + int(ee)
            except Exception:
                pass
        for p in fac:
            if p < 5 or p in out:
                continue
            try:
                fpm = {int(k) for k in factorint(p - 1).keys()}
                o2 = order_from(2, p, fpm)
                o3 = order_from(3, p, fpm)
            except Exception:
                continue
            h = o2 * o3 // math.gcd(o2, o3)
            out[p] = [p, o2, o3, h, "gcd"]
            found += 1
        if i % 5000 == 0 and i:
            print(f"  [B] {i}/{len(pairs)} pairs, +{found} primes, maxgcd {maxg} ({time.time()-t0:.0f}s)", flush=True)
    print(f"[pass B] +{found} new primes (total {len(out)}) maxgcd={maxg} ({time.time()-t0:.0f}s)", flush=True)

    tot = sum(1.0 / r[3] for r in out.values())
    print(f"[TOTAL] {len(out)} primes, global budget sum = {tot:.4f}")
    json.dump({str(k): v for k, v in out.items()}, open(os.path.join(HERE, "w66_deep.json"), "w"))
    print("wrote w66_deep.json")

if __name__ == "__main__":
    main()
