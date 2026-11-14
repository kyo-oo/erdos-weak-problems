"""sweep203b.py — fast complete family sweep (numpy segmented sieve).

Prime q >= 5 is usable on torus L iff ord_q(2)|L and ord_q(3)|L, i.e.
2^L == 1 mod q and 3^L == 1 mod q. Enumerate ALL primes q <= QMAX via a
numpy segmented sieve; test eligibility for L in {55440, 720720, 12252240}
via chained pows; for eligible q compute (h, U, V) exactly.

Output: pal_sweep.json rows [q, h, U, V, o2, o3] sorted by (h, q).
"""
import json, math, os, sys, time
import numpy as np

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10**8
OUT = os.path.dirname(os.path.abspath(__file__)) + "/pal_sweep.json"
CKPT = OUT + ".ckpt"

L1 = 55440
L2 = L1 * 13
L3 = L2 * 17

def mult_order(a, q, fac):
    n = q - 1
    o = n
    for p in fac:
        while o % p == 0 and pow(a, o // p, q) == 1:
            o //= p
    return o

def bsgs_dlog(g, target, h, q):
    if target % q == 1:
        return 0
    m = int(math.isqrt(h)) + 1
    table = {}
    e = 1
    for j in range(m):
        if e not in table:
            table[e] = j
        e = e * g % q
    factor = pow(g, -m, q)
    y = target % q
    for i in range(m + 1):
        if y in table:
            return i * m + table[y]
        y = y * factor % q
    return None

def trial_factor(n):
    fac = {}
    d = 2
    while d * d <= n and d < 100000:
        while n % d == 0:
            fac[d] = fac.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fac[n] = fac.get(n, 0) + 1
    return fac

def full_entry(q):
    fac = trial_factor(q - 1)
    # complete factorization needed for exact order; if a large cofactor
    # remains, orders may be wrong -> skip only if cofactor is composite-ish
    big = [p for p in fac if p >= 100000]
    if big:
        # verify primality of big cofactor pieces via Miller-Rabin (sympy)
        from sympy import isprime
        for p in big:
            if not isprime(p):
                return None
    o2 = mult_order(2, q, fac)
    o3 = mult_order(3, q, fac)
    h = o2 * o3 // math.gcd(o2, o3)
    if h < 4:
        return None
    e = (q - 1) // h
    fh = trial_factor(h)
    g = None
    for base in (5, 6, 7, 10, 11, 12, 13, 17, 19, 23, 2, 3):
        if base % q == 0:
            continue
        cand = pow(base, e, q)
        o = h
        for p in fh:
            while o % p == 0 and pow(cand, o // p, q) == 1:
                o //= p
        if o == h and cand != 1:
            g = cand
            break
    if g is None:
        return None
    U = bsgs_dlog(g, 2 % q, h, q)
    V = bsgs_dlog(g, 3 % q, h, q)
    if U is None or V is None:
        return None
    assert pow(g, U, q) == 2 % q and pow(g, V, q) == 3 % q, (q, U, V)
    assert math.gcd(math.gcd(U, V), h) == 1, (q, U, V, h)
    return [int(q), int(h), int(U), int(V), int(o2), int(o3)]

# ---------- numpy segmented sieve ----------
def primes_upto(QMAX):
    import math
    seg = 1 << 16
    r = int(math.isqrt(QMAX)) + 1
    sv = np.ones(r + 1, dtype=bool); sv[:2] = False
    for p in range(2, int(math.isqrt(r)) + 1):
        if sv[p]:
            sv[p*p::p] = False
    small_primes = np.nonzero(sv)[0]
    out = []
    for lo in range(5, QMAX + 1, seg):
        hi = min(lo + seg, QMAX + 1)
        n = hi - lo
        mark = np.ones(n, dtype=bool)
        for p in small_primes:
            if p * p >= hi:
                break
            # first multiple of p that is >= lo and >= p*p (keep p itself)
            m0 = p * p
            if m0 < lo:
                m0 = ((lo + p - 1) // p) * p
            start = m0 - lo
            if start < n:
                mark[start::p] = False
        for i in np.nonzero(mark)[0]:
            q = lo + i
            if q > QMAX:
                break
            out.append(int(q))
    return out

t0 = time.time()
print("sieve...", flush=True)
PRIMES = primes_upto(QMAX)
print(f"{len(PRIMES)} primes <= {QMAX} ({time.time()-t0:.0f}s)", flush=True)

stats = {"tested": 0, "eL1": 0, "eL2": 0, "eL3": 0}
rows = []
for q in PRIMES:
    if q in (2, 3, 5, 7):
        pass  # keep 5,7 (they are eligible and useful)
    t2 = pow(2, L1, q)
    t3 = pow(3, L1, q)
    if t2 == 1 and t3 == 1:
        stats["eL1"] += 1
        u2 = pow(t2, 13, q); u3 = pow(t3, 13, q)
        if u2 == 1 and u3 == 1:
            stats["eL2"] += 1
            w2 = pow(u2, 17, q); w3 = pow(u3, 17, q)
            if w2 == 1 and w3 == 1:
                stats["eL3"] += 1
                ent = full_entry(q)
                if ent is not None:
                    rows.append(ent)
    elif q > 5:
        u2 = pow(2, L2, q)
        u3 = pow(3, L2, q)
        if u2 == 1 and u3 == 1:
            stats["eL2"] += 1
            w2 = pow(u2, 17, q); w3 = pow(u3, 17, q)
            if w2 == 1 and w3 == 1:
                stats["eL3"] += 1
                ent = full_entry(q)
                if ent is not None:
                    rows.append(ent)
            # also q eligible only via smaller L3? no: L2|L3 nested
        else:
            w2 = pow(2, L3, q)
            w3 = pow(3, L3, q)
            if w2 == 1 and w3 == 1:
                stats["eL3"] += 1
                ent = full_entry(q)
                if ent is not None:
                    rows.append(ent)
    stats["tested"] += 1
    if stats["tested"] % 2_000_000 == 0:
        print(f"tested {stats['tested']}: eL1={stats['eL1']} eL2={stats['eL2']} "
              f"eL3={stats['eL3']} rows={len(rows)} ({time.time()-t0:.0f}s)", flush=True)

rows = sorted({r[0]: r for r in rows}.values(), key=lambda r: (r[1], r[0]))
json.dump(rows, open(OUT, "w"))
for L, key in ((L1, "eL1"), (L2, "eL2"), (L3, "eL3")):
    fam = [r for r in rows if L % r[1] == 0]
    print(f"L={L}: {len(fam)} primes, budget {sum(1.0/r[1] for r in fam):.4f}", flush=True)
print(f"DONE: {len(rows)} rows ({time.time()-t0:.0f}s)", flush=True)
