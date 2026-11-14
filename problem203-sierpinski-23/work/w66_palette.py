#!/usr/bin/env python3
"""
w66_palette.py — W66-P203-E PALETTE EXPANSION ENGINE (Erdős #203, Sierpiński 2·3-smooth).

THE FACT: the enriched palette for torus L = primes p (p >= 5) with
ord_p(2) | L AND ord_p(3) | L  <=>  p | gcd(2^L - 1, 3^L - 1)  =: G_L.
(The mission's sweep "primes dividing 2^d-1 or 3^e-1 for d,e | 55440 with
both ords | L" is the SAME set: p | 2^d-1 for d | L <=> p | 2^L-1, and the
both-ords condition lands exactly on divisors of G_L. The per-d sweep is run
separately in w66_sweep.py as the completeness cross-check.)

This engine:
  1. verifies the factorizations of L (brief said 2^5 for 55440 — corrected),
  2. computes G_L for L in {27720, 55440},
  3. factors G_L COMPLETELY with in-house arithmetic:
       trial division (sieve to 2^24) + Pollard p-1 (natural here: every
       p | G_L has h | L dividing p-1, so p-1 = h*k with h | L) +
       Brent-rho + deterministic Miller-Rabin (extra random bases above the
       deterministic range), recursive with full product verification;
  4. for every prime factor p: ord_p(2), ord_p(3), h = lcm, asserts h | L,
     and the dlog pair (U, V) of (2, 3) w.r.t. a generator of <2,3> mod p
     (subgroup order h), via generator construction + baby-step/giant-step;
  5. diffs against the W65 baseline palette (pal_dlog_full_baseline.json,
     the hmax~4998 / q<=~2.6e5 scan family) -> THE NEW PRIMES + budget growth;
  6. writes pal_dlog_w66.json ([q,h,U,V,o2,o3] for the FULL 55440 family,
     superset-ordered) + palette_w66.txt + pal_growth_w66.json report.

Pure python + numpy only (no sympy in the factoring path; sympy used ONLY in
the separate cross-check mode).
"""
import math, json, os, time, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..")          # problem203-sierpinski-23/

# ---------------------------------------------------------------- factorization
_MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

def is_prime(n):
    if n < 2: return False
    for p in _MR_BASES:
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    if n >= 3317044064679887385961981:      # beyond deterministic range
        for _ in range(8):
            a = random.randrange(2, n - 1)
            x = pow(a, d, n)
            if x in (1, n - 1): continue
            for _ in range(r - 1):
                x = x * x % n
                if x == n - 1: break
            else:
                return False
    return True

def _sieve(limit):
    global _SIEVE_CACHE
    if limit in _SIEVE_CACHE: return _SIEVE_CACHE[limit]
    sv = bytearray(b'\x01') * (limit + 1)
    sv[0:2] = b'\x00\x00'
    for i in range(2, int(limit ** 0.5) + 1):
        if sv[i]:
            sv[i * i::i] = b'\x00' * len(range(i * i, limit + 1, i))
    res = [i for i in range(2, limit + 1) if sv[i]]
    if len(_SIEVE_CACHE) < 6: _SIEVE_CACHE[limit] = res
    return res
_SIEVE_CACHE = {}

SMALL_PRIMES = None   # lazy

def _brent_rho(n, max_rounds=8):
    """Brent's cycle-finding Pollard rho; returns a nontrivial factor or None."""
    if n % 2 == 0: return 2
    for _ in range(max_rounds):
        y = random.randrange(2, n); c = random.randrange(1, n); m = 128
        g = r = q = 1; x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r <<= 1
        if g == n:
            g = 1; y = ys
            while g == 1:
                y = (y * y + c) % n
                g = math.gcd(abs(x - y), n)
        if g != n and g > 1:
            return g
    return None

def _pollard_pminus1(n, L_forced=None, b1=2 * 10**6, b2=60):
    """Pollard p-1. Every p | G_L has h | L dividing p-1, so p-1 = h*k.
    Stage 1 E = L * lcm(1..B1)  (k B1-smooth => a^E == 1 mod p).
    Stage 2: repeated giant steps beyond B1 (a^{E*j}) to catch k ~ prime > B1."""
    if b1 > 2 * 10**6: b1 = 2 * 10**6
    t0 = time.time()
    lcmv = 1
    for p in _sieve(b1):
        pe = p
        while pe * p <= b1: pe *= p
        lcmv = lcmv * pe // math.gcd(lcmv, pe)
    E = (L_forced or 1) * lcmv
    if E.bit_length() > 25 * 10**6:   # safety cap on exponent size
        return None
    a = pow(2, E, n)
    g = math.gcd(a - 1, n)
    if 1 < g < n: return g
    for j in range(2, b2 + 1):
        a = pow(a, j, n)             # a^{E * 2 * 3 * ... * b2}
        g = math.gcd(a - 1, n)
        if 1 < g < n: return g
    return None

def factor_complete(n, L_forced=None, trial_bound=2**24, depth=0):
    """complete factorization of n (n has no small factors below 100 already
    if pre-stripped). Returns dict prime->exp. VERIFIED by product check."""
    fac = {}
    stack = [n]
    guard = 0
    while stack:
        m = stack.pop()
        if m == 1: continue
        guard += 1
        if guard > 10000: raise RuntimeError("factor loop runaway")
        if is_prime(m):
            fac[m] = fac.get(m, 0) + 1
            continue
        # small trial division first (cheap, shrinks m)
        d = _trial_divide_value(m, 100000)
        if d:
            stack.append(d); stack.append(m // d); continue
        f = _pollard_pminus1(m, L_forced, b1=2 * 10**6, b2=60)
        if f and 1 < f < m:
            stack.append(f); stack.append(m // f); continue
        f = _brent_rho(m, max_rounds=16)
        if f and 1 < f < m:
            stack.append(f); stack.append(m // f); continue
        f = _pollard_pminus1(m, L_forced, b1=2 * 10**6, b2=2000)
        if f and 1 < f < m:
            stack.append(f); stack.append(m // f); continue
        f = _brent_rho(m, max_rounds=64)
        if f and 1 < f < m:
            stack.append(f); stack.append(m // f); continue
        raise RuntimeError(f"UNFACTORED composite piece {m} ({m.bit_length()} bits)")
    # verify
    prod = 1
    for p, e in fac.items():
        assert is_prime(p), f"non-prime in output {p}"
        prod *= p ** e
    assert prod == n, "product check failed"
    return fac

def _trial_divide_value(m, bound):
    """find a prime factor of m below bound (by sieved primes), or None"""
    global SMALL_PRIMES
    if SMALL_PRIMES is None: SMALL_PRIMES = _sieve(bound)
    for p in SMALL_PRIMES:
        if p * p > m: return None
        if m % p == 0: return p
    return None

def trial_strip(n, bound=2**24, log=print):
    """strip all prime factors < bound from n; returns (fac dict, residual)"""
    global SMALL_PRIMES
    t0 = time.time()
    if SMALL_PRIMES is None: SMALL_PRIMES = _sieve(bound)
    fac = {}
    for p in SMALL_PRIMES:
        if n == 1: break
        if n % p == 0:
            e = 0
            while n % p == 0: n //= p; e += 1
            fac[p] = e
    log(f"  trial strip to {bound}: {sum(fac.values())} factors from "
        f"{len(fac)} primes, residual {n.bit_length()} bits ({time.time()-t0:.0f}s)")
    return fac, n

# ---------------------------------------------------------------- orders / dlogs
def multiplicative_order(a, p, order, fac_order):
    """ord of a mod p given the group order it lives in + its factorization.
    (a's order divides `order`; e.g. order = p-1, or the subgroup order h.)"""
    o = order
    for q in fac_order:
        while o % q == 0 and pow(a, o // q, p) == 1:
            o //= q
    assert pow(a, o, p) == 1
    return o

def subgroup_generator(p, h, fac_h, pool):
    """generator of the cyclic subgroup <2,3> mod p (order h):
    for each prime power q^e || h find x in S with q^e | ord(x); then
    y = x^{ord(x)/q^e} has order exactly q^e; product over q^e (coprime
    orders) has order h."""
    gen_parts = []
    for q, e in fac_h.items():
        pe = q ** e
        found = None
        for x in pool:
            o = multiplicative_order(x, p, h, fac_h)
            if o % pe == 0:
                y = pow(x, o // pe, p)
                assert multiplicative_order(y, p, h, fac_h) == pe
                found = y
                break
        if found is None:
            return None
        gen_parts.append(found)
    g = 1
    for x in gen_parts: g = g * x % p
    if multiplicative_order(g, p, h, fac_h) != h:
        return None
    return g

def bsgs_dlog(g, target, h, p):
    """discrete log of target in <g> (order h) mod p, or None if not in <g>."""
    m = int(math.isqrt(h)) + 1
    tbl = {}
    x = 1
    for j in range(m):
        if x not in tbl: tbl[x] = j
        x = x * g % p
    factor = pow(pow(g, m, p), p - 2, p)   # g^-m
    y = target
    for i in range(m + 1):
        if y in tbl:
            return (i * m + tbl[y]) % h
        y = y * factor % p
    return None

def closure_set(p):
    """<2,3> mod p as a set (BFS closure)."""
    S = {1}
    frontier = [1]
    while frontier:
        x = frontier.pop()
        for y in (x * 2 % p, x * 3 % p):
            if y not in S:
                S.add(y); frontier.append(y)
    return S

def fam_entry(p):
    """returns (q=p, h, U, V, o2, o3) for prime p with h | L checked by caller,
    or None if <2,3> non-cyclic-covering... (always cyclic as subgroup)."""
    fac_pm1 = factor_complete(p - 1, L_forced=None, trial_bound=100000)
    o2 = multiplicative_order(2, p, p - 1, fac_pm1)
    o3 = multiplicative_order(3, p, p - 1, fac_pm1)
    h = o2 * o3 // math.gcd(o2, o3)
    S = closure_set(p)
    assert len(S) == h, f"closure size {len(S)} != h {h} for p={p}"
    fac_h = factor_complete(h, trial_bound=100000)
    pool = list(S)
    random.shuffle(pool)
    g = subgroup_generator(p, h, fac_h, pool)
    if g is None:
        # brute scan fallback (small h)
        for x in pool:
            if multiplicative_order(x, p, h, fac_h) == h:
                g = x; break
    if g is None:
        return None
    U = bsgs_dlog(g, 2 % p, h, p)
    V = bsgs_dlog(g, 3 % p, h, p)
    if U is None or V is None: return None
    # verify: g^U == 2, g^V == 3 and the (U,V) coset law
    assert pow(g, U, p) == 2 % p and pow(g, V, p) == 3 % p
    return (p, h, U, V, o2, o3)

# ---------------------------------------------------------------- main
def main():
    t0 = time.time()
    random.seed(31337)
    log = lambda s: print(s, flush=True)

    # 1. L factorizations (brief correction: 55440 = 2^4 * 3^2 * 5 * 7 * 11)
    for L in (27720, 55440):
        f = factor_complete(L, trial_bound=1000)
        log(f"L={L} = " + " * ".join(f"{p}^{e}" for p, e in sorted(f.items())))
    assert factor_complete(55440, trial_bound=1000) == {2:4, 3:2, 5:1, 7:1, 11:1}

    results = {}
    for L in (27720, 55440):
        log(f"\n=== L={L} ===")
        tL = time.time()
        G = math.gcd((1 << L) - 1, pow(3, L) - 1)
        log(f"G_{L} = gcd(2^{L}-1, 3^{L}-1): {G.bit_length()} bits")
        fac, resid = trial_strip(G, 2**24, log)
        if resid > 1:
            extra = factor_complete(resid, L_forced=L)
            for p, e in extra.items():
                if p < 2**24:  # merged below trial bound (shouldn't happen)
                    fac[p] = fac.get(p, 0) + e
                else:
                    fac[p] = e
            log(f"  residual factored: {sorted(extra.items())}")
        # verification: product == G
        prod = 1
        for p, e in fac.items(): prod *= p ** e
        assert prod == G, "G product verify FAILED"
        log(f"  G_{L} fully factored and product-verified: {len(fac)} distinct primes")
        # family entries
        fam = {}
        for p in sorted(fac):
            if p in (2, 3): continue
            ent = fam_entry(p)
            if ent is None:
                log(f"  p={p}: fam_entry FAILED"); continue
            q, h, U, V, o2, o3 = ent
            assert h | L, f"p={p} h={h} does not divide {L}"
            fam[p] = ent
        budget = sum(1.0 / e[1] for e in fam.values())
        log(f"  family: {len(fam)} primes, budget = {budget:.6f}")
        results[L] = {"fac": fac, "fam": fam, "budget": budget, "t": time.time() - tL}

    # cross-family sanity: 27720 family ⊆ 55440 family
    f27, f55 = results[27720]["fam"], results[55440]["fam"]
    assert set(f27) <= set(f55)

    # 5. diff vs baseline
    base = json.load(open(os.path.join(OUT, "pal_dlog_full_baseline.json")))
    base55 = {r[0]: r for r in base if 55440 % r[1] == 0}
    base27 = {r[0]: r for r in base if 27720 % r[1] == 0}
    log("\n=== DIFF vs W65 baseline (pal_dlog_full.json scan family) ===")
    for L, fam, basef in ((27720, f27, base27), (55440, f55, base55)):
        newp = sorted(set(fam) - set(basef))
        gone = sorted(set(basef) - set(fam))
        log(f"L={L}: baseline {len(basef)} primes budget "
            f"{sum(1.0/r[1] for r in basef.values()):.6f} -> full {len(fam)} "
            f"budget {results[L]['budget']:.6f}; NEW primes: {newp}; "
            f"baseline-missing: {gone}")
        for p in newp:
            q, h, U, V, o2, o3 = fam[p]
            log(f"  NEW p={p} h={h} o2={o2} o3={o3} U={U} V={V} 1/h={1.0/h:.6f}")

    # 6. outputs
    out_full = [list(f55[p]) for p in sorted(f55, key=lambda p: (-1.0 / f55[p][1], p))]
    json.dump(out_full, open(os.path.join(OUT, "pal_dlog_w66.json"), "w"))
    with open(os.path.join(OUT, "palette_w66.txt"), "w") as fh:
        fh.write(f"# W66-P203-E FULL palette for L=55440 (complete factorization of "
                 f"gcd(2^55440-1, 3^55440-1)); family size {len(f55)}, "
                 f"budget {results[55440]['budget']:.6f}\n")
        fh.write("# format: q h U V o2 o3   (h=lcm(ord_q(2),ord_q(3)); U,V dlogs of 2,3 "
                 "w.r.t. a generator g of <2,3> mod q; coset W covers cells with "
                 "(U*k+V*l) mod h == W)\n")
        for q, h, U, V, o2, o3 in out_full:
            fh.write(f"{q} {h} {U} {V} {o2} {o3}\n")
    report = {
        "L": 55440,
        "family_size": len(f55),
        "budget_full": results[55440]["budget"],
        "baseline_size": len(base55),
        "baseline_budget": sum(1.0 / r[1] for r in base55.values()),
        "family_27720": {"size": len(f27), "budget": results[27720]["budget"],
                         "baseline_size": len(base27),
                         "baseline_budget": sum(1.0 / r[1] for r in base27.values())},
        "fac_G55": {str(p): e for p, e in results[55440]["fac"].items()},
        "fac_G27": {str(p): e for p, e in results[27720]["fac"].items()},
        "new_primes_55440": [f55[p] for p in sorted(set(f55) - set(base55))],
        "new_primes_27720": [f27[p] for p in sorted(set(f27) - set(base27))],
        "wall_s": time.time() - t0,
    }
    json.dump(report, open(os.path.join(OUT, "pal_growth_w66.json"), "w"), indent=1)
    log(f"\nwrote pal_dlog_w66.json, palette_w66.txt, pal_growth_w66.json "
        f"(total {time.time()-t0:.0f}s)")

if __name__ == "__main__":
    main()
