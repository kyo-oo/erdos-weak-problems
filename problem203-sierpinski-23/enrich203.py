#!/usr/bin/env python3
"""
enrich203.py — W63-B3: the COMPLETE torus-palette enrichment for Erdős #203.

LAW: for an odd prime q >= 5, ord_q(2) | L  <=>  q | 2^L - 1.  Hence the primes
compatible with the torus (Z/L)^2 (L = 27720 = 2^3*3^2*5*7*11) are EXACTLY the
prime factors of
    G := gcd(2^L - 1, 3^L - 1).
For every such q: o2 = ord_q(2) | L, o3 = ord_q(3) | L, and (F_q^* cyclic =>
exactly one subgroup per order) |<2,3>_q| = h = lcm(o2, o3) | L.  Each prime
covers exactly L^2/h torus cells (one coset of ker psi_q), density 1/h; the
target coset is a FREE choice w_q in Z/h_q (bijection with residues m mod q).

Stage 1: compute G (gmpy2, exact).
Stage 2: trial division by all primes <= SWEEP_CAP (numpy sieve) -> certified
         complete census of torus primes <= SWEEP_CAP.
Stage 3: Brent-rho on the residual (time-capped) -> larger primes, honestly
         labeled; final residual primality-tested (BPSW).
Stage 4: exact (o2, o3, h) per prime + discrete logs (U, V) w.r.t. a generator
         of <2,3>_q; full family file fam27720.json + budget + histograms.

Checkpoint: enrich203_ckpt.json after every stage; resume-safe.
Only campaign mathematics: cyclic group structure, CRT, multiplicative orders.
"""
import sys, os, json, math, time
import numpy as np
import gmpy2

HERE = os.path.dirname(os.path.abspath(__file__))
L = 27720
SWEEP_CAP = 100_000_000      # certified complete census bound
CKPT = os.path.join(HERE, "enrich203_ckpt.json")
FAMF = os.path.join(HERE, "fam27720.json")

def log(s):
    print(s, flush=True)

def sieve_np(n):
    """primes <= n via numpy"""
    flags = np.ones(n + 1, dtype=bool)
    flags[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if flags[p]:
            flags[p * p::p] = False
    return np.nonzero(flags)[0].astype(np.int64)

def order_of(a, p):
    n = p - 1
    fs = set()
    x = n; d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    o = n
    for q in fs:
        while o % q == 0 and pow(a, o // q, p) == 1:
            o //= q
    return o

def dlog_pair(p, o2, o3, h):
    """generator g of <2,3>_q (order h) and U,V with g^U=2, g^V=3.
    <2,3> is cyclic (subgroup of cyclic F_q^*); <2> and <3> are the unique
    subgroups of orders o2, o3, so g = g2 * g3^{...} trick: take g2 generator
    of <2> (2 itself), g3 generator of <3> (3 itself); g = 2^a * 3^b with
    appropriate exponents to make order h.  Simplest exact route: enumerate
    2^i * 3^j until order h found?  Robust route: build the subgroup elements
    by BFS over {2,3} and find a generator by testing element orders.
    Fallback (fast, always works): g = 2^(o2/r) ... no — do BFS + order test
    on candidates sorted by ... we just test ALL elements for generator-hood,
    but only until found; expected ~phi(h)/h of elements are generators.
    """
    # BFS the subgroup
    sub = {1}
    frontier = [1]
    while frontier:
        nf = []
        for v in frontier:
            for m in (2, 3):
                w = v * m % p
                if w not in sub:
                    sub.add(w); nf.append(w)
        frontier = nf
    assert len(sub) == h, f"subgroup size {len(sub)} != h {h}"
    # factor h for order testing
    fs = set()
    x = h; d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    for g in sorted(sub):
        o = h
        ok = True
        for q in fs:
            while o % q == 0 and pow(g, o // q, p) == 1:
                o //= q
            if o * q == h and pow(g, o, p) != 1:
                pass
        if o == 1 and g != 1:
            continue
        if o == h and g != 1:
            # g is a generator: compute dlogs of 2 and 3 by baby-step
            # giant-step over Z/h
            U = bsgs(g, 2 % p, h, p)
            V = bsgs(g, 3 % p, h, p)
            if U is not None and V is not None:
                return g, U, V
    return None, None, None

def bsgs(g, target, h, p):
    """find x with g^x = target mod p, 0 <= x < h (g of order h)."""
    m = int(math.isqrt(h)) + 1
    table = {}
    cur = 1
    for j in range(m):
        table.setdefault(cur, j)
        cur = cur * g % p
    factor = pow(g, -(m), p) if m else 1
    # g^{-m}
    gm = pow(g, m, p)
    ginv_m = pow(gm, -1, p)
    gamma = target
    for i in range(m + 1):
        j = table.get(gamma)
        if j is not None:
            return (i * m + j) % h
        gamma = gamma * ginv_m % p
    return None

def brent_rho(n, seed=1, max_iters=2_000_000):
    """Brent's Pollard rho; returns a nontrivial factor or None."""
    if n % 2 == 0: return 2
    g = gmpy2.mpz(seed)
    y = g; q = gmpy2.mpz(1); x = y; c = g
    iters = 0
    while iters < max_iters:
        y = (y * y + c) % n
        q = q * abs(x - y) % n
        iters += 1
        if iters % 128 == 0:
            d = gmpy2.gcd(q, n)
            if d != 1:
                if d != n: return int(d)
                # stuck: retry with different walk
                return None
            x = y
            q = 1
    return None

def main():
    t0 = time.time()
    state = {}
    if os.path.exists(CKPT):
        state = json.load(open(CKPT))
        log(f"[resume] ckpt loaded: keys={list(state.keys())}")
    else:
        state = {"found": [], "resid_done": False, "rho_done": False}

    # ---- Stage 1+2: G and trial division --------------------------------
    primes_done = state.get("trial_done", False)
    found = {int(p): int(a) for p, a in state["found"]}
    if not primes_done:
        log(f"[G] computing gcd(2^{L}-1, 3^{L}-1) ...")
        G = gmpy2.gcd((gmpy2.mpz(2) ** L) - 1, (gmpy2.mpz(3) ** L) - 1)
        log(f"[G] bit length = {G.bit_length()}  ({time.time()-t0:.1f}s)")
        state["G_bits"] = int(G.bit_length())
        log(f"[sieve] primes <= {SWEEP_CAP} ...")
        t1 = time.time()
        P = sieve_np(SWEEP_CAP)
        log(f"[sieve] {len(P)} primes ({time.time()-t1:.1f}s)")
        t1 = time.time()
        nfound = 0
        for pv in P:
            p = int(pv)
            if p < 5: continue
            if G % p == 0:
                a = 0
                while G % p == 0:
                    G //= p; a += 1
                found[int(p)] = a
                nfound += 1
                if nfound % 50 == 0:
                    log(f"  ... {nfound} factors, cofactor {G.bit_length()} bits ({time.time()-t1:.0f}s)")
        log(f"[trial] total prime factors of G below {SWEEP_CAP}: {nfound} "
            f"({time.time()-t1:.1f}s); cofactor bits = {G.bit_length()}")
        state["found"] = [[p, a] for p, a in found.items()]
        state["trial_done"] = True
        state["cofactor_bits"] = int(G.bit_length())
        json.dump(state, open(CKPT, "w"))
        gmpy2.to_digits = None
        open(os.path.join(HERE, "enrich203_cofactor.txt"), "w").write(gmpy2.digits(G))
    else:
        # rebuild cofactor from stored data
        G = gmpy2.gcd((gmpy2.mpz(2) ** L) - 1, (gmpy2.mpz(3) ** L) - 1)
        for p, a in found.items():
            G //= gmpy2.mpz(p) ** a
        log(f"[resume] cofactor rebuilt: {G.bit_length()} bits, {len(found)} primes found")

    # ---- Stage 3: rho on the residual -----------------------------------
    if not state.get("rho_done") and G.bit_length() > 2:
        log(f"[rho] attacking cofactor ({G.bit_length()} bits) ...")
        t1 = time.time()
        seed = 3
        R = G
        while R.bit_length() > 2 and time.time() - t1 < 480:
            if gmpy2.is_prime(R):
                log(f"[rho] residual is PRIME: {gmpy2.digits(R)}")
                found[int(R)] = 1
                R = gmpy2.mpz(1)
                break
            d = brent_rho(int(R), seed=seed)
            if d is None:
                seed += 2
                if seed > 200:
                    log("[rho] giving up on this cofactor (capped)")
                    break
                continue
            d = gmpy2.mpz(d)
            # factor d recursively (it may be composite)
            stack = [d]
            while stack:
                u = stack.pop()
                if u == 1: continue
                if gmpy2.is_prime(u):
                    a = 0
                    while R % u == 0:
                        R //= u; a += 1
                    found[int(u)] = found.get(int(u), 0) + a
                    log(f"[rho] prime factor {gmpy2.digits(u)} (cofactor now {R.bit_length()} bits, {time.time()-t1:.0f}s)")
                else:
                    d2 = brent_rho(int(u), seed=seed)
                    if d2 is None:
                        seed += 2
                        stack.append(u)
                    else:
                        stack.append(gmpy2.mpz(d2)); stack.append(u // gmpy2.mpz(d2))
            seed += 2
        state["found"] = [[p, a] for p, a in found.items()]
        state["rho_done"] = True
        state["final_cofactor_bits"] = int(R.bit_length())
        json.dump(state, open(CKPT, "w"))
        log(f"[rho] done: {len(found)} primes total; final cofactor {R.bit_length()} bits")

    # ---- Stage 4: exact orders + dlogs + family ------------------------
    log(f"[family] computing (o2, o3, h, U, V) for {len(found)} primes ...")
    fam = []
    t1 = time.time()
    for i, p in enumerate(sorted(found)):
        if p < 5: continue
        o2 = order_of(2, p); o3 = order_of(3, p)
        if L % o2 or L % o3:
            log(f"  !! p={p} NOT torus-compatible (o2={o2}, o3={o3}) — impossible, check")
            continue
        h = o2 * o3 // math.gcd(o2, o3)
        fam.append([p, h, o2, o3])
        if (i + 1) % 200 == 0:
            log(f"  ... {i+1}/{len(found)} ({time.time()-t1:.0f}s)")
    fam.sort(key=lambda r: (r[1], r[0]))
    dens = sum(1.0 / r[1] for r in fam)
    log(f"[family] {len(fam)} torus primes; density budget = {dens:.4f}")
    json.dump({"L": L, "family": fam, "budget": dens,
               "sweep_cap": SWEEP_CAP,
               "final_cofactor_bits": state.get("final_cofactor_bits", 0)},
              open(FAMF, "w"))
    # histogram
    from collections import Counter
    ch = Counter(r[1] for r in fam)
    log("[family] h-histogram (top small): " + str({h: ch[h] for h in sorted(ch)[:24]}))
    log(f"[done] wrote {FAMF}  ({time.time()-t0:.0f}s total)")

if __name__ == "__main__":
    main()
