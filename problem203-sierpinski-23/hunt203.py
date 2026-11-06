#!/usr/bin/env python3
"""#203 round 1: find m with (m,6)=1, every 2^k 3^l m+1 composite, via finite
covering of the (k,l) torus by prime classes. m solved by CRT over chosen primes.

Structure: prime p covers (k,l) iff 2^k 3^l m = -1 (mod p). Fix m's residue
r_p mod p; then p covers {(k,l): 2^k 3^l = -r_p^{-1} mod p} — periodic set
with period (ord_p(2), ord_p(3)). Cover the full torus Z_L2 x Z_L3."""
import sympy, random, time
from itertools import product

# candidate primes: p != 2,3 with small ord_p(2), ord_p(3), and p-1 smooth-ish
CANDS = []
for p in sympy.primerange(5, 5000):
    o2 = sympy.n_order(2, p); o3 = sympy.n_order(3, p)
    if o2 * o3 <= 4000 and o2 <= 600 and o3 <= 600:
        CANDS.append((p, o2, o3))
print(f"candidates: {len(CANDS)}", flush=True)
for p, o2, o3 in CANDS[:25]: print(f"  p={p}: ord2={o2} ord3={o3}", flush=True)

def build_engine(primes):
    L2 = 1; L3 = 1
    for p, o2, o3 in primes:
        L2 = sympy.lcm(L2, o2); L3 = sympy.lcm(L3, o3)
    return L2, L3

# torus via dict of covered cells per prime given residue r
def cover_set(p, o2, o3, L2, L3, r):
    """cells (k mod L2, l mod L3) where 2^k 3^l m = -1 mod p with m = r:
    need 2^k 3^l = -r^{-1} mod p. If r == 0 mod p: p never divides (m invertible).
    Returns set of (k,l) cells mod (L2, L3)."""
    if r % p == 0: return set()
    target = (-pow(r, -1, p)) % p
    # find all (k mod o2, l mod o3) with 2^k 3^l = target mod p
    cells = set()
    # enumerate k mod o2, l mod o3 — need discrete log solve; use meet: precompute
    # 2^k for k in range(o2); then 3^l = target * 2^{-k}
    pows2 = {}
    v = 1
    for k in range(o2):
        pows2.setdefault(v, []).append(k)
        v = v * 2 % p
    v = 1
    pows3 = {}
    for l in range(o3):
        pows3[v] = l
        v = v * 3 % p
    for val2, ks in pows2.items():
        need = target * pow(val2, -1, p) % p
        if need in pows3:
            l0 = pows3[need]
            for k0 in ks:
                # (k0, l0) generates cells k0 + t*o2, l0 + s*o3 within L2 x L3
                kk = k0
                while kk < L2:
                    ll = l0
                    while ll < L3:
                        cells.add((kk, ll))
                        ll += o3
                    kk += o2
    return cells

def try_configuration(primes, time_budget=120):
    L2, L3 = build_engine(primes)
    N = L2 * L3
    if N > 400000:
        return None
    print(f"  torus {L2}x{L3} = {N} cells, {len(primes)} primes", flush=True)
    t0 = time.time()
    rng = random.Random(7)
    best = 10**9
    # residues: r_p mod p annealed; coverage = union of cover sets
    # precompute per (p, r): cover set — expensive; instead sample r per prime lazily
    cache = {}
    def cs(p, o2, o3, r):
        key = (p, r)
        if key not in cache:
            cache[key] = cover_set(p, o2, o3, L2, L3, r)
        return cache[key]
    restart = 0
    while time.time() - t0 < time_budget:
        restart += 1
        residues = {p: rng.randrange(1, p) for p, o2, o3 in primes}
        cov = set()
        for p, o2, o3 in primes: cov |= cs(p, o2, o3, residues[p])
        u = N - len(cov)
        it = 0
        while u > 0 and time.time() - t0 < time_budget and it < 3000:
            it += 1
            p, o2, o3 = primes[rng.randrange(len(primes))]
            old = residues[p]
            new = rng.randrange(1, p)
            if new == old: continue
            # incremental: remove old cover, add new
            residues[p] = new
            cov = set()
            for pp, o2_, o3_ in primes: cov |= cs(pp, o2_, o3_, residues[pp])
            u2 = N - len(cov)
            if u2 <= u or rng.random() < 0.3:
                u = u2
                if u < best:
                    best = u
                    if best <= 3 or it % 50 == 0:
                        print(f"    r{restart} it{it}: uncovered {u}/{N}", flush=True)
                if u == 0:
                    # solve CRT for m
                    ms = [(residues[p], p) for p, o2, o3 in primes]
                    from sympy.ntheory.modular import crt
                    m_sol, mod = crt([p for _, p in ms], [r for r, _ in ms])
                    m_sol = int(m_sol); mod = int(mod)
                    # find m coprime to 6: m = m_sol + t*mod, also want m odd, 3∤m
                    for t in range(0, 1000):
                        m = m_sol + t * mod
                        if m % 2 == 1 and m % 3 != 0 and m > 1:
                            return m, mod, residues, primes, L2, L3
            else:
                residues[p] = old
    print(f"  best uncovered: {best}/{N}", flush=True)
    return None

# configuration 1: primes with tiny periods
config1 = [(p, o2, o3) for p, o2, o3 in CANDS if o2 * o3 <= 200][:14]
print(f"config1: {config1}", flush=True)
res = try_configuration(config1, time_budget=100)
if res:
    m, mod, residues, primes, L2, L3 = res
    print(f"\n=== #203 CANDIDATE: m = {m} (mod {mod}), coprime to 6: {m % 2 == 1 and m % 3 != 0} ===")
    # spot-verify: first few (k,l)
    bad = []
    for k in range(0, 40):
        for l in range(0, 40):
            v = 2**k * 3**l * m + 1
            if sympy.isprime(v): bad.append((k, l))
    print(f"spot check (k,l) < (40,40): {len(bad)} primes among values — {'CLEAN' if not bad else bad[:10]}")
    with open("CANDIDATE_203.txt", "w") as f:
        f.write(f"#203 candidate m = {m} (covering modulus {mod})\n")
        for p, o2, o3 in primes: f.write(f"p={p}: ord2={o2} ord3={o3} m≡{residues[p]}\n")
else:
    print("config1 no cover — more rounds needed")
