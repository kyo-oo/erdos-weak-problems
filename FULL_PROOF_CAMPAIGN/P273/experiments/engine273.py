#!/usr/bin/env python3
"""P273 engine: split-tiling-tree construction of a covering system with
distinct moduli all of the form p-1 (p >= 5 prime).

Math (see PROOF.md):
  Lemma 1: p-1 covering  <=>  two disjoint-modulus covering systems of Z with
           moduli m in M = {m>=2 : 2m+1 prime}  (E-side even residues, O-side odd).
  Lemma 2: a prefix-split tree of classes (leaves partition Z) + distinct m_j | nu_j
           assigned to leaves => covering system {(c_j mod m_j)}.
  We build T_E with even m's, T_O with odd m's (automatic disjointness), then lift:
  (c,m) in T_E -> class 2c mod 2m ; (c,m) in T_O -> class 2c+1 mod 2m.
"""
import sys, time
from heapq import heappush, heappop
from sympy import factorint, isprime

# ---------------- pools: m with 2m+1 prime ----------------
def sieve_M(mlimit):
    """return set of m in [2, mlimit] with 2m+1 prime (all parities together)."""
    N = 2*mlimit + 2
    sv = bytearray([1]) * N
    sv[0] = sv[1] = 0
    i = 2
    while i*i < N:
        if sv[i]:
            sv[i*i::i] = bytearray(len(range(i*i, N, i)))
        i += 1
    return set(m for m in range(2, mlimit) if sv[2*m+1])

_divcache = {}
def divisors_of(n):
    if n in _divcache: return _divcache[n]
    f = factorint(n)
    ds = [1]
    for q, e in f.items():
        ds = [d * q**k for d in ds for k in range(e+1)]
    if len(_divcache) < 200000: _divcache[n] = ds
    return ds

def fresh(nu, poolset, used):
    return [m for m in divisors_of(nu) if m in poolset and m not in used]

def comb_look(nu, poolset, used, depth=4):
    """how many of the next `depth` 2-multiples of nu have >=1 fresh m (lookahead)."""
    h, v = 0, nu
    for _ in range(depth):
        v *= 2
        if fresh(v, poolset, used): h += 1
    return h

QS = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]

def build_tree(poolset, label, mlimit, max_leaves=600, verbose=True):
    """greedy split-tree growth. node=(c,nu). Returns leaves [(c,nu,m)]."""
    used = set()
    # frontier: min-heap by nu (process smallest modulus first)
    frontier = [(1, 0)]   # heap of (nu, c)
    leaves = []
    nsplit = 0
    t0 = time.time()
    while frontier:
        if len(leaves) > max_leaves:
            raise RuntimeError(f"{label}: leaf cap hit ({max_leaves})")
        nu, c = heappop(frontier)
        nsplit += 1
        # evaluate candidate split primes
        best = None
        for q in QS:
            fr = fresh(q*nu, poolset, used)
            kept = min(q, len(fr))
            pushed = q - kept
            look = comb_look(q*nu, poolset, used) if pushed > 0 or kept < q else 99
            key = (-pushed, kept, look, -q)
            if best is None or key > best[0]:
                best = (key, q, fr)
        q, fr = best[1], best[2]
        if not fr:
            # fully dry at all q*nu: enrich by smallest prime not dividing nu
            f = factorint(nu)
            q = next(p for p in QS if p not in f)
        kept = min(q, len(fr))
        ms = sorted(fr)[:kept]
        children = [(q*nu, c + j*nu) for j in range(q)]
        for (nch, cch), m in zip(children[:kept], ms):
            leaves.append((cch, nch, m)); used.add(m)
        for nch, cch in children[kept:]:
            heappush(frontier, (nch, cch))
        if verbose and nsplit % 50 == 0:
            print(f"  [{label}] splits={nsplit} leaves={len(leaves)} frontier={len(frontier)} "
                  f"maxnu={max(x[0] for x in frontier) if frontier else 0} t={time.time()-t0:.0f}s", flush=True)
    if verbose:
        print(f"  [{label}] DONE: splits={nsplit} leaves={len(leaves)} t={time.time()-t0:.0f}s", flush=True)
    return leaves

# ---------------- verification ----------------
from fractions import Fraction

def verify_tiling(leaves, label):
    """leaves (c,nu,m): check (a) sum 1/nu == 1, (b) pairwise disjoint => partition of Z."""
    s = sum(Fraction(1, nu) for _, nu, _ in leaves)
    assert s == 1, f"{label}: sum 1/nu = {s} != 1"
    L = [(c, nu) for c, nu, _ in leaves]
    for i in range(len(L)):
        ci, ni = L[i]
        for j in range(i+1, len(L)):
            cj, nj = L[j]
            g = ni * nj // math_gcd(ni, nj)
            assert ci % g != cj % g, f"{label}: leaves {i},{j} overlap ({ci} mod {ni}, {cj} mod {nj})"
    return True

def math_gcd(a, b):
    while b: a, b = b, a % b
    return a

def verify_full(leaves_E, leaves_O, window=2_000_000):
    """full verification of the final p-1 covering system."""
    # 1. moduli m: distinct, >=2, 2m+1 prime
    ms = [m for _, _, m in leaves_E] + [m for _, _, m in leaves_O]
    assert len(set(ms)) == len(ms), "duplicate m"
    for m in ms:
        assert m >= 2 and isprime(2*m+1), f"bad m={m}"
    # 2. m | nu
    for c, nu, m in leaves_E + leaves_O:
        assert nu % m == 0, f"m={m} not dividing nu={nu}"
    # 3. tilings
    verify_tiling(leaves_E, "E"); verify_tiling(leaves_O, "O")
    # 4. final classes: E: 2c mod 2m ; O: 2c+1 mod 2m ; window check
    classes = [( (2*c) % (2*m), 2*m) for c, _, m in leaves_E] + \
              [((2*c+1) % (2*m), 2*m) for c, _, m in leaves_O]
    n = len(classes)
    assert len(set(nm for _, nm in classes)) == n, "duplicate final modulus"
    # window check every integer in [0, window)
    mods = [nm for _, nm in classes]
    reses = [a for a, _ in classes]
    uncovered = []
    for x in range(window):
        ok = False
        for a, nm in classes:
            if x % nm == a: ok = True; break
        if not ok:
            uncovered.append(x)
            if len(uncovered) > 20: break
    return classes, uncovered

if __name__ == "__main__":
    mlimit = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    print(f"sieving M up to {mlimit} ...", flush=True)
    t0 = time.time()
    M = sieve_M(mlimit)
    print(f"M: {len(M)} values, t={time.time()-t0:.0f}s", flush=True)
    E_pool = set(m for m in M if m % 2 == 0)
    O_pool = set(m for m in M if m % 2 == 1)
    print(f"even-m pool: {len(E_pool)}, odd-m pool: {len(O_pool)}", flush=True)
    print("smallest even:", sorted(E_pool)[:20])
    print("smallest odd:", sorted(O_pool)[:20])

    print("building E tree (even m)...", flush=True)
    leaves_E = build_tree(E_pool, "E", mlimit)
    print("building O tree (odd m)...", flush=True)
    leaves_O = build_tree(O_pool, "O", mlimit)

    print(f"leaves_E={len(leaves_E)} leaves_O={len(leaves_O)}", flush=True)
    classes, unc = verify_full(leaves_E, leaves_O, window=1_000_000)
    if unc:
        print("UNCOVERED in window:", unc[:20]); sys.exit(1)
    print("WINDOW CLEAN + structural checks passed. Witness:", len(classes), "classes")
    with open("/home/z/my-project/erdos-weak-problems/FULL_PROOF_CAMPAIGN/P273/experiments/WITNESS_273.txt", "w") as f:
        f.write("#273 WITNESS: covering system, distinct moduli p-1, p>=5 prime\n")
        f.write(f"# {len(classes)} classes; E-side (even residues) then O-side (odd residues)\n")
        for a, nm in sorted(classes, key=lambda t: t[1]):
            f.write(f"x = {a} mod {nm}   (p = {nm+1})\n")
    print("WITNESS WRITTEN")
