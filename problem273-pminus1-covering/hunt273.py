#!/usr/bin/env python3
"""#273 covering-system hunt: moduli ALL of form p-1, p>=5 prime.
Exact-cover search on Z_L via greedy + restart. Witness => unconditional kill."""
import sympy, sys
from functools import lru_cache

def primes_for_L(L):
    """primes p>=5 with (p-1) | L"""
    out=[]
    for p in sympy.primerange(5, 5000):
        if L % (p-1) == 0: out.append(p)
    return out

def greedy_cover(L, moduli, order=None, seed=0):
    """greedy: repeatedly pick (a mod n) covering most uncovered residues."""
    import random
    rng = random.Random(seed)
    uncovered = set(range(L))
    chosen = []
    mods = list(moduli)
    while uncovered and mods:
        best = None; best_cnt = -1
        # candidates: for each modulus, the best shift
        mlist = order(mods) if order else mods
        for n in mlist:
            # count coverage per shift via buckets
            buckets = {}
            for r in uncovered:
                buckets.setdefault(r % n, []).append(r)
            if not buckets: continue
            a, hits = max(buckets.items(), key=lambda kv: len(kv[1]))
            # tie-break random
            if len(hits) > best_cnt or (len(hits)==best_cnt and rng.random()<0.3):
                best = (a, n, hits); best_cnt = len(hits)
        if best is None or best_cnt == 0: break
        a, n, hits = best
        chosen.append((a, n))
        s = set(hits); uncovered -= s
        mods.remove(n)
    return chosen, uncovered

def verify_cover(L, chosen):
    """brute verify: every residue in Z_L satisfies some a mod n."""
    for r in range(L):
        if not any(r % n == a for a, n in chosen):
            return False, r
    return True, None

def exact_cover_dp(L, moduli, chosen_so_far=(), uncovered=None, timeout_nodes=20_000_000):
    """DLX-style: pick the uncovered residue with fewest covering classes."""
    if uncovered is None: uncovered = frozenset(range(L))
    if not uncovered: return list(chosen_so_far)
    # classes covering residue r: (a=r%n, n) for each n
    def candidates(r):
        return [(r % n, n) for n in moduli]
    # choose r with fewest candidate classes
    r_star = min(uncovered, key=lambda r: len(candidates(r)))
    for a, n in candidates(r_star):
        new_un = uncovered - frozenset(range(a, L, n)) if a==0 else frozenset(x for x in uncovered if x % n == a)
        # cheaper: recompute set
        new_un = frozenset(x for x in uncovered if x % n != a)
        res = exact_cover_dp(L, [m for m in moduli if m != n], chosen_so_far + ((a, n),), new_un, timeout_nodes-1)
        if res is not None: return res
    return None

if __name__ == "__main__":
    L = 720720
    ps = primes_for_L(L)
    moduli = sorted(set(p-1 for p in ps))
    dens = sum(1/n for n in moduli)
    print(f"L={L}, primes p>=5 with (p-1)|L: {len(ps)} -> moduli {moduli}")
    print(f"density sum 1/n = {dens:.4f}")
    # greedy multistart
    best = None
    for seed in range(40):
        import random
        mods = sorted(moduli, reverse=(seed%2==0))
        if seed>20: random.Random(seed).shuffle(mods)
        chosen, unc = greedy_cover(L, list(mods), seed=seed)
        if best is None or len(unc) < best[1]: best = (chosen, len(unc), seed)
        if not unc:
            print(f"SEED {seed}: FULL COVER with {len(chosen)} classes!")
            ok, bad = verify_cover(L, chosen)
            print("verified:", ok)
            if ok:
                for a,n in chosen: print(f"  x ≡ {a} (mod {n})   [p={n+1}]")
                sys.exit(0)
    print(f"greedy best leftover: {best[1]} uncovered (seed {best[2]}, {len(best[0])} classes)")
