#!/usr/bin/env python3
"""#273 hunt v2: bitmask greedy multistart + bounded exact-cover polish."""
import sympy, random, sys

L = 720720
FULL = (1 << L) - 1

def build(L):
    ps = [p for p in sympy.primerange(5, 5000) if L % (p-1) == 0]
    moduli = sorted(set(p-1 for p in ps))
    return ps, moduli

def class_mask(n, a, L, base):
    # rotate base (bits at multiples of n) by a: bits {r: r%n==a}
    m = (base >> a) | ((base << (L - a)) & FULL_MASKS[L])
    return m & FULL_MASKS[L]

FULL_MASKS = {L: FULL}

def rot(mask, a, L):
    return ((mask >> a) | (mask << (L - a))) & FULL

def greedy(L, moduli, seed, shuffle=False):
    rng = random.Random(seed)
    mods = list(moduli)
    if shuffle: rng.shuffle(mods)
    else: mods.sort(reverse=(seed % 2 == 0))
    # base masks: bits at multiples of n
    base = {n: 0 for n in mods}
    for n in mods:
        b = 0
        for k in range(0, L, n):
            b |= 1 << k
        base[n] = b
    unc = FULL
    remaining = unc.bit_count()
    chosen = []
    while remaining > 0 and mods:
        best = (-1, None, None)
        for n in mods:
            bn = base[n]
            # try all shifts a in 0..n-1: coverage = popcount(unc & rot(bn,a))
            u = unc
            # iterate shifts by rotating unc progressively? cheaper: rotate base
            for a in range(n):
                c = (u & rot(bn, a, L)).bit_count()
                if c > best[0]:
                    best = (c, a, n)
        c, a, n = best
        if c == 0: break
        chosen.append((a, n))
        unc &= ~rot(base[n], a, L)
        remaining = unc.bit_count()
        mods.remove(n)
    return chosen, remaining

def verify(L, chosen):
    for r in range(L):
        if not any(r % n == a for a, n in chosen): return False, r
    return True, None

if __name__ == "__main__":
    ps, moduli = build(L)
    print(f"moduli({len(moduli)}): {moduli}")
    print(f"density = {sum(1/n for n in moduli):.4f}")
    best = (10**9, None, -1)
    t0 = __import__('time').time()
    for seed in range(24):
        ch, rem = greedy(L, moduli, seed, shuffle=(seed >= 12))
        if rem < best[0]: best = (rem, ch, seed)
        print(f"seed {seed:2d}: leftover {rem:6d} classes {len(ch)}")
        if rem == 0:
            ok, bad = verify(L, ch)
            print("FULL COVER! verified:", ok)
            if ok:
                with open("WITNESS_273.txt","w") as f:
                    f.write(f"#273 WITNESS: covering system, all moduli p-1, p>=5 prime\nL = {L}\n")
                    for a, n in ch: f.write(f"x = {a} mod {n}   (p = {n+1})\n")
                print("WITNESS WRITTEN"); sys.exit(0)
    print("best leftover:", best[0], "seed", best[2])
