#!/usr/bin/env python3
# THE EXPONENT-TRIT BAD-TREE SIEVE — engine layer, exact modular arithmetic.
#
# The fire engine (chamber-certified row_common_two_iff_prefix_killing_trit):
#   row p+1 is common-two (both 4^K and 4^(K+1) have digit 2 there) IFF
#     heq(r, p) AND t_p = kill(r, p)
#   where r = K mod 3^p (the prefix), t_p = p-th trit of K,
#     heq(r, p) := digit_{p+1}(4^r) = digit_{p+1}(4^(r+1))
#     kill(r, p) := 2 - digit_{p+1}(4^r)
#
# A counterexample to the climb tail (no common-two row >= 3) is a path
# through the tree avoiding every bad edge at levels p >= 2.
#
# This sieve measures: survivor counts per level, heq frequency, the
# surviving residue sets, and the natural (eventually-zero) survivors.
# NO-OOM compliant: pure modular arithmetic, bounded levels.

import sys

def heq_kill(r, p):
    """heq(r,p) and kill(r,p) for the level-p node r < 3^p."""
    q = p + 1
    p3 = 3 ** q
    d0 = pow(4, r, p3) // (3 ** p) % 3
    d1 = pow(4, r + 1, p3) // (3 ** p) % 3
    return d0 == d1, (2 - d0)

def sieve(max_level):
    frontier = list(range(9))  # nodes at level 2 (K mod 9), all alive so far
    print(f"level 2: {len(frontier)} nodes (all)")
    for p in range(2, max_level):
        heq_count = 0
        new_frontier = []
        for r in frontier:
            h, k = heq_kill(r, p)
            if h:
                heq_count += 1
            for t in range(3):
                if h and t == k:
                    continue  # bad edge: fire at row p+1
                new_frontier.append(r + t * (3 ** p))
        print(f"level {p}: {len(frontier)} nodes, heq on {heq_count} "
              f"({100*heq_count/max(1,len(frontier)):.1f}%), "
              f"children {len(new_frontier)} "
              f"(ratio {len(new_frontier)/max(1,len(frontier)):.3f})")
        frontier = new_frontier
        if len(frontier) > 3_000_000:
            print("frontier too large, stopping")
            break
    return frontier

def natural_survivors(frontier, level):
    """Among surviving nodes at this level, find naturals K = r whose
    all-zero tail also survives: no row q+1 (q >= level) where both
    4^K and 4^(K+1) carry digit 2."""
    survivors = []
    for r in frontier:
        ok = True
        top = int(1.27 * r) + 6 if r > 0 else 3
        for q in range(level, top):
            p3q = 3 ** (q + 1)
            if pow(4, r, p3q) // (3 ** q) % 3 == 2:
                if pow(4, r + 1, p3q) // (3 ** q) % 3 == 2:
                    ok = False
                    break
        if ok:
            survivors.append(r)
    return survivors

if __name__ == "__main__":
    max_level = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    frontier = sieve(max_level)
    print(f"\nFinal frontier at level {max_level}: {len(frontier)} nodes")
    if len(frontier) < 300000:
        nat = natural_survivors(frontier, max_level)
        print(f"Natural (zero-tail) survivors: {len(nat)}")
        big = [r for r in nat if r > 500]
        print(f"  of which > 500: {len(big)}: {big[:60]}")
        small = [r for r in nat if r <= 500]
        print(f"  <= 500: {small[:60]}")
