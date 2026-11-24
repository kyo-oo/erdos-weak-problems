#!/usr/bin/env python3
# PHASE 1 ENGINE v2 — certificates for TailAssault406.lean
#
# DATA MODEL (fixed):
#   S_level = set of residues mod 3^level surviving all bad edges at
#   levels 2..level-1 (the Band-I survivor set).
#   A residue r mod 3^level FIRES by row `level` iff its path hits a bad
#   edge at some level p in [2, level-1]: node r_p = r mod 3^p,
#   heq(r_p, p) and trit_p(r) = kill(r_p, p). The fired CLASS is
#   r_p + kill*3^p mod 3^(p+1) -- verified on the class representative.
#
# Two-method: every fired class verified by (a) big-int digits of 4^K,
# (b) modular pow digits, for the representative K of the class.

import json

def heq_kill(r, p):
    q = p + 1
    p3 = 3 ** q
    d0 = pow(4, r, p3) // (3 ** p) % 3
    d1 = pow(4, r + 1, p3) // (3 ** p) % 3
    return d0 == d1, (2 - d0)

def fire_mod(K, q):
    p3 = 3 ** (q + 1)
    return (pow(4, K, p3) // (3 ** q) % 3 == 2
            and pow(4, K + 1, p3) // (3 ** q) % 3 == 2)

def fire_big(K, q):
    n = 4 ** K
    a = (n // (3 ** q)) % 3
    n2 = 4 ** (K + 1)
    b = (n2 // (3 ** q)) % 3
    return a == 2 and b == 2

def build_levels(max_level):
    """Return S[level] for level in 3..max_level plus per-class fire data."""
    frontier = set(range(9))  # level-2 nodes (no edges checked below level 2)
    S = {2: sorted(frontier)}
    fire_witness = {}  # residue class mod 3^level -> (row, node, kill)
    for p in range(2, max_level):
        new_frontier = set()
        for r in frontier:
            h, k = heq_kill(r, p)
            for t in range(3):
                child = r + t * (3 ** p)
                if h and t == k:
                    # class child (mod 3^(p+1)) fires at row p+1
                    fire_witness[(p + 1, child % (3 ** (p + 1)))] = (r, k)
                else:
                    new_frontier.add(child)
        frontier = new_frontier
        S[p + 1] = sorted(frontier)
    return S, fire_witness

if __name__ == "__main__":
    MAXLEV = 6
    S, fire_witness = build_levels(MAXLEV)
    out = {"survivor_tables": {}, "fired_classes": {}}
    for lev in range(3, MAXLEV + 1):
        print(f"S_{lev}: {len(S[lev])} survivors of 3^{lev}={3**lev} "
              f"({100*len(S[lev])/3**lev:.1f}%)")
        out["survivor_tables"][str(lev)] = S[lev]
        out["fired_counts"] = out.get("fired_counts", {})
        out["fired_counts"][str(lev)] = 3 ** lev - len(S[lev])

    # TWO-METHOD verification of every fired class at level 6 (mod 729)
    S6 = set(S[6])
    problems = []
    nchecked = 0
    for r in range(729):
        if r in S6:
            continue
        # find the earliest bad edge on r's path
        fired = None
        node = r
        for p in range(5, 1, -1):
            pass  # we walk forward instead
        node = r % 9
        for p in range(2, 6):
            h, k = heq_kill(node, p)
            t = (r // (3 ** p)) % 3
            if h and t == k:
                fired = (p, node, k)
                break
            node = r % (3 ** (p + 1))
        if fired is None:
            problems.append((r, "no-fire"))
            continue
        p, node, k = fired
        cls = (node + k * (3 ** p)) % (3 ** (p + 1))
        # the class representative cls fires at row p+1: two-method check
        if not fire_mod(cls, p + 1):
            problems.append((r, "mod-fail", cls, p + 1))
        elif not fire_big(cls, p + 1):
            problems.append((r, "big-fail", cls, p + 1))
        else:
            nchecked += 1
    print(f"level-6 fired classes two-method verified: {nchecked}, "
          f"problems: {len(problems)} {problems[:6]}")

    # NATURAL narrowing: naturals in S_6 (>=8) -- they enter Band II
    nat_S6 = [r for r in S[6] if r >= 8]
    print(f"naturals >= 8 in S_6 (Band-II entrants, mod 729 classes): "
          f"{len(nat_S6)}")

    # BASE EXTENSION [501, 1500]: witnesses (K, first fire row), two-method
    def first_fire(K):
        n = 4 ** K
        d = []
        while n:
            d.append(n % 3)
            n //= 3
        ln = len(d)
        C = 0
        for q in range(ln + 2):
            dq = d[q] if q < ln else 0
            e = (C + 4 * dq) % 3
            if q >= 3 and dq == 2 and e == 2:
                return q
            C = (C + 4 * dq) // 3
        return None

    witnesses = []
    nofire = []
    maxrow = 0
    for K in range(501, 1501):
        q = first_fire(K)
        if q is None:
            nofire.append(K)
            continue
        assert fire_mod(K, q), (K, q)
        witnesses.append([K, q])
        maxrow = max(maxrow, q)
    print(f"base extension [501,1500]: {len(witnesses)} witnesses, "
          f"no-fire: {len(nofire)}, max row {maxrow}")
    out["base_witnesses"] = witnesses
    out["max_row"] = maxrow
    out["band2_entrants_mod729"] = nat_S6

    with open("scripts/tail_assault_data.json", "w") as f:
        json.dump(out, f)
    print("wrote scripts/tail_assault_data.json")
