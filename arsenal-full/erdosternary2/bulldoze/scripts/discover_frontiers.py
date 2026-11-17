#!/usr/bin/env python3
"""STRUCK A: two-seed Stanley S(0,t) family discovery.
STRUCK B: odd-p kernel law discovery (extends Kill #4).
Exact integer arithmetic only."""
import math

# ---------- STRIKE A: greedy two-seed Stanley engine ----------
def greedy_stanley(t, limit):
    """Greedy 3-AP-free set seeded {0, t}, up to limit."""
    S = []
    Sset = set()
    for m in range(limit):
        if m == 0 or m == t:
            S.append(m); Sset.add(m); continue
        blocked = False
        # m as third term: (a, b, m) with 2b = a + m
        for a in S:
            if (a + m) % 2 == 0:
                b = (a + m) // 2
                if b in Sset:
                    blocked = True; break
        if not blocked:
            # m as middle: (a, m, c) => c = 2m - a
            for a in S:
                c = 2 * m - a
                if c in Sset:
                    blocked = True; break
        # m as first term: (m, b, c) future — cannot block (b,c > m not in S yet)
        if not blocked:
            S.append(m); Sset.add(m)
    return S

def census(S, top):
    """|S ∩ [0, 3^k)| for k = 1.. """
    out = []
    k = 1
    while 3**k <= top:
        out.append(sum(1 for x in S if x < 3**k))
        k += 1
    return out

# Known Odlyzko-Stanley families: t = 3^k (digit law: ternary digits in {0,1})
#                               t = 2*3^k (the Kill #3 law)
# NEW FAMILY HUNT: t = 4..40
print("=" * 72)
print("STRIKE A — TWO-SEED S(0,t) FAMILY DISCOVERY")
print("=" * 72)
LIMIT = 2200  # past 3^7
for t in [4, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19, 20]:
    S = greedy_stanley(t, LIMIT)
    c = census(S, LIMIT)
    print(f"t={t:3d}  |A(t)|={len(S):5d}  census[3^k] k=1..7: {c}")
    if t in (4, 5):
        print(f"      first 24: {S[:24]}")
