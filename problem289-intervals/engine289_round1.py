#!/usr/bin/env python3
# #289 interval hunt: 1 = sum_{i=1}^{k} sum_{n in I_i} 1/n with k
# disjoint, non-adjacent intervals, each of length >= 2.
# Strategy: exact-rational beam/DFS over interval placements.
# Intervals within [2, M]; harmonic interval sums computed exactly.
from fractions import Fraction

M = 240

# interval table: (a, b) with b - a + 1 >= 2, sum exact
intervals = []
for a in range(2, M + 1):
    s = Fraction(1, a)
    for b in range(a + 1, M + 1):
        s += Fraction(1, b)
        intervals.append((a, b, s))
        assert s == sum(Fraction(1, x) for x in range(a, b + 1))

# For each k target: find sets of k compatible intervals summing to 1.
# DFS over intervals sorted; prune by remaining sum range.
def compatible(used, a, b):
    for (ua, ub) in used:
        if not (b + 1 < a or ub + 1 < ua):   # requires gap >= 1 (non-adjacent)
            return False
    return True

def hunt(k, target=Fraction(1), depth=0, used=None, start=0, results=None):
    if results is None:
        results = []
    if used is None:
        used = []
    if depth == k:
        if target == 0:
            results.append(list(used))
        return results
    # bound: remaining intervals can add at most sum of largest possible
    for idx in range(start, len(intervals)):
        a, b, s = intervals[idx]
        if len(used) > 0 and a <= used[-1][1] + 1:
            continue
        if s > target:
            # sums grow as a decreases... intervals sorted by a asc, b asc:
            # s increases with b for fixed a; a asc: later a start fresh.
            continue
        # min possible additional: 0 (take tiny intervals) — but need exact
        hunt(k, target - s, depth + 1, used + [(a, b)], idx + 1, results)
        if len(results) >= 3:
            return results
    return results

# greedy known seed: 1 = 1/3+1/4+1/5+1/6 + 1/20? — 20 alone is length 1.
# Find k=2 with both lengths >= 2 first (known hard), then k=3, 4...
for k in [2, 3, 4, 5]:
    res = hunt(k)
    if res:
        print(f"#289 k={k}: FOUND")
        for r in res[:2]:
            pretty = []
            total = Fraction(0)
            for (a, b) in r:
                pretty.append(f"[{a}..{b}]")
                total += sum(Fraction(1, x) for x in range(a, b + 1))
            assert total == 1
            print(f"   1 = {' + '.join('sum(1/n, n in ' + p + ')' for p in pretty)}")
            print(f"   intervals: {pretty}")
        break
    else:
        print(f"#289 k={k}: no witness at M={M} (this run)")
