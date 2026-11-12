#!/usr/bin/env python3
"""Extend a found config toward K_{6,4}: full common-row set, full common-column set."""
import sys
from math import isqrt
sys.path.insert(0, '/home/z/my-project/erdos-weak-problems/FULL_PROOF_CAMPAIGN/P885/experiments')
import biclique_engine as E

rows = [216, 567, 1128, 1848, 5496]
Cs = [1198800, 2695680, 22269520]

# sanity: verify the config exactly
M = E.verify_config(rows, Cs, quiet=False)
assert M is not None, "config invalid!"
print("[ext] base K_{5,3} verified:", rows, Cs)

# Q1: ALL common rows of the 3 C's (exact, from factor pairs of pairwise deltas)
R = set(E.common_rows(min(Cs[0], Cs[1]), max(Cs[0], Cs[1])))
for c in Cs[2:]:
    R &= set(E.common_rows(min(c, Cs[0]), max(c, Cs[0])))
R = sorted(R)
print(f"[ext] Q1 full common-row set of the 3 C's: {R}  (|R| = {len(R)})")

# Q2: common columns of the 5 rows up to X
X = int(sys.argv[1]) if len(sys.argv) > 1 else 10**13
colsets = []
for s in rows:
    cs = set()
    m = s + 1
    while m * m - s * s <= X:
        cs.add(m * m - s * s)
        m += 1
    colsets.append(cs)
    print(f"[ext] row {s}: {len(cs)} candidate columns <= {X}")
common = set.intersection(*colsets)
common.discard(0)
print(f"[ext] Q2 common columns of the 5 rows <= {X}: {sorted(common)}")

# Q3: for every row in R (beyond the 5), which columns in `common' work?
for s in R:
    if s in rows:
        continue
    ok = [c for c in common if isqrt(s * s + c) ** 2 == s * s + c]
    print(f"[ext] Q3 extra row {s}: works with columns {ok}")
