#!/usr/bin/env python3
"""#1212 ROUND 2b — the DIRECTED infinite-path hunt.

Directed walk: only forward moves (x+2 via (x+1,y)) or (y+2 via (x,y+1)).
An infinite directed walk in the habitat = the FULL problem answered YES.
Strategy: DFS with growth pressure + step-pattern periodicity detection:
a periodic step pattern (0/1 sequence of x/y moves) sustained with all
habitat conditions = the candidate certificate (needs the residue-cycle
verification, engine round 3)."""
import sys
from math import gcd
sys.setrecursionlimit(100000)

def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n**0.5) + 1):
        if spf[i] == i:
            for j in range(i*i, n + 1, i):
                if spf[j] == j: spf[j] = i
    return spf

SPF_MAX = 4_000_000
spf = spf_sieve(SPF_MAX)

def composite(x):
    return x < SPF_MAX and x >= 4 and spf[x] != x

def habitat_ok(x, y):
    """Full habitat check with certified compositeness."""
    if x < 2 or y < 2 or x >= SPF_MAX or y < 4:
        return False
    if gcd(x, y) != 1:
        return False
    return composite(x) or composite(y)

def directed_moves(x, y):
    """Forward B-moves with certified in-habitat intermediate + landing."""
    out = []
    # x+2 via (x+1, y): intermediate even >= 4 iff x+1 >= 4 iff x >= 3
    if x + 1 >= 4 and gcd(x + 1, y) == 1 and y >= 3 and habitat_ok(x + 2, y):
        out.append((0, x + 2, y))
    # y+2 via (x, y+1)
    if y + 1 >= 4 and gcd(x, y + 1) == 1 and x >= 3 and habitat_ok(x, y + 2):
        out.append((1, x, y + 2))
    return out

def dfs_directed(x0, y0, target_steps=4000, node_budget=2_000_000):
    """DFS forward-only; maximize steps taken. Returns (path, exhausted)."""
    best = []
    path = [(x0, y0)]
    budget = [node_budget]
    def rec(x, y):
        if budget[0] <= 0:
            return
        budget[0] -= 1
        if len(path) > len(best):
            best[:] = path[:]
        if len(path) >= target_steps:
            raise RuntimeError("TARGET")
        for _, nx, ny in directed_moves(x, y):
            path.append((nx, ny))
            rec(nx, ny)
            path.pop()
    try:
        rec(x0, y0)
        return best, True
    except RuntimeError:
        return path, False

def pattern_of(path):
    """The 0/1 step pattern (x-move=0, y-move=1)."""
    return ''.join('0' if b[0] != a[0] else '1' for a, b in zip(path, path[1:]))

def find_period(s, min_block=4, max_block=400):
    """Smallest block b such that s is (s[:b]) repeated, sustained >= min_block."""
    n = len(s)
    for b in range(2, min(max_block, n // min_block) + 1):
        if n >= b * min_block and s[:b] * (n // b) == s[:b * (n // b)]:
            return b
    return None

if __name__ == "__main__":
    print("=== #1212 ROUND 2b: DIRECTED infinite-path hunt ===")
    # strong composite starts
    starts = [(9, 25), (25, 9), (15, 16), (25, 27), (9, 49), (21, 25),
              (27, 25), (33, 25), (25, 33), (27, 49), (35, 27), (9, 121)]
    best = None
    for s in starts:
        path, exhausted = dfs_directed(*s, target_steps=2500, node_budget=300_000)
        pat = pattern_of(path)
        per = find_period(pat)
        print(f"start {s}: {len(path)} steps, exhausted={exhausted}, "
              f"pattern-period={per}, max coord {max(max(p[0] for p in path), max(p[1] for p in path))}")
        if per and len(path) >= 8 * per:
            print(f"  *** PERIODIC DIRECTED PATTERN: block='{pat[:per]}' "
                  f"({pat[:per].count('0')} x-moves, {pat[:per].count('1')} y-moves) ***")
            # verify the translation: after one block, net (A, B)
            A = 2 * pat[:per].count('0')
            B = 2 * pat[:per].count('1')
            print(f"  translation per block: ({A}, {B})")
            # sustained over all full blocks?
            blocks = len(path) // per
            consistent = all(
                path[(k+1)*per] == (path[k*per][0] + A, path[k*per][1] + B)
                for k in range(blocks - 1))
            print(f"  translation sustained over {blocks} blocks: {consistent}")
        if best is None or len(path) > len(best[0]):
            best = (path, s)
    print(f"\nbest: {len(best[0])} steps from {best[1]}")
