#!/usr/bin/env python3
"""#1212 round 1 — the coprime-composite path engine.
Statement (verbatim, erdosproblems.com/1212):
  Let G be the graph with vertex set those pairs (x,y) in N^2 with
  gcd(x,y)=1, in which we join two vertices if they differ in only one
  coordinate, and thereby by ±1. Is there a path going to infinity on G,
  say P, such that for all (x,y) in P both min(x,y)>1 and at least one of
  x or y is composite?

Engine: DFS with backtracking inside a growing box, maximizing path length
in the habitat H = {(x,y) : gcd(x,y)=1, min(x,y)>1, (x composite or y composite)}.
Report: longest paths found, their step patterns, and structural fingerprints
(periodicity of (x mod M, y mod M), compositeness carriers)."""
from math import gcd

def is_composite(n):
    if n < 4:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return True
        d += 1
    return False

def in_habitat(x, y):
    if x < 2 or y < 2:
        return False
    if gcd(x, y) != 1:
        return False
    return is_composite(x) or is_composite(y)

def dfs_longest(x0, y0, box, time_budget=2_000_000):
    """Iterative DFS from (x0,y0); returns the longest habitat path."""
    best = []
    path = [(x0, y0)]
    seen = {(x0, y0)}
    steps = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    budget = [time_budget]
    def rec(x, y):
        if budget[0] <= 0:
            return
        budget[0] -= 1
        if len(path) > len(best):
            best[:] = path[:]
        for dx, dy in steps:
            nx, ny = x + dx, y + dy
            if 2 <= nx <= box and 2 <= ny <= box and (nx, ny) not in seen \
               and in_habitat(nx, ny):
                seen.add((nx, ny))
                path.append((nx, ny))
                rec(nx, ny)
                path.pop()
                seen.remove((nx, ny))
    rec(x0, y0)
    return best

if __name__ == "__main__":
    print("=== #1212 round 1: habitat path search ===")
    # sample starts where both coords are composite (safe habitat interior)
    starts = [(4, 9), (8, 9), (9, 10), (4, 15), (9, 25), (15, 16), (25, 27)]
    for s in starts:
        p = dfs_longest(*s, box=80, time_budget=300_000)
        xs = [q[0] for q in p]; ys = [q[1] for q in p]
        print(f"start {s}: length {len(p)}, x-range [{min(xs)},{max(xs)}], "
              f"y-range [{min(ys)},{max(ys)}], end {p[-1]}")
        if len(p) >= 12:
            print("   path:", p[:24], "..." if len(p) > 24 else "")
    # structural check on the best path: which coordinate carries compositeness,
    # and the step directions
    p = dfs_longest(9, 10, box=120, time_budget=2_000_000)
    dirs = []
    for (a, b), (c, d) in zip(p, p[1:]):
        dirs.append('R' if c > a else 'L' if c < a else 'U' if d > b else 'D')
    print(f"\nbest path from (9,10): length {len(p)}")
    print("steps:", ''.join(dirs[:120]))
    comp_carrier = ['X' if is_composite(a) and is_composite(b)
                    else 'x' if is_composite(a) else 'y' for (a, b) in p]
    print("compositeness carrier:", ''.join(comp_carrier[:120]))
    both_coprime_prime = [q for q in p if not is_composite(q[0]) and not is_composite(q[1])]
    print("vertices with BOTH coords prime (should be []):", both_coprime_prime[:5])
