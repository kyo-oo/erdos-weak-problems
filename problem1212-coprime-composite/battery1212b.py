#!/usr/bin/env python3
"""battery1212 round 2 — remaining census data for Kernel 65:
BFS orders, longest paths in small components, directed-death depths
(the r2b engine law), ring boxes for the no-exit sweeps."""
from math import gcd
from collections import deque
from itertools import permutations

def is_composite(n):
    if n < 4: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return True
        d += 1
    return False

def habitat(x, y):
    return x >= 2 and y >= 2 and gcd(x, y) == 1 and (is_composite(x) or is_composite(y))

def adjc(a, b):
    (x1, y1), (x2, y2) = a, b
    if x1 == x2: return abs(y1 - y2) == 1
    if y1 == y2: return abs(x1 - x2) == 1
    return False

def neighbors(v, B):
    x, y = v
    for w in ((x+1, y), (x-1, y), (x, y+1), (x, y-1)):
        if 2 <= w[0] < B and 2 <= w[1] < B and habitat(*w):
            yield w

def bfs_component(start, B):
    comp, order, q = {start}, [start], deque([start])
    while q:
        v = q.popleft()
        for w in neighbors(v, B):
            if w not in comp:
                comp.add(w); order.append(w); q.append(w)
    return order

def longest_path(order):
    """Longest simple path over the component vertex set (n <= 13: DFS)."""
    verts = order
    n = len(verts)
    best = []
    def rec(path, seen):
        nonlocal best
        if len(path) > len(best): best[:] = path[:]
        v = path[-1]
        for w in verts:
            if w not in seen and adjc(v, w):
                seen.add(w); path.append(w)
                rec(path, seen)
                path.pop(); seen.remove(w)
    for s in verts:
        rec([s], {s})
    return best

def live(x, y, k):
    """liveB x y k = exists directed habitat path of k+1 vertices from (x,y)."""
    if k == 0: return habitat(x, y)
    if not habitat(x, y): return False
    return live(x+1, y, k-1) or live(x, y+1, k-1)

if __name__ == "__main__":
    print("=== BATTERY 1212 round 2 ===")
    # BFS orders for the certified component censuses
    cens = [((4, 9), 20), ((9, 25), 30), ((15, 16), 30), ((25, 27), 30),
            ((15, 49), 60)]
    for (s, B) in cens:
        order = bfs_component(s, B)
        xs = [v[0] for v in order]; ys = [v[1] for v in order]
        ring = (min(xs)-1, max(xs)+1, min(ys)-1, max(ys)+1)
        w = ring[1]-ring[0]+1; h = ring[3]-ring[2]+1
        print(f"\ncomponent {s} box [2,{B}): {len(order)} vertices")
        print(f"  BFS order: {order}")
        print(f"  x-range [{min(xs)},{max(xs)}] y-range [{min(ys)},{max(ys)}] "
              f"ring box x[{ring[0]},{ring[1]}] y[{ring[2]},{ring[3]}] "
              f"({h}x{w} = {h*w} cells)")
        lp = longest_path(order)
        print(f"  longest path ({len(lp)}): {lp}")

    # directed-death depths for the 12 r2b engine starts
    print("\n=== directed-death (r2b engine law) ===")
    starts = [(9, 25), (25, 9), (15, 16), (25, 27), (9, 49), (21, 25),
              (27, 25), (33, 25), (25, 33), (27, 49), (35, 27), (9, 121)]
    for s in starts:
        d = 0
        while live(s[0], s[1], d):
            d += 1
            if d > 30: break
        # d = first k with liveB false => max directed path = d vertices
        print(f"start {s}: max directed path vertices = {d} (liveB false at k={d})")

    # quick parity check for phase structures
    print("\n=== phase numerics ===")
    print("gcd(303,10201) =", gcd(303, 10201), " gcd(404,10201) =", gcd(404, 10201))
    print("gcd(21,49) =", gcd(21, 49), " gcd(20,49) =", gcd(20, 49))
    print("gcd(301,10206) =", gcd(301, 10206), " gcd(301,10207) =", gcd(301, 10207))
    for k in range(0, 5):
        print(f"  gcd(15+{k},49) = {gcd(15+k,49)}")
    for k in range(0, 5):
        print(f"  gcd(301,10201+{k}) = {gcd(301,10201+k)}")
    # the 99-cell phase gcd sweep: k in [0,98]
    ok = all(gcd(203+k, 10201) == 1 for k in range(0, 99))
    print("phase gcd sweep k<99 all-coprime:", ok)
    ok = all(gcd(203+k, 10201) == 1 for k in range(0, 102))
    print("k<102 (incl. walls at 100,101):", ok, "(False expected: 303,404 walls)")
