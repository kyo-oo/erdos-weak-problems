#!/usr/bin/env python3
"""#1212 ROUND 6c — PHASE-CALCULUS DFS GIANT WITNESS.

Sheared coordinates (a,b), a=(X+Y)/2, b=(X-Y)/2. Hub valid:
gcd(a,b)=1 ∧ a+b odd ∧ a-b>=3 ∧ a+b>=9 ∧ (X=a+b composite ∨ Y=a-b composite).
Midpoint gcds checked exactly. DFS over the 4 moves (+x,+y,-y,-x) with
visited-set undo (self-avoidance), node budget, deep backtracking. Priorities
favor +x (long x-phases at fixed composite Y = the round-2 phase calculus in
shear form; x-run length = first multiple of a prime of Y above b).
Checkpoint to JSON; dual verify by full (X,Y) rebuild (second method).
"""
import sys, json, time
from math import gcd

def smallf(n):
    if n < 4: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return True
        i += 1
    return False

MOVES = (('+x', 1, 1), ('+y', 1, -1), ('-y', -1, 1), ('-x', -1, -1))

def hub_ok(a, b):
    return (gcd(a, b) == 1 and (a + b) % 2 == 1 and (a - b) >= 3
            and (a + b) >= 9 and (smallf(a + b) or smallf(a - b)))

def mid_ok(a, b, mv):
    if mv == '+x':  return gcd(a + b + 1, a - b) == 1
    if mv == '-x':  return gcd(a + b - 1, a - b) == 1
    if mv == '+y':  return gcd(a + b, a - b + 1) == 1
    return gcd(a + b, a - b - 1) == 1

def iv_of(a, b, mv):
    return {'+x': (a + b + 1, a - b), '-x': (a + b - 1, a - b),
            '+y': (a + b, a - b + 1), '-y': (a + b, a - b - 1)}[mv]

def dfs(a0, b0, node_budget, time_budget):
    t0 = time.time()
    visited = {(a0, b0)}
    ivs = set()
    path = [(a0, b0)]
    best = [list(path)]
    nodes = [0]
    sys.setrecursionlimit(100000)

    def rec(a, b):
        if len(path) > len(best[0]):
            best[0] = list(path)
        nodes[0] += 1
        if nodes[0] > node_budget or time.time() - t0 > time_budget:
            return False
        for mv, da, db in MOVES:
            na, nb = a + da, b + db
            if not hub_ok(na, nb) or (na, nb) in visited:
                continue
            if not mid_ok(a, b, mv):
                continue
            iv = iv_of(a, b, mv)
            if iv in ivs:
                continue
            visited.add((na, nb)); ivs.add(iv); path.append((na, nb))
            rec(na, nb)
            path.pop(); ivs.discard(iv); visited.discard((na, nb))
            if nodes[0] > node_budget or time.time() - t0 > time_budget:
                return False
        return False

    rec(a0, b0)
    return best[0], nodes[0], time.time() - t0

def dual_verify(path):
    """SECOND METHOD: rebuild (X,Y) vertices, full independent checks."""
    full = [(path[0][0] + path[0][1], path[0][0] - path[0][1])]
    for i in range(1, len(path)):
        pa, pb = path[i - 1]; ca, cb = path[i]
        X, Y = pa + pb, pa - pb; CX, CY = ca + cb, ca - cb
        if CX == X + 2 and CY == Y:      full.append((X + 1, Y))
        elif CX == X - 2 and CY == Y:    full.append((X - 1, Y))
        elif CY == Y + 2 and CX == X:    full.append((X, Y + 1))
        elif CY == Y - 2 and CX == X:    full.append((X, Y - 1))
        else: return None, f"BAD MOVE at hub {i}"
        full.append((CX, CY))
    for i in range(len(full) - 1):
        x1, y1 = full[i]; x2, y2 = full[i + 1]
        if not ((abs(x1 - x2) == 1 and y1 == y2) or (abs(y1 - y2) == 1 and x1 == x2)):
            return None, f"NON-ADJACENT at vertex {i}"
    for (x, y) in full:
        if gcd(x, y) != 1:  return None, f"NON-COPRIME {(x, y)}"
        if min(x, y) <= 1: return None, f"MIN<=1 {(x, y)}"
        if not (smallf(x) or smallf(y)): return None, f"NON-COMPOSITE {(x, y)}"
    if len(set(full)) != len(full):
        return None, "REPEATED VERTEX"
    return full, None

if __name__ == "__main__":
    a0, b0 = 17, 8          # (X,Y) = (25,9): both composite, coprime
    nb, tb = 8_000_000, 420.0
    path, nodes, dt = dfs(a0, b0, nb, tb)
    print(f"DFS: best path {len(path)} hubs, nodes={nodes}, {dt:.1f}s")
    full, err = dual_verify(path)
    if err:
        print("DUAL VERIFY FAIL:", err); sys.exit(1)
    print(f"DUAL VERIFY GREEN: {len(full)} vertices; X: {full[0][0]} -> {full[-1][0]}; "
          f"Y: {full[0][1]} -> {full[-1][1]}")
    json.dump({"a0": a0, "b0": b0, "hubs_ab": path, "nverts": len(full)},
              open("witness1212_giant.json", "w"))
    print("saved witness1212_giant.json")
