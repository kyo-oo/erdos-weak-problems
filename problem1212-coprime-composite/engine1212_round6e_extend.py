#!/usr/bin/env python3
"""#1212 ROUND 6e — P103 EXTENSION DFS (the giant-witness assault).

Continue the certified 103-vertex witness p103 (ends at (301, 10205)) by a
4-move DFS (+x,+y,-y,-x) with self-avoidance against ALL p103 vertices and
all new vertices; hub validity = exact gcd/min/composite checks on (X,Y).
Priorities: +y (climb Y), -y, +x, -x. Deep backtracking, node budget.
Dual verification: full independent rebuild + checks (second method).
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

def hub_ok(X, Y):
    return (gcd(X, Y) == 1 and min(X, Y) > 1 and
            (smallf(X) or smallf(Y)) and X % 2 == 1 and Y % 2 == 1)

def inter_ok(X, Y):
    """mixed-parity intermediate: even coordinate >= 4 is the composite."""
    if X % 2 == Y % 2:
        return False
    if X % 2 == 0:
        return X >= 4 and gcd(X, Y) == 1 and min(X, Y) > 1
    return Y >= 4 and gcd(X, Y) == 1 and min(X, Y) > 1

def load_p103():
    """read p103 vertices from the kernel witness file"""
    txt = open("witness1212_P103.txt").read()
    verts = []
    for tok in txt.split("/"):
        tok = tok.strip().replace("(", "").replace(")", "")
        if "," in tok:
            a, b = tok.split(",")[:2]
            try:
                verts.append((int(a), int(b)))
            except ValueError:
                pass
    return verts

def dfs_extend(start_verts, node_budget=6_000_000, time_budget=420.0):
    t0 = time.time()
    visited = set(start_verts)
    path = list(start_verts)
    best = [list(path)]
    nodes = [0]
    sys.setrecursionlimit(2000000)
    # moves on the RAW (X,Y): (+x: (2,0)), (+y: (0,2)), (-y: (0,-2)), (-x: (-2,0))
    MV = ((2, 0), (0, 2), (0, -2), (-2, 0))

    def rec(X, Y):
        if len(path) > len(best[0]):
            best[0] = list(path)
        nodes[0] += 1
        if nodes[0] > node_budget or time.time() - t0 > time_budget:
            return
        for dx, dy in MV:
            # intermediate first
            nx, ny = X + dx, Y + dy
            ix, iy = X + dx // 2, Y + dy // 2
            if not hub_ok(nx, ny) or not inter_ok(ix, iy):
                continue
            if (nx, ny) in visited or (ix, iy) in visited:
                continue
            visited.add((nx, ny)); visited.add((ix, iy))
            path.append((ix, iy)); path.append((nx, ny))
            rec(nx, ny)
            path.pop(); path.pop()
            visited.discard((nx, ny)); visited.discard((ix, iy))
        return

    rec(path[-1][0], path[-1][1])
    return best[0], nodes[0], time.time() - t0

def dual_verify(verts):
    for i in range(len(verts) - 1):
        x1, y1 = verts[i]; x2, y2 = verts[i + 1]
        if not ((abs(x1 - x2) == 1 and y1 == y2) or (abs(y1 - y2) == 1 and x1 == x2)):
            return f"NON-ADJ at {i}: {verts[i]} -> {verts[i+1]}"
    for (x, y) in verts:
        if gcd(x, y) != 1: return f"NON-COPRIME {(x,y)}"
        if min(x, y) <= 1: return f"MIN {(x,y)}"
        if not (smallf(x) or smallf(y)): return f"NON-COMP {(x,y)}"
    if len(set(verts)) != len(verts): return "DUP VERTEX"
    return None

if __name__ == "__main__":
    p103 = load_p103()
    print(f"p103 loaded: {len(p103)} vertices, start {p103[0]}, end {p103[-1]}")
    err = dual_verify(p103)
    print("p103 self-dual:", "FAIL " + str(err) if err else "GREEN")
    best, nodes, dt = dfs_extend(p103)
    print(f"DFS EXTENSION: {len(best)} vertices (from {len(p103)}), "
          f"nodes={nodes}, {dt:.1f}s; end={best[-1]}")
    err = dual_verify(best)
    print("DUAL:", "FAIL " + str(err) if err else "GREEN")
    json.dump({"verts": best}, open("witness1212_extended.json", "w"))
    print("saved witness1212_extended.json")
