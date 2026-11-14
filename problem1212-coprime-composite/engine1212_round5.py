#!/usr/bin/env python3
"""#1212 ROUND 5 — THE SELF-AVOIDING STRIP SNAKE (non-monotone periodic block).

The monotone periodic lanes are certified DEAD (round 4: M=210 depth<=5 over
525 bases; M=2310 depth<=14 over 6930 bases — the coverage/(B) coupling kills
every monotone staircase). THE REMAINING PERIODIC FREEDOM: the walk may use
BACKWARD moves (-1 in a coordinate), as long as the whole block is
SELF-AVOIDING and confined to the box [X0, X0+M] x [Y0, Y0+M] with net
translation (M, M) — then period copies tile disjointly and the infinite
walk is simple (cross-period distinctness by the box; within-block by the
visited set).

Vertex conditions (uniform, the round-4 scheduling lemma):
  BAND: 1 <= |x - y| <= 12 with hub |d| even in {2..12}, intermediate |d'|
        odd in {1,3,5,7,9,11} — every prime of the translated gcd divides M.
  (B):  for q in {3,5,7,11}:  q | (x - y) -> q does not divide x.
  PAR:  not both even (hubs odd-odd; intermediates mixed — automatic).
  COV:  hubs: some q in {3,5,7,11} divides x or y; intermediates: the even
        coordinate is the 2-carrier — automatic.

DFS at the vertex level with move priorities (+x, +y, -y, -x), self-avoidance
visited set, dead-end backtracking, node budget.
"""
import sys, json, time

M = 2310
QCOV = (3, 5, 7, 11)
DHUB = {2, 4, 6, 8, 10, 12}      # |d| at hubs
DINT = {1, 3, 5, 7, 9, 11}        # |d'| at intermediates

def hub_ok(X, Y):
    d = X - Y
    ad = d if d >= 0 else -d
    if ad not in DHUB:
        return False
    for q in QCOV:
        if d % q == 0 and X % q == 0:
            return False
    for q in QCOV:
        if X % q == 0 or Y % q == 0:
            return True
    return False

def inter_ok(X, Y):
    """intermediate vertex (X, Y) — mixed parity, d' = X - Y."""
    d = X - Y
    ad = d if d >= 0 else -d
    if ad not in DINT:
        return False
    for q in QCOV:
        if d % q == 0 and X % q == 0:
            return False
    return True

def snake_search(X0, Y0, node_budget=4_000_000, time_budget=300.0):
    """DFS: vertex-level walk from (X0, Y0) to (X0+M, Y0+M), self-avoiding."""
    TX, TY = X0 + M, Y0 + M
    visited = set()
    path = []
    nodes = [0]
    t0 = time.time()
    # move = (dx, dy) on the VERTEX level; priority toward target
    # from a hub (odd,odd): try +x, +y, -y, -x (each goes to mixed, then the
    # forced continuation to the next hub) — we search at HUB level with
    # 2-step moves; intermediate checked via inter_ok.
    def dfs(x, y):
        if (x, y) == (TX, TY):
            return True
        if nodes[0] > node_budget or time.time() - t0 > time_budget:
            return False
        nodes[0] += 1
        # candidate hub-moves (dx, dy) with |dx|+|dy|=2 in one coordinate
        for dx, dy in ((2, 0), (0, 2), (0, -2), (-2, 0)):
            nx, ny = x + dx, y + dy
            if not (X0 <= nx <= TX and Y0 <= ny <= TY):
                continue
            if (nx, ny) in visited:
                continue
            # intermediate
            ix, iy = x + dx // 2, y + dy // 2
            if (ix, iy) in visited:
                continue
            if not inter_ok(ix, iy):
                continue
            if not hub_ok(nx, ny):
                continue
            visited.add((nx, ny)); visited.add((ix, iy))
            path.append(((ix, iy), (nx, ny)))
            if dfs(nx, ny):
                return True
            path.pop()
            visited.discard((nx, ny)); visited.discard((ix, iy))
        return False
    if not hub_ok(X0, Y0):
        return None
    visited.add((X0, Y0))
    ok = dfs(X0, Y0)
    if not ok:
        return None
    verts = [(X0, Y0)]
    for interm, hubv in path:
        verts.append(interm); verts.append(hubv)
    assert verts[-1] == (TX, TY)
    assert all(v not in verts[:i] for i, v in enumerate(verts)) or True
    # verify distinctness properly
    assert len(set(verts)) == len(verts)
    return verts

if __name__ == "__main__":
    X0, Y0 = 1393, 1387   # the round-4 deepest base (d0=6, u=238)
    t0 = time.time()
    v = snake_search(X0, Y0, node_budget=6_000_000, time_budget=420.0)
    dt = time.time() - t0
    if v is None:
        print(f"SNAKE FAILED (or budget) after {dt:.1f}s")
        sys.exit(1)
    print(f"SNAKE FOUND: {len(v)} vertices in {dt:.1f}s")
    print("first 10:", v[:10])
    print("last 6:", v[-6:])
    with open("block1212_snake.json", "w") as f:
        json.dump({"X0": X0, "Y0": Y0, "M": M, "verts": v}, f)
