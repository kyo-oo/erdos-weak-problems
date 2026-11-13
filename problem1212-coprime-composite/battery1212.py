#!/usr/bin/env python3
"""#1212 battery — the certified-fact extractor for Kernel 65 (Erdos1212.lean).

Pure Python (L55: no sympy). Computes and cross-verifies every concrete fact
the kernel embeds:
  1. habitat membership, adjacency, path checks (mirror of the Lean Bool defs)
  2. BFS component censuses in boxes (the round-1 'components are small' law)
  3. explicit path witnesses (DFS long paths, the two-phase 103-vertex witness)
  4. degree tables for named vertices
  5. the phase-law instances ((15,49): 2 moves, wall at j=2;
     (203,10201): 49 moves, wall at j=49) — the engine-corrected landing law
  6. emits the Lean literal lists for the kernel
"""
from math import gcd
from collections import deque

def is_composite(n):
    if n < 4:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return True
        d += 1
    return False

def habitat(x, y):
    return x >= 2 and y >= 2 and gcd(x, y) == 1 and (is_composite(x) or is_composite(y))

def adj(a, b):
    (x1, y1), (x2, y2) = a, b
    if x1 == x2:
        return abs(y1 - y2) == 1
    if y1 == y2:
        return abs(x1 - x2) == 1
    return False

def neighbors(v, B):
    x, y = v
    for w in ((x+1, y), (x-1, y), (x, y+1), (x, y-1)):
        if 2 <= w[0] < B and 2 <= w[1] < B and habitat(*w):
            yield w

def bfs_component(start, B):
    """Habitat component of start within [2,B)^2, BFS order."""
    if not habitat(*start):
        return None
    comp = {start}
    order = [start]
    q = deque([start])
    while q:
        v = q.popleft()
        for w in neighbors(v, B):
            if w not in comp:
                comp.add(w)
                order.append(w)
                q.append(w)
    return order, comp

def deg(v, B=10**9):
    x, y = v
    return sum(1 for w in ((x+1,y),(x-1,y),(x,y+1),(x,y-1)) if habitat(*w))

def path_check(P):
    """All vertices habitat + consecutive adjacent."""
    for v in P:
        if not habitat(*v):
            return False, f"habitat fail at {v}"
    for a, b in zip(P, P[1:]):
        if not adj(a, b):
            return False, f"adjacency fail {a}->{b}"
    return True, None

def no_exit_check(comp, B):
    """No habitat vertex of the box outside comp is adjacent to comp."""
    for x in range(2, B):
        for y in range(2, B):
            if (x, y) in comp or not habitat(x, y):
                continue
            for w in neighbors((x, y), B):
                if w in comp:
                    return False, ((x, y), w)
    return True, None

def phase_check(x, y, m, q):
    """Certified x-phase: x odd composite, y odd composite, x % rad? here:
    verify all intermediates (x+2j+1, y) and landings (x+2j+2, y) for j<m are
    G-vertices coprime to y, and the wall lands at j=m if 2m+3=q."""
    ok = True
    for j in range(m):
        if gcd(x + 2*j + 1, y) != 1: return False, f"intermediate collision j={j}"
        if gcd(x + 2*j + 2, y) != 1: return False, f"landing collision j={j}"
    wall_int = gcd(x + 2*m + 1, y) != 1
    wall_land = gcd(x + 2*m + 2, y) != 1
    return True, (wall_int, wall_land)

if __name__ == "__main__":
    print("=== BATTERY 1212 (Kernel 65 fact extraction) ===")
    # 1. round-1 type analysis spot-checks
    print("\n--(1) type analysis: parity/carrier spot checks--")
    for (x, y) in [(9, 25), (15, 49), (203, 10201), (301, 10205)]:
        print(f"({x},{y}): habitat={habitat(x,y)} composite_x={is_composite(x)} "
              f"composite_y={is_composite(y)} gcd={gcd(x,y)} odd={x%2==1 and y%2==1}")

    # 2. component censuses (round-1 'components small at low coordinates')
    print("\n--(2) component censuses--")
    for start, B in [((9, 25), 30), ((9, 25), 50), ((15, 16), 30), ((4, 9), 20),
                     ((25, 27), 30), ((15, 49), 60)]:
        order, comp = bfs_component(start, B)
        ok, bad = no_exit_check(comp, B)
        print(f"component of {start} in [2,{B})^2: {len(comp)} vertices; "
              f"no-exit-check: {ok}")
        if B == 30 and start == (9, 25):
            print("  BFS order:", order)

    # 3. degree table
    print("\n--(3) degree table (unbounded habitat-degree)--")
    for v in [(9, 25), (8, 25), (8, 27), (15, 49), (16, 49), (19, 49),
              (203, 10201), (204, 10201), (301, 10205)]:
        x, y = v
        nb = [w for w in ((x+1,y),(x-1,y),(x,y+1),(x,y-1)) if habitat(*w)]
        print(f"deg {v} = {len(nb)}: {nb}")

    # 4. phase instances
    print("\n--(4) phase-law instances--")
    # (15,49): q_min(49)=7 -> (7-3)/2 = 2 certified moves; wall at j=2 (landing 21)
    ok, walls = phase_check(15, 49, 2, 7)
    print(f"phase (15,49) m=2: ok={ok} walls(int,land)={walls}; "
          f"gcd(21,49)={gcd(21,49)} gcd(20,49)={gcd(20,49)}")
    # (203,10201): q_min=101 -> 49 certified moves; wall landing at j=49 (303)
    ok, walls = phase_check(203, 10201, 49, 101)
    print(f"phase (203,10201) m=49: ok={ok} walls(int,land)={walls}; "
          f"gcd(303,10201)={gcd(303,10201)} gcd(404,10201)={gcd(404,10201)}")
    # intermediate wall at j=100: 404 = 4*101
    print(f"intermediate wall: gcd(203+2*100+1,10201)={gcd(404,10201)} (404=4*101)")
    # y-phase after (301,10201): 2 certified moves -> (301,10205)
    ok, walls = phase_check(10201, 301, 2, 7)  # symmetric call
    print(f"y-phase from (301,10201) m=2 (roles swapped): ok={ok} walls={walls}; "
          f"gcd(301,10206)={gcd(301,10206)}")

    # 5. the two-phase 103-vertex witness
    print("\n--(5) the two-phase witness--")
    P = [(203, 10201)]
    for j in range(49):
        P.append((203 + 2*j + 1, 10201))
        P.append((203 + 2*j + 2, 10201))
    P.append((301, 10202))
    P.append((301, 10203))
    P.append((301, 10204))
    P.append((301, 10205))
    ok, bad = path_check(P)
    print(f"two-phase witness: length={len(P)} path_ok={ok} {bad if bad else ''}")
    print(f"  first={P[0]} last={P[-1]} "
          f"composite(last)=({is_composite(P[-1][0])},{is_composite(P[-1][1])})")

    # 6. a DFS long path from (9,25) in box 60 (round-1 engine evidence witness)
    print("\n--(6) DFS witness from (9,25), box 60--")
    def dfs(start, box, budget=400000):
        best, path, seen = [], [start], {start}
        steps = [(1,0),(-1,0),(0,1),(0,-1)]
        cnt = [budget]
        def rec(x, y):
            if cnt[0] <= 0: return
            cnt[0] -= 1
            if len(path) > len(best): best[:] = path[:]
            for dx, dy in steps:
                nx, ny = x+dx, y+dy
                if 2 <= nx <= box and 2 <= ny <= box and (nx,ny) not in seen \
                   and habitat(nx, ny):
                    seen.add((nx,ny)); path.append((nx,ny))
                    rec(nx, ny)
                    path.pop(); seen.remove((nx,ny))
        rec(*start)
        return best
    p = dfs((9, 25), 60, 300000)
    ok, bad = path_check(p)
    print(f"DFS path from (9,25) box 60: length={len(p)} ok={ok}")
    print("  path:", p[:30], "..." if len(p) > 30 else "")

    # 7. component of (203,10201) in a 1032-box slice is HUGE (engine: growth)
    #    (skip full BFS at 10201 scale; report the phase structure instead)
    print("\n--(7) parity of path witnesses (all B-hubs odd/odd; intermediates even)--")
    for v in P[:6]:
        print(f"   {v}: x%2={v[0]%2} y%2={v[1]%2}")

    # 8. Emit the Lean literal list for the two-phase witness + DFS witness
    print("\n--(8) Lean literals--")
    def lean_pair(v): return f"({v[0]}, {v[1]})"
    print("P103 (two-phase) — emit to file")
    with open("witness1212_P103.txt", "w") as f:
        f.write(" / ".join(lean_pair(v) for v in P))
    with open("witness1212_P925.txt", "w") as f:
        f.write(" / ".join(lean_pair(v) for v in p))
    print("  wrote witness1212_P103.txt, witness1212_P925.txt")
