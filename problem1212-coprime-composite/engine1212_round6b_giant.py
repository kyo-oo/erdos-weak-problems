#!/usr/bin/env python3
"""#1212 ROUND 6b — THE SHEARED-CORRIDOR GIANT WITNESS ENGINE.

THE SHEAR (round-6 discovery, the clean reduction):
  a = (X+Y)/2, b = (X-Y)/2  (X > Y > 0, both odd; hubs = lattice pts).
  Hub validity: gcd(X,Y)=1 ∧ X,Y odd ⟺ gcd(a,b)=1 ∧ a+b odd.
  X-compositeness carrier: keep X = a+b ≡ 0 (mod 3) by taking x-moves in
  blocks of 3 (X += 6); y-moves leave X unchanged. Then X ≥ 9 composite.
  During an x-run, Y = a-b is fixed and hub i has gcd = gcd(Y, b+i) (since
  gcd(a+i, b+i) = gcd(Y, b+i)); the run stalls when b+s shares a prime | Y.
  During a y-run, X fixed: hub j has gcd = gcd(X, b-1-j) roughly.
  Midpoint (intermediate) gcd divides gcd(2a±1, 2b±1) — checked exactly.

Moves from (a,b): (+1,+1)[+x], (+1,-1)[+y], (-1,-1)[-x], (-1,+1)[-y];
x-moves taken in blocks of 3 to preserve X ≡ 0 mod 3; a y-move preserves X
too. Block discipline: we track 'pending x' so x-moves come in 3s (or we
use single x-moves only when X's carrier is served by Y ≡ 0 mod 3 instead).

Self-avoidance: visited set over (a,b) hubs AND intermediate vertices
(X,Y) mixed pairs.

Greedy priorities: finish pending x-blocks first, then +x, +y, -y, -x.
Goal: max |vertices|, growth a → ∞. Output: vertex list + dual check.
"""
import sys, json, time
from math import gcd

def midpoint_ok(a, b, mv):
    """intermediate gcd exactly: +x: (X+1,Y) i.e. gcd(a+b+1, a-b);
    -x: (X-1,Y); +y: (X,Y+1) => gcd(a+b, a-b+1); -y: (X,Y-1)."""
    if mv == '+x':  return gcd(a + b + 1, a - b) == 1
    if mv == '-x':  return gcd(a + b - 1, a - b) == 1
    if mv == '+y':  return gcd(a + b, a - b + 1) == 1
    if mv == '-y':  return gcd(a + b, a - b - 1) == 1

def hub_ok(a, b):
    return gcd(a, b) == 1 and (a + b) % 2 == 1 and (a - b) >= 3 and (a + b) >= 9

def run_greedy(a0, b0, node_budget=2_000_000, time_budget=480.0):
    a, b = a0, b0
    assert hub_ok(a, b) and (a + b) % 3 == 0
    visited = {(a, b)}
    inter_visited = set()
    path = [(a, b)]          # hub sequence in (a,b) coords
    pending = 0              # x-moves pending to complete a block of 3
    t0 = time.time(); nodes = 0
    def try_moves(cands):
        nonlocal a, b, pending
        for mv in cands:
            da, db = {'+x': (1, 1), '+y': (1, -1), '-x': (-1, -1), '-y': (-1, 1)}[mv]
            na, nb = a + da, b + db
            np_ = (pending + 1) % 3 if mv in '+x-x' else pending
            # X parity/compositeness: X = a+b must stay ≡ 0 mod 3 at hubs.
            if (na + nb) % 3 != 0:
                continue
            if not hub_ok(na, nb):
                continue
            if (na, nb) in visited:
                continue
            if not midpoint_ok(a, b, mv):
                continue
            # intermediate vertex (exact (X,Y)):
            if mv == '+x':  iv = (a + b + 1, a - b)
            elif mv == '-x': iv = (a + b - 1, a - b)
            elif mv == '+y': iv = (a + b, a - b + 1)
            else:            iv = (a + b, a - b - 1)
            if iv in inter_visited:
                continue
            # COMMIT
            inter_visited.add(iv)
            visited.add((na, nb))
            path.append((na, nb))
            a, b = na, nb
            pending = np_
            return mv
        return None
    last_report = 0
    while nodes < node_budget and time.time() - t0 < time_budget:
        nodes += 1
        # order: finish pending block, else fresh +x; then +y, -y, -x
        if pending == 1:
            mv = try_moves(['+x', '-x'])
        elif pending == 2:
            mv = try_moves(['+x', '-x'])
        else:
            mv = try_moves(['+x', '+y', '-y', '-x'])
        if mv is None:
            if pending == 0:
                # fully stuck
                break
            else:
                # must finish a block but cannot: try any y move to reposition
                mv = try_moves(['+y', '-y'])
                if mv is None:
                    break
        if len(path) - last_report >= 5000:
            last_report = len(path)
    return path, a, b, time.time() - t0

def dual_verify(path):
    """SECOND METHOD: rebuild every (X,Y) vertex from the (a,b) list; check
    walk validity: adjacency (one coord ±1), gcd=1 (exact), min>1, composite
    (X≡0 mod 3 ∧ X>3 carrier or even≥4), distinctness; growth. Independent
    arithmetic — no reuse of engine predicates."""
    n = len(path)
    verts = []
    for i, (a, b) in enumerate(path):
        verts.append((a + b, a - b))
    # the full vertex list includes intermediates: reconstruct moves
    full = [verts[0]]
    for i in range(1, n):
        pa, pb = path[i - 1]; ca, cb = path[i]
        X, Y = verts[i - 1]; CX, CY = verts[i]
        # the move: which coord changed by 2
        if CX == X + 2 and CY == Y:
            full.append((X + 1, Y))
        elif CX == X - 2 and CY == Y:
            full.append((X - 1, Y))
        elif CY == Y + 2 and CX == X:
            full.append((X, Y + 1))
        elif CY == Y - 2 and CX == X:
            full.append((X, Y - 1))
        else:
            return None, f"BAD MOVE at {i}"
        full.append((CX, CY))
    # checks
    for i in range(len(full) - 1):
        (x1, y1), (x2, y2) = full[i], full[i + 1]
        if not ((abs(x1 - x2) == 1 and y1 == y2) or (abs(y1 - y2) == 1 and x1 == x2)):
            return None, f"NON-ADJACENT at {i}"
    for (x, y) in full:
        if gcd(x, y) != 1:  return None, f"NON-COPRIME {(x,y)}"
        if min(x, y) <= 1:  return None, f"MIN<=1 {(x,y)}"
        comp = (x % 2 == 0 and x >= 4) or (y % 2 == 0 and y >= 4) or \
               (x % 3 == 0 and x > 3) or (y % 3 == 0 and y > 3) or \
               (has_smaller_factor(x) if x > 3 else False) or \
               (has_smaller_factor(y) if y > 3 else False)
        if not comp: return None, f"NON-COMPOSITE {(x, y)}"
    if len(set(full)) != len(full):
        return None, f"REPEAT VERTEX"
    return full, None

def has_smaller_factor(n):
    if n < 4: return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return True
        i += 1
    return False

if __name__ == "__main__":
    a0, b0 = 21, 6   # X0 = 27 = 3^3 (composite carrier), Y0 = 15 (composite), gcd=3?? -> check
    # need gcd(a0,b0)=1, a0+b0 odd, X0 ≡ 0 mod 3
    # X0 = 27: a+b = 27 (odd? NO). pick: a0=20,b0=7: X=27 odd, Y=13, gcd(20,7)=1
    a0, b0 = 20, 7
    print(f"start (a,b)={(a0,b0)} -> (X,Y)=({a0+b0},{a0-b0})")
    path, a, b, dt = run_greedy(a0, b0)
    print(f"greedy: {len(path)} hubs, {dt:.1f}s, end (a,b)={(a,b)}")
    full, err = dual_verify(path)
    if err:
        print("DUAL VERIFY FAIL:", err)
        sys.exit(1)
    print(f"DUAL VERIFY GREEN: {len(full)} vertices, all adjacent, coprime, "
          f"composite, distinct; X range {full[0][0]}..{full[-1][0]}")
    with open("witness1212_giant.json", "w") as f:
        json.dump({"a0": a0, "b0": b0, "hubs_ab": path,
                   "verts": full}, f)
    print("saved witness1212_giant.json")
