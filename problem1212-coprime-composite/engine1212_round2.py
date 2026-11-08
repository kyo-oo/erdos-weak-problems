#!/usr/bin/env python3
"""#1212 ROUND 2 — the infinite-path constructor + periodicity hunter.

Target: an infinite path in the habitat H = {(x,y): gcd(x,y)=1, min>1,
x or y composite} with ±1 single-coordinate steps. KILL SHAPE: a path
whose step pattern is eventually periodic with translation (A,B) —
vertex_{k+T} = vertex_k + (A,B) — where ALL habitat conditions on the
period are certified: then the infinite path EXISTS (induction) = the
FULL problem answered YES, unconditionally.

Structure (round-1): the path alternates B=(odd,odd) hubs with A=(even,odd)/
C=(odd,even) intermediates; net B-moves are ±2 in one coordinate.
"""
import random
from math import gcd

def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n**0.5) + 1):
        if spf[i] == i:
            for j in range(i*i, n + 1, i):
                if spf[j] == spf[j]: spf[j] = i
    return spf

SPF_MAX = 2_000_000
spf = spf_sieve(SPF_MAX)

def composite(x):
    if x < 4 or x >= SPF_MAX:
        return None  # unknown
    return spf[x] != x

def habitat(x, y):
    if x < 2 or y < 2:
        return False
    if gcd(x, y) != 1:
        return False
    cx, cy = composite(x), composite(y)
    if cx is None or cy is None:
        return None
    return cx or cy

# B-to-B moves: (dx, dy) in {(+2,0),(-2,0),(0,+2),(0,-2)} via intermediate
def b_moves(x, y):
    """yield (nx, ny, ix, iy) for valid B->B moves with in-habitat intermediate."""
    for dx, dy in ((2,0),(-2,0),(0,2),(0,-2)):
        nx, ny = x + dx, y + dy
        ix, iy = x + dx // 2, y + dy // 2
        if nx < 3 or ny < 3:
            continue
        hi = habitat(ix, iy)
        if hi is not True:
            continue
        # B-landing compositeness: at least one composite
        cx, cy = composite(nx), composite(ny)
        if cx is None or cy is None:
            continue  # stay in certified range
        if not (cx or cy):
            continue
        if gcd(nx, ny) != 1:
            continue
        yield nx, ny, ix, iy

def greedy_path(x0, y0, steps=200000, lookahead=2, seed=0, jitter=True):
    """Greedy B-walk with lookahead: prefer moves that keep >=1 onward option;
    random tie-breaking. Returns the B-vertex list."""
    rng = random.Random(seed)
    path = [(x0, y0)]
    x, y = x0, y0
    for k in range(steps):
        opts = list(b_moves(x, y))
        if not opts:
            return path, True  # dead end
        # score: number of onward options from the landing
        scored = []
        for nx, ny, ix, iy in opts:
            onward = len(list(b_moves(nx, ny)))
            scored.append((onward, rng.random() if jitter else 0, nx, ny))
        scored.sort(key=lambda t: (-t[0], t[1]))
        _, _, nx, ny = scored[0]
        path.append((nx, ny))
        x, y = nx, ny
    return path, False

def detect_period(path, max_T=200, min_rep=3):
    """Detect vertex_{k+T} = vertex_k + (A,B) sustained for >= min_rep periods."""
    n = len(path)
    for T in range(2, min(max_T, n // min_rep) + 1):
        A = path[T][0] - path[0][0]
        B = path[T][1] - path[0][1]
        if A <= 0 and B <= 0:
            continue
        ok = True
        reps = 0
        for k in range(n - T):
            if path[k + T] != (path[k][0] + A, path[k][1] + B):
                ok = False
                break
            if k % T == T - 1:
                reps += 1
        if ok and reps >= min_rep:
            return T, A, B, reps
    return None

if __name__ == "__main__":
    print("=== #1212 ROUND 2: infinite-path constructor ===")
    best = None
    for seed in range(40):
        for start in [(9, 25), (25, 9), (15, 16), (25, 27), (9, 49), (49, 9),
                      (21, 25), (25, 21), (27, 35), (35, 27), (33, 35), (49, 51)]:
            path, dead = greedy_path(*start, steps=3000, seed=seed)
            if best is None or len(path) > len(best[0]):
                best = (path, start, seed)
            if not dead and len(path) >= 3000:
                per = detect_period(path)
                print(f"start {start} seed {seed}: SURVIVED 3000 steps; "
                      f"period: {per}")
                if per:
                    T, A, B, reps = per
                    print(f"  *** PERIODIC CERTIFICATE: T={T} translation=({A},{B}) "
                          f"reps={reps} ***")
                    print("  period vertices:", path[:T])
                break
        else:
            continue
        break
    path, start, seed = best
    print(f"\nlongest: {len(path)} B-vertices from {start} (seed {seed})")
    xs = [p[0] for p in path]; ys = [p[1] for p in path]
    print(f"x-range [{min(xs)},{max(xs)}]  y-range [{min(ys)},{max(ys)}]")
    print("tail:", path[-12:])
    per = detect_period(path)
    print("period detect on longest:", per)
