#!/usr/bin/env python3
"""#1212 ROUND 6d — THE PHASE-LADDER GIANT WITNESS (multi-phase, CRT restore).

Shear coords: hub (a,b) <-> (X,Y) = (a+b, a-b). X-run at fixed Y: hub i is
gcd(Y, b+i)=1; mid (X_i+1, Y) needs gcd=1: collisions b+i = 0 mod q or
b+i = (q+1)/2 mod q for q | Y. With invariant b = (q+1)/2 mod q (i.e.
X = 2b+Y = 1 mod q), certified i <= (q_min(Y)-3)/2 (THE PHASE LAW).
Y-run at fixed X': hub j: gcd(X', b+m-j)=1; mid (X', Y+2j-1): collisions
c = 0 mod p or Y+2j = 1 mod p for p | X'.
STRONG RESTORE (the ladder): after x-run to X' and y-run m', next x-run at
Y''=Y+2m' needs X' = 1 mod q for all q | Y'', i.e. rad(Y'') | X'-1.

Phase DFS with backtracking over (m, m') choices; nodes budget; checkpoints.
Output: full vertex path + dual verification (independent rebuild).
"""
import sys, json, time
from math import gcd

def prime_factors(n):
    fs = set()
    x = n
    d = 2
    while d * d <= x:
        while x % d == 0:
            fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    return fs

def smallf(n):
    if n < 4: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return True
        i += 1
    return False

def qmin(n):
    fs = prime_factors(n)
    return min(fs)

def xrun_cert(b, Y):
    """max i (1-based) such that hubs i=1..i and mids 1..i-1..i all clean.
    hub collision: b+i = 0 mod q; mid collision: b+i = (q+1)/2 mod q."""
    best = 10**9
    for q in prime_factors(Y):
        # hub: i = (-b) mod q, smallest >=1
        ih = (-b) % q
        ih = ih if ih >= 1 else q
        # mid: i = ((q+1)/2 - b) mod q, smallest >=1
        im = ((q + 1) // 2 - b) % q
        im = im if im >= 1 else q
        best = min(best, ih - 1, im - 1)  # runs clean for i <= best
    return best

def yrun_cert(bm, Xp, Y):
    """from hub (a, bm) with fixed X', y-run j=1..: hub gcd(X', bm - j)=1 ->
    collision bm-j = 0 mod p (p | X'); mid (X', Y+2j-1): p | Y+2j-1 ->
    j = (1-Y)/2 mod p. Returns max clean j."""
    best = 10**9
    for p in prime_factors(Xp):
        # hub collision: j = bm mod p, smallest >=1
        jh = bm % p
        jh = jh if jh >= 1 else p
        # mid collision: j = (1-Y)*inv2 mod p
        inv2 = (p + 1) // 2
        jm = ((1 - Y) % p) * inv2 % p
        jm = jm if jm >= 1 else p
        best = min(best, jh - 1, jm - 1)
    return best

def phase_dfs(X0, Y0, node_budget=400000, time_budget=420.0, target_phases=10**9):
    """X0 ≡ 1 mod rad(Y0) assumed; both composite, odd, coprime."""
    t0 = time.time()
    best = {"verts": 0, "phases": [], "end": None}
    phases = []   # list of (m, m') per phase
    nodes = [0]

    def emit(phases):
        """build vertex path from phase list"""
        X, Y = X0, Y0
        b = (X - Y) // 2
        verts = []
        for (m, mp) in phases:
            for i in range(1, m + 1):
                verts.append((X + 2 * i - 1, Y))   # mid
                verts.append((X + 2 * i, Y))       # hub
            X = X + 2 * m
            b = (X - Y) // 2
            for j in range(1, mp + 1):
                verts.append((X, Y + 2 * j - 1))
                verts.append((X, Y + 2 * j))
            Y = Y + 2 * mp
        return verts, X, Y

    def rec(X, Y, depth):
        nodes[0] += 1
        if nodes[0] > node_budget or time.time() - t0 > time_budget:
            return
        verts, _, _ = emit(phases)
        if len(verts) > best["verts"]:
            best["verts"] = len(verts); best["phases"] = list(phases)
        if depth >= target_phases:
            return
        b = (X - Y) // 2
        mmax = xrun_cert(b, Y)
        # candidate m: prefer large but allow all (X' = X + 2m composite, big qmin)
        cands_m = []
        for m in range(mmax, 0, -1):
            Xp = X + 2 * m
            if not smallf(Xp):
                continue
            qX = qmin(Xp)
            # y-run cert at bm = b + m
            bm = b + m
            mpmax = yrun_cert(bm, Xp, Y)
            if mpmax < 1:
                continue
            # search m' with Y'' = Y + 2m' X'-1-smooth & composite & big qmin
            good = []
            for mp in range(mpmax, 0, -1):
                Ypp = Y + 2 * mp
                radXm1 = Xp - 1
                if Ypp % 1 == 0 and all(radXm1 % q == 0 for q in prime_factors(Ypp)):
                    qY = qmin(Ypp)
                    if qY >= 5:
                        good.append((mp, qY))
            if good:
                # prefer the m' with the largest next x-run potential
                good.sort(key=lambda t: -t[1])
                cands_m.append((m, Xp, good[:6], mpmax))
        if not cands_m:
            return
        for (m, Xp, goods, mpmax) in cands_m[:12]:
            for (mp, qY) in goods:
                phases.append((m, mp))
                rec(Xp, Y + 2 * mp, depth + 1)
                phases.pop()
                if nodes[0] > node_budget or time.time() - t0 > time_budget:
                    return

    rec(X0, Y0, 0)
    return best, nodes[0], time.time() - t0

def dual_verify(verts):
    for i in range(len(verts) - 1):
        x1, y1 = verts[i]; x2, y2 = verts[i + 1]
        if not ((abs(x1 - x2) == 1 and y1 == y2) or (abs(y1 - y2) == 1 and x1 == x2)):
            return f"NON-ADJ {i}"
    for (x, y) in verts:
        if gcd(x, y) != 1: return f"NON-COPRIME {(x,y)}"
        if min(x, y) <= 1: return f"MIN {(x,y)}"
        if not (smallf(x) or smallf(y)): return f"NON-COMP {(x,y)}"
    if len(set(verts)) != len(verts): return "DUP"
    return None

if __name__ == "__main__":
    # base: X ≡ 1 mod rad(Y), both composite: Y = 10201 = 101^2, X ≡ 1 mod 101
    # e.g. X = 203 = 7*29: 203 mod 101 = 1 ✓; X composite ✓ Y composite ✓
    X0, Y0 = 203, 10201
    best, nodes, dt = phase_dfs(X0, Y0)
    verts, Xe, Ye = (lambda ph: (lambda e: (e[0], e[1], e[2]))(  # ugly; redo below
        None)) if False else (None, None, None)
    # rebuild
    X, Y = X0, Y0
    vv = []
    for (m, mp) in best["phases"]:
        for i in range(1, m + 1):
            vv.append((X + 2 * i - 1, Y)); vv.append((X + 2 * i, Y))
        X = X + 2 * m
        for j in range(1, mp + 1):
            vv.append((X, Y + 2 * j - 1)); vv.append((X, Y + 2 * j))
        Y = Y + 2 * mp
    err = dual_verify(vv)
    print(f"PHASE DFS: {len(best['phases'])} phases, {len(vv)} vertices, "
          f"nodes={nodes}, {dt:.1f}s; end (X,Y)=({X},{Y})")
    print("phases (m, m'):", best["phases"][:30])
    print("DUAL:", "FAIL " + str(err) if err else "GREEN")
    json.dump({"X0": X0, "Y0": Y0, "phases": best["phases"], "verts": vv},
              open("witness1212_giant.json", "w"))
    print("saved witness1212_giant.json")
