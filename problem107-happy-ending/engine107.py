#!/usr/bin/env python3
"""engine107.py — commander's engine for problem107-happy-ending. v3: verified-witness program.

 (a) 8-POINT NO-CONVEX-5 WITNESSES: the four 5x5-lattice witnesses (first wave's receipt,
     recovered) + the interleaved cup/cap family (8 points: even-x parabola cup + odd-x cap,
     the first wave's n5b family). EVERY witness verified by TWO methods:
     M1 full brute force over all C(8,5)=56 subsets (hull-vertex test);
     M2 the cups/caps DP certificate (sound absence: max_{p<q}(U[q]+D[p]) < k+2 ==> no k-gon)
     — certificate may be inconclusive (crude); brute is decisive.
 (b) f(4)=5 SWEEP: 10^4 random GP 5-point sets all contain a convex 4-gon (two methods:
     hull-size >= 4 AND brute 4-subsets).
 (c) FRONTIER TABLE: binom(2n-4,n-2)+1 vs 2^{n-2}+1, n=3..40 (the certified open gap).
 (d) LABEL EXPERIMENT: injectivity machine truth for (cup-ending, cap-ending) labels.
 (e) 4-POINT NO-CONVEX-4 WITNESS + 16-point no-convex-6 structured attempt:
     4 points with one inside the triangle of others (explicit, verified);
     16-point hunt: best-effort structured (honest report).

Exact integer arithmetic only.
"""
from fractions import Fraction
import itertools, math, random, time

X, Y = 0, 1

def orient(a, b, c):
    return (b[X]-a[X])*(c[Y]-a[Y]) - (b[Y]-a[Y])*(c[X]-a[X])

def general_position(S):
    n = len(S)
    for i in range(n):
        dirs = set()
        for j in range(n):
            if i == j:
                continue
            dx, dy = S[j][X]-S[i][X], S[j][Y]-S[i][Y]
            g = math.gcd(dx, dy)
            dx, dy = dx//g, dy//g
            if dx < 0 or (dx == 0 and dy < 0):
                dx, dy = -dx, -dy
            d = (dx, dy)
            if d in dirs:
                return False
            dirs.add(d)
    return True

def hull_vertices(S):
    pts = sorted(set(map(tuple, S)))
    if len(pts) <= 2:
        return set(pts)
    def half(seq):
        h = []
        for p in seq:
            while len(h) >= 2 and orient(h[-2], h[-1], p) <= 0:
                h.pop()
            h.append(p)
        return h
    lower = half(pts)
    upper = half(list(reversed(pts)))
    return set(lower[:-1]) | set(upper[:-1])

def in_convex_position(sub):
    return all(tuple(p) in hull_vertices(sub) for p in sub)

def brute_no_convex_kgon(S, k):
    """Decisive brute: ANY k-subset in convex position?"""
    for sub in itertools.combinations(S, k):
        if in_convex_position(list(sub)):
            return False, list(sub)
    return True, None

def cups_caps(S):
    n = len(S)
    cb = [dict() for _ in range(n)]; U = [1]*n
    for i in range(n):
        for j in range(i):
            if S[i][X] == S[j][X]:
                continue
            m = Fraction(S[i][Y]-S[j][Y], S[i][X]-S[j][X])
            if m == 0:
                continue
            if 2 not in cb[i] or m < cb[i][2]:
                cb[i][2] = m
            if U[i] < 2:
                U[i] = 2
            for (L, s) in cb[j].items():
                if s < m:
                    c = L+1
                    if c not in cb[i] or m < cb[i][c]:
                        cb[i][c] = m
                    if c > U[i]:
                        U[i] = c
    cabR = [dict() for _ in range(n)]; D = [1]*n
    for i in range(n-1, -1, -1):
        for j in range(i+1, n):
            if S[j][X] == S[i][X]:
                continue
            m = Fraction(S[j][Y]-S[i][Y], S[j][X]-S[i][X])
            if m == 0:
                continue
            if 2 not in cabR[i] or m < cabR[i][2]:
                cabR[i][2] = m
            if D[i] < 2:
                D[i] = 2
            for (L, s) in cabR[j].items():
                if s > m:
                    c = L+1
                    if c not in cabR[i] or m < cabR[i][c]:
                        cabR[i][c] = m
                    if c > D[i]:
                        D[i] = c
    return U, D

def certificate_best(S):
    S = sorted(S)
    U, D = cups_caps(S)
    n = len(U)
    best = 0
    for p in range(n):
        for q in range(p+1, n):
            v = U[q] + D[p]
            if v > best:
                best = v
    return best, max(U), max(D)

KNOWN_LATTICE_WITNESSES = [
    [(0, 0), (0, 3), (1, 1), (1, 2), (3, 1), (3, 2), (4, 0), (4, 3)],
    [(0, 0), (0, 4), (1, 1), (1, 3), (2, 1), (2, 3), (3, 0), (3, 4)],
    [(0, 1), (0, 4), (1, 2), (1, 3), (3, 2), (3, 3), (4, 1), (4, 4)],
    [(1, 0), (1, 4), (2, 1), (2, 3), (3, 1), (3, 3), (4, 0), (4, 4)],
]

def interleaved_family(m=4, A=1, B=1):
    """8 points: even x = 2t with y = A*t^2 (cup, high); odd x = 2t+1 with y = -(m-1-t)^2 - B (cap, low).
    Generalizes the first wave's n5b family ((0,0),(2,1),(4,4),(6,9)) + ((1,-7),(3,-2),(5,1),(7,2))
    [t^2: 0,1,4,9; -(3-t)^2-...: -7,-2,1,2 = -(3-t)^2+2... pattern matched with B offset]."""
    S = []
    for t in range(m):
        S.append((2*t, A * t * t))
    for t in range(m):
        S.append((2*t + 1, -(m - 1 - t) ** 2 + 2))
    return S

def part_a():
    print("=" * 78)
    print("A  8-POINT NO-CONVEX-5 WITNESSES — every one TWO-method verified (brute decisive)")
    ok = True
    witnesses = [("lattice-%d" % (i+1), w) for i, w in enumerate(KNOWN_LATTICE_WITNESSES)]
    witnesses.append(("interleaved-cup-cap", interleaved_family()))
    for name, w in witnesses:
        S = sorted(w)
        gp = general_position(S)
        brute, found = brute_no_convex_kgon(S, 5)
        best, mc, mcap = certificate_best(S)
        print(f"  {name:22s} GP={gp} brute56(no conv-5)={brute} [found={found}] "
              f"DPcert(no-5: best<7)={best < 7} bestU+D={best} maxcup={mc} maxcap={mcap}")
        ok &= gp and brute
    # 4-point no-convex-4 witness: one point inside the triangle of the others
    S4 = [(0, 0), (6, 0), (3, 9), (3, 2)]
    gp4 = general_position(S4)
    b4, _ = brute_no_convex_kgon(S4, 4)
    print(f"  4-pt witness (1 interior): GP={gp4} brute(no conv-4)={b4}  ==> f(4) >= 5 machine-witnessed")
    ok &= gp4 and b4
    print(f"  A ALL-GREEN: {ok}")
    return ok

def part_b():
    print("=" * 78)
    print("B  f(4)=5 SWEEP: 10^4 RANDOM GP 5-POINT SETS ALL CONTAIN A CONVEX 4-GON")
    rng = random.Random(970)
    fails = disagree = 0
    for t in range(10 ** 4):
        while True:
            pts = [(rng.randint(-1000, 1000), rng.randint(-1000, 1000)) for _ in range(5)]
            if len(set(pts)) == 5 and general_position(pts):
                break
        m1 = len(hull_vertices(pts)) >= 4
        m2 = any(in_convex_position(list(s)) for s in itertools.combinations(pts, 4))
        if not m1 and not m2:
            disagree += 1
        if not m2:
            fails += 1
            print(f"  COUNTEREXAMPLE: {pts}")
    print(f"  B: failures={fails}/10^4  both-method-failures={disagree}  (m2 = brute 4-subsets = DEFINITIVE;")
    print(f"     m1 hull>=4 is sufficient-only: hull=3 + 2 interior CAN still contain convex 4-subsets")
    print(f"     -- exactly the classical interior-pair mechanism of the f(4)=5 proof)")
    return fails == 0 and disagree == 0

def part_c():
    print("=" * 78)
    print("C  FRONTIER TABLE: upper binom(2n-4,n-2)+1 vs conjectured 2^{n-2}+1 (n = 3..40)")
    for n in range(3, 41):
        up = math.comb(2*n-4, n-2) + 1
        lo = 2**(n-2) + 1
        print(f"  n={n:2d}  upper={up:.6e}  conjecture={lo:6d}  log2(upper)/n={math.log2(up)/n:.4f}")
    print("  the gap IS the open frontier (f(n)=2^{n-2}+1 conjecture OPEN for n>=7; f(6)=17 classical)")

def part_d():
    print("=" * 78)
    print("D  LABEL EXPERIMENT: (max-cup-ending, max-cap-ending) injectivity on random GP sets")
    rng = random.Random(61)
    total = dup = 0
    for t in range(300):
        n = rng.randint(6, 14)
        while True:
            pts = [(rng.randint(-50, 50), rng.randint(-50, 50)) for _ in range(n)]
            if len(set(pts)) == n and general_position(pts):
                break
        S = sorted(pts)
        U, D = cups_caps(S)
        labels = list(zip(U, D))
        total += 1
        if len(set(labels)) != n:
            dup += 1
    print(f"  sets tested={total}  sets-with-duplicated-labels={dup}")
    print(f"  => injectivity {'HOLDS' if dup == 0 else 'FAILS'} (machine truth for the audit lane)")

def part_e():
    print("=" * 78)
    print("E  16-POINT NO-CONVEX-6 STRUCTURED ATTEMPT (honest best-effort)")
    rng = random.Random(66)
    t0 = time.time()
    found = None
    tries = 0
    # structured random: 16 points in a tight 'two-layer' pattern + random hunts
    while time.time() - t0 < 60 and tries < 30000:
        tries += 1
        # pattern: two near-parallel jagged layers
        pts = []
        for i in range(16):
            x = i
            y = (i * i * 7 % 23) + rng.choice([0, 3, 17, 40]) * (1 if i % 2 else -1)
            pts.append((x, y))
        if len(set(pts)) != 16 or not general_position(pts):
            continue
        b, _ = brute_no_convex_kgon(pts, 6)
        if b:
            found = pts
            break
    if found:
        b2, _ = brute_no_convex_kgon(found, 6)
        print(f"  FOUND 16-pt no-convex-6 witness ({tries} tries): {found} verified={b2}")
    else:
        print(f"  no 16-pt witness found in {tries} structured tries (the classical ES 1961")
        print(f"  construction is the cited existence proof for all n; machine witness at n=5 stands)")

if __name__ == "__main__":
    t0 = time.time()
    a = part_a()
    b = part_b()
    part_c()
    part_d()
    part_e()
    print("=" * 78)
    print(f"ENGINE107 v3 COMPLETE wall={time.time()-t0:.1f}s  ALL-GREEN={'YES' if (a and b) else 'NO'}")
