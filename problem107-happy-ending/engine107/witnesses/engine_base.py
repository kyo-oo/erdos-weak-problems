#!/usr/bin/env python3
# scratch: core engine pieces for W69-F
import itertools, math, random, sys, time
from fractions import Fraction as F

def det3(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])

def normalize(S):
    mx = min(p[0] for p in S); my = min(p[1] for p in S)
    return [(p[0]-mx, p[1]-my) for p in S]

# ---------------- integer E(k,l) construction (ErSz61 Thm 2.5) -------------
def E_build(k, l):
    """Integer extremal cup/cap set: |E| = C(k+l-4,k-2), no k-cup, no l-cap,
    all pairwise slopes in (0, 1/4], min corner (0,0). Pure python ints."""
    if k <= 2 or l <= 2:
        return [(0, 0)]
    A = normalize([(4*x, 4*y) for (x, y) in E_build(k-1, l)])
    B = normalize([(4*x, 4*y) for (x, y) in E_build(k, l-1)])
    WA = max(x for x, _ in A); HA = max(y for _, y in A)
    WB = max(x for x, _ in B); HB = max(y for _, y in B)
    D = max(4*(HA+HB) + 2*(WA+WB), 8)
    Tx = WA + D
    Ty = HA + (D + WA + WB)//2
    U = list(A) + [(Tx+x, Ty+y) for (x, y) in B]
    # exact structural self-checks (pre-rescale: union slopes in (0, 3/4];
    # A/B-internal <= 1/4; A->B cross in [1/2, 3/4])
    for (pa, pb) in itertools.combinations(U, 2):
        dx = pb[0]-pa[0]; dy = pb[1]-pa[1]
        assert dx > 0 and 0 < 4*dy <= 3*dx, ("union slope", k, l, pa, pb)
    for (pa, pb) in itertools.combinations(A, 2):
        assert 0 < 4*(pb[1]-pa[1]) <= (pb[0]-pa[0]), ("A internal", k, l)
    for (pa, pb) in itertools.combinations(B, 2):
        assert 0 < 4*(pb[1]-pa[1]) <= (pb[0]-pa[0]), ("B internal", k, l)
    for pa in A:
        for pb in B:
            q = (pb[0]+Tx, pb[1]+Ty)
            dy = 4*(q[1]-pa[1]); dx = q[0]-pa[0]
            assert 2*dx <= dy <= 3*dx, ("cross", k, l, pa, q)
    return normalize([(3*x, y) for (x, y) in U])

# ---------------- cup/cap machinery ----------------------------------------
def is_cup(sub):
    s = sorted(sub)
    for i in range(len(s)-1):
        if s[i][0] == s[i+1][0]:
            return False
    for i in range(len(s)-2):
        if det3(s[i], s[i+1], s[i+2]) <= 0:
            return False
    return True

def is_cap(sub):
    s = sorted(sub)
    for i in range(len(s)-1):
        if s[i][0] == s[i+1][0]:
            return False
    for i in range(len(s)-2):
        if det3(s[i], s[i+1], s[i+2]) >= 0:
            return False
    return True

def has_kcup_lcap(pts, k, l):
    for sub in itertools.combinations(pts, k):
        if len(sub) >= 3 and is_cup(sub):
            return ('cup', sub)
    for sub in itertools.combinations(pts, l):
        if len(sub) >= 3 and is_cap(sub):
            return ('cap', sub)
    return None

def max_cup_cap_len(pts):
    s = sorted(pts)
    n = len(s)
    if n == 0:
        return (0, 0)
    bestc = 1; besth = 1
    fc = [[0]*n for _ in range(n)]
    fh = [[0]*n for _ in range(n)]
    for j in range(n):
        for i in range(j):
            fc[i][j] = 2; fh[i][j] = 2
            for h in range(i):
                if fc[h][i] + 1 > fc[i][j] and det3(s[h], s[i], s[j]) > 0:
                    fc[i][j] = fc[h][i] + 1
                if fh[h][i] + 1 > fh[i][j] and det3(s[h], s[i], s[j]) < 0:
                    fh[i][j] = fh[h][i] + 1
            bestc = max(bestc, fc[i][j]); besth = max(besth, fh[i][j])
    return (bestc, besth)

def cup_cap_end_labels(pts):
    s = sorted(pts); n = len(s)
    fc = [[0]*n for _ in range(n)]
    fh = [[0]*n for _ in range(n)]
    cend = [1]*n; hend = [1]*n
    for j in range(n):
        for i in range(j):
            fc[i][j] = 2; fh[i][j] = 2
            for h in range(i):
                if fc[h][i] + 1 > fc[i][j] and det3(s[h], s[i], s[j]) > 0:
                    fc[i][j] = fc[h][i] + 1
                if fh[h][i] + 1 > fh[i][j] and det3(s[h], s[i], s[j]) < 0:
                    fh[i][j] = fh[h][i] + 1
            cend[j] = max(cend[j], fc[i][j]); hend[j] = max(hend[j], fh[i][j])
    return {s[j]: (cend[j], hend[j]) for j in range(n)}

# ---------------- convexity engines ----------------------------------------
def hull_chain(pts):
    P = sorted(set(pts))
    if len(P) <= 2:
        return list(P)
    def half(seq):
        st = []
        for p in seq:
            while len(st) >= 2 and det3(st[-2], st[-1], p) <= 0:
                st.pop()
            st.append(p)
        return st
    return half(P)[:-1] + half(P[::-1])[:-1]

def convex_B(pts):
    n = len(pts)
    if n < 3 or len(set(pts)) != n:
        return False
    h = hull_chain(pts)
    if len(h) != n:
        return False
    m = len(h)
    def fan(v):
        return sum(det3(h[v], h[i], h[(i+1) % m])
                   for i in range(m) if i != v and (i+1) % m != v)
    f0 = fan(0)
    return f0 != 0 and fan(1 % m) == f0 and fan(2 % m) == f0

def convex_4criterion(pts):
    n = len(pts)
    if n < 3:
        return False
    if n == 3:
        return det3(*pts) != 0
    for q in itertools.combinations(pts, 4):
        s1 = det3(q[0], q[1], q[2]); s2 = det3(q[0], q[1], q[3])
        s3 = det3(q[0], q[2], q[3]); s4 = det3(q[1], q[2], q[3])
        if not (s1 > 0 and s2 > 0 and s3 > 0 and s4 > 0) and not (s1 < 0 and s2 < 0 and s3 < 0 and s4 < 0):
            return False
    return True

# ---------------- run tests -------------------------------------------------
t0 = time.time()
print("== E(k,l) sizes and properties ==")
for k in range(3, 6):
    for l in range(3, 6):
        E = E_build(k, l)
        m = len(E)
        want = math.comb(k+l-4, k-2)
        mc, mh = max_cup_cap_len(E)
        bf = has_kcup_lcap(E, k, l)
        print(f"E({k},{l}): |E|={m} (want {want}), maxcup={mc} (<= {k-1}), maxcap={mh} (<= {l-1}), brute={bf is None}")
        assert m == want and mc <= k-1 and mh <= l-1 and bf is None

print("E(5,5) coord magnitude:", max(max(abs(x), abs(y)) for x, y in E_build(5, 5)))
print("E(4,4):", E_build(4, 4))
print("elapsed %.1fs" % (time.time()-t0))

for (k, l) in ((4, 4), (5, 5)):
    E = E_build(k, l)
    lab = cup_cap_end_labels(E)
    vals = list(lab.values())
    coll = len(vals) - len(set(vals))
    print(f"E({k},{l}) labels: {sorted(vals)}")
    print(f"  collisions: {coll}")

rng = random.Random(1)
collsets = 0
for t in range(300):
    n = rng.randint(3, 12)
    while True:
        xs = rng.sample(range(0, 200), n)
        pts = sorted((x, rng.randrange(0, 200)) for x in xs)
        if all(det3(a, b, c) != 0 for a, b, c in itertools.combinations(pts, 3)):
            break
    lab = cup_cap_end_labels(pts)
    vals = list(lab.values())
    if len(vals) != len(set(vals)):
        collsets += 1
        if collsets <= 3:
            print("  random collision:", pts, sorted(vals))
print(f"random sets with label collisions: {collsets}/300")
print("elapsed %.1fs" % (time.time()-t0))
