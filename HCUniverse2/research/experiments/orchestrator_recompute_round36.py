#!/usr/bin/env python3
# ORCHESTRATOR INDEPENDENT RECOMPUTE — AUDIT-36 / Round 36 (different-algorithm check)
# Engines deliberately DIFFERENT from field_letter_generation_round36_checks.py:
#   Φ_m coefficients: sympy.cyclotomic_poly (vs recursive poly division)
#   determinant signs: inversion-count Leibniz (vs cycle-parity Leibniz)
#   monomial reduction: own shift-reduction loop fed by sympy's Φ_m (vs red table)
#   kernels/ranks: sympy.Matrix nullspace/rank + modular ranks over 3 primes
#                  (vs hand-rolled Fraction RREF)
#   orbit counting: BFS over translate frozensets (vs sorted-tuple orbit sets)
#   arity totals: sympy det of I+P_k permutation matrices, averaged (vs closed
#                 formula / 2^{2m} subset character enumeration)
# Bounded: m <= 24, words <= C(8,4)=70, matrices <= 320x70, zero floats, exact only.
from itertools import combinations, permutations
from math import gcd
import sympy
from sympy import symbols, Poly, Matrix, ZZ, cyclotomic_poly

x = symbols('x')
PASS = 0
FAIL = 0

def rep(name, cond, detail=""):
    global PASS, FAIL
    if cond:
        PASS += 1
        print(f"  ok  {name} {detail}")
    else:
        FAIL += 1
        print(f"  FAIL {name} {detail}")

def units(m):
    return [a for a in range(1, m) if gcd(a, m) == 1]

# ---------------- my own reduction machinery (sympy-sourced cyclotomic) ----------
def my_red_table(m):
    cs = Poly(cyclotomic_poly(m, x), x, domain=ZZ).all_coeffs()  # descending
    asc = cs[::-1]  # ascending
    phi = len(asc) - 1
    assert asc[-1] == 1  # monic
    red = {}
    red[0] = [1] + [0] * (phi - 1)
    for e in range(1, m + 4 * m):  # bounded headroom
        if e < phi:
            v = [0] * phi
            v[e] = 1
        else:
            prev = red[e - 1]
            shifted = [0] + prev[:]  # x * x^{e-1}
            v = shifted[:phi]
            overflow = shifted[phi] if len(shifted) > phi else 0
            if overflow:
                for j in range(phi):
                    v[j] -= overflow * asc[j]
        red[e] = v
    return red, phi

def my_det_zeta(rows_exp, m, red, phi):
    """Leibniz determinant with INVERSION-COUNT signs (certificate uses cycle parity)."""
    n = len(rows_exp)
    acc = [0] * phi
    for perm in permutations(range(n)):
        inv = sum(1 for a in range(n) for b in range(a + 1, n) if perm[a] > perm[b])
        sgn = -1 if inv % 2 else 1
        e = 0
        for a in range(n):
            e += rows_exp[a][perm[a]]
        v = red[e % m]
        for k in range(phi):
            if v[k]:
                acc[k] += sgn * v[k]
    return acc

# ---------------- my own orbit counting (BFS frozensets) ------------------------
def my_orbit_dim(m, Phi, deg):
    """dim Hdg_deg = sum of orbit sizes over pure-balanced orbits, by BFS."""
    G = frozenset(units(m))
    p = deg // 2
    Phiset = frozenset(Phi)
    remaining = {frozenset(U) for U in combinations(sorted(G), deg)}
    total = 0
    while remaining:
        U = next(iter(remaining))
        orbit = {U}
        frontier = [U]
        while frontier:
            V = frontier.pop()
            for t in G:
                W = frozenset((t * u) % m for u in V)
                if W not in orbit:
                    orbit.add(W)
                    frontier.append(W)
        remaining -= orbit
        if all(sum(1 for u in V if u in Phiset) == p for V in orbit):
            total += len(orbit)
    return total

# ---------------- arity totals via permutation determinants ---------------------
def arity_total(m):
    """(1/m) sum_k det(I + rho(r^k)) via sympy exact det (two free C_m-orbits)."""
    n = 2 * m
    tot = 0
    for k in range(m):
        P = Matrix.zeros(n, n)
        for i in range(n):
            if i < m:
                j = (i + k) % m
            else:
                j = m + ((i - m + k) % m)
            P[i, j] = 1
        A = Matrix.eye(n) + P
        tot += int(A.det())
    assert tot % m == 0
    return tot // m

# ================= THE RECOMPUTES =================
print("=== (i)+(ii) orbit-count dims (my BFS, independent) ===")
for (m, Phi, degs) in [
    (5, (1, 2), {2: 2, 4: 1}),
    (7, (1, 2, 3), {2: 3, 4: 3, 6: 1}),
    (9, (1, 2, 4), {2: 3, 4: 3, 6: 1}),
    (15, (1, 2, 4, 7), {2: 4, 4: 6, 6: 4, 8: 1}),
    (16, (3, 5, 7, 15), {2: 4, 4: 6, 6: 4, 8: 1}),
    (20, (3, 7, 9, 19), {2: 4, 4: 6, 6: 4, 8: 1}),
    (24, (5, 7, 11, 23), {2: 4, 4: 6, 6: 4, 8: 1}),
]:
    for deg, expect in degs.items():
        v = my_orbit_dim(m, Phi, deg)
        rep(f"orbit-dim m={m} Phi={list(Phi)} deg={deg}", v == expect, f"-> {v} (expect {expect})")

print("=== (iii) THE SPAN at m=15 Phi=[1,2,4,7] (sympy kernels + modular ranks) ===")
m, Phi = 15, (1, 2, 4, 7)
red, phi = my_red_table(m)
G = units(m)
Phiset = set(Phi)

def hodge_kernel(deg):
    p = deg // 2
    Is = list(combinations(range(phi), deg))
    Us = list(combinations(sorted(G), deg))
    unb = [U for U in Us if sum(1 for u in U if u in Phiset) != p]
    rows = []
    for U in unb:
        dets = []
        for I in Is:
            mat = [[(u * i) % m for i in I] for u in U]
            dets.append(my_det_zeta(mat, m, red, phi))
        for k in range(phi):
            rows.append([dets[j][k] for j in range(len(Is))])
    M = Matrix(rows)
    ns = M.nullspace()
    basis = [[sympy.Rational(c) for c in v] for v in ns]
    return Is, Us, unb, basis

Is2, Us2, unb2, B2 = hodge_kernel(2)
rep("dim Hdg_2 at m=15 primitive via sympy nullspace", len(B2) == 4, f"-> {len(B2)} (expect 4)")

Is4, Us4, unb4, B4 = hodge_kernel(4)
rep("dim Hdg_4 at m=15 primitive via sympy nullspace", len(B4) == 6, f"-> {len(B4)} (expect 6)")

# the products d_a ^ d_b in Is4 coordinates (my own wedge accumulation)
idx4 = {I: k for k, I in enumerate(Is4)}
def wedge2(va, vb):
    out = [sympy.Rational(0)] * len(Is4)
    for i, I in enumerate(Is2):
        qa = va[i]
        if qa == 0:
            continue
        for j, J in enumerate(Is2):
            qb = vb[j]
            if qb == 0:
                continue
            if set(I) & set(J):
                continue
            seq = list(I) + list(J)
            inv = sum(1 for a in range(len(seq)) for b in range(a + 1, len(seq)) if seq[a] > seq[b])
            sgn = -1 if inv % 2 else 1
            out[idx4[tuple(sorted(I + J))]] += qa * qb * sgn
    return out

prods = []
for a in range(len(B2)):
    for b in range(a, len(B2)):
        prods.append(wedge2(B2[a], B2[b]))
rep("number of two-fold products (C(4+1,2)=10)", len(prods) == 10, f"-> {len(prods)}")

Mp = Matrix(prods).T  # 70 x 10
r_q = Mp.rank()
rep("product-span rank over Q (sympy rank)", r_q == 6, f"-> {r_q} (expect 6)")

def rat_to_mod(c, p):
    """Rational a/b -> a * b^{-1} mod p (exact modular image; b coprime to p)."""
    a, b = sympy.Rational(c).as_numer_denom()
    return (int(a) % p) * pow(int(b), -1, p) % p

def gf_rank(rows, p):
    """Gaussian elimination rank of a list of integer vectors over F_p (own code)."""
    mat = [[c % p for c in row] for row in rows]
    ncols = len(mat[0]) if mat else 0
    rank = 0
    pivots = []
    for col in range(ncols):
        pr = None
        for r in range(rank, len(mat)):
            if mat[r][col] % p:
                pr = r
                break
        if pr is None:
            continue
        mat[rank], mat[pr] = mat[pr], mat[rank]
        inv = pow(mat[rank][col], -1, p)
        mat[rank] = [(c * inv) % p for c in mat[rank]]
        for r in range(len(mat)):
            if r != rank and mat[r][col] % p:
                f = mat[r][col]
                mat[r] = [(a - f * b) % p for a, b in zip(mat[r], mat[rank])]
        pivots.append(col)
        rank += 1
        if rank == len(mat):
            break
    return rank

for p in (10007, 10009, 10037):
    rows_mod = [[rat_to_mod(c, p) for c in row] for row in prods]
    r_p = gf_rank(rows_mod, p)
    rep(f"product-span rank mod {p} (own F_p elimination)", r_p == 6, f"-> {r_p} (expect 6)")

# membership: every product vector vanishes on every unbalanced 4-word (independent dets)
member_ok = True
for v in prods:
    for U in unb4:
        acc = [0] * phi
        for idx, I in enumerate(Is4):
            if v[idx] == 0:
                continue
            mat = [[(u * i) % m for i in I] for u in U]
            d = my_det_zeta(mat, m, red, phi)
            for k in range(phi):
                if d[k]:
                    acc[k] += int(v[idx]) * d[k]
        if any(c != 0 for c in acc):
            member_ok = False
rep("degree-4 product membership (my independent dets)", member_ok, "-> all products Hodge")

print("=== (iv) the operator's arity totals (permutation determinants, sympy det) ===")
for mm, expect in [(1, 4), (2, 8), (3, 24), (4, 64), (5, 208), (6, 688)]:
    v = arity_total(mm)
    rep(f"arity total m={mm}", v == expect, f"-> {v} (expect {expect})")

print("=" * 80)
print(f"RESULT: {PASS} passed, {FAIL} failed (orchestrator independent recompute)")
import sys
sys.exit(0 if FAIL == 0 else 1)
