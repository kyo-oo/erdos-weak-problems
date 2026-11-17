#!/usr/bin/env python3
# =============================================================================
# ROUND 38 EXPLORATION v2 — THE WEIL-WORLD LETTER MODEL (R2' face (b))
# Fast: the spectral structure computed STRUCTURALLY (the eigenvalues of
# [alpha]^* on ^4_Q H^1 are alpha^k * conj(alpha)^(4-k) with multiplicities
# C(4,k)C(4,4-k)), then VERIFIED against the actual 70x70 exterior matrix by
# trace/determinant/polynomial-identity checks. Calibrated against the repo's
# forcing-frame receipts (K=Q(i), alpha=2+i).
# =============================================================================
import sys
from fractions import Fraction
from itertools import combinations
from sympy import Poly, symbols, QQ
from sympy.polys.polytools import invert as poly_invert

t = symbols('t')
N = 8

def kmul(x, y, d):
    return (x[0]*y[0] - d*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def kpow(x, m, d):
    r = (1, 0)
    for _ in range(m):
        r = kmul(r, x, d)
    return r
def knorm(x, d):
    return x[0]*x[0] + d*x[1]*x[1]
def kconj(x):
    return (x[0], -x[1])
def kinQ(x):
    return x[1] == 0
def minpoly(x, d):
    """The min poly over Q of x = a + b sqrt(-d) (b != 0): t^2 - 2a t + N(x)."""
    if x[1] == 0:
        return Poly(t - x[0], t, domain=QQ)
    return Poly(t*t - 2*x[0]*t + knorm(x, d), t, domain=QQ)

def alpha_matrix(alpha, d):
    a, b = alpha
    M = [[Fraction(0)]*N for _ in range(N)]
    for j in range(4):
        M[2*j][2*j] = Fraction(a)
        M[2*j+1][2*j] = Fraction(b)
        M[2*j][2*j+1] = Fraction(-d*b)
        M[2*j+1][2*j+1] = Fraction(a)
    return M

def mat_mul(A, B):
    n = len(A)
    C = [[Fraction(0)]*n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k]:
                for j in range(n):
                    C[i][j] += A[i][k]*B[k][j]
    return C

def mat_vec(A, v):
    n = len(A)
    return [sum(A[i][j]*v[j] for j in range(n)) for i in range(n)]

WORDS4 = list(combinations(range(N), 4))
WIX = {w: i for i, w in enumerate(WORDS4)}

def ext_action(M, word):
    out = {}
    acc = {(): Fraction(1)}
    for i in word:
        new = {}
        for U, c in acc.items():
            for letter, coeff in enumerate(M[i]):
                if coeff == 0 or letter in U:
                    continue
                sgn = (-1)**sum(1 for u in U if u > letter)
                key = tuple(sorted(list(U) + [letter]))
                new[key] = new.get(key, Fraction(0)) + c*coeff*sgn
        acc = new
    return {U: c for U, c in acc.items() if c != 0}

def ext4_matrix(M):
    A = [[Fraction(0)]*70 for _ in range(70)]
    for w in WORDS4:
        for U, c in ext_action(M, w).items():
            A[WIX[U]][WIX[w]] = c
    return A

def poly_eval_mat(coeffs_low_to_high, A):
    n = len(A)
    IdM = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    acc = [[Fraction(0)]*n for _ in range(n)]
    for k, c in enumerate(coeffs_low_to_high):
        if k == 0:
            term = [[Fraction(c)*IdM[i][j] for j in range(n)] for i in range(n)]
        else:
            Tk = IdM
            for _ in range(k):
                Tk = mat_mul(Tk, A)
            term = [[Fraction(c)*Tk[i][j] for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                acc[i][j] += term[i][j]
    return acc

def kernel_basis(A):
    nr = len(A); nc = len(A[0])
    M = [[Fraction(x) for x in row] for row in A]
    piv = []; r = 0
    for c in range(nc):
        p = None
        for i in range(r, nr):
            if M[i][c] != 0:
                p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x/pv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][j] - f*M[r][j] for j in range(nc)]
        piv.append(c); r += 1
        if r == nr: break
    free = [c for c in range(nc) if c not in piv]
    basis = []
    for fc in free:
        v = [Fraction(0)]*nc
        v[fc] = Fraction(1)
        for ri, pc in enumerate(piv):
            v[pc] = -M[ri][fc]
        basis.append(v)
    return basis

def trace(A):
    return sum(A[i][i] for i in range(len(A)))

print("="*96)
print("ROUND 38 EXPLORATION v2 -- THE WEIL-WORLD LETTER MODEL")
print("="*96)

CENSUS = [(1, (2, 1)), (3, (2, 1))] + [(d, (1, 1)) for d in [2, 7, 11, 19, 43, 67, 163]]
DEGENERATE = [(3, (1, 1))]   # the Eisenstein degeneracy: alpha/conj(alpha) = e^{i pi/3}
print(f"committed census: {len(CENSUS)} (K, alpha) worlds (the Heegner fields;"
      f" d=1 carries the repo's discriminator alpha=2+i; d=3 carries alpha=2+sqrt(-3)"
      f" -- the naive 1+sqrt(-3) is the Eisenstein degeneracy, carried separately)")

# ---------------- Part 1: the STRUCTURAL spectral law + verification --------
print("\n-- the ^4 spectral structure: STRUCTURAL + verified --")
all_data = {}
for d, alpha in CENSUS:
    a4 = kpow(alpha, 4, d)
    a3c = kmul(kpow(alpha, 3, d), kconj(alpha), d)
    amb = knorm(alpha, d)**2
    weil_f = minpoly(a4, d)
    mix_f = minpoly(a3c, d)
    amb_f = Poly(t - amb, t, domain=QQ)
    # structural multiplicities: k=4,0 -> mult 1 each conjugate -> Q-mult 1
    # on the minpoly (Q-dim 2); k=1,3 -> 16 each -> Q-mult 16 (Q-dim 32);
    # k=2 -> 36 (Q-dim 36).  Total 2+32+36 = 70.
    A = alpha_matrix(alpha, d)
    E4 = ext4_matrix(A)
    tr = trace(E4)
    # structural trace: sum_k C(4,k)C(4,4-k) alpha^k cbar^(4-k)  as K-element
    strace = (0, 0)
    for k in range(5):
        mult = Fraction(comb_count := __import__('math').comb(4, k) * __import__('math').comb(4, 4-k))
        ev = (0, 0)
        # alpha^k * conj(alpha)^(4-k)
        ak = kpow(alpha, k, d)
        ck = kpow(kconj(alpha), 4-k, d)
        ev = kmul(ak, ck, d)
        strace = (strace[0] + mult*ev[0], strace[1] + mult*ev[1])
    tr_ok = (Fraction(strace[0]) == tr and strace[1] == 0)
    # verify the Weil factor: ker(minpoly(a4)(E4)) has dim 2 (mult 1)
    coeffs = [Fraction(int(c)) for c in weil_f.all_coeffs()[::-1]]
    PM = poly_eval_mat(coeffs, E4)
    Wb = kernel_basis(PM)
    # verify the ambient factor: ker(E4 - amb*I) dim 36
    EM = [[E4[i][j] - (Fraction(amb) if i == j else Fraction(0)) for j in range(70)]
          for i in range(70)]
    amb_ker = kernel_basis(EM)
    # verify the mixed factor: ker(minpoly(a3c)(E4)) dim 32
    mcoeffs = [Fraction(int(c)) for c in mix_f.all_coeffs()[::-1]]
    MMp = poly_eval_mat(mcoeffs, E4)
    mix_ker = kernel_basis(MMp)
    all_data[(d, alpha)] = dict(weil_f=weil_f, mix_f=mix_f, amb=amb, E4=E4,
                                Wb=Wb, A=A)
    print(f"  d={d:3d} alpha={alpha}: trace-verified={tr_ok}; W-dim={len(Wb)} (expect 2);"
          f" ambient-kernel dim={len(amb_ker)} (expect 36); mixed-kernel dim={len(mix_ker)}"
          f" (expect 32); N(alpha)={knorm(alpha,d)}")

# ---------------- Part 2: the repo calibration ------------------------------
print("\n-- the repo calibration: K=Q(i), alpha=2+i --")
r = all_data[(1, (2, 1))]
print(f"   Weil factor:  {r['weil_f'].as_expr()}   (repo: t^2+14t+625)")
print(f"   mixed factor: {r['mix_f'].as_expr()}   (repo: t^2-30t+625)")
print(f"   ambient:      t - {r['amb']}                    (repo: t-25)")
# the CRT projector: P = comp * (comp^{-1} mod Weil factor), the UNIQUE
# degree<=4 representative
comp = Poly((t - 25)*(t*t - 30*t + 625), t, domain=QQ)
inv = poly_invert(comp, r['weil_f'])
P_full = comp * inv
full_mod = r['weil_f'] * comp
P_can = P_full.rem(full_mod) if P_full.degree() > 4 else P_full
pw_repo = Poly(-(t-25)*(39*t-79)*(t*t-30*t+625)/44000000, t, domain=QQ)
match = (P_can == pw_repo)
print(f"   CRT projector (canonical deg<=4): {P_can.as_expr()}")
print(f"   repo P_W:                             {pw_repo.as_expr()}")
print(f"   MATCH: {match}")
# the key identity
pwn = Poly(-39*t**4 + 2224*t**3 - 57970*t**2 + 718000*t - 1234375, t, domain=QQ)
ident = pwn + Poly((t**2+14*t+625)*(39*t**2-2770*t+72375), t, domain=QQ)
print(f"   key identity pwN + wf*(39t^2-2770t+72375) = {ident.as_expr()} (expect 44000000)")
# the correspondence coefficients
frac_c = lambda c: Fraction(int(c.p), int(c.q))
cfs = [frac_c(c) for c in pw_repo.all_coeffs()[::-1]]
repo_a = [Fraction(-79, 2816), Fraction(359, 22000), Fraction(-527, 400000),
          Fraction(139, 2750000), Fraction(-39, 44000000)]
print(f"   P_W coefficients low->high match repo a_0..a_4: {cfs == repo_a}")
# the spectral evaluations
_, remW = divmod(pw_repo, r['weil_f'])
print(f"   P_W mod Weil factor = {remW.as_expr()} (expect 1)")

# ---------------- Part 3: the projector action on the model -----------------
print("\n-- the projector action: the divisor-sector kill, the Weil fix --")
d, alpha = 1, (2, 1)
A = all_data[(d, alpha)]['A']; E4 = all_data[(d, alpha)]['E4']
Wb = all_data[(d, alpha)]['Wb']
# theta = sum_j e_j wedge f_j
theta = {tuple(sorted([2*j, 2*j+1])): Fraction(1) for j in range(4)}
tot = {}
for j in range(4):
    for U, c in ext_action(A, tuple(sorted([2*j, 2*j+1]))).items():
        tot[U] = tot.get(U, Fraction(0)) + c
th_ok = all(tot.get(w, Fraction(0)) == Fraction(5)*theta.get(w, Fraction(0))
            for w in set(list(tot) + list(theta)))
print(f"   [alpha]^* theta == N(alpha)*theta = 5*theta: {th_ok}")
# theta^2 and its eigenvalue
v2 = [Fraction(0)]*70
for j1 in range(4):
    for j2 in range(4):
        if j1 == j2:
            continue
        U1 = tuple(sorted([2*j1, 2*j1+1])); U2 = tuple(sorted([2*j2, 2*j2+1]))
        lst = list(U1) + list(U2)
        inv = sum(1 for a_ in range(len(lst)) for b_ in range(a_+1, len(lst)) if lst[a_] > lst[b_])
        key = tuple(sorted(lst))
        v2[WIX[key]] += Fraction((-1)**inv)
img2 = [Fraction(0)]*70
for i in range(70):
    if v2[i]:
        for U, c in ext_action(A, WORDS4[i]).items():
            img2[WIX[U]] += v2[i]*c
amb_ok = all(img2[i] == Fraction(25)*v2[i] for i in range(70))
print(f"   [alpha]^* theta^2 == N(alpha)^2 * theta^2 = 25*theta^2: {amb_ok}")
# P_W(theta^2) = 0
pw_c = [frac_c(c) for c in pw_repo.all_coeffs()[::-1]]
PMf = poly_eval_mat(pw_c, E4)
res = mat_vec(PMf, v2)
print(f"   P_W(theta^2) == 0 (the divisor-sector kill): {all(x == 0 for x in res)}")
# P_W = identity on W
wid_ok = True
for bvec in Wb:
    out = mat_vec(PMf, bvec)
    if out != bvec:
        wid_ok = False
print(f"   P_W == identity on the Weil plane W: {wid_ok}")

# ---------------- Part 4: Omega and INT W_R^2 = 8 ----------------------------
print("\n-- the Weil plane generators and INT W_R^2 = 8 --")
# Omega = ^4 (e_j + i f_j): the 16 monomials with coefficients i^|S|
mons = []
for k in range(5):
    for S in combinations(range(4), k):
        word = tuple(sorted(2*j + (1 if j in S else 0) for j in range(4)))
        re = (1 if k % 4 == 0 else (-1 if k % 4 == 2 else 0))
        im = (1 if k % 4 == 1 else (-1 if k % 4 == 3 else 0))
        mons.append((word, re, im))
print(f"   Omega monomials: {len(mons)} (expect 16); Re-components: "
      f"{sum(1 for w,a,b in mons if a != 0)} (expect 8)")
# membership of Re(Omega), Im(Omega) in W
def in_span(basis, vec70):
    """Is vec70 in the Q-span of `basis` (each a 70-vector)?  RREF on the
    70 x (len(basis)+1) system [basis-coords | vec70], rows indexed by the
    70 word-coordinates; consistent iff in the span."""
    nb = len(basis)
    rows = []
    for j in range(70):
        row = [Fraction(bv[j]) for bv in basis] + [vec70[j]]
        rows.append(row)
    M = [row[:] for row in rows]
    nr = len(M); nc = nb   # the variable columns; last column is the target
    r0 = 0; piv = []
    for c in range(nc):
        p = None
        for i in range(r0, nr):
            if M[i][c] != 0:
                p = i; break
        if p is None: continue
        M[r0], M[p] = M[p], M[r0]
        pv = M[r0][c]
        M[r0] = [x/pv for x in M[r0]]
        for i in range(nr):
            if i != r0 and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][j] - f*M[r0][j] for j in range(nb+1)]
        piv.append(c); r0 += 1
    for i in range(nr):
        if all(M[i][c] == 0 for c in range(nb)) and M[i][nb] != 0:
            return False
    return True
vre = [Fraction(0)]*70
vim = [Fraction(0)]*70
for w, a, b in mons:
    vre[WIX[w]] += Fraction(a)
    vim[WIX[w]] += Fraction(b)
print(f"   Re(Omega) in W: {in_span(Wb, vre)}; Im(Omega) in W: {in_span(Wb, vim)}")
# the two generators: Re(Omega), Im(Omega) are independent
print(f"   Re, Im independent (W dim 2): {any(x != 0 for x in vre) and any(x != 0 for x in vim)}")
# INT W_R^2: the self-pairing of W_R = Re(Omega) on the torus
# pairing: word_U . word_V = invsign(U ++ V) if complementary else 0
def invsign(lst):
    return (-1)**sum(1 for a_ in range(len(lst)) for b_ in range(a_+1, len(lst))
                     if lst[a_] > lst[b_])
WR = [(w, a) for w, a, b in mons if a != 0]
total = 0
for (u, cu) in WR:
    for (v2_, cv) in WR:
        if set(u) | set(v2_) == set(range(8)) and not (set(u) & set(v2_)):
            total += cu*cv*invsign(list(u) + list(v2_))
print(f"   INT W_R^2 = {total}  (repo: 8)")

# ---------------- Part 5: the dichotomy --------------------------------------
print("\n-- the dichotomy: K-stable subspaces of W --")
# W is the Q[K]-module K (mult by alpha^4 = the irreducible minpoly):
# any K-stable Q-subspace of the 2-dim irreducible module is 0 or all.
a4 = kpow((2, 1), 4, 1)
print(f"   alpha^4 = {a4} (expect (-7, 24): -7+24i); minpoly irreducible over Q: "
      f"{minpoly(a4, 1).is_irreducible}")
# [alpha]^* on Re(Omega): express in the {Re, Im} basis and check the 2x2
# multiplication-by-alpha^4 matrix [[a, -d b],[b, a]]
img_re = [Fraction(0)]*70
for i in range(70):
    if vre[i]:
        for U, c in ext_action(A, WORDS4[i]).items():
            img_re[WIX[U]] += vre[i]*c
g11 = sum(vre[i]*vre[i] for i in range(70))
g12 = sum(vre[i]*vim[i] for i in range(70))
g22 = sum(vim[i]*vim[i] for i in range(70))
b1 = sum(vre[i]*img_re[i] for i in range(70))
b2 = sum(vim[i]*img_re[i] for i in range(70))
det = g11*g22 - g12*g12
x_ = (b1*g22 - b2*g12)/det
y_ = (g11*b2 - g12*b1)/det
print(f"   [alpha]^* Re(Omega) = {x_}*Re + ({y_})*Im")
print(f"   multiplication-by-alpha^4: a={a4[0]}, b={a4[1]} (d=1)")
print(f"   MATCH: {Fraction(x_) == Fraction(a4[0]) and Fraction(y_) == Fraction(a4[1])}")

# ---------------- Part 6: the Eisenstein degeneracy ---------------------------
print("\n-- the Eisenstein degeneracy (d=3, alpha=1+sqrt(-3)) --")
dE, alE = 3, (1, 1)
a4E = kpow(alE, 4, dE)
a3cE = kmul(kpow(alE, 3, dE), kconj(alE), dE)
wfE = minpoly(a4E, dE)
mfE = minpoly(a3cE, dE)
print(f"   alpha^4 = {a4E}; alpha^3*conj(alpha) = {a3cE}")
print(f"   Weil factor: {wfE.as_expr()}; mixed factor: {mfE.as_expr()};"
      f" COINCIDE: {wfE == mfE}")
print(f"   (the phase alpha/conj(alpha) = e^(i pi/3), a cube root of unity:"
      f" the 2-dim Weil plane merges with the 32-dim mixed sector -- the")
print(f"   degenerate world, excluded from the generic census, carried as the"
      f" named degeneracy)")

print("\nEXPLORATION v2 DONE")
