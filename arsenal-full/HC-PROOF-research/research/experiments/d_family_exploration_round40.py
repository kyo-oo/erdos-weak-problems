#!/usr/bin/env python3
# =============================================================================
# ROUND 40 EXPLORATION -- THE D-FAMILY TRANSPORT (pre-certificate probe)
#
# QUESTION: does the Round 38/39 Weil-world package (the spectral law 2/36/32,
# the CRT projector, the integral Weil lattice wR_hat/wI_hat with the periods
# 8d^2 / 8d, the (6,2)/(3,3) crossing with the d^2-charges, the leaf, the
# K-spread) hold at squarefree d BEYOND the nine Heegner seeds -- and does it
# hold at the ORDER-4 phase collar (d=1, alpha = a+b i with a = +-b) that the
# Round-38 "k <= 4" criterion conservatively excluded?
#
# The sharpening under test: the dichotomy is K-IRREDUCIBILITY (the operator
# algebra span{[beta]^*|_W} = the regular K-representation), which is d-uniform
# -- so the order-4 and order-6 phase worlds are FULL family members, and the
# true exclusion collar is exactly {b=0} u {a=0} u {(3, a=+-b)}.
#
# Bounded: 12 (K, alpha) instances, matrices <= 70x70, exact Fraction
# arithmetic, zero floats, < 120 s.
# =============================================================================
import sys, time
from fractions import Fraction
from itertools import combinations
from math import gcd as _gcd
from sympy import symbols, Poly, QQ
from sympy import gcd as polygcd

T0 = time.time()
t = symbols('t')
N = 8

def timer(msg):
    print(f"  [t +{time.time()-T0:6.1f}s] {msg}", file=sys.stderr, flush=True)

# ---- the word-dict class algebra (the committed representation) -------------
def wedge(d1, d2):
    out = {}
    for w1, c1 in d1.items():
        for w2, c2 in d2.items():
            if set(w1) & set(w2):
                continue
            cnt = sum(1 for a in w1 for b in w2 if a > b)
            sgn = (-1) ** cnt
            key = tuple(sorted(w1 + w2))
            out[key] = out.get(key, Fraction(0)) + c1 * c2 * Fraction(sgn)
    return {w: c for w, c in out.items() if c != 0}

def wpow(d, k):
    r = {(): Fraction(1)}
    for _ in range(k):
        r = wedge(r, d)
    return r

def sc(d, lam):
    return {w: c * Fraction(lam) for w, c in d.items() if c * Fraction(lam) != 0}

def addc(*ds):
    out = {}
    for d in ds:
        for w, c in d.items():
            out[w] = out.get(w, Fraction(0)) + c
    return {w: c for w, c in out.items() if c != 0}

def word_top_sign(word8):
    sgn = 1
    lst = list(word8)
    for i in range(8):
        for j in range(i + 1, 8):
            if lst[i] > lst[j]:
                sgn = -sgn
    return sgn

def integral(d):
    tot = Fraction(0)
    for w, c in d.items():
        if len(w) == 8:
            tot += c * Fraction(word_top_sign(w))
    return tot

def is_integral_class(d):
    return all(c.denominator == 1 for c in d.values())

# ---- the letter model (Round 38/39 machinery verbatim) ----------------------
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
def minpoly(x, d):
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
    return [sum(A[i][j]*v[j] for j in range(len(v))) for i in range(len(A))]

WORDS4 = list(combinations(range(N), 4))
WIX = {w: i for i, w in enumerate(WORDS4)}

def ext_action(M, word):
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
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x/pv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][j] - f*M[r][j] for j in range(nc)]
        piv.append(c); r += 1
        if r == nr:
            break
    free = [c for c in range(nc) if c not in piv]
    basis = []
    for fc in free:
        v = [Fraction(0)]*nc
        v[fc] = Fraction(1)
        for ri, pc in enumerate(piv):
            v[pc] = -M[ri][fc]
        basis.append(v)
    return basis

def poly_invert(a, m):
    r0, r1 = m, a
    s0, s1 = Poly(0, t, domain=QQ), Poly(1, t, domain=QQ)
    while not (r1.degree() < 0):
        q2, rr = divmod(r0, r1)
        r0, r1 = r1, rr
        s0, s1 = s1, s0 - q2*s1
    assert r0.degree() == 0, f"gcd not constant: {r0}"
    return s0 * Poly(1/r0.LC(), t, domain=QQ)

def in_span_Q(basis, vec):
    nb = len(basis)
    M = [[Fraction(bv[j]) for bv in basis] + [vec[j]] for j in range(70)]
    nr = len(M); r0 = 0; piv = []
    for c in range(nb):
        p = None
        for i in range(r0, nr):
            if M[i][c] != 0:
                p = i; break
        if p is None:
            continue
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

def vec_to_dict(v):
    return {WORDS4[i]: v[i] for i in range(70) if v[i] != 0}
def dict_to_vec(d):
    v = [Fraction(0)]*70
    for w, c in d.items():
        if len(w) == 4:
            v[WIX[w]] = c
    return v

def wh_dict_classes(d):
    vR = {}
    vI = {}
    for S in range(16):
        letters = tuple(sorted(2*j + ((S >> j) & 1) for j in range(4)))
        tf = sum(1 for L in letters if L % 2 == 1)
        if tf == 0:
            vR[letters] = Fraction(1)
        elif tf == 2:
            vR[letters] = Fraction(-d)
        elif tf == 4:
            vR[letters] = Fraction(d*d)
        elif tf == 1:
            vI[letters] = Fraction(1)
        elif tf == 3:
            vI[letters] = Fraction(-d)
    return vR, vI

THETA = addc(*[{tuple(sorted([2*j, 2*j+1])): Fraction(1)} for j in range(4)])
TH2 = wpow(THETA, 2)

def phase_order(alpha, d):
    """least k in {1,2,3,4,6} with alpha^k == cbar^k (else None = generic)."""
    for k in (1, 2, 3, 4, 6):
        if kpow(alpha, k, d) == kpow(kconj(alpha), k, d):
            return k
    return None

# =============================================================================
# THE PROBE
# =============================================================================
# family members under test: non-Heegner squarefree d (beyond the 9 seeds)
#   + the ORDER-4 member (1, (1,1)) + the ORDER-6 member (3, (3,1))
#   + non-primitive order-4 member (1, (2,2))
FAMILY_PROBE = [
    (5, (1, 1)), (5, (2, 1)),
    (6, (1, 1)), (6, (2, 1)),
    (10, (1, 1)), (13, (1, 1)),
    (17, (1, 1)), (26, (1, 1)),
    (1, (1, 1)),     # ORDER-4 member (phase i) -- the sharpening
    (3, (3, 1)),     # ORDER-6 member (phase e^{i pi/3})
    (1, (2, 2)),     # non-primitive order-4 member
]
# collars under test: must FAIL the spectral law
COLLAR_PROBE = [
    (3, (1, 1)),     # order-3 (Eisenstein)
    (5, (0, 1)),     # order-2 (alpha = sqrt(-5))
    (5, (3, 0)),     # order-1 (alpha = 3 in Q)
    (3, (2, 2)),     # non-primitive order-3
]

print("=" * 96)
print("ROUND 40 EXPLORATION -- THE D-FAMILY TRANSPORT PROBE")
print("=" * 96)

for d, alpha in FAMILY_PROBE:
    tag = f"[d={d}, alpha={alpha}]"
    ph = phase_order(alpha, d)
    A = alpha_matrix(alpha, d)
    E4 = ext4_matrix(A)
    a4 = kpow(alpha, 4, d)
    a3c = kmul(kpow(alpha, 3, d), kconj(alpha), d)
    amb = knorm(alpha, d)**2
    weil_f = minpoly(a4, d)
    mix_f = minpoly(a3c, d)
    amb_f = Poly(t - amb, t, domain=QQ)
    g1 = polygcd(weil_f, amb_f); g2 = polygcd(weil_f, mix_f); g3 = polygcd(amb_f, mix_f)
    cop = (g1.degree() == 0 and g2.degree() == 0 and g3.degree() == 0)
    coeffs = [Fraction(int(c.p), int(c.q)) for c in weil_f.all_coeffs()[::-1]]
    PM = poly_eval_mat(coeffs, E4)
    Wb = kernel_basis(PM)
    EM = [[E4[i][j] - (Fraction(amb) if i == j else Fraction(0)) for j in range(70)]
          for i in range(70)]
    amb_ker = kernel_basis(EM)
    mcoeffs = [Fraction(int(c.p), int(c.q)) for c in mix_f.all_coeffs()[::-1]]
    MMp = poly_eval_mat(mcoeffs, E4)
    mix_ker = kernel_basis(MMp)
    vR, vI = wh_dict_classes(d)
    vR70 = dict_to_vec(vR)
    vI70 = dict_to_vec(vI)
    span = in_span_Q(Wb, vR70) and in_span_Q(Wb, vI70)
    qRR = integral(wedge(vR, vR))
    qII = integral(wedge(vI, vI))
    qRI = integral(wedge(vR, vI))
    qRt = integral(wedge(vR, TH2))
    # the K-irreducibility dichotomy: beta_0 with B(beta_0^4) != 0
    beta0 = (2, 1) if d == 1 else (1, 1)
    b4 = kpow(beta0, 4, d)
    disc = Fraction(-4 * d * b4[1] * b4[1])
    # the leaf: CRT projector fixes wR_hat
    comp_w = Poly((t - amb), t, domain=QQ) * mix_f
    inv_w = poly_invert(comp_w, weil_f)
    P_w = comp_w * inv_w
    full_mod_w = weil_f * comp_w
    P_can = P_w.rem(full_mod_w) if P_w.degree() > 4 else P_w
    pc = [Fraction(int(c.p), int(c.q)) for c in P_can.all_coeffs()[::-1]]
    PMw = poly_eval_mat(pc, E4)
    outv = mat_vec(PMw, vR70)
    leaf = (outv == vR70)
    th270 = dict_to_vec(TH2)
    resv = mat_vec(PMw, th270)
    kill = all(x == 0 for x in resv)
    # the crossing at (6,2): branch data + charges
    ep = addc(sc(vR, Fraction(3, 1)), TH2)
    em = addc(sc(vR, Fraction(-1, 1)), sc(TH2, -1))
    qep = integral(wedge(vR, ep))
    qem = integral(wedge(vR, em))
    c2p = sc(ep, -1); c2m = sc(em, -1)
    c4p = integral(wedge(c2p, c2p)) / 2
    c4m = integral(wedge(c2m, c2m)) / 2
    cross = integral(wedge(c2p, c2m))
    carrier = c4p + c4m + cross
    verdict = (len(Wb) == 2 and len(amb_ker) == 36 and len(mix_ker) == 32 and cop
               and span and qRR == Fraction(8*d*d) and qII == Fraction(8*d)
               and qRI == 0 and qRt == 0 and disc < 0 and leaf and kill
               and is_integral_class(ep) and is_integral_class(em)
               and qep == Fraction(24*d*d) and qem == Fraction(-8*d*d)
               and c4p == Fraction(9*8*d*d + 24, 2)
               and c4m == Fraction(8*d*d + 24, 2)
               and cross == Fraction(-(3*8*d*d + 24), 1)
               and carrier == Fraction(16*d*d))
    print(f"  {tag} phase-order={ph}  dims {len(Wb)}/{len(amb_ker)}/{len(mix_ker)}"
          f"  coprime={cop}  span={span}  periods ({qRR},{qII},{qRI},{qRt})"
          f"  disc(beta0^4)={disc}  leaf={leaf} kill={kill}"
          f"  charges ({qep},{qem})  c4 ({c4p},{c4m},{cross}) carrier={carrier}")
    print(f"    ==> FAMILY MEMBER: {verdict}")
    timer(f"{tag} done")

print("-" * 96)
for d, alpha in COLLAR_PROBE:
    tag = f"[d={d}, alpha={alpha}]"
    ph = phase_order(alpha, d)
    A = alpha_matrix(alpha, d)
    E4 = ext4_matrix(A)
    a4 = kpow(alpha, 4, d)
    a3c = kmul(kpow(alpha, 3, d), kconj(alpha), d)
    amb = knorm(alpha, d)**2
    weil_f = minpoly(a4, d)
    mix_f = minpoly(a3c, d)
    amb_f = Poly(t - amb, t, domain=QQ)
    g1 = polygcd(weil_f, amb_f); g2 = polygcd(weil_f, mix_f); g3 = polygcd(amb_f, mix_f)
    cop = (g1.degree() == 0 and g2.degree() == 0 and g3.degree() == 0)
    coeffs = [Fraction(int(c.p), int(c.q)) for c in weil_f.all_coeffs()[::-1]]
    PM = poly_eval_mat(coeffs, E4)
    Wb = kernel_basis(PM)
    print(f"  {tag} phase-order={ph}  weil-minpoly-degree={weil_f.degree()}"
          f"  dim-primary={len(Wb)}  coprime={cop}"
          f"   ==> COLLAR (excluded): {not cop or len(Wb) != 2}")
    timer(f"{tag} done")

print("=" * 96)
print("PROBE COMPLETE")
