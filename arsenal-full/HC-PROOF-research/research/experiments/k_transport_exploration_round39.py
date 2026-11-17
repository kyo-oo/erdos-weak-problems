#!/usr/bin/env python3
# ROUND 39 EXPLORATION -- THE K-TRANSPORT FEASIBILITY SCAN
# Question: does the discovery-strike crossing machinery transport from the
# Gaussian discriminator (d=1) to the eight remaining Heegner worlds?
# Layers verified per world:
#   (W1) the letter model + the spectral law (Round-38 machinery, re-derived)
#   (W2) the INTEGRAL Weil lattice W cap Z^70 -- the d-weighted generators
#        wR_hat = sum_t (d^2, -d, 1) words (t = #f letters even)
#        wI_hat = sum_t (d, -1) words (t odd)  -- spanning, integrality,
#        primitivity
#   (W3) the q-values: INT wR_hat^2 (expected 8 d^2), INT wI_hat^2,
#        INT wR_hat.wI_hat, the theta^2 disjointness
#   (W4) the CRT projector P: P(wR_hat) = wR_hat != 0  (THE LEAF)
#   (W5) the crossing arithmetic: the branch classes, the parity iff, the
#        born instance (6,2)/(3,3) closure -- calibrated at d=1 against the
#        discovery-strike receipts, then run at every world.
# Bounded: 9 worlds, matrices <= 70x70, sweeps <= 19x19x7, < 120 s.
# Exact Fraction arithmetic, zero floats.

import sys, time
from fractions import Fraction
from itertools import combinations
from sympy import symbols, Poly, QQ
from sympy import gcd as polygcd

T0 = time.time()
def timer(msg):
    print(f"  [t +{time.time()-T0:6.1f}s] {msg}", file=sys.stderr, flush=True)

t = symbols('t')
N = 8
GENERIC = [(1, (2, 1)), (3, (2, 1))] + [(d, (1, 1)) for d in [2, 7, 11, 19, 43, 67, 163]]

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

def fr(c):
    return Fraction(int(c.p), int(c.q))

def poly_invert(a, m):
    # inverse of a mod m (both sympy Polys in t), for gcd(a, m) constant.
    # extended Euclid maintaining s_i * a == r_i (mod m):
    #   r0 = m, s0 = 0 ; r1 = a, s1 = 1 ; iterate until r1 == 0.
    # the inverse is s0 / LC(gcd).
    r0, r1 = m, a
    s0, s1 = Poly(0, t, domain=QQ), Poly(1, t, domain=QQ)
    while not (r1.degree() < 0):
        q2, rr = divmod(r0, r1)
        r0, r1 = r1, rr
        s0, s1 = s1, s0 - q2*s1
    assert r0.degree() == 0, f"gcd not constant: {r0}"
    return s0 * Poly(1/r0.LC(), t, domain=QQ)

# ---- the letter pairing: the symplectic top integral -----------------------
# letters 2j = e_j, 2j+1 = f_j; theta = sum e_j ^ f_j.
# The integral of a top word (all 8 letters, each once): bring to the
# canonical order e1 f1 e2 f2 e3 f3 e4 f4 via the permutation sign.
CANON = [0, 1, 2, 3, 4, 5, 6, 7]

def word_sign(word8):
    # sign of the permutation sorting word8 (a tuple of the 8 letters in
    # wedge order) into CANON, times the pairing sign (+1 for the
    # symplectic canonical order)
    lst = list(word8)
    sgn = 1
    for i in range(8):
        for j in range(i+1, 8):
            if lst[i] > lst[j]:
                sgn = -sgn
    return sgn

def wedge_word(w1, w2):
    # wedge of two disjoint 4-letter words -> the signed 8-letter word
    if set(w1) & set(w2):
        return None
    lst = list(w1) + list(w2)
    sgn = 1
    # bubble count: number of pairs (a in w1, b in w2) with a > b
    cnt = sum(1 for a in w1 for b in w2 if a > b)
    sgn = (-1)**cnt
    key = tuple(sorted(lst))
    return key, sgn

TOPIDX = {}
def integral_pair(v1, v2):
    # INT (v1 ^ v2) for 70-vectors: only complementary words contribute
    tot = Fraction(0)
    for i in range(70):
        if v1[i] == 0:
            continue
        w1 = WORDS4[i]
        for j in range(70):
            if v2[j] == 0:
                continue
            w2 = WORDS4[j]
            if set(w1) & set(w2):
                continue
            key, sgn = wedge_word(w1, w2)
            tot += v1[i]*v2[j]*Fraction(sgn)*Fraction(word_sign(key))
    return tot

# ---- the integral Weil classes (TRANSVERSAL words only) ---------------------
# The committed letter model's [alpha]^* acts by the ROWS of alpha_matrix
# (the pullback/contravariant convention of the Round-38 certificate): the
# eigen-combination (e_j + x f_j) satisfies x^2 = -d, x = sqrt(-d), with
# eigenvalue alpha. Hence Omega' = wedge^4_j (e_j + sqrt(-d) f_j) is the
# alpha^4-eigenvector of E4, with transversal-word coefficients
# (sqrt(-d))^t. The Q-classes:
#   v1 = Re Omega'   = sum_{t even} (-1)^(t/2) d^(t/2) w_T  = (1, -d, d^2)
#   v2 = Im Omega'/sqrt(d) = sum_{t odd} (-1)^((t-1)/2) d^((t-1)/2) w_T
#        = (1, -d) by t = 1,3
# BOTH INTEGRAL and PRIMITIVE at every world (the leading coefficient 1);
# at d = 1 they are exactly the discovery-strike W_R, W_I.
def wh_classes(d):
    vR = [Fraction(0)]*70
    vI = [Fraction(0)]*70
    for S in range(16):
        letters = [2*j + ((S >> j) & 1) for j in range(4)]
        w = tuple(sorted(letters))
        tf = sum(1 for L in w if L % 2 == 1)
        if tf == 0:
            vR[WIX[w]] = Fraction(1)
        elif tf == 2:
            vR[WIX[w]] = Fraction(-d)
        elif tf == 4:
            vR[WIX[w]] = Fraction(d*d)
        elif tf == 1:
            vI[WIX[w]] = Fraction(1)
        elif tf == 3:
            vI[WIX[w]] = Fraction(-d)
    return vR, vI

def theta2_vec():
    # theta^2 = (sum_j e_j f_j)^2 = 2 sum_{j1<j2} (e_{j1} f_{j1}) ^ (e_{j2} f_{j2})
    # with the block-word signs
    v2 = [Fraction(0)]*70
    for j1 in range(4):
        for j2 in range(4):
            if j1 == j2:
                continue
            U1 = tuple(sorted([2*j1, 2*j1+1])); U2 = tuple(sorted([2*j2, 2*j2+1]))
            lst = list(U1) + list(U2)
            iv = sum(1 for a_ in range(len(lst)) for b_ in range(a_+1, len(lst))
                     if lst[a_] > lst[b_])
            v2[WIX[tuple(sorted(lst))]] += Fraction((-1)**iv)
    return v2

def theta4_int():
    # INT theta^4 -- calibration: expected 24 (discovery A0: int th^4 = 24)
    th = [Fraction(0)]*70
    for j in range(4):
        w = tuple(sorted([2*j, 2*j+1]))
        th[WIX[w]] = Fraction(1)
    # theta^4 = INT of the wedge of theta with itself 4 times on the 8-letter
    # top space: expand
    acc = {(): Fraction(1)}
    # brute: the 8-letter words from 4 block-pairs: 2^4 = 16 orderings; do the
    # full multilinear expansion via repeated wedging with theta (a 2-form)
    def wedge_form(form, pair):
        # form: dict word(tuple of letters) -> coeff ; wedge with e_j f_j
        out = {}
        for U, c in form.items():
            for L1, L2 in ((2*j, 2*j+1),):
                for o in ((L1, L2), (L2, L1)):
                    a, b = o
                    if a in U or b in U:
                        continue
                    sgn = (-1)**sum(1 for u in U if u > a)
                    U2 = U + (a,)
                    sgn2 = (-1)**sum(1 for u in U2 if u > b)
                    key = tuple(sorted(U2 + (b,)))
                    out[key] = out.get(key, Fraction(0)) + c*Fraction(sgn*sgn2)
        return out
    form = {(): Fraction(1)}
    for j in range(4):
        form = wedge_form(form, j)
    tot = Fraction(0)
    for w, c in form.items():
        if len(w) == 8:
            tot += c*Fraction(word_sign(w))
    return tot

THETA2 = theta2_vec()

def is_integral_class(v):
    return all(c.denominator == 1 for c in v)

def in_span_Q(basis, vec):
    nb = len(basis)
    rows = [[Fraction(bv[j]) for bv in basis] + [vec[j]] for j in range(70)]
    M = [row[:] for row in rows]
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

print("=" * 96)
print("ROUND 39 EXPLORATION -- THE K-TRANSPORT FEASIBILITY AT 9 WORLDS")
print("=" * 96)

RES = {}
for d, alpha in GENERIC:
    tag = f"d={d}, alpha={alpha}"
    A = alpha_matrix(alpha, d)
    E4 = ext4_matrix(A)
    a4 = kpow(alpha, 4, d)
    weil_f = minpoly(a4, d)
    coeffs = [fr(c) for c in weil_f.all_coeffs()[::-1]]
    PM = poly_eval_mat(coeffs, E4)
    Wb = kernel_basis(PM)
    assert len(Wb) == 2, f"{tag}: W dim {len(Wb)}"
    vR, vI = wh_classes(d)
    r1 = in_span_Q(Wb, vR)
    r2 = in_span_Q(Wb, vI)
    # integrality + primitivity
    primR = not is_integral_class([Fraction(x, 2) for x in vR])
    primI = not is_integral_class([Fraction(x, 2) for x in vI])
    # the q-values
    qRR = integral_pair(vR, vR)
    qII = integral_pair(vI, vI)
    qRI = integral_pair(vR, vI)
    qRt = integral_pair(vR, THETA2)
    qtt = integral_pair(THETA2, THETA2)
    # the CRT projector and the leaf
    nrm = knorm(alpha, d)
    amb = nrm*nrm
    a3c = kmul(kpow(alpha, 3, d), kconj(alpha), d)
    mix_f = minpoly(a3c, d)
    comp_w = Poly((t - amb), t, domain=QQ) * mix_f
    inv_w = poly_invert(comp_w, weil_f)
    P_w = comp_w * inv_w
    full_mod_w = weil_f * comp_w
    P_can = P_w.rem(full_mod_w) if P_w.degree() > 4 else P_w
    pc = [fr(c) for c in P_can.all_coeffs()[::-1]]
    PMw = poly_eval_mat(pc, E4)
    leaf = mat_vec(PMw, vR)
    leafOK = leaf == vR
    kill = all(x == 0 for x in mat_vec(PMw, THETA2))
    RES[(d, alpha)] = dict(Wb=Wb, vR=vR, vI=vI, qRR=qRR, qII=qII, qRI=qRI,
                           qRt=qRt, qtt=qtt, leafOK=leafOK, kill=kill,
                           P_can=P_can, E4=E4, amb=amb, weil_f=weil_f,
                           mix_f=mix_f)
    print(f"[{tag}] W-dim 2 | vR in W: {r1} | vI in W: {r2} | "
          f"primR: {primR} primI: {primI}")
    print(f"    q(wR,wR) = {qRR} (expect 8 d^2 = {8*d*d}) | q(wI,wI) = {qII} "
          f"| q(wR,wI) = {qRI} | q(wR,th2) = {qRt} | q(th2,th2) = {qtt} "
          f"(expect 24)")
    print(f"    LEAF P(wR) == wR: {leafOK} | KILL P(th2) == 0: {kill}")

timer("the world-interface scan complete at all 9 worlds")

# ---- the crossing arithmetic ------------------------------------------------
print("\n== the crossing closure -- calibration at d=1, then all worlds ==")

def branch_ch2(m, w, b, bp, vR):
    # ch2(E_+) = ((m+2w)/2) wR_hat + ((b-b')/2) th^2
    # ch2(E_-) = ((m-2w)/2) wR_hat - ((b-b')/2) th^2
    half_R_p = Fr_(m + 2*w, 2)
    half_R_m = Fr_(m - 2*w, 2)
    half_T = Fr_(b - bp, 2)
    ep = [Fraction(x)*half_R_p for x in vR]
    em = [Fraction(x)*half_R_m for x in vR]
    for i in range(70):
        ep[i] += THETA2[i]*half_T
        em[i] -= THETA2[i]*half_T
    return ep, em

def Fr_(p, q):
    return Fraction(p, q)

def is_int(v):
    return all(c.denominator == 1 for c in v)

# the parity iff at every world (bounded sweep)
print("the parity iff (m+2w even <=> branches integral):")
for d, alpha in GENERIC:
    vR = RES[(d, alpha)]['vR']
    okk = True
    for m in range(-4, 9):
        for w in range(-4, 9):
            for (b, bp) in [(2, -2), (0, 0), (1, 1), (5, 2)]:
                ep, em = branch_ch2(m, w, b, bp, vR)
                got = is_int(ep) and is_int(em)
                want = ((m + 2*w) % 2 == 0)
                if got != want:
                    okk = False
    print(f"  [d={d}] parity iff holds: {okk}")

# the born instance (6,2)/(3,3): branch data ch2 = (3 wR + th2, -wR - th2)
print("\nthe born instance (6,2) branch data and closure at every world:")
for d, alpha in GENERIC:
    vR = RES[(d, alpha)]['vR']
    ep, em = branch_ch2(2, 2, 1, -1, vR)  # m=w=2: (3 wR + th2, -wR - th2)
    integ = is_int(ep) and is_int(em)
    # charges: q(ch2(E_+)), q(ch2(E_-)), trace q(ep+em), diff q(ep-em)
    qpp = integral_pair(ep, ep)
    qmm = integral_pair(em, em)
    qpm = integral_pair(ep, em)
    tr = integral_pair([ep[i]+em[i] for i in range(70)],
                       [ep[i]+em[i] for i in range(70)])
    df = integral_pair([ep[i]-em[i] for i in range(70)],
                       [ep[i]-em[i] for i in range(70)])
    # the four-face chain: Z = wR (q=8d^2), B = ep+em = 2w wR + 0 th2
    # -> q(B) = 16 w^2 d^2 ; at w=m=2: 64 d^2
    print(f"  [d={d}] branches integral: {integ} | q(E+) = {qpp} (24 d^2 = "
          f"{24*d*d}) | q(E-) = {qmm} (8 d^2 = {8*d*d}) | q(E+.E-) = {qpm} "
          f"(-16 d^2 = {-16*d*d})")
    print(f"         trace q = {tr} | diff q = {df}")

timer("the crossing closure scan complete")
print("\nEXPLORATION COMPLETE")
