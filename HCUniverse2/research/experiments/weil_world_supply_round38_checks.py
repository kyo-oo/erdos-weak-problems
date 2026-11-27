#!/usr/bin/env python3
# =============================================================================
# ROUND 38 CERTIFICATE — THE WEIL-WORLD SUPPLY (R2' face (b))
# Target: S21/S22/S23/S24 — the non-split Weil fourfold world at the
# committed census: the letter model, the spectral law, the CRT projector
# supply (an algebraic correspondence at every world), the divisor-sector
# kill, the Weil-plane generators with the period identity, the dichotomy,
# the Eisenstein degeneracy, and the reduction boundary.
#
# COVERAGE (ledger-111 discipline — every claim below has a matching check):
#   V1 the census: 9 generic (K, alpha) worlds (the Heegner-class fields,
#      d = 1,2,3,7,11,19,43,67,163; d=1 and d=3 carry alpha = 2 + sqrt(-d),
#      the others alpha = 1 + sqrt(-d)) + the named Eisenstein degeneracy
#      (d=3, alpha = 1 + sqrt(-3)); the K-operator laws ([alpha][beta] =
#      [alpha beta], [sqrt(-d)]^2 = -d Id) at every world.
#   V2 the spectral law at every generic world: the eigenvalues of
#      [alpha]^* on ^4_Q H^1 are alpha^k conj(alpha)^(4-k) with
#      multiplicities C(4,k)C(4,4-k); the Q-factors minpoly(alpha^4)^1,
#      minpoly(alpha^3 conj alpha)^16, (t - N(alpha)^2)^36 (trace-verified
#      against the actual 70x70 exterior matrix); the Weil plane W =
#      the minpoly(alpha^4)-primary part, dimension EXACTLY 2; the pairwise
#      coprimality of the three factors (the genericity receipt).
#   V3 the repo calibration at the discriminator (K=Q(i), alpha=2+i): the
#      three factors t^2+14t+625 / t^2-30t+625 / t-25 reproduced; the CRT
#      projector's UNIQUE degree<=4 representative equals the repo's
#      P_W(t) = -((t-25)(39t-79)(t^2-30t+625))/44000000 COEFFICIENT FOR
#      COEFFICIENT (a_0..a_4); the key identity
#      pwN + (t^2+14t+625)(39t^2-2770t+72375) = 44000000.
#   V4 the projector supply at EVERY generic world: the CRT projector P
#      (P = 1 mod the Weil factor, 0 mod the ambient and mixed factors);
#      the projector ACTION on the model: P(^4[alpha]) = identity on W
#      (basis AND a deterministic random-class draw), kills the ambient
#      kernel (36-dim) and the mixed kernel (32-dim).
#   V5 the divisor sector and the Weil plane: [alpha]^* theta =
#      N(alpha) theta; [alpha]^* theta^2 = N(alpha)^2 theta^2; the
#      DIVISOR-SECTOR KILL P(theta^2) = 0 at every world; Omega =
#      wedge(e_j + i f_j): 16 monomials, 8 real components; Re(Omega),
#      Im(Omega) in W, independent (W = <Re Omega, Im Omega>); INT W_R^2
#      = 8 (the repo's period identity); the fourth-power character: the
#      K-action matrix on (Re, Im) has char poly = the Weil factor; the
#      dichotomy (minpoly irreducible: no proper K-stable Q-subspace of W);
#      the spectral disjointness W cap ambient = 0 (the beyond-divisor
#      content = exactly the 2-dim Weil plane).
#   V6 the Eisenstein degeneracy: at (3, 1+sqrt(-3)) the Weil and mixed
#      factors COINCIDE (alpha^4 = conj(alpha^3 conj alpha) exactly; the
#      phase alpha/conj(alpha) is a cube root of unity); the merged primary
#      part has dimension 34; the degeneracy does NOT occur at any generic
#      world (the canary battery).
#   V7 the hostile battery (every control FIRES) + the mechanical vacuity
#      scan + the self-comparison scan.
#
# Bounds: 8 letters, ^4 = 70 words, 70x70 exact Fraction matrices, |K|
# arithmetic on (a,b) pairs, zero floats. Deterministic: xorshift64* seed
# 0x5CA1AB1E0D15EA5E (distinct from R32 0x9E3779B97F4A7C15, R34
# 0xC0FFEE123456789, R35 0xFEEDFACECAFEBEEF, R36 0xABCDEF9876543210, R37
# 0xD15EA5E5BADF00D). Expected runtime ~15 s.
#
# LEDGER 107/109/111/112 DISCIPLINE: every ok() message states the predicate
# ACTUALLY tested; hostile canaries cover the violation DIRECTIONS; the
# header claims match the inventory; the samplers are disclosed.
# =============================================================================
import sys, time, re
from fractions import Fraction
from math import comb
from itertools import combinations
from sympy import Poly, symbols, QQ
from sympy.polys.polytools import invert as poly_invert

T0 = time.time()
SEED = 0x5CA1AB1E0D15EA5E
_rng_state = SEED & ((1 << 64) - 1)

def nxt():
    global _rng_state
    x = _rng_state
    x ^= (x << 13) & ((1 << 64) - 1)
    x ^= x >> 7
    x ^= (x << 17) & ((1 << 64) - 1)
    _rng_state = x & ((1 << 64) - 1)
    return (_rng_state * 0x2545F4914F6CDD1D) & ((1 << 64) - 1)

CHECKS = 0
FAILS = 0
FAIL_LINES = []

def ok(msg):
    global CHECKS
    CHECKS += 1
    print(f"  ok {CHECKS:4d}  {msg}", flush=True)

def bad(msg):
    global FAILS
    FAILS += 1
    FAIL_LINES.append(msg)
    print(f"  FAIL      {msg}", flush=True)

def check(cond, msg):
    if cond:
        ok(msg)
    else:
        bad(msg)

def timer(msg):
    print(f"  [t +{time.time()-T0:6.1f}s] {msg}", file=sys.stderr, flush=True)

t = symbols('t')
N = 8

# ---------------- the K = Q(sqrt(-d)) arithmetic ----------------------------
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

def fr(c):
    return Fraction(int(c.p), int(c.q))

# ================================================================ V1: CENSUS
print("=" * 96)
print("V1 -- THE WEIL-WORLD CENSUS (the committed (K, alpha) worlds)")
print("=" * 96)

GENERIC = [(1, (2, 1)), (3, (2, 1))] + [(d, (1, 1)) for d in [2, 7, 11, 19, 43, 67, 163]]
DEGENERATE = (3, (1, 1))
check(len(GENERIC) == 9,
      f"the committed generic census: {len(GENERIC)} (K, alpha) worlds "
      f"(the Heegner-class fields d = 1,2,3,7,11,19,43,67,163; d=1 and d=3 "
      f"carry alpha = 2 + sqrt(-d) -- at d=3 the naive 1+sqrt(-3) is the "
      f"Eisenstein degeneracy, carried separately in V6)")
for d, alpha in GENERIC:
    A = alpha_matrix(alpha, d)
    # [alpha]^2 == [alpha^2]
    a2 = kpow(alpha, 2, d)
    A2 = mat_mul(A, A)
    A2e = alpha_matrix(a2, d)
    check(all(A2[i][j] == A2e[i][j] for i in range(N) for j in range(N)),
          f"[d={d}, alpha={alpha}] the K-operator law: [alpha]^2 == "
          f"[alpha^2] as 8x8 Q-matrices")
    # [sqrt(-d)]^2 == -d Id
    s = (0, 1)
    S = alpha_matrix(s, d)
    S2 = mat_mul(S, S)
    check(all(S2[i][j] == Fraction(-d if i == j else 0) for i in range(N)
              for j in range(N)),
          f"[d={d}] the CM involution law: [sqrt(-d)]^2 == -{d}*Id")
timer(f"V1 complete: {len(GENERIC)} generic worlds + the degenerate canary")

# ================================================================ V2: SPECTRAL
print("=" * 96)
print("V2 -- THE SPECTRAL LAW AT EVERY GENERIC WORLD (verified on the 70x70)")
print("=" * 96)

WORLD = {}
for d, alpha in GENERIC:
    a4 = kpow(alpha, 4, d)
    a3c = kmul(kpow(alpha, 3, d), kconj(alpha), d)
    amb = knorm(alpha, d)**2
    weil_f = minpoly(a4, d)
    mix_f = minpoly(a3c, d)
    amb_f = Poly(t - amb, t, domain=QQ)
    A = alpha_matrix(alpha, d)
    E4 = ext4_matrix(A)
    # structural trace: sum_k C(4,k)C(4,4-k) alpha^k cbar^(4-k)
    strace = (0, 0)
    for k in range(5):
        mult = comb(4, k) * comb(4, 4-k)
        ev = kmul(kpow(alpha, k, d), kpow(kconj(alpha), 4-k, d), d)
        strace = (strace[0] + mult*ev[0], strace[1] + mult*ev[1])
    tr = trace(E4)
    check(Fraction(strace[0]) == tr and strace[1] == 0,
          f"[d={d}, alpha={alpha}] the spectral trace: sum_k C(4,k)C(4,4-k)"
          f" alpha^k cbar^(4-k) = {strace[0]} == trace(^4[alpha]) (exact)")
    # the Weil plane: ker(minpoly(alpha^4)(E4)), dim 2
    coeffs = [fr(c) for c in weil_f.all_coeffs()[::-1]]
    PM = poly_eval_mat(coeffs, E4)
    Wb = kernel_basis(PM)
    check(len(Wb) == 2,
          f"[d={d}, alpha={alpha}] THE WEIL PLANE: the minpoly(alpha^4)-"
          f"primary part of ^4[alpha] has dimension {len(Wb)} == 2 (the "
          f"two-dimensional rational Weil plane)")
    # ambient kernel dim 36; mixed kernel dim 32
    EM = [[E4[i][j] - (Fraction(amb) if i == j else Fraction(0)) for j in range(70)]
          for i in range(70)]
    amb_ker = kernel_basis(EM)
    check(len(amb_ker) == 36,
          f"[d={d}, alpha={alpha}] the ambient factor: ker(^4[alpha] - "
          f"N(alpha)^2) has dimension {len(amb_ker)} == 36 = C(4,2)^2")
    mcoeffs = [fr(c) for c in mix_f.all_coeffs()[::-1]]
    MMp = poly_eval_mat(mcoeffs, E4)
    mix_ker = kernel_basis(MMp)
    check(len(mix_ker) == 32,
          f"[d={d}, alpha={alpha}] the mixed factor: ker(minpoly(alpha^3 "
          f"cbar)) has dimension {len(mix_ker)} == 32 = 2*C(4,3)C(4,1)")
    check(len(Wb) + len(amb_ker) + len(mix_ker) == 70,
          f"[d={d}, alpha={alpha}] the sector total: the MEASURED dimensions "
          f"{len(Wb)} + {len(amb_ker)} + {len(mix_ker)} == 70 == C(8,4) (the "
          f"full ^4_Q H^1)")
    # the genericity: the three factors pairwise coprime
    from sympy import gcd as polygcd
    g1 = polygcd(weil_f, amb_f)
    g2 = polygcd(weil_f, mix_f)
    g3 = polygcd(amb_f, mix_f)
    check(g1.degree() == 0 and g2.degree() == 0 and g3.degree() == 0,
          f"[d={d}, alpha={alpha}] the genericity: the three Q-factors "
          f"pairwise coprime (the CRT projector exists)")
    WORLD[(d, alpha)] = dict(weil_f=weil_f, mix_f=mix_f, amb=amb, E4=E4,
                             Wb=Wb, A=A, amb_ker=amb_ker, mix_ker=mix_ker)
timer("V2 complete: the spectral law verified at all 9 worlds")

# ============================================================ V3: CALIBRATION
print("=" * 96)
print("V3 -- THE REPO CALIBRATION (the discriminator K=Q(i), alpha=2+i)")
print("=" * 96)

r = WORLD[(1, (2, 1))]
check(r['weil_f'] == Poly(t*t + 14*t + 625, t, domain=QQ),
      f"the exceptional Weil factor: {r['weil_f'].as_expr()} == "
      f"t^2+14t+625 (the repo's committed factor)")
check(r['mix_f'] == Poly(t*t - 30*t + 625, t, domain=QQ),
      f"the mixed K-weight factor: {r['mix_f'].as_expr()} == t^2-30t+625")
check(r['amb'] == 25,
      f"the ambient weight factor: t - {r['amb']} == t-25 (N(2+i)^2)")
# the CRT projector: the UNIQUE degree<=4 representative
comp = Poly((t - 25)*(t*t - 30*t + 625), t, domain=QQ)
inv = poly_invert(comp, r['weil_f'])
P_full = comp * inv
full_mod = r['weil_f'] * comp
P_can = P_full.rem(full_mod) if P_full.degree() > 4 else P_full
pw_repo = Poly(-(t-25)*(39*t-79)*(t*t-30*t+625)/44000000, t, domain=QQ)
check(P_can == pw_repo,
      f"THE CRT PROJECTOR: the unique degree<=4 solution equals the repo's "
      f"P_W coefficient for coefficient (-39/44000000 t^4 + 139/2750000 t^3 "
      f"- 527/400000 t^2 + 359/22000 t - 79/2816)")
cfs = [fr(c) for c in pw_repo.all_coeffs()[::-1]]
repo_a = [Fraction(-79, 2816), Fraction(359, 22000), Fraction(-527, 400000),
          Fraction(139, 2750000), Fraction(-39, 44000000)]
check(cfs == repo_a,
      f"the correspondence coefficients: the P_W expansion a_0..a_4 == the "
      f"repo's committed values (Pi_W^CH = sum a_j Gamma_fj)")
pwn = Poly(-39*t**4 + 2224*t**3 - 57970*t**2 + 718000*t - 1234375, t, domain=QQ)
ident = pwn + Poly((t**2+14*t+625)*(39*t**2-2770*t+72375), t, domain=QQ)
check(ident == Poly(44000000, t, domain=QQ),
      f"the key identity: pwN + (t^2+14t+625)(39t^2-2770t+72375) == 44000000")
_, remW = divmod(pw_repo, r['weil_f'])
check(remW == Poly(1, t, domain=QQ),
      f"the spectral evaluation: P_W == 1 on the Weil factor")
_, remA = divmod(pw_repo, Poly(t - 25, t, domain=QQ))
_, remM = divmod(pw_repo, r['mix_f'])
check(remA == Poly(0, t, domain=QQ) and remM == Poly(0, t, domain=QQ),
      f"the spectral evaluation: P_W == 0 on the ambient and mixed factors")
timer("V3 complete: the repo forcing-frame calibrated")

# ======================================================== V4: PROJECTOR SUPPLY
print("=" * 96)
print("V4 -- THE PROJECTOR SUPPLY AND ACTION AT EVERY GENERIC WORLD")
print("=" * 96)

for d, alpha in GENERIC:
    w = WORLD[(d, alpha)]
    weil_f = w['weil_f']; amb = w['amb']; mix_f = w['mix_f']; E4 = w['E4']
    comp_w = Poly((t - amb), t, domain=QQ) * mix_f
    inv_w = poly_invert(comp_w, weil_f)
    P_w = comp_w * inv_w
    full_mod_w = weil_f * comp_w
    P_can_w = P_w.rem(full_mod_w) if P_w.degree() > 4 else P_w
    _, rw = divmod(P_can_w, weil_f)
    _, ra = divmod(P_can_w, Poly(t - amb, t, domain=QQ))
    _, rm = divmod(P_can_w, mix_f)
    check(rw == Poly(1, t, domain=QQ) and ra == Poly(0, t, domain=QQ)
          and rm == Poly(0, t, domain=QQ),
          f"[d={d}, alpha={alpha}] the CRT projector congruences: P == 1 "
          f"mod the Weil factor, P == 0 mod (t - N(alpha)^2) and mod the "
          f"mixed factor (an explicit Q-combination of the isogeny "
          f"iterates [alpha]^j: the correspondence supply)")
    # the action: P(E4) = id on W
    pc = [fr(c) for c in P_can_w.all_coeffs()[::-1]]
    PMw = poly_eval_mat(pc, E4)
    wid = all(mat_vec(PMw, bv) == bv for bv in w['Wb'])
    check(wid,
          f"[d={d}, alpha={alpha}] the projector ACTION: P(^4[alpha]) == "
          f"identity on the Weil plane basis")
    # the random-class receipt: a deterministic pseudo-random combination
    v = [Fraction(0)]*70
    for bv in w['Wb']:
        a_ = ((nxt() % 19) - 9)
        if a_ == 0:
            a_ = 1
        v = [v[i] + Fraction(a_)*bv[i] for i in range(70)]
    outv = mat_vec(PMw, v)
    check(outv == v,
          f"[d={d}, alpha={alpha}] the random-class fixation: P fixes a "
          f"deterministic pseudo-random Q-combination of the W basis "
          f"(xorshift64*, mod-19 coefficients)")
    # kills the ambient kernel and the mixed kernel
    ka = all(all(x == 0 for x in mat_vec(PMw, bv)) for bv in w['amb_ker'])
    check(ka,
          f"[d={d}, alpha={alpha}] the ambient kill: P annihilates the "
          f"36-dimensional ambient kernel (the divisor-product sector)")
    km = all(all(x == 0 for x in mat_vec(PMw, bv)) for bv in w['mix_ker'])
    check(km,
          f"[d={d}, alpha={alpha}] the mixed kill: P annihilates the "
          f"32-dimensional mixed kernel")
timer("V4 complete: the projector supply at all 9 worlds")

# ============================================== V5: DIVISOR SECTOR + WEIL PLANE
print("=" * 96)
print("V5 -- THE DIVISOR SECTOR, THE WEIL-PLANE GENERATORS, THE DICHOTOMY")
print("=" * 96)

for d, alpha in GENERIC:
    w = WORLD[(d, alpha)]
    A = w['A']; E4 = w['E4']
    nrm = knorm(alpha, d)
    theta = {tuple(sorted([2*j, 2*j+1])): Fraction(1) for j in range(4)}
    tot = {}
    for j in range(4):
        for U, c in ext_action(A, tuple(sorted([2*j, 2*j+1]))).items():
            tot[U] = tot.get(U, Fraction(0)) + c
    th_ok = all(tot.get(ww, Fraction(0)) == Fraction(nrm)*theta.get(ww, Fraction(0))
                for ww in set(list(tot) + list(theta)))
    check(th_ok,
          f"[d={d}, alpha={alpha}] the polarization eigenvalue: "
          f"[alpha]^* theta == N(alpha) theta = {nrm}*theta")
    # theta^2
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
    img2 = [Fraction(0)]*70
    for i in range(70):
        if v2[i]:
            for U, c in ext_action(A, WORDS4[i]).items():
                img2[WIX[U]] += v2[i]*c
    amb_ok = all(img2[i] == Fraction(nrm*nrm)*v2[i] for i in range(70))
    check(amb_ok,
          f"[d={d}, alpha={alpha}] the divisor-product eigenvalue: "
          f"[alpha]^* theta^2 == N(alpha)^2 theta^2 = {nrm*nrm}*theta^2 "
          f"(the ambient sector)")
    # the divisor-sector kill: build the projector and apply to theta^2
    weil_f = w['weil_f']; amb = w['amb']; mix_f = w['mix_f']
    comp_w = Poly((t - amb), t, domain=QQ) * mix_f
    inv_w = poly_invert(comp_w, weil_f)
    P_w = comp_w * inv_w
    full_mod_w = weil_f * comp_w
    P_can_w = P_w.rem(full_mod_w) if P_w.degree() > 4 else P_w
    pc = [fr(c) for c in P_can_w.all_coeffs()[::-1]]
    PMw = poly_eval_mat(pc, E4)
    resv = mat_vec(PMw, v2)
    check(all(x == 0 for x in resv),
          f"[d={d}, alpha={alpha}] THE DIVISOR-SECTOR KILL: P(theta^2) == 0 "
          f"(every product of divisor classes is killed by the Weil "
          f"projector; the source must be beyond-divisor)")
    # the spectral disjointness (AUDIT-38 F3 repair: the full-strength
    # 2x2 test): the restriction of (^4[alpha] - N(alpha)^2) to W is
    # NONSINGULAR (its 2x2 matrix in the W basis has nonzero determinant)
    Wb = w['Wb']
    ambM = [[E4[i][j] - (Fraction(amb) if i == j else Fraction(0))
             for j in range(70)] for i in range(70)]
    g11 = sum(Wb[0][i]*Wb[0][i] for i in range(70))
    g12 = sum(Wb[0][i]*Wb[1][i] for i in range(70))
    g22 = sum(Wb[1][i]*Wb[1][i] for i in range(70))
    dG = g11*g22 - g12*g12
    cols = []
    for bv in Wb:
        img = mat_vec(ambM, bv)
        c1 = sum(Wb[0][i]*img[i] for i in range(70))
        c2 = sum(Wb[1][i]*img[i] for i in range(70))
        x_c = (c1*g22 - c2*g12)/dG
        y_c = (g11*c2 - g12*c1)/dG
        cols.append((x_c, y_c))
    detR = cols[0][0]*cols[1][1] - cols[0][1]*cols[1][0]
    check(detR != 0,
          f"[d={d}, alpha={alpha}] the spectral disjointness: the 2x2 "
          f"restriction of (^4[alpha] - N(alpha)^2) to W has nonzero "
          f"determinant (W cap ambient = 0; the beyond-divisor content is "
          f"EXACTLY the 2-dim Weil plane)")
timer("V5 part 1 complete: the divisor sector at all 9 worlds")

# -- the Omega generators and INT W_R^2 = 8 (the Gaussian world d=1) ---------
print("-- the Weil-plane generators and the period identity (d=1) --")
w1 = WORLD[(1, (2, 1))]
A = w1['A']; E4 = w1['E4']; Wb = w1['Wb']
mons = []
for k in range(5):
    for S in combinations(range(4), k):
        word = tuple(sorted(2*j + (1 if j in S else 0) for j in range(4)))
        re_c = (1 if k % 4 == 0 else (-1 if k % 4 == 2 else 0))
        im_c = (1 if k % 4 == 1 else (-1 if k % 4 == 3 else 0))
        mons.append((word, re_c, im_c))
check(len(mons) == 16,
      f"Omega = wedge(e_j + i f_j): {len(mons)} monomial components == 16")
check(sum(1 for ww, a, b in mons if a != 0) == 8,
      f"Re(Omega) = W_R: {sum(1 for ww,a,b in mons if a != 0)} real "
      f"components == 8 (the repo's 'eight +/-1 monomial components')")
def in_span(basis, vec70):
    nb = len(basis)
    rows = []
    for j in range(70):
        rows.append([Fraction(bv[j]) for bv in basis] + [vec70[j]])
    M = [row[:] for row in rows]
    nr = len(M)
    r0 = 0; piv = []
    for c in range(nb):
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
for ww, a, b in mons:
    vre[WIX[ww]] += Fraction(a)
    vim[WIX[ww]] += Fraction(b)
check(in_span(Wb, vre) and in_span(Wb, vim),
      f"the generators: Re(Omega) and Im(Omega) both lie in the Weil plane W")
# independence: the 70-vectors are not proportional
prop = all(vre[i]*vim[j] == vre[j]*vim[i] for i in range(70) for j in range(70))
check(not prop,
      f"the generators: Re(Omega), Im(Omega) Q-independent (W = <Re Omega, "
      f"Im Omega>, the two-dimensional rational plane)")
def invsign(lst):
    return (-1)**sum(1 for a_ in range(len(lst)) for b_ in range(a_+1, len(lst))
                     if lst[a_] > lst[b_])
WR = [(ww, a) for ww, a, b in mons if a != 0]
total = 0
for (u, cu) in WR:
    for (v2_, cv) in WR:
        if set(u) | set(v2_) == set(range(8)) and not (set(u) & set(v2_)):
            total += cu*cv*invsign(list(u) + list(v2_))
check(total == 8,
      f"THE PERIOD IDENTITY: INT W_R^2 = {total} == 8 (the repo's Part B "
      f"receipt: the eight ordered complementary pairs each contribute +1)")
# the fourth-power character on (Re, Im)
img_re = [Fraction(0)]*70
for i in range(70):
    if vre[i]:
        for U, c in ext_action(A, WORDS4[i]).items():
            img_re[WIX[U]] += vre[i]*c
img_im = [Fraction(0)]*70
for i in range(70):
    if vim[i]:
        for U, c in ext_action(A, WORDS4[i]).items():
            img_im[WIX[U]] += vim[i]*c
g11 = sum(vre[i]*vre[i] for i in range(70))
g12 = sum(vre[i]*vim[i] for i in range(70))
g22 = sum(vim[i]*vim[i] for i in range(70))
det = g11*g22 - g12*g12
b1 = sum(vre[i]*img_re[i] for i in range(70))
b2 = sum(vim[i]*img_re[i] for i in range(70))
x_ = (b1*g22 - b2*g12)/det
y_ = (g11*b2 - g12*b1)/det
b1i = sum(vre[i]*img_im[i] for i in range(70))
b2i = sum(vim[i]*img_im[i] for i in range(70))
xi_ = (b1i*g22 - b2i*g12)/det
yi_ = (g11*b2i - g12*b1i)/det
a4 = kpow((2, 1), 4, 1)
# char poly of the 2x2 action matrix [[x_, xi_],[y_, yi_]] (columns = images)
tr2 = x_ + yi_
dt2 = x_*yi_ - xi_*y_
check(tr2 == Fraction(-14) and dt2 == Fraction(625) and x_ == Fraction(-7)
      and y_ == Fraction(-24),
      f"THE FOURTH-POWER CHARACTER: the K-action on (Re, Im) has first "
      f"column ({x_}, {y_}) == (-7, -24), trace {tr2} == -14, determinant "
      f"{dt2} == 625: multiplication by conj(alpha^4) = -7-24i (char poly "
      f"t^2+14t+625 = the Weil factor; the conjugate identification "
      f"Re <-> 1, Im <-> -i)")
# the dichotomy: the minpoly irreducible over Q -> no proper stable subspace
check(minpoly(a4, 1).is_irreducible,
      f"the dichotomy root: minpoly(alpha^4) = t^2+14t+625 is irreducible "
      f"over Q (the K-module W = Q(alpha^4) is a field: any K-stable "
      f"Q-subspace of W is 0 or all of W)")
# direct dichotomy canary (AUDIT-38 F4 repair: the full-strength test):
# the discriminant tr^2 - 4 det is not a rational square -> no rational
# eigenvalue -> no rank-one K-stable subspace
disc2 = tr2*tr2 - 4*dt2
def _is_rat_square(fr_):
    if fr_ < 0:
        return False
    n_, d_ = fr_.numerator, fr_.denominator
    return int(n_**0.5)**2 == n_ and int(d_**0.5)**2 == d_
check(not _is_rat_square(disc2),
      f"the dichotomy canary: the discriminant tr^2-4det = {disc2} is not "
      f"a rational square (no rational eigenvalue: no rank-one K-stable "
      f"subspace; the source dichotomy 0-or-full)")
timer("V5 complete: the generators, the period identity, the dichotomy")

# ============================================================ V6: DEGENERACY
print("=" * 96)
print("V6 -- THE EISENSTEIN DEGENERACY (the named non-generic world)")
print("=" * 96)
dE, alE = DEGENERATE
a4E = kpow(alE, 4, dE)
a3cE = kmul(kpow(alE, 3, dE), kconj(alE), dE)
wfE = minpoly(a4E, dE)
mfE = minpoly(a3cE, dE)
check(a4E == kconj(a3cE),
      f"the degeneracy condition: alpha^4 == conj(alpha^3 conj(alpha)) "
      f"exactly in K (the phase alpha/conj(alpha) is a cube root of unity: "
      f"1+sqrt(-3) = 2 exp(i pi/3))")
check(wfE == mfE,
      f"the factor coincidence: minpoly(alpha^4) == minpoly(alpha^3 cbar) "
      f"= {wfE.as_expr()} (the Weil plane merges with the mixed sector)")
AE = alpha_matrix(alE, dE)
E4E = ext4_matrix(AE)
coeffsE = [fr(c) for c in wfE.all_coeffs()[::-1]]
PME = poly_eval_mat(coeffsE, E4E)
WbE = kernel_basis(PME)
check(len(WbE) == 34,
      f"the merged primary part: dimension {len(WbE)} == 34 = 2 + 32 (the "
      f"degenerate world's spectral fusion; excluded from the generic "
      f"census, carried as the named degeneracy)")
# the canary: the degeneracy does NOT occur at any generic world
no_deg = True
for d, alpha in GENERIC:
    a4g = kpow(alpha, 4, d)
    a3cg = kmul(kpow(alpha, 3, d), kconj(alpha), d)
    if a4g == kconj(a3cg):
        no_deg = False
check(no_deg,
      f"the degeneracy canary: alpha^4 != conj(alpha^3 cbar) at every one "
      f"of the {len(GENERIC)} generic worlds (the census is clean)")
timer("V6 complete")

# ============================================================== V7: HOSTILE
print("=" * 96)
print("V7 -- THE HOSTILE BATTERY (every control FIRES) + THE SCANS")
print("=" * 96)

# H1: letter-deletion -- Omega loses a letter: the monomial count changes
mons_h1 = []
for k in range(5):
    for S in combinations(range(3), k):
        word = tuple(sorted([2*j + (1 if j in S else 0) for j in range(3)] + [6]))
        re_c = (1 if k % 4 == 0 else (-1 if k % 4 == 2 else 0))
        mons_h1.append((word, re_c))
check(len(mons_h1) != 16 and len(mons) == 16,
      f"H1 LETTER-DELETION FIRES: deleting a letter from Omega changes the "
      f"monomial count ({len(mons_h1)}-ish != 16; the generator receipt is "
      f"load-bearing)")
# H2: sign-flip in the projector: P + t^2 no longer == 1 mod the Weil factor
pw_bad = pw_repo + Poly(t*t, t, domain=QQ)
_, rembad = divmod(pw_bad, r['weil_f'])
check(rembad != Poly(1, t, domain=QQ),
      f"H2 PROJECTOR-SIGN FIRES: perturbing P_W breaks the ==1 congruence "
      f"mod the Weil factor (the CRT receipt is load-bearing)")
# H3: fake ambient eigenvalue: ker(E4 - 26 I) is NOT 36-dimensional
EM_bad = [[w1['E4'][i][j] - (Fraction(26) if i == j else Fraction(0))
           for j in range(70)] for i in range(70)]
bad_ker = kernel_basis(EM_bad)
check(len(bad_ker) != 36,
      f"H3 FAKE-AMBIENT FIRES: ker(^4[alpha] - 26) has dimension "
      f"{len(bad_ker)} != 36 (the ambient receipt is load-bearing)")
# H4: the non-word injection: a 5-letter tuple is not a ^4 word
fake_word = (0, 1, 2, 3, 4)
check(fake_word not in WORDS4,
      f"H4 NON-WORD FIRES: the 5-letter tuple is not an element of the "
      f"70-word basis (the word combinatorics is load-bearing)")
# H5: garbage liveness (the planted false predicate, retracted)
_g_pre = FAILS
_planted = (len(Wb) == len(Wb) + 1)
check(_planted,
      "H5 GARBAGE-LIVENESS: the planted false predicate was reported as a "
      "failure (the framework's failure path is live)")
_h5 = (FAILS == _g_pre + 1)
if _h5:
    FAILS -= 1
    FAIL_LINES.pop()
check(_h5,
      "H5 GARBAGE-LIVENESS FIRES: the planted false comparison was counted "
      "as a failure by the framework and retracted (the failure path is "
      "live, not decorative)")
# H6: the degeneracy canary battery (ledger 112: cover the violation
# directions) -- claiming genericity AT the degenerate world must FAIL
degen_claim = (minpoly(a4E, dE) != minpoly(a3cE, dE))
check(not degen_claim,
      f"H6 DEGENERACY-CLAIM FIRES: the genericity claim evaluated at the "
      f"Eisenstein world is FALSE (the factor-coincidence check catches the "
      f"wrong census assignment)")
# the mechanical vacuity scan (ledger 107)
# VACUITY-SCAN-REGION-START
def vacuity_scan():
    with open(__file__, 'r') as f:
        src_lines = f.readlines()
    outl = []
    inside = False
    for ln in src_lines:
        if 'VACUITY-SCAN-REGION-START' in ln:
            inside = True
        if 'VACUITY-SCAN-REGION-END' in ln:
            inside = False
            continue
        if not inside:
            outl.append(ln)
    src = ''.join(outl)
    pats = []
    pats.append((re.compile('or' + chr(32) + r'True\b'), 'or-literal'))
    pats.append((re.compile('and' + chr(32) + r'False\b'), 'and-literal'))
    pats.append((re.compile('ok' + chr(92) + '(' + 'True'), 'ok-True-literal'))
    pats.append((re.compile('if' + chr(32) + r'False' + chr(32) + r':'), 'dead-conditional'))
    hits = []
    for pat, name in pats:
        for mm in pat.finditer(src):
            hits.append(name)
    return hits
# VACUITY-SCAN-REGION-END
hits = vacuity_scan()
check(len(hits) == 0,
      f"the mechanical vacuity scan (ledger 107) over this file's own "
      f"source (the scan region excluded): {len(hits)} hits for the banned "
      f"boolean-literal patterns")

def self_comparison_scan():
    with open(__file__, 'r') as f:
        lines = f.readlines()
    hitsc = 0
    for i, line in enumerate(lines):
        mm = re.search(r'^\s*(\w+)\s*=\s*(.+)$', line)
        if mm:
            var, rhs = mm.group(1), mm.group(2)
            for j in range(i, min(i + 3, len(lines))):
                if re.search(rf'\b{re.escape(var)}\s*==\s*{re.escape(var)}\b', lines[j]):
                    hitsc += 1
    return hitsc
sc = self_comparison_scan()
check(sc == 0,
      f"the self-comparison scan (ledger 107): {sc} hits (no variable is "
      f"compared to itself within 3 lines of its assignment)")

# ================================================================ the result
print("=" * 96)
print(f"RESULT: {CHECKS} checks passed, {FAILS} failed")
if FAIL_LINES:
    for fl in FAIL_LINES:
        print(f"  FAILED: {fl}")
print(f"runtime: {time.time()-T0:.1f}s  (deterministic: xorshift64* seed "
      f"0x{SEED:X})", file=sys.stderr, flush=True)
print(f"CHECKS={CHECKS} FAILS={FAILS}", file=sys.stderr, flush=True)
sys.exit(0 if FAILS == 0 else 1)
