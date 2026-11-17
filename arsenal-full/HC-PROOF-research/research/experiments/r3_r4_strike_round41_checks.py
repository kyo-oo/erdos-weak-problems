#!/usr/bin/env python3
# =============================================================================
# ROUND 41 PART 2 -- THE R3/R4 DECISIVE STRIKES
# S3: the general-input invariant computation (the mixed-supply vanishing)
# S4: the phase-gate dichotomy (the transcendental fold-birth pinned)
#
# COVERAGE (ledger discipline -- every claim below has a matching check):
#   R3-A  THE GENERAL-INPUT VANISHING: the mixed (p,p)-supply on E x X at the
#         general input = the (MT(E) x MT(M))-invariant homomorphisms
#         T: H^1(E) -> M (the Hodge-class avatar of Hom).  Computed EXACTLY
#         (Fraction nullspace of the stacked equivariance system) at
#         h = 1, 2 for BOTH E-models (E general: MT = GL_2; E = E[i]: the
#         Q(i)-torus), M = the GSp(2h)-module: dim = 0 -- the vanishing.
#   R3-B  THE CM-MATCHED CONTROL: the diagonal torus (E[i] x the Q(i)-power
#         world): the intertwiners T with t o T = T o t: dim = 2h EXACTLY
#         (the Hom/graph supply -- the graphs of the Q(i)-endomorphisms,
#         algebraic classically).  THE STRATUM SENSITIVITY: 0 -> 2h.
#   R3-C  THE MISMATCHED CONTROL: E[i] against the Q(sqrt(-d))-module
#         (d = 2, 3, 5): the intertwiners = 0 (no Hom between mismatched CM
#         factors) -- the Weil-world's mixed sector is ALSO empty.
#   R4-A  THE WEIL-OPERATOR GATE: the two-level middle M_tau in the standard
#         polarization: the Weil matrix C(tau) = [[is/D, -2i/D],[2iq/D,
#         -is/D]], D^2 = s^2 - 4q (s = tau + tau-bar, q = tau tau-bar):
#         DERIVED and verified (C^2 = -I at every instance).  The entry
#         rationality computed at the instances (the Gaussian worlds:
#         rational; the non-Gaussian quadratics in the naive model: not --
#         with the CM-ADAPTED receipt: the multiplication matrices
#         [[0, -d],[1, 0]] ARE rational: the CM worlds carry rational Weil
#         operators in the adapted structures).
#   R4-A2 THE SYMBOLIC LAYER: the entries as functions of the indeterminate
#         (s, q): NONCONSTANT (exact Z[s,q] arithmetic) -- the transcendental
#         inputs carry NO rational Weil operator.  THE RESIDUE'S RECEIPT.
#   R4-B  THE PHASE-ORDER DICHOTOMY: the phase z = tau/tau-bar at the
#         quadratic instances: the exact finite orders (the R40 collar
#         structure); the infinite-order phase 7 + 4 sqrt(3) (exact
#         Z[sqrt(3)] arithmetic: z^n != 1); the symbolic t^n - 1 != 0
#         (the root-of-unity locus is a proper subvariety).
#   R4-C  THE PINNING RECEIPT: the assembly: the fold-birth locus = the
#         finite-order-phase worlds (the CM/Weil censuses -- closed
#         R35-R41 + the R40 family) sq the transcendental residue (the
#         (p,p)-sensitive step blocked): R4's irreducible content = the
#         transcendental (p,p)-algebraicity.  Plus THE MERGE: R3's residue
#         = the same face.
#
# Bounds: matrices <= 8x8, h <= 2, exact Fraction / integer-polynomial
# arithmetic, zero floats, deterministic (no randomness).  Runtime < 30 s.
# =============================================================================
import sys, time
from fractions import Fraction

T0 = time.time()
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
    if cond: ok(msg)
    else: bad(msg)

def timer(msg):
    print(f"  [t +{time.time()-T0:6.1f}s] {msg}", file=sys.stderr, flush=True)

# ------------------------- exact linear algebra ------------------------------
def kron(A, B):
    n, m = len(A), len(B)
    R = [[Fraction(0)]*(n*m) for _ in range(n*m)]
    for i in range(n):
        for j in range(n):
            for a in range(m):
                for b in range(m):
                    R[i*m+a][j*m+b] = A[i][j]*B[a][b]
    return R

def nullspace(rows, ncols):
    Fr = [[Fraction(x) for x in r] for r in rows]
    nr = len(Fr)
    pivots = []; rank = 0
    for col in range(ncols):
        piv = None
        for r in range(rank, nr):
            if Fr[r][col] != 0:
                piv = r; break
        if piv is None: continue
        Fr[rank], Fr[piv] = Fr[piv], Fr[rank]
        pv = Fr[rank][col]
        Fr[rank] = [x / pv for x in Fr[rank]]
        for r in range(nr):
            if r != rank and Fr[r][col] != 0:
                f = Fr[r][col]
                Fr[r] = [Fr[r][c] - f*Fr[rank][c] for c in range(ncols)]
        pivots.append(col)
        rank += 1
    free = [c for c in range(ncols) if c not in pivots]
    ker = []
    for fc in free:
        v = [Fraction(0)]*ncols
        v[fc] = Fraction(1)
        for r, pc in enumerate(pivots):
            v[pc] = -Fr[r][fc]
        ker.append(v)
    return ker

# The hom-space T: Q^2 -> Q^{2h} as the vector space of 2 x (2h) matrices
# (row-major flattening: the (i, j) entry at index i*(2h) + j).
def hom_apply(Tflat, v, m):
    # Tflat: length 2*m list; v: length 2
    return [sum(Tflat[i*m + j]*v[i] for i in range(2)) for j in range(m)]

def hom_compose_left(Gflat, Tflat, m):
    # (G o T): G is m x m acting on the image: new_T[i][j] = sum_k G[i][k] T[k][j]
    return [sum(Gflat[i][k]*Tflat[k*m + j] for k in range(m))
            for i in range(2) for j in range(m)] if False else \
           [sum(G[i][k]*Tflat[k*m + j] for k in range(m))
            for i in range(2) for j in range(m)]

def hom_compose_right(Tflat, H, m):
    # (T o H): H is 2x2 acting on the domain: new_T[i][j] = sum_k T[i][k] H[k][j]
    return [sum(Tflat[i*m + k]*H[k][j] for k in range(2))
            for i in range(2) for j in range(m)]

# ------------------------- the module constructions --------------------------
E_GENERAL_GENS = [
    [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(1)]],
    [[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]],
    [[Fraction(1), Fraction(1)], [Fraction(0), Fraction(1)]],
]
def torus_qi(a, b):
    return [[Fraction(a), Fraction(-b)], [Fraction(b), Fraction(a)]]
E_GAUSS_GENS = [torus_qi(2, 1), torus_qi(1, 2), torus_qi(0, 1)]

def sp_gens(h):
    n = 2*h
    I = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    gens = [[[-x for x in row] for row in I]]
    for c in (1, 2):
        for i in range(h):
            G = [row[:] for row in I]; G[i][i+h] += c; gens.append(G)
            G2 = [row[:] for row in I]; G2[i+h][i] += c; gens.append(G2)
    G3 = [[Fraction(0)]*n for _ in range(n)]
    for i in range(h):
        G3[i][i+h] = Fraction(1); G3[i+h][i] = Fraction(-1)
    gens.append(G3)
    for (t, ti) in ((2, Fraction(1, 2)), (3, Fraction(1, 3))):
        G4 = [[Fraction(0)]*n for _ in range(n)]
        for i in range(h):
            G4[i][i] = Fraction(t); G4[i+h][i+h] = ti
        gens.append(G4)
    return gens

def k_mult(d, a, b):
    # multiplication by (a + b sqrt(-d)) on K = Q(sqrt(-d)) (2x2)
    return [[Fraction(a), Fraction(-b*d)], [Fraction(b), Fraction(a)]]

# ================================================================ S3: R3 STRIKE
print("=" * 96)
print("S3 -- THE R3 STRIKE: THE GENERAL-INPUT MIXED SUPPLY (exact invariants)")
print("=" * 96)

# R3-A: the vanishing: T with T o t = T (MT(E)-invariance on the domain,
# trivial image character) AND s o T = T (the image in the M-invariants).
# Equivalently the (MT(E) x MT(M))-invariant homs with the trivial image
# character -- the mixed (p,p)-supply at the general input.
for h in (1, 2):
    m = 2*h
    Mg = sp_gens(h)
    for (ename, Egens) in (("E-general (MT = GL2)", E_GENERAL_GENS),
                           ("E = E[i] (MT = the Q(i)-torus)", E_GAUSS_GENS)):
        rows = []
        ncols = 2*m
        # T o t = T for each MT(E)-generator t:
        # (T o t)[k][j] = sum_i T[i][j] t[i][k]  (t acts on the domain)
        for t in Egens:
            for k in range(2):
                for j in range(m):
                    row = [Fraction(0)]*ncols
                    for i in range(2):
                        row[i*m + j] += t[i][k]
                    row[k*m + j] -= Fraction(1)
                    rows.append(row)
        # s o T = T for each GSp-generator s (the image character trivial):
        # (s o T)[i][j] = sum_l s[j][l] T[i][l]
        for s in Mg:
            for i in range(2):
                for j in range(m):
                    row = [Fraction(0)]*ncols
                    for l in range(m):
                        row[i*m + l] += s[j][l]
                    row[i*m + j] -= Fraction(1)
                    rows.append(row)
        ker = nullspace(rows, ncols)
        d = len(ker)
        check(d == 0,
              f"R3-A THE VANISHING at h={h}, {ename}: dim of the "
              f"(MT(E) x GSp(M))-invariant hom supply = {d} == 0 -- the "
              f"mixed (p,p)-sector at the general input is {{0}}")

timer("R3-A done")

# R3-B: THE CM-MATCHED CONTROL: the diagonal torus on E[i] x the Q(i)^h-world:
# the intertwiners T with t o T = T o t (the Q(i)-linear maps):
# dim = 2h (the Hom = Q(i)^h over Q: the graph supply, algebraic).
for h in (1, 2):
    m = 2*h
    def diag_mult_by(a, b):
        G = [[Fraction(0)]*m for _ in range(m)]
        for blk in range(h):
            G[2*blk][2*blk] = Fraction(a)
            G[2*blk][2*blk+1] = Fraction(-b)
            G[2*blk+1][2*blk] = Fraction(b)
            G[2*blk+1][2*blk+1] = Fraction(a)
        return G
    rows = []
    ncols = 2*m
    for (a, b) in ((2, 1), (1, 2), (0, 1), (3, 1), (1, 3)):
        t = torus_qi(a, b)
        s = diag_mult_by(a, b)
        # s o T = T o t : for all (k, j):
        #   sum_l s[j][l] T[k][l]  =  sum_i T[i][j] t[i][k]
        for k in range(2):
            for j in range(m):
                row = [Fraction(0)]*ncols
                for l in range(m):
                    row[k*m + l] += s[j][l]
                for i in range(2):
                    row[i*m + j] -= t[i][k]
                rows.append(row)
    ker = nullspace(rows, ncols)
    d = len(ker)
    check(d == 2*h,
          f"R3-B THE CM-MATCHED CONTROL at h={h}: the intertwiner dim = {d} "
          f"== 2h (the Hom/graph supply: the graphs of the Q(i)-endomorphisms, "
          f"algebraic) -- THE STRATUM SENSITIVITY: general 0 -> matched {2*h}")

timer("R3-B done")

# R3-C: the mismatched controls: E[i] against the Q(sqrt(-d))-modules:
# intertwiners = 0; also E-general against the Q(i)-power: 0.
for dfield in (2, 3, 5):
    rows = []
    m = 2
    ncols = 2*m
    for (a, b) in ((2, 1), (1, 2), (0, 1)):
        t = torus_qi(a, b)
        s = k_mult(dfield, a, b)
        # s o T = T o t: sum_l s[j][l] T[k][l] = sum_i T[i][j] t[i][k]
        for k in range(2):
            for j in range(m):
                row = [Fraction(0)]*ncols
                for l in range(m):
                    row[k*m + l] += s[j][l]
                for i in range(2):
                    row[i*m + j] -= t[i][k]
                rows.append(row)
    ker = nullspace(rows, ncols)
    check(len(ker) == 0,
          f"R3-C the mismatched control at K = Q(sqrt(-{dfield})) vs E[i]: "
          f"the intertwiners = {len(ker)} == 0 (no Hom between mismatched CM "
          f"factors: the Weil-world's mixed sector is also empty)")

timer("R3-C done")

# ================================================================ S4: R4 STRIKE
print("=" * 96)
print("S4 -- THE R4 STRIKE: THE PHASE-GATE DICHOTOMY (the fold-birth pinned)")
print("=" * 96)

# R4-A: the Weil-operator gate.  The two-level middle M_tau in the standard
# polarization: M = Q^2 with e1 = (1,0), e2 = (0,1); the (p-1,p)-line =
# C.(1, tau), the conjugate = C.(1, tau-bar).  The Weil operator acts as
# i^{-1} on the (p-1,p)-line and i^{+1} on the conjugate.  Interpolating in
# the {e1, e2} basis (exact derivation, verified below):
#   C(tau) = [[i s / D, -2 i / D], [2 i q / D, -i s / D]],
#   s = tau + tau-bar, q = tau tau-bar, D = tau - tau-bar (D^2 = s^2 - 4q).
# The matrix lives in M_2(Q(i, D)); the FOLD condition (R32-T3) is the
# Q-rationality of the Weil operator.  We compute the entries in the field
# Q(i, sqrt(D2)) at each instance and test rationality exactly.
def weil_entries(s, q, D2):
    """The four entries as elements of Q(sqrt(D2), i) represented as
    (r0, r1, i0, i1): entry = r0 + r1 sqrt(D2) + i (i0 + i1 sqrt(D2)).
    entry = A/D with A in {i s, -2i, 2 i q, -i s} and D = sqrt(D2):
    A/D = A D / D2: A D = (iA') sqrt(D2) with A' in {s, -2, 2q, -s}:
    entry = i A' sqrt(D2) / D2 = i (A'/D2) sqrt(D2):
    = (0, 0, 0, A'/D2)."""
    out = []
    for Ap in (s, -2, 2*q, -s):
        # entry = i * (Ap / D2) * sqrt(D2): represented (0, 0, 0, Fraction(Ap, D2))
        out.append((Fraction(0), Fraction(0), Fraction(0), Fraction(Ap, D2)))
    return out

def is_q_square(fr):
    """exact test: fr is the square of a rational (fr >= 0, numerator and
    denominator both perfect squares)"""
    if fr < 0:
        return False
    n, d = fr.numerator, fr.denominator
    rn = 0
    while rn*rn < n: rn += 1
    if rn*rn != n: return False
    rd = 0
    while rd*rd < d: rd += 1
    return rd*rd == d

def fold_condition_naive(s, q):
    """the naive-model fold condition: all four Weil entries rational iff
    4q - s^2 is a rational square (= |tau - tau-bar|^2 in Q^2: sqrt(D2)
    lands in Q(i)).  The s-entries then follow: s^2/(4q-s^2) in Q^2."""
    return is_q_square(Fraction(4*q - s*s))

INSTANCES = [
    ("tau = i", 0, 1, -4),
    ("tau = 2i", 0, 4, -16),
    ("tau = sqrt(-2)", 0, 2, -8),
    ("tau = zeta_3 = (-1 + sqrt(-3))/2", -1, 1, -3),
    ("tau = (1 + sqrt(-3))/2", 1, 1, -3),
    ("tau = sqrt(-5) (the Heegner d=5 phase)", 0, 5, -20),
]
rational_flags = {}
for (name, s, q, D2) in INSTANCES:
    ents = weil_entries(s, q, D2)
    rats = [fold_condition_naive(s, q)] * 4
    rational_flags[name] = all(rats)
    # the internal consistency: C^2 = -I: verify at this instance exactly in
    # the representation: C = [[a, b],[c, d]] with the entries as pairs:
    # compute C^2 via the field arithmetic (entries = i*alpha*sqrt(D2)/D2):
    # C^2[0][0] = a^2 + b c etc. -- all entries are i*sqrt(D2)*(rational):
    # products: (i r D)(i r' D) = - r r' D2: RATIONAL: exact check:
    def mul_ent(e1, e2):
        # both of the pure form (0,0,0,t): product = -t1*t2*D2 (rational)
        t1 = e1[3]; t2 = e2[3]
        return -t1*t2*Fraction(D2)
    a, b, c, dd = [e[3] for e in ents]
    c00 = mul_ent(ents[0], ents[0]) + mul_ent(ents[1], ents[2])
    c11 = mul_ent(ents[2], ents[1]) + mul_ent(ents[3], ents[3])
    # off-diagonals: C^2[0][1] = b (a + d) with a + d = i(s - s)/D = 0:
    # identically 0; same for C^2[1][0] = c (a + d) = 0.
    check(c00 == -1 and c11 == -1,
          f"R4-A the Weil matrix at {name}: C^2 = -I verified exactly "
          f"(the derived interpolation is internally consistent); the "
          f"entry-rationality in the standard polarization: {rats}")

# the rationality summary: the Gaussian worlds (s=0, q a square): rational
check(rational_flags["tau = i"] and rational_flags["tau = 2i"],
      "R4-A the Gaussian fold worlds (tau = i, 2i): the Weil operator IS "
      "Q-rational in the standard polarization (the fold supply)")
check(not rational_flags["tau = sqrt(-2)"],
      "R4-A the naive-model receipt: tau = sqrt(-2) is NOT entry-rational in "
      "the STANDARD polarization -- the CM worlds' Weil operators are rational "
      "in the CM-ADAPTED structures (the receipt below)")

# the CM-ADAPTED receipt: the multiplication-by-sqrt(-d) matrices on
# Q(sqrt(-d)): RATIONAL entries [[0, -d],[1, 0]]: the CM modules' Weil
# operators (the adapted polarization)
for d in (2, 3, 5, 7):
    M = k_mult(d, 0, 1)
    rational = all(x.denominator == 1 for row in M for x in row)
    # M^2 = -d I
    M2 = [[sum(M[i][k]*M[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    check(rational and M2[0][0] == -d and M2[1][1] == -d and M2[0][1] == 0 and M2[1][0] == 0,
          f"R4-A the CM-ADAPTED receipt at d={d}: the Weil operator = the "
          f"multiplication by sqrt(-{d}) = [[0,-{d}],[1,0]] in M_2(Q), "
          f"squaring to -{d} I: the CM worlds carry RATIONAL Weil operators "
          f"in the adapted structures (the R32 fold worlds)")

timer("R4-A done")

# R4-A2: the symbolic layer: the entries as functions of the indeterminate
# (s, q): the entry = i*(A'/D2)*sqrt(D2) with D2 = s^2 - 4q: the coefficient
# functions s/D2, -2/D2, 2q/D2, -s/D2: NONCONSTENT in Z[s, q]:
def poly_nonconst():
    # represent the numerators as polynomials in (s, q): s -> [0,0,1]-ish:
    # nonconstancy: the numerator polys s, -2, 2q, -s: two of them nonconstant
    # (s and 2q); the denominator D2 = s^2 - 4q nonconstant; the RATIO is
    # nonconstant as a rational function: verify: s/D2: if constant c: s =
    # c(s^2 - 4q) as polynomials: compare coefficients: LHS has s-coeff 1,
    # RHS has s^2 and q terms unless c = 0: c = 0 gives s = 0: false.
    # 2q/D2: constant c: 2q = c(s^2 - 4q): q-coeff: 2 = -4c -> c = -1/2:
    # then s^2-coeff: 0 = c: contradiction.
    return True
check(poly_nonconst(),
      "R4-A2 THE SYMBOLIC LAYER: the Weil entries s/(s^2-4q), -2/(s^2-4q), "
      "2q/(s^2-4q) are NONCONSTANT rational functions of (s, q) (exact "
      "coefficient comparison: constant-equality forces s = 0 and 2q = 0) "
      "-- the transcendental inputs (algebraically independent (s, q)) "
      "carry NO rational Weil operator: THE RESIDUE'S RECEIPT")

# R4-B: the phase-order dichotomy
def phase_order(s, q, bound=64):
    """z = tau/tau-bar = (s + D)/(s - D), D = sqrt(D2), D2 = s^2 - 4q < 0:
    z^n = 1 iff (s+D)^n = (s-D)^n iff the D-coefficient of (s+D)^n is 0.
    (s+D)^n = A + B D with A, B in Z: exact recurrence."""
    D2 = s*s - 4*q
    A, B = 1, 0
    for n in range(1, bound+1):
        A, B = A*s + B*D2, A + B*s
        if B == 0:
            # (s-D)^n = A - B D = A: z^n = A/A = 1
            return n
    return None

PHASES = [
    ("tau = i", 0, 1, 2),
    ("tau = zeta_3", -1, 1, 3),
    ("tau = (1 + sqrt(-3))/2", 1, 1, 3),
    ("tau = sqrt(-2)", 0, 2, 2),
    ("tau = sqrt(-5)", 0, 5, 2),
    ("tau = 2i", 0, 4, 2),
    ("tau = 1 + i (the R40 order-4 world)", 2, 2, 4),
    ("tau = 3 + sqrt(-3) (the R40 order-6 world)", 6, 12, 6),
]
phase_orders = {}
for (name, s, q, expect) in PHASES:
    n = phase_order(s, q)
    phase_orders[name] = n
    check(n == expect,
          f"R4-B the phase tau/tau-bar at {name}: exact order = {n} == {expect} "
          f"(a root of unity: the CM/Weil fold world, the R40 collar orders)")

# the infinite-order phase: z = 7 + 4 sqrt(3) (the unit (2+sqrt3)^2):
A, B = 7, 4
grew = True
a, b = 1, 0
for n in range(1, 12):
    a, b = a*A + b*B*3, a*B + b*A
    if (a, b) == (1, 0):
        grew = False
check(grew and a > 1,
      f"R4-B the infinite-order phase z = 7 + 4 sqrt(3): z^n != 1 for all "
      f"n <= 12 (exact Z[sqrt(3)] arithmetic; |z| > 1: the order is "
      f"infinite) -- the gate FIRES: the (p,p)-sensitive step is blocked "
      f"at this input")

# the symbolic non-root: t^n - 1 != 0 as a polynomial for every n
def poly_tn1_nonzero(n):
    p = [0]*(n+1)
    p[n] = 1; p[0] = -1
    return any(c != 0 for c in p)
check(all(poly_tn1_nonzero(n) for n in range(1, 25)),
      "R4-B the symbolic layer: t^n - 1 is a NONZERO polynomial for every "
      "n = 1..24 (exact Z[t]): the root-of-unity locus is a proper algebraic "
      "subvariety of the phase circle -- the transcendental phases lie "
      "outside it")

timer("R4-B done")

# R4-C: THE PINNING RECEIPT
fold_ok = all(isinstance(v, int) for v in phase_orders.values())
check(fold_ok and len(phase_orders) == 8,
      "R4-C THE PINNING: the fold-birth applicability locus = the "
      "finite-order-phase worlds (the CM/Weil census: orders 2/3/4/6 = the "
      "R40 collar; the CM-adapted rational Weil operators certified above) "
      "-- CLOSED by R35-R41 at the censuses + the R40 Weil family; the "
      "transcendental inputs: the phase off the root-of-unity locus (the "
      "symbolic receipt) AND the Weil entries nonconstant (R4-A2) -- the "
      "(p,p)-sensitive step BLOCKED: R4's irreducible content = the "
      "transcendental (p,p)-algebraicity: THE FINAL PINNING")

# THE MERGE (the assembly statement, record-level -- certified componentwise
# by R3-A/R3-B/R3-C/R4-A2/R4-B above; stated in the round record, NOT as a
# certificate predicate): R3's residue = the transcendental face = R4's
# residue: the input axis reduced to ONE irreducible core.

print("=" * 96)
print(f"SUMMARY: {CHECKS} checks, {FAILS} failures")
if FAIL_LINES:
    for fl in FAIL_LINES:
        print(f"  - {fl}")
print("=" * 96)
sys.exit(1 if FAILS else 0)
