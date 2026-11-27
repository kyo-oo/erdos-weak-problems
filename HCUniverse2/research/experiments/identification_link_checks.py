#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GST IDENTIFICATION LINK -- certificate script (Round 24; the operator's
standing order: the one mechanism rot at max, the actual mathematics on
the single remaining construction).

THE CONSTRUCTION CERTIFIED, WITH ITS HYPOTHESIS ON THE FACE (the 24-b
audit's B1 repair). This round delivers the TARGET-SIDE CALCULUS of the
identification link Lambda_p at the conduit's grade p (the model
instantiation at p = 2, the middle degree of the committed four-factor
letter world), under the STRIP-SHAPE HYPOTHESIS:

  HYPOTHESIS (the strip shape, assumed here; the 21-c item (ii)
  remains the reduction step): after the D2/D3 strip the two-cell of
  the input pair at scale m with content alpha is the iota-shaped
  curvature cochain
      c_{m,alpha}(v, w) = theta(v,w) * iota(m*alpha),
      iota(x) = (x, -x) in M_alpha (+) M_alpha,
  theta = the committed symplectic form Sum_j e_j ^ f_j (the world's
  Kahlerr class as the curvature), v, w the groupoid arrows (the
  monodromy letters). The committed strip control and the traceless
  decks certify the iota-shape as the strip's own OUTPUT TYPE at the
  cochain level; the reduction of the ACTUAL GL(H_z)-valued two-cell
  to this cochain is NOT performed here and is recorded as the
  remaining step of the construction.

  LAMBDA-P (the grade-typed parity reduction, defined on the strip's
  output shape): the link reads the two-cell's theta-line and carries
  it to the deck cohomology of the CONTENT at the conduit's grade:
      Lambda_p([c]) := [ iota(m * pi_p(alpha)) ] in H^1(C_4; iota(M)),
  pi_p = the (p,p)-typed content projection (the committed typing
  machinery), M = the content module.

THE LAWS (each a finite instance of a derivation identity, exact
arithmetic; the check-discipline claim: every counted check is an
asserted comparison that the audit's mutation battery verified able to
fail -- the five documentation-as-assert sites found by the audit were
REMOVED, and the audit's p-only mutation is caught by the filter check
in LA2):

LA1  THE REDUCTION LAWS (on the assumed shape). The transport identity
     gamma.c = c_{gamma.alpha} (the symplectic law gamma in Sp(8,Z) +
     the intertwining (gamma x gamma) o iota = iota o gamma); the bar
     complex's law (a formality receipt, labeled as such); the norm law
     N(c) = theta * iota(m * N_gamma alpha) = 0 on the computed
     all-odd plane instances (the R1 norm degeneration applied AT THE
     COCHAIN LEVEL -- with its own boundary on the face: the norm law
     holds for EVERY iota-shaped content and does NOT by itself
     distinguish the (A,-A) witness; the iota-specificity is the
     STRIP's traceless condition, computed; the pair-level residue is
     discharged only through the two-cell reduction, NOT claimed
     here); the H^2(C_4; iota(M)) = 0 receipt (the doubled pair
     module; the iota-submodule carries H^1 = Z/2); THE PARITY LAW for
     the PRIMITIVE contents (nonzero H^1-class): the least kill-scale
     2 on every (2,2) plane and both Weil rays; the degenerate-content
     boundary (contents already in im(gamma-1) die at every scale --
     the audit's counterexample, computed as a receipt).

LA2  THE GATE (the grade law; the link's DOMAIN condition). The link
     Lambda_p exists as an identification exactly when
     pi_p(alpha) != 0. The all-odd sector partitions into EIGHT
     typed-pure orbit planes: the Weil plane (4,0)+(0,4), four
     (3,1)+(1,3) planes, three (2,2) planes. pi_2 is nonzero EXACTLY
     on the three (2,2) planes; on the other five the target module is
     zero and NO identification exists (the link does not carry their
     two-cell -- the domain condition; the gated content's own module
     law survives, the positive non-killing datum). THE
     CHARACTER-COLLISION RECEIPT: the product deck (the total
     rotation) acts by the scalar i^{p-q}: +1 on the (2,2) planes AND
     on the Weil plane, -1 on the (3,1) planes -- the deck character
     does NOT separate (2,2) from (4,0)+(0,4); the grade projection
     does; the collision sector is exactly the transcendental
     discriminator sector (W_R, W_I). The gate is the grade; the deck
     character is (p-q) mod 4. The (p,p)-specificity of the filter is
     itself certified (the p-only mutation caught).

LA3  THE SECTOR ACCOUNTING. The typed-pure lattices S22/S40/S31
     (ranks 6/2/8, the type-system kernels); the rational typed
     partition; the exact indices (the plane spans: 16 in S22, 1 for
     the W-plane, 256 in S31; the word lattice over the typed-pure
     sum: 4096). The all-even (2,2) content is the divisor-product
     sector (Sector 1, the committed compiler). The all-odd typed-
     pure (2,2) lattice S22 is THIS ROUND's sector: the link's
     target-side laws are certified on it in full (deck-stable,
     gamma^2 = -I, H^2 = 0, H^1 = (Z/2)^3, the sector kill-scale 2
     exact). THE COMPOSITION BOUNDARY ON THE FACE: the descent and
     the conduit are NOT computed here -- they require the two-cell
     reduction (the 21-c item (ii)) and remain the composition's
     remaining steps; no algebraicity is claimed for any sector in
     this round's artifacts. The mixed-parity (2,2) content is the
     other remaining sector (the next strike's target).

HOSTILE CONTROLS: the broken symplectic (a non-unit letter map: BOTH the
symplectic law and the transport identity FAIL, computed); the 2-torsion
degeneration (the parity residue dies mod 2); the all-even contrast (the
pair-product module: H^1 = 0 and the 4-torsion scale-4 law -- a
DIFFERENT law from the parity law, the two sectors discriminated); the
mixed-grade control (a (2,2)+(4,0) content: the link carries EXACTLY the
(2,2)-part; the Weil part has no grade-2 content -- the conduit's purity
hypothesis, recorded as a stated hypothesis of the two-center descent
law, not a computed conduit rejection); the gate filter's
(p,p)-specificity; the strip's trace control (the (x,+x) shape is NOT
traceless: the iota-specificity is the strip's).

Scope: letter-lattice laws on the committed model world; the
mixed-parity sector and the general-input transport (ledger 085) are
the recorded remaining sector; the Lean face
EveryHodgeClassIsRationalAlgebraic remains the target.

Deterministic: no randomness anywhere; fixed bounded instances; exact
Fraction/int arithmetic; zero floats; zero complex; double-run
byte-identical.
"""

import sys
from fractions import Fraction as Fr
from itertools import combinations

CHECKS = 0

def ok(cond, label):
    global CHECKS
    assert cond, label
    CHECKS += 1
    print("  [PASS] " + label)

# =====================================================================
# THE MODEL (the committed conventions, verbatim from the campaign core:
# wi_vertex_pin_checks.py / rotation_deck_checks.py -- the eight-letter
# exterior algebra, the sorted-word basis, the exact wedge, the Gaussian
# Weil classes, the four-rotation family, the cyclic cohomology engine,
# the committed typing machinery)
# =====================================================================
VOL = (0, 1, 2, 3, 4, 5, 6, 7)
ZERO = {}

def wedge(d1, d2):
    out = {}
    for w1, c1 in d1.items():
        for w2, c2 in d2.items():
            if set(w1) & set(w2):
                continue
            inv = sum(1 for x in w1 for y in w2 if x > y)
            w = tuple(sorted(w1 + w2))
            out[w] = out.get(w, 0) + c1 * c2 * (1 if inv % 2 == 0 else -1)
    return {w: c for w, c in out.items() if c != 0}

def sc(d, s):
    return {w: c * s for w, c in d.items() if c * s != 0}

def addc(*ds):
    out = {}
    for d in ds:
        for w, c in d.items():
            out[w] = out.get(w, 0) + c
    return {w: c for w, c in out.items() if c != 0}

def gauss_weil():
    om = {(): (1, 0)}
    for j in range(4):
        nxt = {}
        for w, (re, im) in om.items():
            for let, (dre, dim) in ((2 * j, (1, 0)), (2 * j + 1, (0, 1))):
                nre, nim = re * dre - im * dim, re * dim + im * dre
                nw = tuple(sorted(w + (let,)))
                pr, pi = nxt.get(nw, (0, 0))
                nxt[nw] = (pr + nre, pi + nim)
        om = nxt
    WR = {w: Fr(re) for w, (re, im) in om.items() if im == 0}
    WI = {w: Fr(im) for w, (re, im) in om.items() if re == 0}
    return WR, WI

W_R, W_I = gauss_weil()
THETA = addc(*[{(2 * j, 2 * j + 1): Fr(1)} for j in range(4)])

# ---------------------------------------------------------------------
# the four-rotation family (the committed G_LETTER convention on every
# factor j: e_j |-> -f_j, f_j |-> e_j, the other letters fixed)
# ---------------------------------------------------------------------
def letter_map_for_factor(j):
    m = {}
    m[2 * j] = (2 * j + 1, -1)      # e_j |-> -f_j
    m[2 * j + 1] = (2 * j, 1)       # f_j |-> e_j
    for L in range(8):
        if L not in (2 * j, 2 * j + 1):
            m[L] = (L, 1)
    return m

def map_with(LM):
    def gmap(cls):
        out = {}
        for w, c in cls.items():
            imgs = [LM[l][0] for l in w]
            sgn = 1
            for l in w:
                sgn *= LM[l][1]
            perm = 0
            for i in range(len(imgs)):
                for jj in range(i + 1, len(imgs)):
                    if imgs[i] > imgs[jj]:
                        perm += 1
            if perm % 2:
                sgn = -sgn
            nw = tuple(sorted(imgs))
            out[nw] = out.get(nw, 0) + c * sgn
        return {w: c for w, c in out.items() if c != 0}
    return gmap

GAMMA = [map_with(letter_map_for_factor(j)) for j in range(4)]

# the product deck: the total rotation (i,i,i,i) -- every factor rotated
PROD_LETTER = {}
for j in range(4):
    PROD_LETTER[2 * j] = (2 * j + 1, -1)
    PROD_LETTER[2 * j + 1] = (2 * j, 1)
PROD = map_with(PROD_LETTER)

# ---------------------------------------------------------------------
# exact integer linear algebra (the committed engine, verbatim)
# ---------------------------------------------------------------------
def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]

def rref(mat):
    A = [[Fr(x) for x in row] for row in mat]
    rows, cols = len(A), len(A[0])
    piv = []
    r = 0
    for c in range(cols):
        pr = None
        for i in range(r, rows):
            if A[i][c] != 0:
                pr = i
                break
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(cols)]
        piv.append(c)
        r += 1
    return A, piv

def kernel_basis(mat):
    if not mat or not mat[0]:
        return []
    R, piv = rref(mat)
    rows, cols = len(R), len(R[0])
    free = [c for c in range(cols) if c not in piv]
    kb = []
    for fc in free:
        v = [Fr(0)] * cols
        v[fc] = Fr(1)
        for r, pc in enumerate(piv):
            v[pc] = -R[r][fc]
        den = 1
        for x in v:
            if x != 0:
                from math import gcd
                den = den * x.denominator // gcd(den, x.denominator)
        vi = [int(x * den) for x in v]
        kb.append(vi)
    return kb

def membership_coords(vec, basis):
    n = len(basis)
    if n == 0:
        return None
    m = len(basis[0])
    aug = []
    for j in range(m):
        aug.append([Fr(basis[i][j]) for i in range(n)] + [Fr(vec[j])])
    R, piv = rref(aug)
    x = [Fr(0)] * n
    for r, pc in enumerate(piv):
        if pc < n:
            x[pc] = R[r][n]
    for r in range(len(R)):
        if all(R[r][c] == 0 for c in range(n)) and R[r][n] != 0:
            return None
    for j in range(m):
        s = sum(x[i] * basis[i][j] for i in range(n))
        if s != vec[j]:
            return None
    return x

def to_coords(cls, basis):
    words = sorted(set().union(*[set(b) for b in basis]) | set(cls)) if basis else sorted(cls)
    space = list(words)
    B = []
    for b in basis:
        v = [0] * len(space)
        for w, c in b.items():
            v[space.index(w)] = int(c)
        B.append(v)
    tgt = [0] * len(space)
    for w, c in cls.items():
        tgt[space.index(w)] = int(c)
    if any(c.denominator != 1 for c in cls.values()):
        return None, B, tgt
    return membership_coords(tgt, B), B, tgt

def cyclic_cohomology(gammaB):
    """C_4 = <gamma> on Z^n: H^2 = ker(gamma-1)/im(N); H^1 = ker(N)/im(gamma-1)."""
    n = len(gammaB)
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    gB = gammaB
    g2 = mat_mul(gB, gB)
    g3 = mat_mul(g2, gB)
    N = [[gB[i][j] + g2[i][j] + g3[i][j] + I[i][j] for j in range(n)]
         for i in range(n)]
    gm1 = [[gB[i][j] - I[i][j] for j in range(n)] for i in range(n)]

    def quotient_torsion(kern, gens):
        if not kern:
            return []
        coords = []
        for colv in gens:
            c = membership_coords(colv, kern)
            if c is None:
                return None
            coords.append([int(x) if x.denominator == 1 else x for x in c])
        if coords:
            R, piv = rref(coords)
            if len(piv) < len(kern):
                raise AssertionError(
                    "rank-deficient generator system: pivot form != torsion")
        # the row-Hermite gcd-echelon (the committed contract: full-rank
        # generator systems with pivot-divisibility chains)
        A = [list(map(int, r)) + [0] * (len(kern) - len(r)) for r in coords]
        rows = len(A)
        piv = []
        Rk = 0
        for C in range(len(kern)):
            if Rk >= rows:
                break
            while True:
                nz = [i for i in range(Rk, rows) if A[i][C] != 0]
                if len(nz) <= 1:
                    break
                nz.sort(key=lambda i: abs(A[i][C]))
                p0 = nz[0]
                moved = False
                for i in nz[1:]:
                    q = A[i][C] // A[p0][C]
                    A[i] = [A[i][k] - q * A[p0][k] for k in range(len(kern))]
                    if A[i][C] != 0:
                        moved = True
                if not moved:
                    break
            nz = [i for i in range(Rk, rows) if A[i][C] != 0]
            if not nz:
                continue
            p = nz[0]
            A[Rk], A[p] = A[p], A[Rk]
            piv.append(abs(A[Rk][C]))
            Rk += 1
        return sorted(x for x in piv if x > 1)

    kern = kernel_basis(gm1)
    Ncols = [[N[i][j] for i in range(n)] for j in range(n)]
    h2 = quotient_torsion(kern, Ncols)
    if h2 is None:
        h2 = ["ANOMALY"]
    kernN = kernel_basis(N)
    d1cols = [[gm1[i][j] for i in range(n)] for j in range(n)]
    h1 = quotient_torsion(kernN, d1cols)
    if h1 is None:
        h1 = ["ANOMALY"]
    return {"H2": (len(kern), h2), "H1": (len(kernN), h1)}

def cyclic_cohomology_mod2(gammaB):
    n = len(gammaB)
    g = [[gammaB[i][j] % 2 for j in range(n)] for i in range(n)]
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    def m2_sub(A, Bm):
        return [[(A[i][j] - Bm[i][j]) % 2 for j in range(n)] for i in range(n)]
    def m2_mul(A, Bm):
        return [[sum(A[i][k] * Bm[k][j] for k in range(n)) % 2 for j in range(n)] for i in range(n)]
    def m2_rank(Mx):
        A = [r[:] for r in Mx]
        r = 0
        for c in range(n):
            pr = None
            for i in range(r, n):
                if A[i][c]:
                    pr = i
                    break
            if pr is None:
                continue
            A[r], A[pr] = A[pr], A[r]
            for i in range(n):
                if i != r and A[i][c]:
                    A[i] = [(A[i][k] ^ A[r][k]) for k in range(n)]
            r += 1
        return r
    g2 = m2_mul(g, g)
    g3 = m2_mul(g2, g)
    N = [[(g[i][j] + g2[i][j] + g3[i][j] + I[i][j]) % 2 for j in range(n)] for i in range(n)]
    gm1 = m2_sub(g, I)
    rk_gm1 = m2_rank(gm1)
    rk_N = m2_rank(N)
    return {"H2_rank": rk_gm1 - rk_N}

# ---------------------------------------------------------------------
# the committed typing machinery (census-repair, verbatim: the
# dz/dzbar expansion with the T1 duplicate filter, the T2 reordering
# sign, and the e/f half-coefficients)
# ---------------------------------------------------------------------
def coord_of(letter):
    return letter // 2

def expand_word(w):
    out = {(frozenset(), frozenset()): (Fr(1), Fr(0))}
    for l in w:
        c = coord_of(l)
        if l % 2 == 0:
            fz, fb = (Fr(1, 2), 0), (Fr(1, 2), 0)
        else:
            fz, fb = (0, Fr(-1, 2)), (0, Fr(1, 2))
        nxt = {}
        for (zs, bs), (re, im) in out.items():
            if c not in zs:
                sgn = -1 if len(bs) % 2 else 1
                key = (frozenset(zs | {c}), bs)
                nre = (re * fz[0] - im * fz[1]) * sgn
                nim = (re * fz[1] + im * fz[0]) * sgn
                pr, pi = nxt.get(key, (Fr(0), Fr(0)))
                nxt[key] = (pr + nre, pi + nim)
            if c not in bs:
                key = (zs, frozenset(bs | {c}))
                nre = re * fb[0] - im * fb[1]
                nim = re * fb[1] + im * fb[0]
                pr, pi = nxt.get(key, (Fr(0), Fr(0)))
                nxt[key] = (pr + nre, pi + nim)
        out = nxt
    return out

def type_multiset(cls):
    out = {}
    for w, c in cls.items():
        for (zs, bs), (re, im) in expand_word(w).items():
            key = (len(zs), len(bs), tuple(sorted(zs)), tuple(sorted(bs)))
            tre, tim = out.get(key, (Fr(0), Fr(0)))
            out[key] = (tre + c * re, tim + c * im)
    return {k: v for k, v in out.items() if v != (Fr(0), Fr(0))}

def type_degrees(cls):
    return sorted((k[0], k[1]) for k in type_multiset(cls))

def pi_p_entries(cls, p):
    """the (p,p)-typed entries of the committed typed decomposition"""
    return {k: v for k, v in type_multiset(cls).items()
            if k[0] == p and k[1] == p}

def gauss_mix(sgn):
    om = {(): (1, 0)}
    for j in range(4):
        s = sgn[j]
        nxt = {}
        for w, (re, im) in om.items():
            for let, (dre, dim) in ((2 * j, (1, 0)), (2 * j + 1, (0, s))):
                nre, nim = re * dre - im * dim, re * dim + im * dre
                nw = tuple(sorted(w + (let,)))
                pr, pi = nxt.get(nw, (0, 0))
                nxt[nw] = (pr + nre, pi + nim)
        om = nxt
    return {w: Fr(re) for w, (re, im) in om.items() if im == 0}

def gauss_mix_im(sgn):
    """the imaginary partner: Im(prod_j (e_j + i s_j f_j)) as a class"""
    om = {(): (1, 0)}
    for j in range(4):
        s = sgn[j]
        nxt = {}
        for w, (re, im) in om.items():
            for let, (dre, dim) in ((2 * j, (1, 0)), (2 * j + 1, (0, s))):
                nre, nim = re * dre - im * dim, re * dim + im * dre
                nw = tuple(sorted(w + (let,)))
                pr, pi = nxt.get(nw, (0, 0))
                nxt[nw] = (pr + nre, pi + nim)
        om = nxt
    return {w: Fr(im) for w, (re, im) in om.items() if re == 0}

# =====================================================================
# LA-A: THE EIGHT TYPED-PURE PLANES -- the complete all-odd partition
# =====================================================================
print("== LA-A: THE EIGHT-PLANE PARTITION of the all-odd sector ==")
# the eight blocks A ~ A^c of the subsets of the four factors; the sign
# pattern s_j = +1 iff j in A (the holomorphic factors); the plane is
# span(Re X_s, Im X_s), X_s = prod_{j in A} dz_j * prod_{j not in A} dbar_j
BLOCKS = [
    ("W",   (1, 1, 1, 1)),       # A = {} ~ A = full : (4,0)+(0,4)
    ("M0",  (1, -1, -1, -1)),    # A = {0}           : (1,3)+(3,1)
    ("M1",  (-1, 1, -1, -1)),    # A = {1}           : (1,3)+(3,1)
    ("M2",  (-1, -1, 1, -1)),    # A = {2}           : (1,3)+(3,1)
    ("M3",  (-1, -1, -1, 1)),    # A = {3}           : (1,3)+(3,1)
    ("P01", (1, 1, -1, -1)),     # A = {0,1}         : (2,2)
    ("P02", (1, -1, 1, -1)),     # A = {0,2}         : (2,2)
    ("P03", (1, -1, -1, 1)),     # A = {0,3}         : (2,2)
]

PLANES = {}
for name, s in BLOCKS:
    b0 = gauss_mix(s)
    b1 = gauss_mix_im(s)
    ok(b0 != ZERO and b1 != ZERO,
       f"plane {name}: the Re/Im basis classes are nonzero (the block {(s[0]>0, s[1]>0, s[2]>0, s[3]>0)})")
    PLANES[name] = {"s": s, "b0": b0, "b1": b1}

# the anchors: the W-plane is the committed Weil plane
ok(PLANES["W"]["b0"] == W_R and PLANES["W"]["b1"] == W_I,
   "the W-block plane is EXACTLY the committed Weil plane (Re/Im of the holomorphic form)")

# the typed purity of every plane
EXPECT_TYPE = {"W": [(0, 4), (4, 0)], "M0": [(1, 3), (3, 1)],
               "M1": [(1, 3), (3, 1)], "M2": [(1, 3), (3, 1)],
               "M3": [(1, 3), (3, 1)], "P01": [(2, 2), (2, 2)],
               "P02": [(2, 2), (2, 2)], "P03": [(2, 2), (2, 2)]}
for name in PLANES:
    p = PLANES[name]
    ok(type_degrees(p["b0"]) == EXPECT_TYPE[name],
       f"plane {name}: the Re-class is typed-pure {EXPECT_TYPE[name]} (the committed machinery)")
    ok(type_degrees(p["b1"]) == EXPECT_TYPE[name],
       f"plane {name}: the Im-class is typed-pure {EXPECT_TYPE[name]}")

# the deck stability: every single-factor rotation acts on every plane
# (the 2x2 integer matrix per (plane, factor); each squares to -I)
print("  -- the 32 deck matrices (8 planes x 4 factors) --")
fam_ok = True
fam_squares = []
for name, p in PLANES.items():
    basis = [p["b0"], p["b1"]]
    for j in range(4):
        cA = to_coords(GAMMA[j](p["b0"]), basis)[0]
        cB = to_coords(GAMMA[j](p["b1"]), basis)[0]
        if cA is None or cB is None:
            fam_ok = False
            continue
        GM = [[int(cA[0]), int(cB[0])], [int(cA[1]), int(cB[1])]]
        GM2 = mat_mul(GM, GM)
        fam_squares.append(GM2)
        if GM2 != [[-1, 0], [0, -1]]:
            fam_ok = False
ok(fam_ok and len(fam_squares) == 32,
   "LA1: every one of the 32 (plane, factor) deck matrices squares to -I "
   "(gamma_j^2 = -1 on every all-odd plane: the whole all-odd sector is "
   "gamma^2 = -1)")

# the product deck (the total rotation): the character table
print("  -- the product deck's character table --")
char_ok = True
CHAR = {}
for name, p in PLANES.items():
    basis = [p["b0"], p["b1"]]
    cA = to_coords(PROD(p["b0"]), basis)[0]
    cB = to_coords(PROD(p["b1"]), basis)[0]
    if cA is None or cB is None:
        char_ok = False
        continue
    PM = [[int(cA[0]), int(cB[0])], [int(cA[1]), int(cB[1])]]
    CHAR[name] = PM
    expected = [[1, 0], [0, 1]] if EXPECT_TYPE[name] != [(1, 3), (3, 1)] else [[-1, 0], [0, -1]]
    if PM != expected:
        char_ok = False
ok(char_ok,
   "LA2 CHARACTER TABLE: the product deck acts by +I on the W-plane and the "
   "three (2,2) planes and by -I on the four (3,1)+(1,3) planes (the scalar "
   "i^{p-q}, matrix-exact)")

# THE CHARACTER-COLLISION RECEIPT: the character does NOT separate (2,2)
# from (4,0)+(0,4); the grade does
ok(CHAR["W"] == CHAR["P01"] == CHAR["P02"] == CHAR["P03"] == [[1, 0], [0, 1]],
   "LA2 THE COLLISION: the (2,2) planes and the Weil plane carry the SAME "
   "product-deck character (+I) -- the deck character cannot gate between "
   "them (the character is the value (p-q) mod 4)")
ok(CHAR["M0"] == [[-1, 0], [0, -1]],
   "LA2: the (3,1)+(1,3) plane carries character -I (i^2): the character "
   "separates the mixed-type planes but NOT the collision pair")

# THE GATE: pi_2 on every plane (nonzero exactly on the three (2,2) planes)
print("  -- THE GRADE GATE: the pi_2 projection on every plane --")
# THE FILTER'S (p,p)-SPECIFICITY (the 24-b audit's N7 repair: the mutation
# "k[0]==p only" passed the prior battery -- this check catches it through
# the real path: the (3,1)+(1,3) plane carries (1,3)- and (3,1)-typed keys
# with k[0] in {1,3}; the correct (p,p)-filter returns EMPTY at both p = 1
# and p = 3; a p-only filter would return the (1,3)/(3,1) entries)
ok(pi_p_entries(PLANES["M0"]["b0"], 1) == {} and
   pi_p_entries(PLANES["M0"]["b0"], 3) == {},
   "LA2 GATE FILTER: pi_1 and pi_3 on the (3,1)+(1,3) class return EMPTY "
   "(the projection is (p,p)-specific, not p-specific: the (1,3)/(3,1) "
   "entries are NOT gated at p = 1 or p = 3 -- computed through the real "
   "path; the audit's p-only mutation is caught by this check)")
for name, p in PLANES.items():
    nz2 = (pi_p_entries(p["b0"], 2) != {}) or (pi_p_entries(p["b1"], 2) != {})
    expect_nz = name in ("P01", "P02", "P03")
    ok(nz2 == expect_nz,
       f"LA2 GATE: pi_2(plane {name}) {'NONZERO' if expect_nz else 'ZERO'} "
       f"(computed): the grade-2 content exists exactly on the (2,2) planes")

# =====================================================================
# LA-B: THE REDUCTION LAWS (the two-cell, the transport, the norm, the
# parity)
# =====================================================================
print("\n== LA-B: THE REDUCTION LAWS (the link's mechanics, computed) ==")

# (B0) the symplectic law: gamma_j in Sp(8,Z)
def theta_form(v, w):
    return sum(v[2 * j] * w[2 * j + 1] - v[2 * j + 1] * w[2 * j] for j in range(4))

def letter_matrix(j):
    LM = letter_map_for_factor(j)
    M = [[0] * 8 for _ in range(8)]
    for k in range(8):
        tgt, sgn = LM[k]
        M[tgt][k] = sgn
    return M

def transpose(M):
    return [[M[i][j] for i in range(len(M))] for j in range(len(M[0]))]

TH8 = [[0] * 8 for _ in range(8)]
for j in range(4):
    TH8[2 * j][2 * j + 1] = 1
    TH8[2 * j + 1][2 * j] = -1

sympl_ok = True
for j in range(4):
    G = letter_matrix(j)
    if mat_mul(mat_mul(transpose(G), TH8), G) != TH8:
        sympl_ok = False
ok(sympl_ok,
   "LA1 SYMPLECTIC: gamma_j^T * Theta * gamma_j = Theta for all four factors "
   "(every rotation preserves the curvature form: the 8x8 matrices, exact)")

# (B1) the theta/TH8 cross-verification runs after the arrow instances
# are defined (see the cross-check block below)

# (B2) the two-cell: c_{m,alpha}(v,w) = theta(v,w) * iota(m*alpha)
def iota_pair(cls):
    return (cls, sc(cls, -1))

def pair_add(P, Q):
    return (addc(P[0], Q[0]), addc(P[1], Q[1]))

def two_cell(m, alpha, v, w):
    t = theta_form(v, w) * m
    return (sc(alpha, t), sc(alpha, -t))

def apply_pair_gmap(P, j):
    return (GAMMA[j](P[0]), GAMMA[j](P[1]))

def mat_vec(M, v):
    return [sum(M[i][k] * v[k] for k in range(len(v))) for i in range(len(M))]

# bounded fixed instances (deterministic; no randomness)
ARROWS = [
    [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1],
    [1, 2, 0, 0, -1, 1, 0, 0], [0, 0, 1, -2, 3, 0, 1, 1],
    [2, 1, 1, 1, 1, 1, 1, 1], [-1, 0, 2, 1, 0, 0, 1, 0],
]
PAIRS = [(ARROWS[0], ARROWS[1]), (ARROWS[2], ARROWS[3]),
         (ARROWS[0], ARROWS[9]), (ARROWS[8], ARROWS[9]),
         (ARROWS[10], ARROWS[0]), (ARROWS[11], ARROWS[4])]
TRIPLES = [(ARROWS[0], ARROWS[1], ARROWS[2]),
           (ARROWS[8], ARROWS[9], ARROWS[10]),
           (ARROWS[0], ARROWS[3], ARROWS[11])]

# (B1) the theta/TH8 cross-verification (the 24-b audit's N4 repair: the
# alternating form and the matrix are two encodings of the curvature --
# the cross-check is a real comparison, able to fail under either
# corruption)
th_cross = True
for (v, w) in PAIRS:
    mv = sum(v[i] * sum(TH8[i][k] * w[k] for k in range(8)) for i in range(8))
    if theta_form(v, w) != mv:
        th_cross = False
ok(th_cross,
   "LA1 CROSS-CHECK: the alternating form theta and the matrix Theta8 agree "
   "on every fixed arrow instance (the two encodings of the curvature "
   "verified against each other, computed)")

def sc_pair(P, s):
    return (sc(P[0], s), sc(P[1], s))

# (B3) the bar-cocycle law on the abelian arrow lattice (trivial
# coefficient action): the alternating two-cell is a 2-cocycle
bar_ok = True
for (a, b, c) in TRIPLES:
    # inhomogeneous differential: dc(a,b,c) = c(b,c) - c(a+b,c) + c(a,b+c) - c(a,b)
    t1 = two_cell(1, W_R, b, c)
    ab = [x + y for x, y in zip(a, b)]
    t2 = two_cell(1, W_R, ab, c)
    bc = [x + y for x, y in zip(b, c)]
    t3 = two_cell(1, W_R, a, bc)
    t4 = two_cell(1, W_R, a, b)
    total = pair_add(pair_add(t1, sc_pair(t2, -1)), pair_add(t3, sc_pair(t4, -1)))
    if total != (ZERO, ZERO):
        bar_ok = False
ok(bar_ok,
   "LA1 BAR LAW (a formality receipt, on the face): the alternating "
   "two-cell satisfies the inhomogeneous bar identity on the abelian arrow "
   "lattice -- every alternating cochain passes this law (the receipt "
   "records the complex's law; the load-bearing layers are the transport "
   "and the parity below)")

# (B4) the transport identity: gamma.c_{m,alpha} = c_{m, gamma.alpha}
trans_ok = True
for name in ("P01", "P02", "P03", "W"):
    p = PLANES[name]
    alpha = p["b0"]
    galpha = GAMMA[0](alpha)
    for (v, w) in PAIRS:
        G = letter_matrix(0)
        Ginv = mat_mul(mat_mul(G, G), G)   # gamma^{-1} = gamma^3 (gamma^4 = id)
        vi = mat_vec(Ginv, v)
        wi = mat_vec(Ginv, w)
        lhs = apply_pair_gmap(two_cell(1, alpha, vi, wi), 0)
        rhs = two_cell(1, galpha, v, w)
        if lhs != rhs:
            trans_ok = False
ok(trans_ok,
   "LA1 TRANSPORT: gamma.c_{m,alpha}(v,w) = c_{m,gamma.alpha}(v,w) on the "
   "(2,2) planes and the Weil plane (the symplectic pullback + the iota "
   "intertwining, computed on the fixed arrow instances)")

# (B5) the intertwining receipt (the pair level, verbatim re-verification)
itw = True
for name in ("P01", "P02", "P03", "W"):
    p = PLANES[name]
    for b in (p["b0"], p["b1"]):
        x0, x1 = iota_pair(b)
        lhs = iota_pair(GAMMA[0](b))
        rhs = (GAMMA[0](x0), GAMMA[0](x1))
        if lhs != rhs:
            itw = False
ok(itw,
   "LA1 INTERTWINING: (gamma x gamma) o iota = iota o gamma on every plane "
   "basis (the pair module's deck is the content deck: the reduction is "
   "defined at the pair level, matrix-exact)")

# (B6) the norm law: N(c) = theta * iota(m * N_gamma alpha) = 0
norm_ok = True
for name in PLANES:
    p = PLANES[name]
    for b in (p["b0"], p["b1"]):
        Nb = addc(b, GAMMA[0](b), GAMMA[0](GAMMA[0](b)),
                  GAMMA[0](GAMMA[0](GAMMA[0](b))))
        if Nb != ZERO:
            norm_ok = False
ok(norm_ok,
   "LA1 NORM (class level): N_gamma = 1+g+g^2+g^3 = 0 on every plane basis "
   "(the R1 degeneration, word-exact)")
norm_cell_ok = True
for name in ("P01", "W"):
    p = PLANES[name]
    alpha = p["b0"]
    for (v, w) in PAIRS[:3]:
        G = letter_matrix(0)
        Ginv = mat_mul(mat_mul(G, G), G)      # gamma^{-1} = gamma^3
        acc = (ZERO, ZERO)
        T = [[int(i == j) for j in range(8)] for i in range(8)]   # gamma^{-k}
        for k in range(4):
            vk = mat_vec(T, v)
            wk = mat_vec(T, w)
            val = two_cell(1, alpha, vk, wk)   # c(gamma^{-k} v, gamma^{-k} w)
            # apply (gamma x gamma)^k to the pair value
            for _ in range(k):
                val = apply_pair_gmap(val, 0)
            acc = pair_add(acc, val)
            T = mat_mul(T, Ginv)
        if acc != (ZERO, ZERO):
            norm_cell_ok = False
ok(norm_cell_ok,
   "LA1 NORM (two-cell level, the computed instances): the deck orbit sum "
   "of the two-cell is ZERO on the P01 plane and the Weil plane instances "
   "(N(c) = theta*iota(N_gamma alpha) = 0, cochain-exact). BOUNDARY ON THE "
   "FACE: the norm law is (1+gamma)(1+gamma^2) = 0 -- it holds for EVERY "
   "iota-shaped content and does NOT by itself distinguish the (A,-A) "
   "witness from the (A,+A) shape; the iota-specificity is the STRIP's own "
   "traceless condition (the trace check below); the pair-level residue "
   "is reached only through the two-cell reduction (the 21-c item (ii)), "
   "not claimed discharged here")

# (B6b) THE STRIP'S TRACE RECEIPT (the 24-b audit's M3 repair: the
# iota-shape is the strip's own output -- the traceless pair condition,
# computed; the (x,+x) shape FAILS it)
def pair_trace(P):
    # the committed pair-trace functional tr(x,y) = x + y at the class level
    return addc(P[0], P[1])
ok(pair_trace(iota_pair(W_R)) == ZERO,
   "LA1 STRIP RECEIPT: the iota-shape (x,-x) is TRACELESS (the pair-trace "
   "functional vanishes: the strip's own output condition, computed)")
ok(pair_trace((W_R, W_R)) != ZERO,
   "LA1 STRIP CONTROL: the (x,+x) shape is NOT traceless (its pair trace is "
   "2x != 0: the strip excludes it -- the iota-specificity is the strip's, "
   "not the norm law's; the 24-b audit's mutation MU7 boundary on the face)")

# (B7) the defect law: gamma.c - c = theta * iota(m (gamma - 1) alpha)
# (the 24-b audit's N6 repair: the instances run at m = 1, 2, 3)
defect_ok = True
for name in ("P01", "W"):
    p = PLANES[name]
    alpha = p["b0"]
    gap = addc(GAMMA[0](alpha), sc(alpha, -1))
    for m_def in (1, 2, 3):
        for (v, w) in PAIRS[:4]:
            G = letter_matrix(0)
            Ginv = mat_mul(mat_mul(G, G), G)
            vi = mat_vec(Ginv, v)
            wi = mat_vec(Ginv, w)
            lhs = pair_add(apply_pair_gmap(two_cell(m_def, alpha, vi, wi), 0),
                           sc_pair(two_cell(m_def, alpha, v, w), -1))
            rhs = iota_pair(sc(gap, m_def * theta_form(v, w)))
            if lhs != rhs:
                defect_ok = False
ok(defect_ok,
   "LA1 DEFECT: gamma.c - c = theta * iota(m (gamma-1) alpha), computed on "
   "the fixed instances at m = 1, 2, 3 (the transport defect is iota-shaped: "
   "the reduction's input datum)")

# (B8) the parity law: the PRIMITIVE content's least kill-scale (the
# 24-b audit's M1 repair: the iff-law is stated for contents with a
# NONZERO H^1-class; degenerate contents (already in im(gamma-1)) die at
# every scale -- the boundary receipt is computed below (B8b))
print("  -- the parity law (the primitive content's least kill-scale) --")
def plane_entry(b0, b1, m):
    col0 = addc(GAMMA[0](b0), sc(b0, -1))
    col1 = addc(GAMMA[0](b1), sc(b1, -1))
    res = to_coords(sc(b0, m), [col0, col1])
    if res[0] is None:
        return False
    return all(x.denominator == 1 for x in res[0])

for name in ("P01", "P02", "P03", "W"):
    p = PLANES[name]
    res = [plane_entry(p["b0"], p["b1"], m) for m in range(1, 13)]
    ok(res == [False, True] * 6,
       f"LA1 PARITY: the primitive generator's class of m*alpha in "
       f"H^1(C_4; {name}) (its H^1-class is nonzero at m = 1) dies at the "
       f"even scales and at no odd scale, m = 1..12 (the parity bit; the "
       f"primitive hypothesis is verified by the m = 1 refusal)")
    ok(res.index(True) == 1,
       f"LA1 PIN: the least kill-scale on {name} is m = 2 (the least scale "
       f"carrying the primitive content into im(gamma-1))")

# (B8a) the W_I parity (the 24-b audit's N6 repair: the imaginary ray's
# own receipt, computed in this certificate)
resI = [plane_entry(W_I, W_R, m) for m in range(1, 13)]
ok(resI == [False, True] * 6 and resI.index(True) == 1,
   "LA1 PARITY (the imaginary ray): the W_I content carries the same law "
   "(nonzero H^1-class at m = 1; least kill-scale 2: both Weil rays, "
   "computed in this certificate)")

# (B9) the doubled pair module M (+) M: H^2 = 0 (the killing), H^1 =
# (Z/2)^2 (the 24-b audit's M2 repair: this is the DOUBLED module's
# group; the iota-submodule itself carries H^1 = Z/2 -- the explicit
# receipt is the plane engine's H^1 below), computed on the doubled
# deck matrix
for name in ("P01", "P02", "P03"):
    p = PLANES[name]
    basis = [p["b0"], p["b1"]]
    cA = to_coords(GAMMA[0](p["b0"]), basis)[0]
    cB = to_coords(GAMMA[0](p["b1"]), basis)[0]
    GM = [[int(cA[0]), int(cB[0])], [int(cA[1]), int(cB[1])]]
    DBL = [[GM[i][j] if i < 2 and j < 2 else (GM[i-2][j-2] if i >= 2 and j >= 2 else 0)
            for j in range(4)] for i in range(4)]
    coh = cyclic_cohomology(DBL)
    ok(coh["H2"][0] == 0 and coh["H2"][1] == [],
       f"LA1 KILLING: H^2(C_4; the doubled pair module of {name}) = 0 "
       f"(gamma^2 = -1 on both slots kills the pair-level obstruction; no "
       f"symmetrization)")
    ok(sorted(coh["H1"][1]) == [2, 2],
       f"LA1 PARITY (the doubled module M (+) M): H^1(C_4; M (+) M) = "
       f"(Z/2)^2 -- the witness-shaped residue carries the parity bit on "
       f"both slots; the iota-SUBMODULE itself (isomorphic to M) carries "
       f"H^1 = Z/2, the plane engine's receipt below")
    coh_plane = cyclic_cohomology(GM)
    ok(sorted(coh_plane["H1"][1]) == [2] and coh_plane["H2"][1] == [],
       f"LA1 PARITY (the iota-submodule): H^1(C_4; iota({name})) = Z/2 and "
       f"H^2 = 0 (the submodule is C_4-isomorphic to the content plane: "
       f"the audit's M2 relabel, computed)")

# the iota-module entry test (the parity on the pair module itself)
p01 = PLANES["P01"]
icol0 = (addc(GAMMA[0](p01["b0"]), sc(p01["b0"], -1)),
         sc(addc(GAMMA[0](p01["b0"]), sc(p01["b0"], -1)), -1))
icol1 = (addc(GAMMA[0](p01["b1"]), sc(p01["b1"], -1)),
         sc(addc(GAMMA[0](p01["b1"]), sc(p01["b1"], -1)), -1))
def iota_entry(m):
    tgt = (sc(p01["b0"], m), sc(p01["b0"], -m))
    words = sorted(set(tgt[0]) | set(icol0[0]) | set(icol1[0]))
    B = []
    for pr in (icol0, icol1):
        v = [0] * len(words)
        for w, c in pr[0].items():
            v[words.index(w)] = int(c)
        B.append(v)
    tvec = [0] * len(words)
    for w, c in tgt[0].items():
        tvec[words.index(w)] = int(c)
    # the second slot is the negative of the first (the iota shape): the
    # membership in the doubled module reduces to the first slot
    co = membership_coords(tvec, B)
    if co is None:
        return False
    return all(x.denominator == 1 for x in co)
ok([iota_entry(m) for m in range(1, 13)] == [False, True] * 6,
   "LA1 PARITY (iota module): the primitive generator's iota(m*alpha) "
   "dies in H^1(C_4; iota(M)) at the even scales and at no odd scale "
   "(the pair-level residue = the content parity, computed on the doubled "
   "generators; the primitive hypothesis as above)")

# =====================================================================
# LA-C: HOSTILE CONTROLS
# =====================================================================
print("\n== LA-C: THE HOSTILE CONTROLS ==")

# (C1) the broken symplectic: a non-unit letter map breaks the transport
BAD_LETTER = dict(letter_map_for_factor(0))
BAD_LETTER[0] = (1, -2)          # e_0 |-> -2 f_0 (non-unit)
badmap = map_with(BAD_LETTER)
def bad_letter_matrix():
    M = [[0] * 8 for _ in range(8)]
    for k in range(8):
        tgt, sgn = BAD_LETTER[k]
        M[tgt][k] = sgn
    return M
BG = bad_letter_matrix()
ok(mat_mul(mat_mul(transpose(BG), TH8), BG) != TH8,
   "HOSTILE (broken symplectic): the non-unit letter map does NOT preserve "
   "theta (gamma^T Theta gamma != Theta, computed)")
bad_transport = True
v, w = PAIRS[0]
Binv_attempt = mat_mul(mat_mul(BG, BG), BG)
# the transport with the broken map: apply the same construction
lhs_bad = (badmap(two_cell(1, W_R, mat_vec(Binv_attempt, v),
                           mat_vec(Binv_attempt, w))[0]),
           badmap(two_cell(1, W_R, mat_vec(Binv_attempt, v),
                           mat_vec(Binv_attempt, w))[1]))
rhs_good = two_cell(1, badmap(W_R), v, w)
ok(lhs_bad != rhs_good,
   "HOSTILE (broken symplectic): the transport identity FAILS for the "
   "non-unit map (the symplectic law is load-bearing: computed)")

# (C2) the 2-torsion degeneration: the parity residue dies mod 2
cA = to_coords(GAMMA[0](p01["b0"]), [p01["b0"], p01["b1"]])[0]
cB = to_coords(GAMMA[0](p01["b1"]), [p01["b0"], p01["b1"]])[0]
GM01 = [[int(cA[0]), int(cB[0])], [int(cA[1]), int(cB[1])]]
coh2t = cyclic_cohomology_mod2(GM01)
ok(coh2t["H2_rank"] == 1,
   "HOSTILE (2-torsion): on the (Z/2)-plane the deck degenerates (H^2-rank "
   "1 != 0): the killing fails exactly on 2-torsion (the parity law's "
   "torsion boundary, computed)")

# (C3) the all-even contrast: the pair-product module's DIFFERENT law
G_EVEN = [[int(i == j) for j in range(6)] for i in range(6)]
coh_even = cyclic_cohomology(G_EVEN)
ok(coh_even["H1"][0] == 0 and coh_even["H1"][1] == [],
   "HOSTILE (all-even): the pair-product module has H^1 = 0 (the parity bit "
   "does NOT fire on the deck-fixed sector)")
ok(sorted(coh_even["H2"][1]) == [4, 4, 4, 4, 4, 4],
   "HOSTILE (all-even): H^2(C_4; the pair-product lattice) = (Z/4)^6 (the "
   "deck-fixed sector carries the 4-torsion law, NOT the parity law)")
PAIRWORDS = [tuple(sorted((2 * a, 2 * a + 1, 2 * b, 2 * b + 1)))
             for (a, b) in combinations(range(4), 2)]
PAIR01 = {PAIRWORDS[0]: Fr(1)}     # F_0 F_1, the primitive pair word
def even_scale4(m):
    basis = [{w: Fr(1)} for w in PAIRWORDS]
    fourM = [sc(b, 4) for b in basis]
    res = to_coords(sc(PAIR01, m), fourM)
    if res[0] is None:
        return False
    return all(x.denominator == 1 for x in res[0])
ok(all(even_scale4(m) == (m % 4 == 0) for m in range(1, 13)),
   "HOSTILE (all-even): the pair content dies at scale 4 only (m F_0F_1 in "
   "4M iff 4|m): the even sector's scale law is the 4-law, the odd sector's "
   "is the 2-law (the two laws certified as distinct)")

# (C4) the mixed-grade control: a (2,2)+(4,0) content
MIX22 = PLANES["P01"]["b0"]
MIXED = addc(MIX22, W_R)
ok(pi_p_entries(MIXED, 2) == pi_p_entries(MIX22, 2),
   "HOSTILE (mixed grade): the mixed content's (2,2)-typed components are "
   "EXACTLY the pure (2,2) plane's (the grade projection is additive: the "
   "link carries exactly the gated part, computed)")
ok(pi_p_entries(W_R, 2) == {},
   "HOSTILE (mixed grade): pi_2(W_R) = 0 (the Weil part has no grade-2 "
   "content: the conduit's purity hypothesis excludes it -- a stated "
   "hypothesis of the two-center descent law, recorded on the face, not a "
   "computed conduit rejection)")

# (C4b) THE PROJECTION-EQUIVARIANCE INSTANCE (the 24-b audit's N8
# repair: pi_2 o gamma = gamma o pi_2 on the (2,2)-graded piece, computed
# at the typed-entry level on the mixed content: the deck preserves the
# (2,2)-grade, so the projection of the transported content equals the
# transport's (2,2)-part)
tm_g = type_multiset(GAMMA[0](MIXED))
p22_of = lambda tm: {k: v for k, v in tm.items() if k[0] == 2 and k[1] == 2}
ok(p22_of(tm_g) == p22_of(type_multiset(GAMMA[0](MIX22))),
   "LA2 EQUIVARIANCE INSTANCE: the (2,2)-typed entries of the transported "
   "mixed content are EXACTLY the (2,2)-typed entries of the transported "
   "gated part (pi_2(gamma x) = the (2,2)-part of gamma x: the deck "
   "preserves the (2,2)-grade, computed at the typed-entry level)")

# (C5) the (3,1) gate: no grade-2 content, no identification
ok(all(pi_p_entries(PLANES[nm]["b0"], 2) == {} for nm in ("M0", "M1", "M2", "M3")),
   "HOSTILE (the gate): the four (3,1)+(1,3) planes have ZERO grade-2 "
   "content: the link's target module does not exist there (no "
   "identification: the link does not carry their two-cell -- the DOMAIN "
   "condition, not an equivariance condition)")
# the module-level law on the (3,1) plane is the SAME parity law (the
# boundary's own receipt: the module law is input-blind; the gate is the
# grade, not the module) -- THE POSITIVE NON-KILLING DATUM: the gated
# content's own H^1-class is NONZERO at m = 1: the obstruction data
# lives on its module and the link refuses to carry it (no descent, no
# conduit)
m0 = PLANES["M0"]
res31 = [plane_entry(m0["b0"], m0["b1"], m) for m in range(1, 13)]
ok(res31 == [False, True] * 6,
   "BOUNDARY RECEIPT (the positive non-killing datum): the (3,1) plane's "
   "own module carries the SAME even-scale parity law and its generator's "
   "H^1-class is NONZERO at m = 1 (the obstruction data lives; the link's "
   "domain condition excludes it: the module law is input-blind -- the "
   "certified boundary; the grade discriminates)")

# =====================================================================
# =====================================================================
# LA-D: THE PARTITION (the typed-pure lattices, computed exactly)
# =====================================================================
print("\n== LA-D: THE PARTITION (the typed-pure lattices) ==")
ALLODD_WORDS = [tuple(c) for c in combinations(range(8), 4)
                if all(sum(1 for l in c if l // 2 == j) == 1 for j in range(4))]
ok(len(ALLODD_WORDS) == 16,
   "the all-odd words are exactly the 16 one-letter-per-factor words "
   "(the complete list, computed)")

def typed_pure_sublattice(allowed):
    """the integral all-odd classes whose typed decomposition lies entirely
    in the allowed (p,q) types: the integer kernel of the typed-component
    system (the committed expansion, exact half-integer coefficients)"""
    keys = set()
    for w in ALLODD_WORDS:
        keys.update(expand_word(w).keys())
    rows = []
    for K in keys:
        if (len(K[0]), len(K[1])) in allowed:
            continue
        for part in (0, 1):
            rows.append([expand_word(w).get(K, (Fr(0), Fr(0)))[part]
                         for w in ALLODD_WORDS])
    return kernel_basis(rows)

S22 = typed_pure_sublattice({(2, 2)})
S40 = typed_pure_sublattice({(4, 0), (0, 4)})
S31 = typed_pure_sublattice({(3, 1), (1, 3)})
ok(len(S22) == 6 and len(S40) == 2 and len(S31) == 8,
   "LA3 THE TYPED-PURE LATTICES: S22 (the (2,2)-pure all-odd classes) has "
   "rank 6, S40 (the (4,0)+(0,4)-pure) rank 2, S31 (the (3,1)+(1,3)-pure) "
   "rank 8 (computed: the type-system kernels; 6+2+8 = 16 = the sector)")

def s_class(vec):
    cls = {}
    for i, c in enumerate(vec):
        if c:
            cls[ALLODD_WORDS[i]] = Fr(c)
    return cls

# the purity control on the S22 basis (the kernel construction verified
# against the committed typing machinery directly)
s22_pure = True
for s in S22:
    degs = type_degrees(s_class(s))
    if degs == [] or any(d != (2, 2) for d in degs):
        s22_pure = False
ok(s22_pure,
   "LA3 CONTROL: every S22 basis class is typed-pure: its committed typed "
   "multiset carries ONLY (2,2) components, nonzero (the kernel verified "
   "against the machinery, not assumed)")

# (D1) the rational typed partition: every all-odd word is a rational sum
# of typed-pure classes (L16 (x) Q = S22 (x) Q + S40 (x) Q + S31 (x) Q)
# (the 24-b audit's B2 repair: the count 6+2+8 = 16 was already asserted
# above; no duplicate count check here)
SUM16 = S22 + S40 + S31
qpart = True
for w in ALLODD_WORDS:
    tv = [0] * len(ALLODD_WORDS)
    tv[ALLODD_WORDS.index(w)] = 1
    if membership_coords(tv, SUM16) is None:
        qpart = False
ok(qpart,
   "LA3 RATIONAL PARTITION: every all-odd word lies in the Q-span of the "
   "typed-pure classes (the typed decomposition IS the partition: "
   "L16 (x) Q = S22 (x) Q (+) S40 (x) Q (+) S31 (x) Q)")

# (D2) the W-plane IS S40 (the committed primitive-ray receipt, upgraded)
Wv = []
for b in (W_R, W_I):
    v = [0] * len(ALLODD_WORDS)
    for w, c in b.items():
        v[ALLODD_WORDS.index(w)] = int(c)
    Wv.append(v)
w_in = all(membership_coords(v, S40) is not None and
           all(x.denominator == 1 for x in membership_coords(v, S40)) for v in Wv)

def det_frac(M):
    A = [[Fr(x) for x in r] for r in M]
    n = len(A)
    det = Fr(1)
    for c in range(n):
        pr = None
        for i in range(c, n):
            if A[i][c] != 0:
                pr = i
                break
        if pr is None:
            return Fr(0)
        if pr != c:
            A[c], A[pr] = A[pr], A[c]
            det = -det
        det *= A[c][c]
        pv = A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / pv
            A[i] = [A[i][j] - f * A[c][j] for j in range(n)]
    return det

def lattice_index(plane_vecs, lattice):
    """the index [lattice : span_Z(plane_vecs)] via the coordinate
    determinant. GUARD (the 24-b audit's N10 repair): every plane vector
    must lie INTEGRALLY in the lattice (the sublattice containment); a
    fractional containment RAISES (the silent inversion of the prior
    version is removed -- the 23-b F4 class of silent-contract engines)."""
    T = []
    for v in plane_vecs:
        co = membership_coords(v, lattice)
        if co is None:
            return None
        if any(x.denominator != 1 for x in co):
            raise AssertionError(
                "lattice_index: plane vector not integrally contained")
        T.append([co[i] for i in range(len(lattice))])
    Tm = [[T[j][i] for j in range(len(T))] for i in range(len(lattice))]
    d = det_frac(Tm)
    if d == 0:
        return None
    if abs(d) < 1:
        raise AssertionError(
            "lattice_index: |det| < 1 contradicts integral containment")
    return abs(d)

ok(w_in and lattice_index(Wv, S40) == 1,
   "LA3 THE W-PLANE IS S40 EXACTLY: the committed Weil classes W_R, W_I "
   "generate the FULL (4,0)+(0,4)-pure all-odd lattice (index 1: the "
   "primitive-ray receipt carried to the typed-pure lattice)")

# (D3) the plane spans' positions (the exact indices, recorded)
Pv = []
for nm in ("P01", "P02", "P03"):
    for b in (PLANES[nm]["b0"], PLANES[nm]["b1"]):
        v = [0] * len(ALLODD_WORDS)
        for w, c in b.items():
            v[ALLODD_WORDS.index(w)] = int(c)
        Pv.append(v)
Mv = []
for nm in ("M0", "M1", "M2", "M3"):
    for b in (PLANES[nm]["b0"], PLANES[nm]["b1"]):
        v = [0] * len(ALLODD_WORDS)
        for w, c in b.items():
            v[ALLODD_WORDS.index(w)] = int(c)
        Mv.append(v)
idx22 = lattice_index(Pv, S22)
idx31 = lattice_index(Mv, S31)
ok(idx22 == 16,
   "LA3: the three (2,2) planes generate an INDEX-16 sublattice of S22 "
   "(the typed-pure lattice is a 16-fold refinement of the plane span: "
   "the sector's law must be -- and below is -- certified on S22 itself)")
ok(idx31 == 256,
   "LA3: the four (3,1)+(1,3) planes generate an index-256 sublattice of "
   "S31 (recorded)")

# (D4) the word lattice vs the typed-pure sum (the recorded position).
# (the 24-b audit's B2 repair: the words' Q-membership is the qpart loop
# above; only the INDEX is computed here -- no duplicate membership check)
Tt = []
for i in range(16):
    co = membership_coords([1 if j == i else 0 for j in range(16)], SUM16)
    if co is None:
        Tt = None
        break
    Tt.append(co)
if Tt is not None:
    Tm = [[Tt[j][i] for j in range(16)] for i in range(16)]
    d16 = det_frac(Tm)
    ok(d16 == Fr(1, 4096),
       "LA3: [L16 : S22 (+) S40 (+) S31] = 4096 (the typed-pure sum is a "
       "finite-index sublattice of the word lattice; the typed-mixed word "
       "classes are the quotient: the recorded exact position, computed "
       "from the words' coordinate determinant)")

# (D5) THE SECTOR LAW ON S22 (the link certified on the FULL typed-pure
# (2,2) lattice -- the plane-level receipts above are instances)
print("  -- the sector law on S22 (the full typed-pure (2,2) lattice) --")
stable = True
GM_cols = []
for s in S22:
    gcls = GAMMA[0](s_class(s))
    gv = [0] * len(ALLODD_WORDS)
    for w, c in gcls.items():
        gv[ALLODD_WORDS.index(w)] = int(c)
    co = membership_coords(gv, S22)
    if co is None or any(x.denominator != 1 for x in co):
        stable = False
    else:
        GM_cols.append([int(x) for x in co])
ok(stable,
   "LA1 SECTOR: S22 is deck-stable (the rotation preserves the (2,2)-typed "
   "purity: every image is an integral S22-class, computed)")
GM22 = [[GM_cols[j][i] for j in range(6)] for i in range(6)]
ok(mat_mul(GM22, GM22) == [[-1 if i == j else 0 for j in range(6)] for i in range(6)],
   "LA1 SECTOR: gamma^2 = -I on S22 (matrix-exact, the whole Hodge sector "
   "is gamma^2 = -1)")
coh22 = cyclic_cohomology(GM22)
ok(coh22["H2"][0] == 0 and coh22["H2"][1] == [],
   "LA1 SECTOR KILLING: H^2(C_4; S22) = 0 (the full typed-pure (2,2) "
   "lattice's deck group is ZERO: the pair-level obstruction dies on the "
   "whole sector, no symmetrization)")
ok(coh22["H1"][0] == 6 and sorted(coh22["H1"][1]) == [2, 2, 2],
   "LA1 SECTOR PARITY: H^1(C_4; S22) = (Z/2)^3 (the parity residue of the "
   "whole (2,2) sector: 2-elementary, computed)")
gm1_cols22 = []
for k in range(6):
    gm1_cols22.append([GM22[i][k] - (1 if i == k else 0) for i in range(6)])
two_all = True
one_any = False
for s in S22:
    co2 = membership_coords([2 * x for x in s], gm1_cols22)
    if co2 is None or any(x.denominator != 1 for x in co2):
        two_all = False
    co1 = membership_coords(s, gm1_cols22)
    if co1 is not None and all(x.denominator == 1 for x in co1):
        one_any = True
ok(two_all and not one_any,
   "LA1 SECTOR KILL-SCALE: 2 EXACT on S22 as the maximum over the PRIMITIVE "
   "contents -- every (2,2)-typed-pure class dies at scale 2 (2*S22 in "
   "im(gamma-1)) and NO basis class dies at scale 1 (the degenerate "
   "contents die at every scale: the B8b boundary receipt above; the "
   "sector's parity law for the primitive contents, sector-complete)")

# (B8b) THE DEGENERATE-CONTENT BOUNDARY (the 24-b audit's M1
# counterexample, now a computed receipt): the class (gamma-1)s0 is
# (2,2)-pure, nonzero, and lies in im(gamma-1) INTEGRALLY -- its link
# class dies at EVERY scale, odd included. The iff-law REQUIRES the
# primitive hypothesis; the sector statement (the maximum over the
# primitive contents) is unaffected.
s0_cls = s_class(S22[0])
alpha_deg = addc(GAMMA[0](s0_cls), sc(s0_cls, -1))
degs = type_degrees(alpha_deg)
ok(alpha_deg != ZERO and degs != [] and all(d == (2, 2) for d in degs),
   "LA1 BOUNDARY (the audit's counterexample, computed): the class "
   "(gamma-1)s0 is a NONZERO (2,2)-pure S22 class lying integrally in "
   "im(gamma-1)")
img_cols_S22 = []
for sv in S22:
    sv_cls = s_class(sv)
    img_cols_S22.append(addc(GAMMA[0](sv_cls), sc(sv_cls, -1)))
def in_image_S22(cls, m):
    res = to_coords(sc(cls, m), img_cols_S22)
    if res[0] is None:
        return False
    return all(x.denominator == 1 for x in res[0])
ok(all(in_image_S22(alpha_deg, m) for m in range(1, 13)),
   "LA1 BOUNDARY: the degenerate content (gamma-1)s0 lies INTEGRALLY in "
   "im(gamma-1) restricted to S22 -- its link class dies at EVERY scale "
   "m = 1..12 (odd included); the iff-parity law requires the nonzero-H^1 "
   "hypothesis (stated on the artifact's face); the sector's kill-scale 2 "
   "is the maximum over the PRIMITIVE contents (the basis classes)")

# (D6) THE GATE ON THE SECTOR PAIR: S40 and S31 have no grade-2 content
ok(all(pi_p_entries(s_class(s), 2) == {} for s in S40 + S31),
   "LA2 SECTOR GATE: S40 (+) S31 have ZERO grade-2 content (the link's "
   "target does not exist on the transcendental planes' full lattices: "
   "the gate fires on the whole non-Hodge typed-pure sector)")

# =====================================================================
# THE ROUND-24 SUMMARY LINES
# =====================================================================
print()
print("== ROUND 24: THE IDENTIFICATION LINK -- the certified laws ==")
print("  LA1 THE REDUCTION (on the strip-shape hypothesis, on its face):")
print("     the transport identity (gamma symplectic + iota intertwining);")
print("     the bar law (a formality receipt); N(c) = 0 at the cochain level")
print("     with its boundary (the norm law does not by itself distinguish")
print("     the witness; the iota-specificity is the strip's trace")
print("     condition, computed); H^2(C_4; M (+) M) = 0 and the iota-")
print("     submodule's H^1 = Z/2; THE PARITY LAW for the PRIMITIVE")
print("     contents: the least kill-scale 2 on all three (2,2) planes and")
print("     both Weil rays; the degenerate-content boundary (the audit's")
print("     counterexample, computed as a receipt); the sector law on S22")
print("     (deck-stable, gamma^2 = -I, H^2 = 0, H^1 = (Z/2)^3, the sector")
print("     kill-scale 2 exact).")
print("  LA2 THE GATE (the link's DOMAIN condition): pi_2 nonzero exactly")
print("     on the (2,2) sector; the product-deck character table (+I on")
print("     (2,2) AND on the Weil plane; -I on (3,1)): the character is")
print("     (p-q) mod 4; the (2,2)/(4,0) collision is separated ONLY by the")
print("     grade -- the collision sector is the transcendental")
print("     discriminator sector (W_R, W_I), and S40 = the W-plane exactly;")
print("     the filter's (p,p)-specificity certified (the audit's p-only")
print("     mutation caught); the positive non-killing datum (the gated")
print("     content's own H^1-class survives; the link refuses to carry it).")
print("  LA3 THE PARTITION: the typed-pure lattices S22/S40/S31 (ranks")
print("     6/2/8, the type-system kernels computed); the rational typed")
print("     partition; the exact indices (the plane spans: 16 in S22, 1 for")
print("     the W-plane, 256 in S31; L16 over the typed-pure sum: 4096).")
print("     THE COMPOSITION BOUNDARY: the descent and the conduit are NOT")
print("     computed here -- the two-cell reduction (the 21-c item (ii)) is")
print("     the remaining step; NO algebraicity is claimed in this round's")
print("     artifacts. The mixed-parity (2,2) content is the other remaining")
print("     sector (the next strike's target).")
print()
print("  SCOPE: letter-lattice laws on the committed model world, under the")
print("     strip-shape hypothesis (on the face). The remaining")
print("     construction: the reduction of the actual two-cell to the")
print("     iota-shaped cochain (the 21-c item (ii)); then the mixed-parity")
print("     (2,2) sector; the general-input transport (ledger 085); the Lean")
print("     face EveryHodgeClassIsRationalAlgebraic remains the target.")
print()
print(f"CHECKS: {CHECKS}")
print("ALL PASS: exit 0")
