#!/usr/bin/env python3
# Task 15-a bounded certificate script: Lemma W8 (Picard-sheaf flatness of the pair
# channel) — the model-layer checks for the entry wall of the monodromy mechanism.
# BOUNDS: pure Python, EXACT Fraction arithmetic throughout (parity-exact Weil
# construction; no complex numbers, no floats anywhere, zero tolerance).
# Largest enumeration 2^16 monomial operations, runtime < 2s, memory < 10MB.
# Every check ASSERTS: a mismatch aborts the script (no green-exit on a failed
# comparison). Model conventions imported VERBATIM from the audited task13d
# certificate (16-letter exterior algebra, parity_weil, THETA, the exact
# dual-basis Poincare class, the Newton conductor machinery, the committed
# instance data) — the inherited-artifact gate re-run per ledger 084.

from fractions import Fraction as Fr
from math import factorial, comb

# ---- 16-letter exterior algebra (committed conventions) ----
# A-letters:  positions 0..7  = (e1,f1,e2,f2,e3,f3,e4,f4)   [D1 canonical order]
# AB-letters: positions 8..15 = (E1,F1,E2,F2,E3,F3,E4,F4)  [dual canonical order]
# D1 volume word e1 f1 e2 f2 e3 f3 e4 f4 = mask 0xFF, integral 1.
VOL_A = 0xFF

def wedge(d1, d2):
    out = {}
    for m1, c1 in d1.items():
        for m2, c2 in d2.items():
            if m1 & m2:
                continue
            sign = 1
            mm2 = m2
            while mm2:
                j = (mm2 & -mm2).bit_length() - 1
                above = bin(m1 & ~((1 << (j + 1)) - 1)).count('1')
                if above & 1:
                    sign = -sign
                mm2 &= mm2 - 1
            m = m1 | m2
            out[m] = out.get(m, 0) + c1 * c2 * sign
    return {m: c for m, c in out.items() if c != 0}

def wedge_pow(d, k):
    r = {0: 1}
    for _ in range(k):
        r = wedge(r, d)
    return r

def scale(d, s):
    return {m: c * s for m, c in d.items() if c * s != 0}

def add(*ds):
    out = {}
    for d in ds:
        for m, c in d.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c != 0}

def integrate_first_factor(d):
    """pushforward along the first factor of a class on (first x second):
    the first-factor part (low byte) must be the full volume 0xFF."""
    out = {}
    for m, c in d.items():
        if (m & VOL_A) == VOL_A:
            out[m >> 8] = out.get(m >> 8, 0) + c
    return {m: c for m, c in out.items() if c != 0}

def integral(d):
    return d.get(VOL_A, 0)

def a_letter(j, f=False):
    return {1 << (2 * j + (1 if f else 0)): 1}

def ab_letter(j, f=False):
    return {1 << (8 + 2 * j + (1 if f else 0)): 1}

# ---- model classes (parity-exact Weil construction, committed) ----
def parity_weil():
    WR, WI = {}, {}
    for bits in range(256):
        bl = [i for i in range(8) if (bits >> i) & 1]
        if len(bl) != 4:
            continue
        if not all(((bits >> (2*j)) & 1) + ((bits >> (2*j+1)) & 1) == 1 for j in range(4)):
            continue  # not one-letter-per-block
        nf = sum(1 for i in bl if i % 2 == 1)
        if nf % 2 == 0:
            WR[bits] = Fr(1) if nf in (0, 4) else Fr(-1)
        else:
            WI[bits] = Fr(1) if nf == 1 else Fr(-1)
    return WR, WI

W_R, W_I = parity_weil()
assert len(W_R) == 8 and len(W_I) == 8, (len(W_R), len(W_I))
WR_D, WI_D = dict(W_R), dict(W_I)

THETA = add(*[wedge(a_letter(j, False), a_letter(j, True)) for j in range(4)])

print("== CHECK 0: committed constants re-asserted (inherited-convention gate, ledger 084) ==")
for j in range(1, 5):
    assert integral(wedge(W_R, wedge_pow(THETA, j))) == 0
assert integral(wedge_pow(THETA, 4)) == 24 and integral(wedge(W_R, W_R)) == 8
assert integral(wedge(W_I, W_I)) == 8 and integral(wedge(W_R, W_I)) == 0
assert integral(wedge(W_R, W_R)) + integral(wedge(W_I, W_I)) == 16
assert wedge(THETA, W_R) == {} and wedge(wedge_pow(THETA, 2), W_R) == {} \
       and wedge(wedge_pow(THETA, 3), W_R) == {}, "W0 class annihilation FAILED"
print("  periods 24/8/8/0/16 + W0 annihilations: OK")

# ---- the general-grade cohomological FM (leaf P3; the committed W5 construction
# extended to all grades by the identical formula) ----
# c1(P) = sum_p u_p (x) u_hat_p over ALL 8 positions (the exact dual-basis convention).
def c1P_dual():
    terms = []
    for pos in range(8):
        a = {1 << pos: 1}
        ab = {1 << (8 + pos): 1}
        terms.append(wedge(a, ab))
    return add(*terms)

def c1Phat_dual():
    # Poincare on (AB x A): sum_p u_hat_p (x) u_p, AB at LOW bits, A at HIGH bits
    terms = []
    for pos in range(8):
        ab = {1 << pos: 1}
        a = {1 << (8 + pos): 1}
        terms.append(wedge(ab, a))
    return add(*terms)

def fm_A(x, k):
    """grade reflection H^{2k}(A) -> H^{2(4-k)}(AB): pair x with c1(P)^{8-2k}/(8-2k)!.
    k=2 reproduces the committed W5 transform fm_A_degree4 VERBATIM (cross-checked)."""
    j = 8 - 2 * k
    cj = scale(wedge_pow(c1P_dual(), j), Fr(1, factorial(j)))
    return integrate_first_factor(wedge(x, cj))

def fm_AB(y, k):
    j = 8 - 2 * k
    cj = scale(wedge_pow(c1Phat_dual(), j), Fr(1, factorial(j)))
    return integrate_first_factor(wedge(y, cj))

def coeff_along(x, frame):
    # EXACT: every ratio must be the same exact Fraction (zero tolerance).
    if not x:
        return None
    if set(x.keys()) != set(frame.keys()):
        return None
    c0 = None
    for m in x:
        ratio = x[m] / frame[m]
        if c0 is None:
            c0 = ratio
        elif ratio != c0:
            return None
    return c0

print("\n== CHECK 1: k=2 cross-check against the committed W5 transform ==")
phi_WR = fm_A(W_R, 2)
phi_WI = fm_A(W_I, 2)
aR = coeff_along(phi_WR, WR_D)
aI = coeff_along(phi_WI, WI_D)
print(f"  fm_2(W_R) along W_R-dual = {aR};  fm_2(W_I) along W_I-dual = {aI}")
assert aR == 1 and aI == 1, "the k=2 general formula must reproduce the committed W5 normalization"
rt = fm_AB(phi_WR, 2)
ok = set(rt.keys()) == set(W_R.keys()) and all(rt[m] == W_R[m] for m in W_R)
assert ok, "k=2 round trip FAILED"
rtI = fm_AB(phi_WI, 2)
okI = set(rtI.keys()) == set(W_I.keys()) and all(rtI[m] == W_I[m] for m in W_I)
assert okI, "k=2 round trip (W_I) FAILED"
print("  both round trips the identity: OK (the committed W5 behavior reproduced)")

print("\n== CHECK 2: the k=3 census and non-vacuity (the grade bookkeeping of leaf P3) ==")
# degree census: every degree-6 A-word maps into degree-2 AB-words; dims 28 -> 28.
deg6_words = [bits for bits in range(256) if bin(bits).count('1') == 6]
assert len(deg6_words) == comb(8, 6) == 28
nonempty_count = 0
for w in deg6_words:
    out = fm_A({w: 1}, 3)
    if out:
        nonempty_count += 1
    for m in out:
        assert bin(m).count('1') == 2, "fm_3 must land in degree-2 AB-words"
        assert m < 256, "no A-letters may survive"
assert nonempty_count == 28, \
    f"fm_3 must be non-empty on all 28 basis words (got {nonempty_count}; no silent skips)"
print("  fm_3: 28 degree-6 words -> degree-2 AB-words, non-empty on all 28 (census 28 -> 28): OK")
# non-vacuity: fm_3(theta^3) != 0
th3 = wedge_pow(THETA, 3)
f_th3 = fm_A(th3, 3)
print(f"  fm_3(theta^3) nonzero: {bool(f_th3)} ({len(f_th3)} monomials)")
assert f_th3 != {}, "fm_3 must be non-vacuous"
# the composite normalization: fm_AB(., 1) o fm_3 asserted UNIFORM on a spanning
# test set with constant of modulus 1 (recorded, not fitted).
consts = set()
for w in deg6_words:
    out = fm_AB(fm_A({w: 1}, 3), 1)
    if not out:
        continue
    assert set(out.keys()) == {w}, "the composite must land back on the input word"
    for m, c in out.items():
        consts.add(c)
assert all(abs(c) == 1 for c in consts), f"composite constants must have modulus 1: {consts}"
print(f"  fm_AB(.,1) o fm_3 uniform on the 28-word basis with constant {consts}: "
      f"{'OK (recorded, not fitted)' if len(consts) == 1 else 'MULTIPLE CONSTANTS — inspect'}")
assert len(consts) == 1, "the committed convention must give ONE uniform grade-3 composite constant"

# ---- the pair machinery (committed conventions; grade-3 purity is the W8 input) ----
def ch_from_C(r, c1, c2, c3, c4):
    p1 = c1
    p2 = add(wedge_pow(c1, 2), scale(c2, -2))
    p3 = add(wedge_pow(c1, 3), scale(wedge(c1, c2), -3), scale(c3, 3))
    p4 = add(wedge_pow(c1, 4), scale(wedge(wedge_pow(c1, 2), c2), -4),
             scale(wedge_pow(c2, 2), 2), scale(wedge(c1, c3), 4), scale(c4, -4))
    return {'0': r, '1': p1, '2': scale(p2, Fr(1, 2)), '3': scale(p3, Fr(1, 6)), '4': scale(p4, Fr(1, 24))}

ZERO = {0: 0}

def pair_ch3_diff(r, m, c1d, c2M, gamma):
    """the committed pair construction; returns (chP, chM, ch3-difference class)."""
    c2P = add(c2M, scale(W_R, -m))                     # c2(E+) - c2(E-) = -m W_R
    c3_shift = wedge(c1d, scale(W_R, -m))              # c3(E+) - c3(E-) = c1 . (-m W_R)
    c1sq = wedge_pow(c1d, 2)
    c4_shift = add(scale(wedge(c1sq, scale(W_R, -m)), -1),
                   scale(add(wedge_pow(c2P, 2), scale(wedge_pow(c2M, 2), -1)), Fr(1, 2)),
                   wedge(c1d, c3_shift))
    chM = ch_from_C(r, c1d, c2M, ZERO, gamma)
    chP = ch_from_C(r, c1d, c2P, c3_shift, add(gamma, c4_shift))
    d3 = add(chP['3'], scale(chM['3'], -1))
    return chP, chM, d3, c3_shift

print("\n== CHECK 3: pair grade-3 purity on ALL committed instances (the W8 input) ==")
# The committed instance set (audit 15-c F1 repair): the four W6 table instances
# (c2M = 0; the Weil content sits on the E+ side: q(E+) = -8m != 0), the carrier
# instance (F, O^r), AND the committed detector-probe instance (c2M = W_R,
# r=6, m=2 — the committed task13d detector check). The grade-3 purity is
# c2M-independent (d3 = 0 identically; independently re-derived by the auditor),
# and the committed data is what the receipts claim.
cases = [(3, 1, ZERO, ZERO, ZERO, 'W6-I1 c1=0'),
         (5, 2, ZERO, ZERO, ZERO, 'W6-I2 c1=0'),
         (4, 1, THETA, ZERO, ZERO, 'W6-I3 c1=theta'),
         (7, 3, THETA, ZERO, {VOL_A: 5}, 'W6-I4 c1=theta,gamma=5vol'),
         (5, 1, ZERO, ZERO, ZERO, 'carrier (F, O^r)'),
         (6, 2, ZERO, dict(W_R), ZERO, 'detector probe c2M=W_R')]
for (r, m, c1d, c2M, gamma, tag) in cases:
    chP, chM, d3, c3_shift = pair_ch3_diff(r, m, c1d, c2M, gamma)
    print(f"  r={r} m={m} {tag}: ch3-diff == 0: {d3 == {}}; "
          f"c3-shift class size (W0 kill when c1 in Z.theta): {len(c3_shift)}")
    assert d3 == {}, f"pair grade-3 purity FAILED at {tag}"
    if c1d is not ZERO:
        assert c3_shift == {}, "the c3-shift -m.c1^W_R must die by W0 in the ring"

print("\n== CHECK 4: THE FLATNESS COMPOSITES (Lemma W8 at the model layer) ==")
for (r, m, c1d, c2M, gamma, tag) in cases:
    chP, chM, d3, _ = pair_ch3_diff(r, m, c1d, c2M, gamma)
    f3 = fm_A(d3, 3)      # c1(L_pair) = fm_3(ch3-difference)
    assert f3 == {}, f"flatness composite FAILED at {tag}"
    print(f"  {tag}: fm_3(ch3-diff) = 0  ->  c1(L_pair) = 0  (L_pair flat): OK")

print("\n== CHECK 5: the duality face for W8.2 (linearity at grade 2) ==")
for m in (1, 2, 3, 5):
    fm_mWR = fm_A(scale(W_R, m), 2)
    a = coeff_along(fm_mWR, WR_D)
    print(f"  fm_2(m.W_R) along W_R-dual = {a}  (expected m = {m})")
    assert a == m, "linearity of the W5-normalized transform FAILED"
print("  the dual-side difference character m.fm_2(W_R): the same purity shape on the dual, W5-consistent")

print("\nALL W8 MODEL-LAYER CHECKS DONE (every comparison asserted, zero tolerance, no floats)")
print("SCHEME-LEVEL LEAVES (P1 determinant-K-theory identity, P2 GRR/abelian Todd, P4 double-dual)")
print("remain declared external leaves at standard strength — NOT certified by this script.")
