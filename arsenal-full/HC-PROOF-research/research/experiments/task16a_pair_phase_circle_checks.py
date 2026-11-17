#!/usr/bin/env python3
# Task 16-a bounded certificate script: Lemma W9 (the Weil phase circle / the
# flat-character exactness theorem) — the model-layer checks for the monodromy
# mechanism's recorded question (round 15-b): do Psi_pair + the per-fiber
# monodromy reps constrain (m,q) beyond the additive profile?
# BOUNDS: pure Python, EXACT Fraction arithmetic throughout (parity-exact Weil
# construction; no complex numbers, no floats anywhere, zero tolerance).
# Largest enumeration 2^16 monomial operations, runtime < 2s, memory < 10MB.
# Every check ASSERTS: a mismatch aborts the script (no green-exit on a failed
# comparison). Model conventions imported VERBATIM from the audited task13d /
# task15a certificates (16-letter exterior algebra, parity_weil, THETA, the
# exact dual-basis Poincare class, the Newton conductor machinery, the
# committed instance data) — the inherited-artifact gate re-run per ledger 084.

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
THETA_D = add(*[wedge(ab_letter(j, False), ab_letter(j, True)) for j in range(4)])

print("== CHECK 0: committed constants re-asserted (inherited-convention gate, ledger 084) ==")
for j in range(1, 5):
    assert integral(wedge(W_R, wedge_pow(THETA, j))) == 0
assert integral(wedge_pow(THETA, 4)) == 24 and integral(wedge(W_R, W_R)) == 8
assert integral(wedge(W_I, W_I)) == 8 and integral(wedge(W_R, W_I)) == 0
assert integral(wedge(W_R, W_R)) + integral(wedge(W_I, W_I)) == 16
assert wedge(THETA, W_R) == {} and wedge(wedge_pow(THETA, 2), W_R) == {} \
       and wedge(wedge_pow(THETA, 3), W_R) == {}, "W0 class annihilation FAILED"
# NEW (W9): the dual-side W0 annihilation, in the SHIFTED (AB-position)
# representation: the dual Weil words annihilate the dual NS class. Under the
# committed relabeling (the fm pushforward maps AB-letters down to low
# positions) this is the same parity statement as the A-side W0 — asserted
# here in the shifted representation as the duality-face consistency of the
# ghost corridor.
WR_D_shift = {w << 8: c for w, c in WR_D.items()}
WI_D_shift = {w << 8: c for w, c in WI_D.items()}
assert wedge(THETA_D, WR_D_shift) == {} and wedge(THETA_D, WI_D_shift) == {}, \
    "dual W0 annihilation FAILED"
assert wedge(wedge_pow(THETA_D, 2), WR_D_shift) == {} \
       and wedge(wedge_pow(THETA_D, 3), WR_D_shift) == {}
print("  periods 24/8/8/0/16 + W0 annihilations (A-side AND dual-side, shifted rep): OK")

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

# ---- the pair machinery (committed conventions; the same construction as task15a) ----
def ch_from_C(r, c1, c2, c3, c4):
    p1 = c1
    p2 = add(wedge_pow(c1, 2), scale(c2, -2))
    p3 = add(wedge_pow(c1, 3), scale(wedge(c1, c2), -3), scale(c3, 3))
    p4 = add(wedge_pow(c1, 4), scale(wedge(wedge_pow(c1, 2), c2), -4),
             scale(wedge_pow(c2, 2), 2), scale(wedge(c1, c3), 4), scale(c4, -4))
    return {'0': r, '1': p1, '2': scale(p2, Fr(1, 2)), '3': scale(p3, Fr(1, 6)), '4': scale(p4, Fr(1, 24))}

ZERO = {0: 0}

def pair_ch_diff(r, m, c1d, c2M, gamma):
    """the committed pair construction; returns the FULL ch-difference dict:
    keys '0' (integer rank difference) and '1'..'4' (exact word dicts)."""
    c2P = add(c2M, scale(W_R, -m))                     # c2(E+) - c2(E-) = -m W_R
    c3_shift = wedge(c1d, scale(W_R, -m))              # c3(E+) - c3(E-) = c1 . (-m W_R)
    c1sq = wedge_pow(c1d, 2)
    c4_shift = add(scale(wedge(c1sq, scale(W_R, -m)), -1),
                   scale(add(wedge_pow(c2P, 2), scale(wedge_pow(c2M, 2), -1)), Fr(1, 2)),
                   wedge(c1d, c3_shift))
    chM = ch_from_C(r, c1d, c2M, ZERO, gamma)
    chP = ch_from_C(r, c1d, c2P, c3_shift, add(gamma, c4_shift))
    d = {'0': chP['0'] - chM['0']}                     # rank difference (integer)
    for g in ('1', '2', '3', '4'):
        d[g] = add(chP[g], scale(chM[g], -1))
    return d

# The committed instance set (audit 15-c F1): the four W6 table instances,
# the carrier instance, AND the committed detector-probe instance.
CASES = [(3, 1, ZERO, ZERO, ZERO, 'W6-I1 c1=0'),
         (5, 2, ZERO, ZERO, ZERO, 'W6-I2 c1=0'),
         (4, 1, THETA, ZERO, ZERO, 'W6-I3 c1=theta'),
         (7, 3, THETA, ZERO, {VOL_A: 5}, 'W6-I4 c1=theta,gamma=5vol'),
         (5, 1, ZERO, ZERO, ZERO, 'carrier (F, O^r)'),
         (6, 2, ZERO, dict(W_R), ZERO, 'detector probe c2M=W_R')]

# the unit ghost: the fixed dual-side class fm_2(W_R) == W_R-dual (the committed W5)
GHOST_UNIT = fm_A(W_R, 2)
assert coeff_along(GHOST_UNIT, WR_D) == 1, "the committed W5 normalization must hold for the unit ghost"

# ---- the family-grade bookkeeping (leaf P3) ----
# The dual-side virtual family Phi_hat(xi_pair) has ch-grade-j component
# = fm_A(xi grade-(4-j) component, 4-j). Hence:
#   fam_g0 (rank of the dual family)  <- integral of xi grade-'4'  (RR, td = 1)
#   fam_g1 (degree-2 AB words)        <- fm_A(xi grade-'3', 3)  == c1(L_pair) (the W8 input)
#   fam_g2 (degree-4 AB words)        <- fm_A(xi grade-'2', 2)
#   fam_g3 (degree-6 AB words)        <- fm_A(xi grade-'1', 1)
#   fam_g4 (top AB degree)            <- xi rank difference
def family_census(d):
    return {'fam_g0': integral(d['4']),
            'fam_g1': fm_A(d['3'], 3),
            'fam_g2': fm_A(d['2'], 2),
            'fam_g3': fm_A(d['1'], 1),
            'fam_g4': d['0']}

print("\n== CHECK 1: the FULL GHOST CENSUS on ALL committed instances (W9(ii)) ==")
# The dual-side family of a pure pair at scale m has ch = m * (unit ghost)
# PURELY at the middle grade: fam_g0 = 0, fam_g1 = 0, fam_g2 = m*(W_R-dual),
# fam_g3 = 0, fam_g4 = 0. The census is m-determined; the ambient
# (r, c1, gamma, c2M)-data — in particular the Weil charge q — is INVISIBLE.
for (r, m, c1d, c2M, gamma, tag) in CASES:
    d = pair_ch_diff(r, m, c1d, c2M, gamma)
    cen = family_census(d)
    assert cen['fam_g0'] == 0, f"family rank must vanish (Euler corridor): {tag}"
    assert cen['fam_g1'] == {}, f"family grade-1 (the W8 c1(L) input) must vanish: {tag}"
    assert cen['fam_g3'] == {}, f"family grade-3 must vanish: {tag}"
    assert cen['fam_g4'] == 0, f"family top grade must vanish (rank difference): {tag}"
    a2 = coeff_along(cen['fam_g2'], WR_D)
    assert a2 == m, f"family grade-2 must be EXACTLY m*(W_R-dual): {tag}, got {a2}"
    # the input Chern data of the pair difference: ch-diff == m*W_R purely at grade 2
    assert d['1'] == {} and d['3'] == {} and d['4'] == {}, f"ch-diff purity FAILED: {tag}"
    a_in = coeff_along(d['2'], W_R)
    assert a_in == m, f"ch-diff must be m*W_R purely at grade 2: {tag}, got {a_in}"
    print(f"  {tag}: census (0, 0, {m}*(W_R-dual), 0, 0): OK")

print("\n== CHECK 2: m-linearity of the FULL census + the q-invisibility face (W9(ii)/(iii)) ==")
# (a) linearity: census(m) == m * census(1) at EVERY grade, fixed ambient data.
for m in (1, 2, 3, 5):
    c1 = family_census(pair_ch_diff(5, 1, ZERO, ZERO, ZERO))
    cm = family_census(pair_ch_diff(5, m, ZERO, ZERO, ZERO))
    assert cm['fam_g0'] == m * c1['fam_g0'] and cm['fam_g4'] == m * c1['fam_g4']
    assert cm['fam_g1'] == scale(c1['fam_g1'], m) and cm['fam_g3'] == scale(c1['fam_g3'], m)
    assert coeff_along(cm['fam_g2'], WR_D) == m * coeff_along(c1['fam_g2'], WR_D)
print("  census(m) = m * census(1) at every grade for m in {1,2,3,5}: OK")
# (b) the q-face: the detector probe (q(E_-) = <W_R, W_R> = 8 != 0) and the
# gamma-loaded instance I4 produce the SAME census shape at their scale as the
# q = 0 instances — the identical per-grade asserts of CHECK 1 are the assertion;
# here the m=2 probe is compared against a synthetic q=0 instance at m=2:
dA = family_census(pair_ch_diff(6, 2, ZERO, dict(W_R), ZERO))
dB = family_census(pair_ch_diff(6, 2, ZERO, ZERO, ZERO))
assert coeff_along(dA['fam_g2'], WR_D) == coeff_along(dB['fam_g2'], WR_D) == 2
assert dA['fam_g1'] == dB['fam_g1'] == {} and dA['fam_g3'] == dB['fam_g3'] == {}
assert dA['fam_g0'] == dB['fam_g0'] == 0 and dA['fam_g4'] == dB['fam_g4'] == 0
print("  q-face: the q=8 probe and the q=0 instance share the identical census: OK")

print("\n== CHECK 3: the W0 twist-scale stability at ALL grades (W9.2) ==")
# ch(xi_pair (x) e^{k theta}) == ch(xi_pair) for every integer k and every grade
# 0..4: each correction term carries a W_R ^ theta^j factor and dies by W0.
# Extends the committed task14c grade-2/3 twist checks to grades 0, 1, 4.

def exp_theta(k):
    out = {0: {0: 1}}
    for j in range(1, 5):
        tj = scale(wedge_pow(THETA, j), Fr(k ** j, factorial(j)))
        if tj:
            out[j] = tj
    return out

def twist_ch_diff(d, expk):
    out = {'0': d['0'] * expk[0][0]}
    for g in range(1, 5):
        acc = {}
        for a in range(0, g + 1):
            b = g - a
            term_b = expk.get(b)
            if b > 0 and term_b is None:
                continue
            if term_b is None:
                term_b = {0: 1}
            if a == 0:
                if d['0'] != 0 and b > 0:
                    acc = add(acc, scale(term_b, d['0']))
                continue
            term_a = d[str(a)]
            if term_a:
                acc = add(acc, wedge(term_a, term_b))
        out[str(g)] = acc
    return out

for (r, m, c1d, c2M, gamma, tag) in CASES:
    d = pair_ch_diff(r, m, c1d, c2M, gamma)
    for k in range(-3, 6):
        d_tw = twist_ch_diff(d, exp_theta(k))
        for g in range(1, 5):
            assert d_tw[str(g)] == d[str(g)], \
                f"twist-scale stability FAILED at {tag}, k={k}, grade {g}"
        assert d_tw['0'] == d['0'], f"twist rank stability FAILED at {tag}, k={k}"
print("  ch(xi.e^{k.theta}) == ch(xi) at all grades 0..4, k in -3..5, all instances: OK")

print("\n== CHECK 4: the character-input layer, certified NON-VACUOUS both ways (W9(iii)) ==")
# (a) the functor input space is nonzero: a family with nonzero grade-3 content
#     produces a nonzero c1(lambda) — the committed non-vacuity instance, plus
#     the 28->28 census, no silent skips, and the uniform +1 composite.
deg6_words = [bits for bits in range(256) if bin(bits).count('1') == 6]
assert len(deg6_words) == comb(8, 6) == 28
th3 = wedge_pow(THETA, 3)
f_th3 = fm_A(th3, 3)
assert f_th3 != {}, "fm_3 must be non-vacuous (the character-input layer is a real functor)"
nonempty_count = 0
consts = set()
for w in deg6_words:
    out = fm_A({w: 1}, 3)
    if out:
        nonempty_count += 1
    for mm in out:
        assert bin(mm).count('1') == 2 and mm < 256
    rt = fm_AB(out, 1) if out else {}
    if out:
        assert set(rt.keys()) == {w}
        for _, c2 in rt.items():
            consts.add(c2)
assert nonempty_count == 28, "fm_3 non-empty on all 28 basis words"
assert consts == {Fr(1)}, f"composite constants must be the uniform +1: {consts}"
print("  input functor non-vacuous: fm_3(theta^3) != 0; census 28->28; composite +1: OK")
# (b) the CHANNEL kills the input: fm_3(ch_3-diff) == 0 on all committed
#     instances (the W8 input; re-asserted as the census face fam_g1 == {}).
for (r, m, c1d, c2M, gamma, tag) in CASES:
    d = pair_ch_diff(r, m, c1d, c2M, gamma)
    assert fm_A(d['3'], 3) == {}, f"channel input kill FAILED at {tag}"
print("  channel input: fm_3(ch_3-diff) = 0 on all committed instances: OK")

print("\n== CHECK 5: the ghost's duality face (the double-dual census, W9) ==")
# (a) the ghost words are degree-4 pure: the unit ghost carries NO degree-2 or
#     degree-6 dual content, so its own lambda-hat input vanishes identically —
#     the same flatness shape at the second dual level (W8.2 extended).
for w in WR_D:
    assert bin(w).count('1') == 4, "the unit ghost must be degree-4 pure"
# (b) the committed W5 round trip: the ghost returns W_R exactly (g = 4 even).
rt = fm_AB(GHOST_UNIT, 2)
assert set(rt.keys()) == set(W_R.keys()) and all(rt[w_] == W_R[w_] for w_ in W_R), \
    "the ghost round trip must be the identity (committed W5)"
# (c) the ghost's own family census: the ghost is a rank-0 Euler-0 middle-grade
# class on the dual (the census of its round trip reproduces the unit A-side
# ghost shape): family-grade-2 == the unit ghost.
ghost_back = {'0': 0, '1': {}, '2': rt, '3': {}, '4': {}}
cen_gb = family_census(ghost_back)
assert cen_gb['fam_g0'] == 0 and cen_gb['fam_g1'] == {} \
       and cen_gb['fam_g3'] == {} and cen_gb['fam_g4'] == 0
assert coeff_along(cen_gb['fam_g2'], WR_D) == 1, "the ghost census must be the unit shape"
print("  ghost duality: degree-4 pure + round trip identity + unit census shape: OK")

print("\nALL W9 MODEL-LAYER CHECKS DONE (every comparison asserted, zero tolerance, no floats)")
print("SCHEME-LEVEL LEAVES (P5 the Appell-Humbert/determinant-holonomy unification,")
print("P6 the Pic^0-invariance/discrete-quotient type-split of the phase) remain")
print("declared external leaves at standard strength — NOT certified by this script.")
