#!/usr/bin/env python3
# Task 13-d bounded certificate script: the pair-channel wall constants.
# BOUNDS: pure Python, EXACT arithmetic throughout (Fraction coefficients; parity-exact
# Weil-class construction -- no complex numbers, no floats anywhere, zero tolerance).
# Largest enumeration 2^16 combined-monomial operations, runtime < 1s, memory < 10MB.
# Every check ASSERTS: a mismatch aborts the script (no green-exit on a failed comparison).

from fractions import Fraction as Fr

# ---- 16-letter exterior algebra ----
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
    """pushforward along the second factor of a class on (first x second):
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

# ---- model classes ----
# PARITY-EXACT construction of the Weil classes (no complex numbers, no floats):
# Omega = wedge_{j=0..3}(e_j + i f_j) expands over one-letter-per-block words; the coefficient
# of a word is i^{#f-letters}: W_R = Re part (sign +1 at #f in {0,4}, -1 at #f = 2 since Re(i^2) = -1),
# W_I = Im part (sign +1 at #f = 1, -1 at #f = 3). All coefficients exact Fractions.
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
# Dual basis position-matched: the dual Weil tables are the same DATA.
WR_D, WI_D = dict(W_R), dict(W_I)

THETA = add(*[wedge(a_letter(j, False), a_letter(j, True)) for j in range(4)])

print("== committed constants re-confirm ==")
for j in range(1, 5):
    print(f"  int W_R theta^{j} = {integral(wedge(W_R, wedge_pow(THETA, j)))}")
print("  int theta^4 =", integral(wedge_pow(THETA, 4)))
print("  int W_R^2   =", integral(wedge(W_R, W_R)))
print("  int W_I^2   =", integral(wedge(W_I, W_I)))
print("  int W_R W_I =", integral(wedge(W_R, W_I)))
print("  int Om Ombar=", integral(wedge(W_R, W_R)) + integral(wedge(W_I, W_I)), "(= W_R^2 + W_I^2, the cross term vanishes)")

# Ring-annihilation lemma: W_R wedge NS-classes vanish
print("\n== ring lemma: W_R wedge NS-sector ==")
print("  theta ^ W_R   =", integral(wedge(THETA, W_R)) if wedge(THETA, W_R) else 0, "(monomials:", len(wedge(THETA, W_R)), ")")
t2w = wedge(wedge_pow(THETA, 2), W_R)
print("  theta^2 ^ W_R = 0 (monomials:", len(t2w), ")")
t3w = wedge(wedge_pow(THETA, 3), W_R)
print("  theta^3 ^ W_R = 0 (monomials:", len(t3w), ")")
assert wedge(THETA, W_R) == {} and t2w == {} and t3w == {}, "W0 class annihilation FAILED"
for j in range(1, 5):
    assert integral(wedge(W_R, wedge_pow(THETA, j))) == 0
assert integral(wedge_pow(THETA, 4)) == 24 and integral(wedge(W_R, W_R)) == 8
assert integral(wedge(W_I, W_I)) == 8 and integral(wedge(W_R, W_I)) == 0
assert integral(wedge(W_R, W_R)) + integral(wedge(W_I, W_I)) == 16

# ---- FM cohomological transform on H^4 (A -> AB) ----
# Exact dual-basis convention: c1(P) = sum_p u_p (x) u_hat_p over ALL 8 positions.
# Grade reflection: x in degree 2k pairs with c^{8-2k}/(8-2k)! ; for k=2: c^4/24.
def c1P_dual():
    terms = []
    for pos in range(8):
        a = {1 << pos: 1}
        ab = {1 << (8 + pos): 1}
        terms.append(wedge(a, ab))
    return add(*terms)

def c1Phat_dual():
    # Poincare on (AB x A): sum_p u_hat_p (x) u_p , AB at LOW bits, A at HIGH bits
    terms = []
    for pos in range(8):
        ab = {1 << pos: 1}
        a = {1 << (8 + pos): 1}
        terms.append(wedge(ab, a))
    return add(*terms)

def fm_A_degree4(x):
    c4 = scale(wedge_pow(c1P_dual(), 4), Fr(1, 24))
    return integrate_first_factor(wedge(x, c4))

def fm_AB_to_A_degree4(y):
    c4 = scale(wedge_pow(c1Phat_dual(), 4), Fr(1, 24))
    return integrate_first_factor(wedge(y, c4))

def coeff_along(x, frame):
    # EXACT: every ratio must be the same exact Fraction (zero tolerance).
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

print("\n== FM transform normalization (exact dual-basis convention) ==")
phi_WR = fm_A_degree4(W_R)
phi_WI = fm_A_degree4(W_I)
aR = coeff_along(phi_WR, WR_D)
aI = coeff_along(phi_WR, WI_D)
bR = coeff_along(phi_WI, WR_D)
bI = coeff_along(phi_WI, WI_D)
print(f"  Phi(W_R) monomials={len(phi_WR)}; along WR_dual={aR}; along WI_dual={aI}")
print(f"  Phi(W_I) monomials={len(phi_WI)}; along WR_dual={bR}; along WI_dual={bI}")
rt = fm_AB_to_A_degree4(phi_WR)
ok = set(rt.keys()) == set(W_R.keys()) and all(rt[m] == W_R[m] for m in W_R)
print(f"  round trip Phi_AB(Phi_A(W_R)) == W_R : {ok}")
assert ok, "W_R round trip FAILED"
rtI = fm_AB_to_A_degree4(phi_WI)
okI = set(rtI.keys()) == set(W_I.keys()) and all(rtI[m] == W_I[m] for m in W_I)
print(f"  round trip Phi_AB(Phi_A(W_I)) == W_I : {okI}")
assert okI, "W_I round trip FAILED"
assert aR == 1 and aI is None and bR is None and bI == 1, (aR, aI, bR, bI)

# ---- characters, Newton, the pair table ----
def ch_from_C(r, c1, c2, c3, c4):
    p1 = c1
    p2 = add(wedge_pow(c1, 2), scale(c2, -2))
    p3 = add(wedge_pow(c1, 3), scale(wedge(c1, c2), -3), scale(c3, 3))
    p4 = add(wedge_pow(c1, 4), scale(wedge(wedge_pow(c1, 2), c2), -4),
             scale(wedge_pow(c2, 2), 2), scale(wedge(c1, c3), 4), scale(c4, -4))
    return {'0': r, '1': p1, '2': scale(p2, Fr(1, 2)), '3': scale(p3, Fr(1, 6)), '4': scale(p4, Fr(1, 24))}

def ch_dual(chE):
    out = {}
    for k, v in chE.items():
        out[k] = v if k == '0' else scale(v, 1 if int(k) % 2 == 0 else -1)
    return out

def ch_product(A, B):
    """full product; return dict degree->class for degrees 1..4 plus scalar '0'"""
    out = {'0': A['0'] * B['0']}
    for deg in range(1, 5):
        acc = {}
        for i in range(0, deg + 1):
            j = deg - i
            ai, bj = A.get(str(i), None), B.get(str(j), None)
            if i == 0 and j == 0:
                continue
            if i == 0:
                if bj:
                    acc = add(acc, scale(bj, ai))
            elif j == 0:
                if ai:
                    acc = add(acc, scale(ai, bj))
            else:
                if ai and bj:
                    acc = add(acc, wedge(ai, bj))
        out[str(deg)] = acc
    return out

def chi_pair(chA, chB):
    return integral(ch_product(chA, chB)['4'])

def ch_diff(chp, chm):
    out = {}
    d0 = chp['0'] - chm['0']
    if d0:
        out['0'] = d0
    for k in '1234':
        d = add(chp[k], scale(chm[k], -1))
        if d:
            out[k] = d
    return out

ZERO = {0: 0}

def pair_check(r, m, c1d, c2M, gamma):
    c2P = add(c2M, scale(W_R, -m))                     # c2(E+) - c2(E-) = -m W_R
    c3_shift = wedge(c1d, scale(W_R, -m))              # c3(E+) - c3(E-) = c1 . (-m W_R)
    c1sq = wedge_pow(c1d, 2)
    c4_shift = add(scale(wedge(c1sq, scale(W_R, -m)), -1),
                   scale(add(wedge_pow(c2P, 2), scale(wedge_pow(c2M, 2), -1)), Fr(1, 2)),
                   wedge(c1d, c3_shift))
    chM = ch_from_C(r, c1d, c2M, ZERO, gamma)
    chP = ch_from_C(r, c1d, c2P, c3_shift, add(gamma, c4_shift))
    D = ch_diff(chP, chM)
    pure = ('0' not in D and '1' not in D and '3' not in D and '4' not in D
            and set(D.get('2', {}).keys()) == set(W_R.keys())
            and all(D['2'][k] == m * W_R[k] for k in W_R))
    chPv, chMv = ch_dual(chP), ch_dual(chM)
    chi_EndP = chi_pair(chP, chPv)
    chi_EndM = chi_pair(chM, chMv)
    chi_PxMv = chi_pair(chP, chMv)
    qM = integral(wedge(W_R, c2M))
    qP = integral(wedge(W_R, c2P))
    return {
        'pure': pure, 'chP': chP, 'chM': chM, 'qP': qP, 'qM': qM,
        't1': (chi_EndP - chi_PxMv, 8 * m * m - m * qM),
        't2': (chi_PxMv - chi_EndM, -m * qM),
        't3': (chi_EndP - chi_EndM, 8 * m * m - 2 * m * qM),
        'charge_split': (qP - qM, -8 * m),
        'c3_shift_class': c3_shift, 'c4_shift_class': c4_shift,
    }

print("\n== Weil-charge / mixed-End table (synthetic pure pairs) ==")
cases = [(3, 1, '0', ZERO, ZERO), (5, 2, '0', ZERO, ZERO),
         (4, 1, 'theta', THETA, ZERO), (7, 3, 'theta', THETA, {VOL_A: 5})]
for (r, m, c1name, c1d, gamma) in cases:
    res = pair_check(r, m, c1d, dict(W_R), gamma)
    print(f"  r={r} m={m} c1={c1name}: purity={res['pure']} q(E+)={res['qP']} q(E-)={res['qM']}")
    print(f"    chi(EndE+)-chi(E+xE-v)   = {res['t1'][0]}  expected {res['t1'][1]}  match={res['t1'][0] == res['t1'][1]}")
    print(f"    chi(E+xE-v)-chi(EndE-)   = {res['t2'][0]}  expected {res['t2'][1]}  match={res['t2'][0] == res['t2'][1]}")
    print(f"    chi(EndE+)-chi(EndE-)    = {res['t3'][0]}  expected {res['t3'][1]}  match={res['t3'][0] == res['t3'][1]}")
    print(f"    charge split q(E+)-q(E-) = {res['charge_split'][0]}  expected {res['charge_split'][1]}  match={res['charge_split'][0] == res['charge_split'][1]}")
    assert res['pure'] and res['t1'][0] == res['t1'][1] and res['t2'][0] == res['t2'][1] \
        and res['t3'][0] == res['t3'][1] and res['charge_split'][0] == res['charge_split'][1], (r, m, c1name)
    if c1name == 'theta':
        print(f"    c3 shift class size (0 = the shift dies by W0, as the derivation states): {len(res['c3_shift_class'])}")
        assert len(res['c3_shift_class']) == 0, "c3 shift must die by W0 on the discriminator"

print("\n== linear detector probe ==")
r, m = 6, 2
res = pair_check(r, m, ZERO, dict(W_R), ZERO)
chP, chM = res['chP'], res['chM']
G = chM
lhs = chi_pair(chP, G) - chi_pair(chM, G)
wr_g = integral(wedge(W_R, G['2']))
print(f"  chi(E+ (x) G) - chi(E- (x) G) = {lhs};  m*<W_R,ch2(G)> = {m * wr_g};  match={lhs == m * wr_g}")
assert lhs == m * wr_g, "detector identity FAILED"

print("\n== carrier instance check (F, O^r): q(E-)=0 recovers chi(EndF)=8m^2 ==")
# E- = O^r: c2 = 0 ; E+ = "F": c2 = -m W_R => q(F) = -8m ; chi(End E+) - chi(End E-) = 8m^2
resC = pair_check(5, 1, ZERO, ZERO, ZERO)   # c2M = 0 (O^r side), m=1 => c2P = -W_R
print(f"  purity={resC['pure']}; q(E+)={resC['qP']} (expected -8); q(E-)={resC['qM']} (expected 0)")
print(f"  chi(EndE+)-chi(EndE-) = {resC['t3'][0]}  expected {resC['t3'][1]}  match={resC['t3'][0] == resC['t3'][1]}")
assert resC['pure'] and resC['qP'] == -8 and resC['qM'] == 0 and resC['t3'][0] == resC['t3'][1]
print("\nALL CHECKS DONE (every comparison asserted, zero tolerance, no floats)")
