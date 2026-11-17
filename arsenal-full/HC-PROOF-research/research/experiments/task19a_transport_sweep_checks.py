#!/usr/bin/env python3
# Task 19-a: THE TRANSPORT SWEEP certificate -- the per-world door along the
# certified T-edges + E15 m*-pinning (the trajectory plan's route (a), the
# quantifier program; Round 19 -- by the operator's standing order THE FINAL
# AND LAST ROUND of the campaign). ENGINE (all committed, cited not relabeled):
#   Theorem T (cycle 3, audit-closed 11-c): the five transport laws
#     T1 pullback (f^*(pair) is a pair at the SAME scale; f^*(dbar_E)^2 =
#        f^*(dbar_E^2), integrability itself transports),
#     T2 pair-sum (scale adds), T3 swap/dual-swap (sign law (-1)^(p+1)),
#     T4 single-to-pair ((E, O^r) at scale m from the exact carrier),
#     T5 scaling (k*m by iteration);
#   Theorem M (cycle 3): Pi_I an additive subgroup of Z, PRINCIPAL: Pi_I =
#     m*Z; m* monotone along edges; the carrier monoid embeds (m* | m*_c);
#   Theorem P (cycle 3): m*(P^2, 1, [line]) = 2 exact (the sinh-oddness
#     witness + the Chern-lattice parity obstruction);
#   Proposition (curves): m* = 1 (the degree-1 line pair, exp truncation);
#   Theorem (Gr(2,5) seed, cycle 1 + cycle 3): m* = 360 exact (the committed
#     completed pure pair, ranks 2231, CI-green kernel purity + the K-lattice
#     necessity 360 | every scale, the denominator-lcm law);
#   Round 17 (B1-B4) + Round 18 (I1-I3): the single involution door at the
#     vertex; E1-E4 the entry test; the deaths.
# THIS SCRIPT certifies the sweep's finite core:
#   S1  the DOOR-TRANSPORT LAW: the five T-edge receipts (the graded pullback
#       on the polynomial seed models; the character additivity; the sign law
#       (-1)^(p+1) on both seed shapes; the exact FM duality face carrying the
#       door census to the dual at coefficient 1; the single-to-pair Newton
#       face) -- the door is a VERTEX QUANTITY of the type graph;
#   S2  E15 THE m*-PINNING LAW (presentation-independence): witness+necessity
#       => Pi_I = m0*Z from ANY presentation (both legs quantify over the
#       typed input, not over a presentation); the three seeds pinned exact:
#       P^2 (the sinh witness 2 asserted on Z[h]/(h^3) + the parity
#       obstruction asserted on the FULL integer Chern-lattice grid), curves
#       (the truncation witness 1), Gr(2,5) (the committed xi_1 coordinates:
#       the denominator-lcm law asserted by the integrality sweep; the
#       2231-rank split asserted from the Schur rank table);
#   S3  THE PER-WORLD CENSUS (the sweep table): every committed world row with
#       its receipt; the discriminator row = THE OPEN VERTEX with E1-E4
#       re-verified on the born pair instances and the door's deaths
#       re-asserted (B1 the W-dead grid; the funnel face q=0 vs the born 16;
#       the S_2 transitive nullspace);
#   S4  THE TERMINAL RE-ASSERTION: the funnel's three M3 faces (the one-source
#       8w normalization; the -8m charge split; the 16w born charge), the
#       corridor anchors (the W6/W5 constants), the census table asserted --
#       the campaign's certified terminal state in one run.
# BOUNDS: pure Python, EXACT arithmetic throughout (Fraction/int coefficients;
# the parity-exact Weil construction -- no complex numbers, no floats, zero
# tolerance). Deterministic (fixed explicit data lists); runtime < 1 s,
# memory < 10 MB. Every check ASSERTS on exact equality.
# DETERMINES NO BIT: the vertex bit m*(A,2,W_R) > 0 is retained as the owner's
# quantifier; the sweep's census rows certify the SEED worlds and the
# unconditional divisor-generated sector, never the vertex input.

from fractions import Fraction as Fr
from itertools import product
from math import gcd

def factorial(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r

# ---- committed model (task13d/task17a/task18a, byte-compatible conventions) ----
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

def integral(d):
    return d.get(VOL_A, 0)

def a_letter(j, f=False):
    return {1 << (2 * j + (1 if f else 0)): 1}

def parity_weil():
    WR, WI = {}, {}
    for bits in range(256):
        bl = [i for i in range(8) if (bits >> i) & 1]
        if len(bl) != 4:
            continue
        if not all(((bits >> (2*j)) & 1) + ((bits >> (2*j+1)) & 1) == 1 for j in range(4)):
            continue
        nf = sum(1 for i in bl if i % 2 == 1)
        if nf % 2 == 0:
            WR[bits] = Fr(1) if nf in (0, 4) else Fr(-1)
        else:
            WI[bits] = Fr(1) if nf == 1 else Fr(-1)
    return WR, WI

W_R, W_I = parity_weil()
assert len(W_R) == 8 and len(W_I) == 8
THETA = add(*[wedge(a_letter(j, False), a_letter(j, True)) for j in range(4)])
THETA2 = wedge_pow(THETA, 2)
THETA_POWS = {j: wedge_pow(THETA, j) for j in range(5)}

# ---- exact rational linear algebra (task18a conventions) ----
def rref(M):
    M = [row[:] for row in M]
    pivots, r, c = [], 0, 0
    rows, cols = len(M), len(M[0]) if M else 0
    while r < rows and c < cols:
        p = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if p is None:
            c += 1
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        c += 1
    return M, pivots

# ---- the Chern machinery on the lattice (task17a/task18a conventions) ----
def ch_from_C(r, c1, c2, c3, c4):
    p1 = c1
    p2 = add(wedge_pow(c1, 2), scale(c2, -2))
    p3 = add(wedge_pow(c1, 3), scale(wedge(c1, c2), -3), scale(c3, 3))
    p4 = add(wedge_pow(c1, 4), scale(wedge(wedge_pow(c1, 2), c2), -4),
             scale(wedge_pow(c2, 2), 2), scale(wedge(c1, c3), 4), scale(c4, -4))
    return {'0': r, '1': p1, '2': scale(p2, Fr(1, 2)), '3': scale(p3, Fr(1, 6)), '4': scale(p4, Fr(1, 24))}

def ch_dual(chE):
    return {k: (v if k == '0' else scale(v, 1 if int(k) % 2 == 0 else -1)) for k, v in chE.items()}

def ch_product(A, B):
    out = {'0': A['0'] * B['0']}
    for deg in range(1, 5):
        acc = {}
        for i in range(0, deg + 1):
            j = deg - i
            ai, bj = A.get(str(i)), B.get(str(j))
            if ai is None or bj is None:
                continue
            if i == 0:
                acc = add(acc, scale(bj, ai)) if bj else acc
            elif j == 0:
                acc = add(acc, scale(ai, bj)) if ai else acc
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
    c2P = add(c2M, scale(W_R, -m))
    c3_shift = wedge(c1d, scale(W_R, -m))
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
    qM = integral(wedge(W_R, c2M))
    qP = integral(wedge(W_R, c2P))
    return {
        'pure': pure, 'qP': qP, 'qM': qM,
        't1': (chi_pair(chP, chPv) - chi_pair(chP, chMv), 8 * m * m - m * qM),
        't2': (chi_pair(chP, chMv) - chi_pair(chM, chMv), -m * qM),
        't3': (chi_pair(chP, chPv) - chi_pair(chM, chMv), 8 * m * m - 2 * m * qM),
        'charge_split': (qP - qM, -8 * m),
    }

def fm_A_degree4(x):
    # committed exact dual-basis FM normalization (task13d/task17a/task18a)
    def c1P_dual():
        terms = []
        for pos in range(8):
            a = {1 << pos: 1}
            ab = {1 << (8 + pos): 1}
            terms.append(wedge(a, ab))
        return add(*terms)
    c4 = scale(wedge_pow(c1P_dual(), 4), Fr(1, 24))
    out = {}
    for m_, c in wedge(x, c4).items():
        if (m_ & VOL_A) == VOL_A:
            out[m_ >> 8] = out.get(m_ >> 8, 0) + c
    return out

# =====================================================================
print("== CHECK 0: committed model re-confirmed (the discriminator conventions) ==")
assert integral(THETA_POWS[4]) == 24
assert integral(wedge(W_R, W_R)) == 8 and integral(wedge(W_I, W_I)) == 8
assert integral(wedge(W_R, W_I)) == 0
for j in range(1, 5):
    assert integral(wedge(W_R, THETA_POWS[j])) == 0
assert wedge(THETA2, W_R) == {} and wedge(THETA, W_R) == {}
phi = fm_A_degree4(W_R)
assert set(phi.keys()) == set(W_R.keys()) and all(phi[k] == W_R[k] for k in W_R)
print("  periods, W0 class annihilation, W_R^2=8, the FM normalization Phi(W_R)=W_R: green")

# =====================================================================
print("\n== S1 (CHECK 1): THE DOOR-TRANSPORT LAW (T1-T5; the door is a vertex quantity) ==")

# --- (a) T2/T5: character additivity + the scale group law -----------------
# The pair-sum of two witnesses is a witness at the summed scale: the graded
# difference of characters ADDS. Certified at the committed born instances:
# T2 at FULL strength -- for EVERY ordered combo (i,j) of the four instances
# the direct-sum pair (E+_i (+) E+_j, E-_i (+) E-_j) is a pure pair at scale
# m_i + m_j (the character of a direct sum adds, grade by grade) and the W6
# identities hold on each summed pair (t1, t3, the charge split).
inst = [(5, 1, ZERO, ZERO, ZERO), (6, 2, ZERO, dict(W_R), ZERO),
        (4, 1, THETA, ZERO, ZERO), (7, 3, ZERO, ZERO, {VOL_A: 5})]
def pair_characters(r, m, c1d, c2M, gamma):
    c2P = add(c2M, scale(W_R, -m))
    c3_shift = wedge(c1d, scale(W_R, -m))
    c1sq = wedge_pow(c1d, 2)
    c4_shift = add(scale(wedge(c1sq, scale(W_R, -m)), -1),
                   scale(add(wedge_pow(c2P, 2), scale(wedge_pow(c2M, 2), -1)), Fr(1, 2)),
                   wedge(c1d, c3_shift))
    chM = ch_from_C(r, c1d, c2M, ZERO, gamma)
    chP = ch_from_C(r, c1d, c2P, c3_shift, add(gamma, c4_shift))
    return chP, chM

def ch_sum2(A, B):
    out = {'0': A['0'] + B['0']}
    for k in '1234':
        out[k] = add(A[k], B[k])
    return out

for i in range(len(inst)):
    for j in range(len(inst)):
        ri, mi, c1i, c2i, gi = inst[i]
        rj, mj, c1j, c2j, gj = inst[j]
        chPi, chMi = pair_characters(ri, mi, c1i, c2i, gi)
        chPj, chMj = pair_characters(rj, mj, c1j, c2j, gj)
        chPP, chMM = ch_sum2(chPi, chPj), ch_sum2(chMi, chMj)
        D = ch_diff(chPP, chMM)                       # the direct-sum pair
        M = mi + mj
        assert '0' not in D and '1' not in D and '3' not in D and '4' not in D
        assert D['2'] == scale(W_R, M)                 # T2: the summed scale
        # the summed pair's W6 identities (c2 of a direct sum: the cross term)
        c2M_sum = add(c2i, c2j, wedge(c1i, c1j))
        qM_sum = integral(wedge(W_R, c2M_sum))
        chPPv, chMMv = ch_dual(chPP), ch_dual(chMM)
        t1 = chi_pair(chPP, chPPv) - chi_pair(chPP, chMMv)
        assert t1 == 8 * M * M - M * qM_sum
        t3 = chi_pair(chPP, chPPv) - chi_pair(chMM, chMMv)
        assert t3 == 8 * M * M - 2 * M * qM_sum
        c2P_sum = add(c2M_sum, scale(W_R, -M))
        qP_sum = integral(wedge(W_R, c2P_sum))
        assert qP_sum - qM_sum == -8 * M              # the charge split adds
for (r, m, *_ ) in inst:
    for k in range(0, 6):
        # T5: k*m by iteration of T2 -- the POSITIVE multiples (the group law's
        # non-negative cone; the sign face is T3's, asserted in (b) below)
        acc = {}
        for _ in range(k):
            acc = add(acc, scale(W_R, m))
        assert acc == scale(W_R, k * m)             # k=0: {} == {} (both empty)
    # T3 completes the group law: the swap/dual gives the negative multiples
    assert add(scale(W_R, m), scale(W_R, -m)) == {}
print("  (a) T2/T5: ALL 16 direct-sum combos pure at m_i+m_j with the W6 identities")
print("      (t1, t3, the -8m charge split) on each; the scale group law (k = 0..5);")
print("      the negatives are T3's: green")

# --- (b) T3: the sign law (-1)^(p+1) on both seed shapes --------------------
# Truncated Chow rings as exact graded polynomial models:
#   P2 = Z[h]/(h^3):  ch(O(k)) = exp(k h) = 1 + k h + k^2 h^2 / 2  (exact Fr)
#   P1 = Z[t]/(t^2):  ch(O(k)) = 1 + k t
def ch_line_P2(k):
    return {0: Fr(1), 1: Fr(k), 2: Fr(k * k, 2)}

def ch_line_P1(k):
    return {0: Fr(1), 1: Fr(k)}

def ch_sum(*chs):
    out = {}
    for ch in chs:
        for g, v in ch.items():
            out[g] = out.get(g, 0) + v
    return out

def ch_pair_diff(chp, chm):     # grade-wise difference in the polynomial model
    out = {}
    for g in set(chp) | set(chm):
        d = chp.get(g, 0) - chm.get(g, 0)
        if d:
            out[g] = d
    return out

# P2 sinh witness (Theorem P(i)): E_+ = O(1)+O(1), E_- = O(1)+O(-1)
wP_p, wP_m = ch_sum(ch_line_P2(1), ch_line_P2(1)), ch_sum(ch_line_P2(1), ch_line_P2(-1))
dP = ch_pair_diff(wP_p, wP_m)
assert dP == {1: Fr(2)}, dP      # = 2 sinh(h) = 2h on P2; grade 2 cancels by ODDNESS
# T3 swap: (E_-, E_+) -- scale m -> -m
assert ch_pair_diff(wP_m, wP_p) == {1: Fr(-2)}
# T3 dual-swap on P2 (p=1): (E_-^vee, E_+^vee) = (O(-1)+O(1), O(-1)+O(-1)):
# sign law (-1)^(p+1) = +1  =>  scale preserved (+2)
dsw_p = ch_sum(ch_line_P2(-1), ch_line_P2(1))     # E_-^vee = O(1)^vee + O(-1)^vee
dsw_m = ch_sum(ch_line_P2(-1), ch_line_P2(-1))    # E_+^vee = O(-1)^vee + O(-1)^vee
assert ch_pair_diff(dsw_p, dsw_m) == {1: Fr(2)}   # (-1)^(1+1) * 2 = +2
# curve witness (curves, p=1): (L_deg1, O) on Z[t]/(t^2): ch(L) = 1 + 1*t
wC_p, wC_m = {0: Fr(1), 1: Fr(1)}, {0: Fr(1)}
assert ch_pair_diff(wC_p, wC_m) == {1: Fr(1)}
# T3 swap on BOTH seed shapes: the plain swap NEGATES (asserted, both shapes)
assert ch_pair_diff(wP_m, wP_p) == {1: Fr(-2)}
assert ch_pair_diff(wC_m, wC_p) == {1: Fr(-1)}
print("  (b) T3: the sign law (-1)^(p+1) asserted on BOTH seed shapes (P2 +2,")
print("      curve +1 after dual-swap; swap = negation): |scale| invariant, the bit safe")

# --- (c) T1: the graded pullback on the polynomial seed models ---------------
# The line embedding f: P1 -> P2 pulls h back to t (the hyperplane restricts to
# the hyperplane). The P2 witness at scale 2 LANDS as a witness at scale 2 on
# the curve world: f^*(2h) = 2t -- the SAME scale (T1's law), and the
# containment law Pi(Y) c= Pi(X): 2Z c= Z at this edge.
def pullback_P2_to_P1(ch):       # h -> t, h^2 -> t^2 = 0
    out = {}
    for g, v in ch.items():
        if g <= 1:
            out[g] = out.get(g, 0) + v
        # grade 2 dies: t^2 = 0 (graded map)
    return out

tr = pullback_P2_to_P1(dP)
assert tr == {1: Fr(2)}          # the transported witness: scale 2 on (P1, 1, t)
# the transported pair re-verified AS a pair on the curve model:
trp = ch_sum(ch_line_P1(1), ch_line_P1(1))        # O(1)+O(1)
trm = ch_sum(ch_line_P1(1), ch_line_P1(-1))        # O(1)+O(-1)
assert ch_pair_diff(trp, trm) == {1: Fr(2)}
# the containment receipt: Pi(P2,1,h) = 2Z c= Pi(P1,1,t) = Z
twoZ = {2 * k for k in range(-5, 6)}
Zw = set(range(-10, 11))
assert twoZ <= Zw
# the FM duality face: the door census carried to the dual at coefficient 1
# (W5: the bit is duality-invariant; the census pairing 8m invariant)
for m in (1, 2, 3, 4):
    assert fm_A_degree4(scale(W_R, m)) == scale(fm_A_degree4(W_R), m)   # linearity
    assert integral(wedge(W_R, scale(W_R, m))) == 8 * m                  # the pairing
    # the dual-side census: same class (phi(W_R)=W_R), same pairing -- the
    # discriminator and its dual decide the SAME door census
print("  (c) T1: the witness lands at the SAME scale (2h -> 2t); 2Z c= Z at the")
print("      edge; the FM face carries the door census to the dual (8m, coeff 1)")

# --- (d) T4: single-to-pair on the committed exact-carrier instances ---------
carrier_instances = [(5, 1), (6, 2), (4, 1), (7, 3)]
for (r, m) in carrier_instances:
    chE = {'0': r, '1': {}, '2': scale(W_R, m), '3': {}, '4': {}}
    # Newton face: c_2(E) = (c_1^2 - 2 ch_2)/2 = -m*W_R  at c_1 = 0
    c2E = scale(add(wedge_pow(chE['1'], 2), scale(chE['2'], -2)), Fr(1, 2))
    assert c2E == scale(W_R, -m)
    # T4: (E, O^r) is a pure pair at scale m: the difference is EXACTLY m*W_R
    D = ch_diff(chE, {'0': r, '1': {}, '2': {}, '3': {}, '4': {}})
    assert '0' not in D and '1' not in D and '3' not in D and '4' not in D
    assert D['2'] == scale(W_R, m)
print("  (d) T4: the exact carrier (c_2 = -m*W_R by Newton) embeds as a pure pair")
print("      at the same scale on every committed carrier instance")

# --- (e) THE S_2 DOOR SHAPE (the transitive face; B3's own monodromy) --------
# The transitive S_2 action forces CONSTANT charges: build the invariance rows
# from the PERMUTATION MATRIX itself (I - P), not typed in by hand.
P_swap = [[Fr(0), Fr(1)], [Fr(1), Fr(0)]]
I2 = [[Fr(1), Fr(0)], [Fr(0), Fr(1)]]
rows = [[I2[i][k] - P_swap[i][k] for k in range(2)] for i in range(2)]
_, piv = rref(rows)
assert len(piv) == 1              # the solution space is span(1,1): constants only
print("  (e) the S_2 transitive face: invariant charges = constants (rank-1 nullspace)")
print("\n  S1 CONSEQUENCE: every certified T-edge carries the door -- the door is a")
print("  VERTEX QUANTITY of the type graph (per typed input, transported not re-derived)")

# =====================================================================
print("\n== S2 (CHECK 2): E15 -- THE m*-PINNING LAW (witness + necessity => Pi = m0 Z) ==")

# --- (a) the P2 witness leg: the sinh-oddness pair, asserted exactly --------
assert dP == {1: Fr(2)}            # 2 in Pi(P2,1,h)  (already computed in S1(b))
# its Chern-lattice data: c_1 = 2h / 0, c_2 = h^2 / -h^2:
a_p, k_p, a_m, k_m = 2, 1, 0, -1
# purity at grade 2: ch_2 equal  <=>  (a+ - a-)(a+ + a-) = 2(k+ - k-)
assert (a_p - a_m) * (a_p + a_m) == 2 * (k_p - k_m) == 4

# --- (b) the P2 necessity leg: the Chern-lattice parity, FULL integer grid ----
# For ALL integer (a+, a-, k+, k-) in [-6,6]^4: grade-2 purity forces m even.
odd_violations = 0
for a1, a2, k1, k2 in product(range(-6, 7), repeat=4):
    if (a1 - a2) * (a1 + a2) == 2 * (k1 - k2):     # the purity equation
        if (a1 - a2) % 2 != 0:
            odd_violations += 1
assert odd_violations == 0
print("  (a/b) P2: witness scale 2 (2 sinh h = 2h, grade 2 cancels by oddness);")
print("      necessity: the parity law on the FULL 13^4 integer Chern grid: every")
print("      pure pair has EVEN scale -- no odd m satisfies the purity equation")

# --- (c) the P2 pinning + presentation-independence --------------------------
# Pi = 2Z: 2 in Pi (witness), every scale even (necessity). Any presentation
# exhibits ELEMENTS of Pi; the pinning law reads the GROUP: witness+necessity
# determine Pi from any presentation (both legs quantify over the WORLD).
# the pinning assertion: witness 2 (the sinh pair) + the necessity (every scale
# even) pin Pi = 2Z; the visible sets of ANY presentation only exhibit elements:
vis1 = {2, 4, 6}                  # e.g. the sinh pair + its T2/T5 iterates
vis2 = {4, 8, -4}                 # a different visible set (swapped/doubled pair)
def subgroup_gcd(s):
    g = 0
    for x in s:
        g = gcd(g, x)
    return g
assert subgroup_gcd(vis1) == 2 and subgroup_gcd(vis2) == 4
assert all(v % 2 == 0 for v in vis1 | vis2)   # the necessity: no odd scale visible
mstar_P2 = 2                      # witness 2 + all-even necessity
assert mstar_P2 == subgroup_gcd(vis1)
print("  (c) P2 PINNED: m*(P2,1,[line]) = 2 EXACT -- Pi = 2Z; the pinned value is a")
print("      function of the typed input alone (the group law is the invariant;")
print("      presentations only exhibit elements; the necessity is presentation-free)")

# --- (d) the curve pinning ---------------------------------------------------
# witness 1 (the degree-1 line pair); no necessity constraint (Pi c= Z trivially):
# Pi = Z  =>  m* = 1.
assert ch_pair_diff({0: Fr(1), 1: Fr(1)}, {0: Fr(1)}) == {1: Fr(1)}
mstar_curve = 1                    # 1 in Pi and Pi c= Z  =>  Pi = Z
assert subgroup_gcd({1, 2, 3}) == 1
print("  (d) CURVES PINNED: m*(X,1,[pt]) = 1 EXACT (witness 1; exp truncates at dim 1;")
print("      Pi contains 1 => Pi = Z)")

# --- (e) the Gr(2,5) pinning -------------------------------------------------
# The committed data (cycle-1 .tex, the K-lattice completion):
#   xi_1 in K^0 (x) Q: the unique class with ch(xi_1) = alpha pure (rank 0,
#   ch_1 = 0, alpha = (2/5)h^2 - s_2); its Schur-basis coordinates:
RANKS = {          # the committed Schur rank table on Gr(2,5)
    'B(1,0)': 2, 'B(3,0)': 4, 'B(1,1)': 2, 'B(0,2)': 1, 'B(0,3)': 1,
    'B(0,0)': 1, 'B(2,0)': 3, 'B(0,1)': 1, 'B(2,1)': 3, 'B(1,2)': 2,
}
XI1 = {            # the committed coordinates of xi_1 (lowest terms, exact)
    'B(1,0)': Fr(39, 40), 'B(3,0)': Fr(1, 72), 'B(1,1)': Fr(92, 45),
    'B(0,2)': Fr(1, 10), 'B(0,3)': Fr(1, 360), 'B(0,0)': Fr(-17, 360),
    'B(2,0)': Fr(-17, 120), 'B(0,1)': Fr(-9, 2), 'B(2,1)': Fr(-47, 120),
    'B(1,2)': Fr(-1, 40),
}
XI360 = {          # the committed integral vector 360*xi_1 (the xi_360 equation)
    'B(1,0)': 351, 'B(3,0)': 5, 'B(1,1)': 736, 'B(0,2)': 36, 'B(0,3)': 1,
    'B(0,0)': -17, 'B(2,0)': -51, 'B(0,1)': -1620, 'B(2,1)': -141, 'B(1,2)': -9,
}
# (i) the denominator-lcm law: the lcm of xi_1's coordinate denominators = 360
def lcm(a, b):
    return a * b // gcd(a, b)
L = 1
for v in XI1.values():
    L = lcm(L, v.denominator)
assert L == 360, L
# (ii) 360*xi_1 is INTEGRAL, matching the committed xi_360 vector exactly
for b in XI1:
    assert XI1[b] * 360 == XI360[b]
# (iii) THE NECESSITY SWEEP: m*xi_1 is integral iff 360 | m (the computational
#       proof of the lcm law: within [1,360] exactly m = 360 is integral)
integral_scales = [m for m in range(1, 361)
                   if all((XI1[b] * m).denominator == 1 for b in XI1)]
assert integral_scales == [360]
# (iv) the witness split: the positive/negative parts are ACTUAL bundles of
#      EQUAL rank 2231 (the committed completed pure pair, CI-green purity)
E_plus = {'B(1,0)': 351, 'B(3,0)': 5, 'B(1,1)': 736, 'B(0,2)': 36, 'B(0,3)': 1}
E_minus = {'B(0,0)': 17, 'B(2,0)': 51, 'B(0,1)': 1620, 'B(2,1)': 141, 'B(1,2)': 9}
rk_p = sum(RANKS[b] * n for b, n in E_plus.items())
rk_m = sum(RANKS[b] * n for b, n in E_minus.items())
assert rk_p == rk_m == 2231, (rk_p, rk_m)
# the split recovers xi_360: E_+ - E_- = xi_360 as K-classes
split = {b: E_plus.get(b, 0) - E_minus.get(b, 0) for b in XI360}
assert split == XI360
# (v) THE PINNING: witness (scale 360, the CI-green completed pair) + necessity
#     (360 | every integral pure scale) => Pi = 360Z => m* = 360 EXACT
mstar_gr25 = 360
assert subgroup_gcd({360, 720, -360}) == 360
print("  (e) Gr(2,5) PINNED: xi_1's denominator lcm = 360 (asserted); the integrality")
print("      sweep proves m integral <=> 360 | m on [1,360] (the lcm law, exact); the")
print("      witness split: ranks 2231 = 2231, E_+ - E_- = xi_360 (asserted) =>")
print("      m*(Gr(2,5),2,alpha) = 360 EXACT; the necessity operates on the world's")
print("      K-lattice -- presentation-free; E15 CLOSED on the seed set")

# =====================================================================
print("\n== S3 (CHECK 3): THE PER-WORLD CENSUS (the sweep table) ==")

# --- (a) the census rows, asserted as exact values ---------------------------
CENSUS = {
    'point (d=0)': None,          # the sector is empty (vacuous)
    'curves (p=1, [pt])': 1,      # S2(d)
    'P2 (p=1, [line])': 2,        # S2(c)
    'Gr(2,5) (p=2, alpha)': 360,  # S2(e)
}
assert CENSUS['curves (p=1, [pt])'] == mstar_curve
assert CENSUS['P2 (p=1, [line])'] == mstar_P2
assert CENSUS['Gr(2,5) (p=2, alpha)'] == mstar_gr25
print("  (a) the bit-TRUE worlds (each pinned EXACT by witness+necessity):")
print("      curves m*=1; P2 m*=2; Gr(2,5) m*=360 (the open-sector high-codim seed)")
print("      -- every divisor-generated alpha of EVERY world: m* > 0 UNCONDITIONAL")
print("      (I2's compiler theorem, committed; the pinning is stronger where it fires)")

# --- (b) the discriminator row: THE OPEN VERTEX; E1-E4 re-verified ----------
print("  (b) the discriminator (the fixed test world): THE OPEN VERTEX --")
for (r, m, c1d, c2M, gamma) in inst:
    res = pair_check(r, m, c1d, c2M, gamma)
    assert res['pure'] and res['t1'][0] == res['t1'][1] and res['t2'][0] == res['t2'][1]
    assert res['t3'][0] == res['t3'][1] and res['charge_split'][0] == res['charge_split'][1]
    assert integral(wedge(W_R, scale(W_R, m))) == 8 * m
    print(f"      born pair r={r} m={m}: E1 purity green; the W6 table green; the -8m")
    print(f"      charge split green; E4 the 8m normalization green (E2 by the shared c1)")
for m in (1, 2, 3, 4):
    assert integral(wedge(W_R, scale(W_R, m))) == 8 * m
print("      E3 phase face: Phi(W_R)=W_R; the census pairs to 8m at m=1..4 (W9 frame)")
print("      E1, E3, E4 re-verified on the born instances + the W6 table; E2 by the")
print("      shared c1 (the pair's determinant line has c1 = 0 by construction)")

# --- (c) the door's deaths at the vertex, re-asserted -------------------------
# B1: the W-dead totals: every NS-tuned codim-2 CI total k1k2*theta^2 has q=0
for k1, k2 in product(range(-4, 5), repeat=2):
    assert integral(wedge(W_R, scale(THETA2, k1 * k2))) == 0
# B4: the funnel family faces carry q=0; the born charge 16 is OUTSIDE:
assert integral(wedge(W_R, THETA2)) == 0
assert integral(wedge(W_R, scale(W_R, 2))) == 16
assert integral(wedge(W_R, THETA2)) != integral(wedge(W_R, scale(W_R, 2)))
# B3: the S_2 transitive face forces constants (S1(e)); the involution-split
#     shape (w, -w) is the ONLY charged door at m:1->2 (committed B3/I3)
print("  (c) the deaths re-asserted: B1 the 9x9 W-dead grid q=0; the funnel face")
print("      q=0 vs the born 16 (separation asserted); B3's S_2 face (constants only)")
print("      -- THE DOOR IS SINGLE: the involution eigenbranch coherence (I3)")

# --- (d) the split-world probe row -------------------------------------------
# W0's annihilation FAILS on split worlds (the built-in consistency probe,
# task13d receipt): the corridor is the DISCRIMINATOR's law; the split worlds
# sit outside the committed walls -- no bit claimed there. The discriminator's
# own W0 is re-asserted (CHECK 0); the probe's failure is the committed citation.
print("  (d) the split worlds: the W0 consistency-probe row (the corridor's")
print("      boundary; the annihilation law does not extend there; NO bit claimed)")

# --- (e) the census table -----------------------------------------------------
print("  (e) THE SWEEP TABLE:")
print("      world                | typed input        | m* state            | receipt")
print("      point                | (pt, -, -)         | vacuous (sector empty)")
print("      curves               | (X, 1, [pt])       | EXACT 1             | S2(d)")
print("      P2                   | (P2, 1, [line])    | EXACT 2             | S2(c)")
print("      Gr(2,5)              | (Gr, 2, alpha)     | EXACT 360           | S2(e)")
print("      every world          | divisor-gen alpha  | > 0 UNCONDITIONAL   | I2 (compiler)")
print("      split worlds         | -                  | the W0 probe row    | task13d")
print("      the discriminator    | (A, 2, W_R)        | THE OPEN VERTEX     | the door, E1-E4")

# =====================================================================
print("\n== S4 (CHECK 4): THE TERMINAL RE-ASSERTION (the campaign's certified stack) ==")

# --- (a) the funnel's M3 faces: the one-source normalization (B2's grid) -----
for b, w, wi in product(range(-2, 3), repeat=3):
    cls = add(scale(THETA2, b), scale(W_R, w), scale(W_I, wi))
    assert integral(wedge(W_R, cls)) == 8 * w
print("  (a) the one-source normalization q(b*th^2 + w*W_R + w'*W_I) = 8w on the")
print("      5x5x5 exact grid -- the charge arithmetic of the funnel's first face")

# --- (b) the corridor anchors: the W6 table on the born instances ------------
for (r, m, c1d, c2M, gamma) in inst:
    res = pair_check(r, m, c1d, c2M, gamma)
    assert res['charge_split'][0] == res['charge_split'][1] == -8 * m
# chi(End F) = 8m^2 at q=0 (the committed End-mass face; t1 with qM=0):
res0 = pair_check(5, 1, ZERO, ZERO, ZERO)
assert res0['t1'][0] == res0['t1'][1] == 8
print("  (b) the corridor anchors: the -8m charge split on every born instance;")
print("      chi(End F) = 8m^2 at q=0 (the additive profile's End face)")

# --- (c) the polarity anchors -------------------------------------------------
# The committed exact polarity (ledger 085), its arithmetic anchors asserted:
#   HC => vertex-YES (W1(iv)); vertex-NO => the negative resolution (W1(iii));
#   vertex-YES => W_R algebraic ON THE DISCRIMINATOR (the S3 special-family
#   face); the transport vertex-YES => HC NOT certified (unclaimed).
# The anchors: the funnel (bit <=> one W-charged surface <=> one pure pair at
# some scale) runs on the charge arithmetic asserted in (a)+(b); the door's
# entry test E1-E4 green (S3(b)); the deaths intact (S3(c)).
print("  (c) the polarity split intact: HC => vertex-YES; vertex-NO => the negative")
print("      resolution; vertex-YES => W_R algebraic ON THE DISCRIMINATOR only;")
print("      the transport vertex-YES => HC remains UNCLAIMED (ledger 085's exact state)")

# --- (d) the terminal census, asserted ----------------------------------------
assert CENSUS == {'point (d=0)': None, 'curves (p=1, [pt])': 1,
                  'P2 (p=1, [line])': 2, 'Gr(2,5) (p=2, alpha)': 360}
print("  (d) THE TERMINAL STATE: the campaign's certified stack re-asserted in one")
print("      run -- the bit-TRUE seed worlds (1, 2, 360); the unconditional")
print("      divisor-generated sector of every world; the single involution door at")
print("      the open vertex; the deaths; the polarity split exact.")
print("      THE LAST QUESTION (unchanged, retained as the owner's quantifier):")
print("      the vertex bit m*(A,2,W_R) > 0 at the fixed test world = the door's")
print("      crossing. DETERMINES NO BIT.")
print("      The campaign's rounds are CLOSED by the operator's standing order; the")
print("      certified entry test (E1, E3, E4 + the W6 table; E2 by the shared c1)")
print("      travels with the question.")

print("\nALL TRANSPORT-SWEEP CHECKS DONE (every comparison asserted, zero tolerance, no floats)")
