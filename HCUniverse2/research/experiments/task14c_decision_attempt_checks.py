#!/usr/bin/env python3
# Task 14-c: the decision-attempt verification layer.
# (1) Lemma W7 sector rigidity of the cohomological FM transform (bitmask model):
#     block-union monomials complement to block-union monomials (NS-sector rigid),
#     Weil words complement to Weil words (W-sector rigid; parity preserved: even to
#     even, odd to odd), T-words to T-words; the exact fm(theta^2) = theta^2-dual
#     equality (coefficient 1); hence the transform preserves the NS / W / T sector
#     decomposition (the five-piece dimension audit lives in the dossier).
# (2) The (m, q)-consistency grid: the W6 additive table (purity + charge split +
#     the three mixed-End identities) is consistent at EVERY grid point
#     m in 1..4, c2(E-) = a*W_R (a in 0..3), c1 in {0, theta, 2theta},
#     gamma in {0, vol}  ->  4*4*3*2 = 96 instances: no additive contradiction
#     anywhere on the grid (the corridor-symmetry certificate).
# BOUNDS: pure Python, exact Fraction arithmetic, <= 2^10 monomial ops per instance,
# 96 instances, runtime < 5 s, memory < 20 MB. No floats anywhere.

from fractions import Fraction as Fr

VOL = 255

def bitlist(m):
    return [i for i in range(8) if (m >> i) & 1]

def inv_pairs(l1, l2):
    return sum(1 for a in l1 for b in l2 if a > b)

def wsign(l1, l2):
    return Fr(1) if inv_pairs(l1, l2) % 2 == 0 else Fr(-1)

def norm_cl(c):
    acc = []
    for coef, mask in c:
        if coef == 0:
            continue
        placed = False
        for i, (qc, qm) in enumerate(acc):
            if qm == mask:
                acc[i] = (qc + coef, mask)
                placed = True
                break
            if mask < qm:
                acc.insert(i, (coef, mask))
                placed = True
                break
        if not placed:
            acc.append((coef, mask))
    return [(qc, qm) for qc, qm in acc if qc != 0]

def wedge_cl(c1, c2):
    out = []
    for a, ma in c1:
        for b, mb in c2:
            if ma & mb:
                continue
            out.append((a * b * wsign(bitlist(ma), bitlist(mb)), ma | mb))
    return norm_cl(out)

def smul_cl(q, c):
    return norm_cl([(q * a, m) for a, m in c])

def add_cl(*cs):
    out = []
    for c in cs:
        out.extend(c)
    return norm_cl(out)

def pow_cl(c, k):
    r = [(Fr(1), 0)]
    for _ in range(k):
        r = wedge_cl(r, c)
    return r

def int_cl(c):
    for a, m in c:
        if m == VOL:
            return a
    return Fr(0)

def fm_cl(x):
    return norm_cl([(a * wsign(bitlist(m), bitlist(255 ^ m)), 255 ^ m) for a, m in x])

WRcl = [(Fr(1), 85), (Fr(-1), 90), (Fr(-1), 102), (Fr(-1), 105),
        (Fr(-1), 150), (Fr(-1), 153), (Fr(-1), 165), (Fr(1), 170)]
WIcl = [(Fr(1), 86), (Fr(1), 89), (Fr(1), 101), (Fr(-1), 106),
        (Fr(1), 149), (Fr(-1), 154), (Fr(-1), 166), (Fr(-1), 169)]
THETAd = [(Fr(1), 3), (Fr(1), 12), (Fr(1), 48), (Fr(1), 192)]

# ---------- (1) Lemma W7: sector rigidity of the FM transform (degree 4) ----------
# The 70 degree-4 monomials = 4-subsets of positions 0..7.
# NS-sector model basis: the six pair-union words (blocks {a,b}), masks of u_ab.
# W-sector model basis: the 16 one-letter-per-block words (8 even = W_R words, 8 odd = W_I words).
# T-sector: the remaining 70 - 6 - 16 = 48 words.
from itertools import combinations

all_words = [sum(1 << i for i in w) for w in combinations(range(8), 4)]
assert len(all_words) == 70

def blocks_of(mask):
    bs = []
    for j in range(4):
        pair = (mask >> (2 * j)) & 3
        bs.append(pair)  # 0 = empty, 1 = letter 2j only, 2 = letter 2j+1 only, 3 = both
    return tuple(bs)

pair_union_words = [m for m in all_words if all(b in (0, 3) for b in blocks_of(m))]
weil_words = [m for m in all_words if all(b in (1, 2) for b in blocks_of(m))]
t_words = [m for m in all_words if m not in pair_union_words and m not in weil_words]
print(f"== W7 sector census: NS-union words = {len(pair_union_words)} (want 6), "
      f"Weil words = {len(weil_words)} (want 16), T words = {len(t_words)} (want 48) ==")
assert len(pair_union_words) == 6 and len(weil_words) == 16 and len(t_words) == 48

def parity_of(mask):
    # number of f-letters (odd positions) among the one-letter-per-block choices
    return sum(1 for j in range(4) if ((mask >> (2 * j + 1)) & 1) == 1)

ok_ns, ok_w_even, ok_w_odd, ok_t = True, True, True, True
for m in pair_union_words:
    cm = 255 ^ m
    ok_ns = ok_ns and (cm in pair_union_words)
for m in weil_words:
    cm = 255 ^ m
    if parity_of(m) % 2 == 0:
        ok_w_even = ok_w_even and (cm in weil_words and parity_of(cm) % 2 == 0)
    else:
        ok_w_odd = ok_w_odd and (cm in weil_words and parity_of(cm) % 2 == 1)
for m in t_words:
    cm = 255 ^ m
    ok_t = ok_t and (cm in t_words)
print(f"  complement of NS-union word is NS-union: {ok_ns}")
print(f"  complement of even Weil word is even Weil: {ok_w_even}")
print(f"  complement of odd Weil word is odd Weil: {ok_w_odd}")
print(f"  complement of T word is T word: {ok_t}")
assert ok_ns and ok_w_even and ok_w_odd and ok_t

# class-level W7: fm of the NS-sector generator theta^2 stays in the NS-sector span
t2 = pow_cl(THETAd, 2)
fm_t2 = fm_cl(t2)
ns_span = [(Fr(1), m) for m in sorted(pair_union_words)]
def in_span_of(cls, basis_masks):
    return all(m in basis_masks for a, m in cls)
print(f"  fm(theta^2) in NS-span: {in_span_of(fm_t2, pair_union_words)} (coeffs: {fm_t2})")
assert in_span_of(fm_t2, pair_union_words)
print(f"  fm(theta^2) == theta^2 EXACTLY (coefficient 1 onto the dual NS line): {fm_t2 == t2}")
assert fm_t2 == t2, "fm(theta^2) must equal the dual theta^2 exactly"
print(f"  fm(W_R) = W_R and fm(W_I) = W_I: {fm_cl(WRcl) == WRcl and fm_cl(WIcl) == WIcl}")
assert fm_cl(WRcl) == WRcl and fm_cl(WIcl) == WIcl

# ---------- (2) the (m, q)-consistency grid ----------
def ch2_of(c1, c2):
    return smul_cl(Fr(1, 2), add_cl(pow_cl(c1, 2), smul_cl(Fr(-2), c2)))

def ch3_of(c1, c2, c3):
    return smul_cl(Fr(1, 6), add_cl(add_cl(pow_cl(c1, 3), smul_cl(Fr(-3), wedge_cl(c1, c2))), smul_cl(Fr(3), c3)))

def ch4_of(c1, c2, c3, c4):
    return smul_cl(Fr(1, 24), add_cl(add_cl(add_cl(add_cl(
        pow_cl(c1, 4), smul_cl(Fr(-4), wedge_cl(pow_cl(c1, 2), c2))),
        smul_cl(Fr(2), pow_cl(c2, 2))), smul_cl(Fr(4), wedge_cl(c1, c3))), smul_cl(Fr(-4), c4)))

def pair_c2p(m, c2m):
    return add_cl(c2m, smul_cl(Fr(-m), WRcl))

def pair_c3shift(c1, m):
    return wedge_cl(c1, smul_cl(Fr(-m), WRcl))

def pair_c4shift(c1, c2m, m):
    return add_cl(smul_cl(Fr(-1), wedge_cl(pow_cl(c1, 2), smul_cl(Fr(-m), WRcl))),
                  add_cl(smul_cl(Fr(1, 2), add_cl(pow_cl(pair_c2p(m, c2m), 2), smul_cl(Fr(-1), pow_cl(c2m, 2)))),
                         wedge_cl(c1, pair_c3shift(c1, m))))

def ch_pair(r, c1, c2, c3, c4):
    return {'r': Fr(r), '1': c1, '2': ch2_of(c1, c2), '3': ch3_of(c1, c2, c3), '4': ch4_of(c1, c2, c3, c4)}

def ch_dual(x):
    return {'r': x['r'], '1': smul_cl(Fr(-1), x['1']), '2': x['2'], '3': smul_cl(Fr(-1), x['3']), '4': x['4']}

def chi_pp(x, y):
    prod4 = add_cl(smul_cl(y['r'], x['4']), add_cl(smul_cl(x['r'], y['4']),
                  add_cl(wedge_cl(x['1'], y['3']), add_cl(wedge_cl(x['2'], y['2']), wedge_cl(x['3'], y['1'])))))
    return int_cl(prod4)

ZERO = []

print("\n== (m,q)-consistency grid: 4*4*3*2 = 96 instances ==")
count, bad = 0, 0
for m in (1, 2, 3, 4):
    for a in (0, 1, 2, 3):
        c2m = smul_cl(Fr(a), WRcl)
        for c1 in (ZERO, THETAd, smul_cl(2, THETAd)):
            for gamma in (ZERO, [(Fr(1), VOL)]):
                r = 5
                ep = ch_pair(r, c1, pair_c2p(m, c2m), pair_c3shift(c1, m), add_cl(gamma, pair_c4shift(c1, c2m, m)))
                em = ch_pair(r, c1, c2m, ZERO, gamma)
                d2 = add_cl(ep['2'], smul_cl(Fr(-1), em['2']))
                d3 = add_cl(ep['3'], smul_cl(Fr(-1), em['3']))
                d4 = add_cl(ep['4'], smul_cl(Fr(-1), em['4']))
                qP = int_cl(wedge_cl(WRcl, pair_c2p(m, c2m)))
                qM = int_cl(wedge_cl(WRcl, c2m))
                chi_endp = chi_pp(ep, ch_dual(ep))
                chi_endm = chi_pp(em, ch_dual(em))
                chi_pxmv = chi_pp(ep, ch_dual(em))
                good = (d2 == smul_cl(Fr(m), WRcl) and d3 == [] and d4 == []
                        and qP - qM == -8 * m
                        and chi_endp - chi_pxmv == 8 * m * m - m * qM
                        and chi_pxmv - chi_endm == -m * qM
                        and chi_endp - chi_endm == 8 * m * m - 2 * m * qM)
                count += 1
                if not good:
                    bad += 1
                    print(f"  FAIL at m={m}, a={a}, c1={'x' if c1 else '0'}, gamma={bool(gamma)}")
print(f"  grid instances checked: {count}; failures: {bad}")
assert bad == 0 and count == 96

print("\n== the twist-preservation check (REAL exponential twist, k enters the computation) ==")
# ch(E (x) O(k Theta)) = ch(E) * e^{k*theta}: the twisted grades are
#   ch_g(E) + ch_{g-1}(E)*(k theta) + ch_{g-2}(E)*(k theta)^2/2 + ... (exact Fractions).
def twist_grades(x, k):
    kt = smul_cl(Fr(k), THETAd)
    kt2 = smul_cl(Fr(1, 2), pow_cl(kt, 2))
    kt3 = smul_cl(Fr(1, 6), pow_cl(kt, 3))
    return {
        'r': x['r'],
        '1': add_cl(x['1'], smul_cl(x['r'], kt)),
        '2': add_cl(add_cl(x['2'], wedge_cl(x['1'], kt)), smul_cl(x['r'], kt2)),
        '3': add_cl(add_cl(add_cl(x['3'], wedge_cl(x['2'], kt)), wedge_cl(x['1'], kt2)), smul_cl(x['r'], kt3)),
    }
twist_failures = 0
twist_configs = 0
for m in (1, 3):
    ep = ch_pair(4, THETAd, pair_c2p(m, WRcl), pair_c3shift(THETAd, m), pair_c4shift(THETAd, WRcl, m))
    em = ch_pair(4, THETAd, WRcl, ZERO, ZERO)
    for k in range(-3, 6):
        twist_configs += 1
        tp, tm = twist_grades(ep, k), twist_grades(em, k)
        d2t = add_cl(tp['2'], smul_cl(Fr(-1), tm['2']))
        d3t = add_cl(tp['3'], smul_cl(Fr(-1), tm['3']))
        ok2 = d2t == smul_cl(Fr(m), WRcl)   # grade-2 difference still m*W_R
        ok3 = d3t == []                      # grade-3 difference still zero (W0 kills W_R AND theta)
        if not (ok2 and ok3):
            twist_failures += 1
            print(f"  FAIL m={m}, k={k}: grade2={ok2} grade3={ok3}")
        assert ok2 and ok3, f"twist purity FAILED at m={m}, k={k}"
    print(f"  m={m}: twisted purity (grades 2 and 3) holds for every k in -3..5")
print(f"  twist-preservation: {twist_configs} twisted configurations, {twist_failures} failures")
assert twist_failures == 0

print("\nALL DECISION-ATTEMPT CHECKS GREEN.")
print("W7 sector rigidity: verified in the model (complements preserve NS / W-even / W-odd / T).")
print("(m,q) grid: the additive table is consistent at every checked point - no additive contradiction.")
