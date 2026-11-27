#!/usr/bin/env python3
# Task 14-a: Lean-DATA pre-verification mirror (the bitmask exterior model).
# Verifies EVERY literal that GSTPairChannelWallsCertificate.lean will decide:
#   W_R / W_I / theta class tables (masks + signs), W0 class annihilation,
#   period constants, FM normalization + round trips, the four synthetic pair
#   instances (purity grades 2/3/4, charge split, mixed-End table t1/t2/t3),
#   the carrier instance, the linear-detector instance.
# BOUNDS: pure Python, exact Fraction arithmetic, <= 2^17 monomial operations,
# runtime < 1s, memory < 10MB. No floats anywhere.

from fractions import Fraction as Fr

# ---- the Lean bitmask model, mirrored exactly ----
# Letters at positions 0..7 = (e1,f1,e2,f2,e3,f3,e4,f4); block j = {2j, 2j+1}.
# A class = list of (coeff : Fraction, mask : int); mask = 8-bit monomial word.
VOL = 255

def bitlist(m):
    return [i for i in range(8) if (m >> i) & 1]

def inv_pairs(l1, l2):
    return sum(1 for a in l1 for b in l2 if a > b)

def wsign(l1, l2):
    return Fr(1) if inv_pairs(l1, l2) % 2 == 0 else Fr(-1)

def norm_cl(c):
    acc = []  # sorted by mask, merged coefficients
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
    # transform of a degree-4 monomial: coeff * wsign(l, l^c) on the complement mask
    return norm_cl([(a * wsign(bitlist(m), bitlist(255 ^ m)), 255 ^ m) for a, m in x])

# ---- DATA tables (the literals the Lean file will carry) ----
# W_R = Re(Omega), Omega = wedge_{j=0..3}(e_j + i f_j); monomial sign = Re(i^#f),
# so +1 for #f in {0,4}, -1 for #f = 2. Ascending masks.
WRcl = [(Fr(1), 85), (Fr(-1), 90), (Fr(-1), 102), (Fr(-1), 105),
        (Fr(-1), 150), (Fr(-1), 153), (Fr(-1), 165), (Fr(1), 170)]
# W_I = Im(Omega): +1 for #f = 1, -1 for #f = 3. Ascending masks.
WIcl = [(Fr(1), 86), (Fr(1), 89), (Fr(1), 101), (Fr(-1), 106),
        (Fr(1), 149), (Fr(-1), 154), (Fr(-1), 166), (Fr(-1), 169)]
# theta = sum of the four pair-words e_j f_j (masks 3, 12, 48, 192).
THETAd = [(Fr(1), 3), (Fr(1), 12), (Fr(1), 48), (Fr(1), 192)]

# ---- independent reconstruction of W_R / W_I from the exterior expansion ----
def letter_mask(j, f):
    return 1 << (2 * j + (1 if f else 0))

def rebuild(parity):
    # accumulate (coeff = Re/Im part, mask) with coeff = sign^(#f) via exact integer-complex
    cls = [(complex(1, 0), 0)]
    for j in range(4):
        nxt = []
        for coef, mask in cls:
            nxt.append((coef * 1, mask | letter_mask(j, False)))
            nxt.append((coef * 1j, mask | letter_mask(j, True)))
        # normalize by mask summing complex coeffs
        acc = {}
        for coef, mask in nxt:
            acc[mask] = acc.get(mask, 0) + coef
        cls = [(c, m) for m, c in acc.items() if c != 0]
    out = []
    for c, m in cls:
        if parity == 're':
            if c.real != 0:
                out.append((Fr(c.real), m))
        else:
            if c.imag != 0:
                out.append((Fr(c.imag), m))
    return norm_cl(out)

WR_re = rebuild('re')
WI_im = rebuild('im')
print("== DATA table check (literal lists vs independent reconstruction) ==")
print("  WRcl == Re(Omega):", WRcl == WR_re)
print("  WIcl == Im(Omega):", WIcl == WI_im)
assert WRcl == WR_re, "W_R literal table WRONG"
assert WIcl == WI_im, "W_I literal table WRONG"

print("\n== W0: class annihilation (theta^j ^ W = the zero class) ==")
for j in (1, 2, 3):
    w = wedge_cl(pow_cl(THETAd, j), WRcl)
    print(f"  theta^{j} ^ W_R = [] : {w == []}")
    assert w == []
    wi = wedge_cl(pow_cl(THETAd, j), WIcl)
    print(f"  theta^{j} ^ W_I = [] : {wi == []}")
    assert wi == []

print("\n== period constants (re-confirm the committed greens in the bitmask model) ==")
t4 = int_cl(pow_cl(THETAd, 4))
wr2 = int_cl(wedge_cl(WRcl, WRcl))
wi2 = int_cl(wedge_cl(WIcl, WIcl))
wrwi = int_cl(wedge_cl(WRcl, WIcl))
oom = int_cl(add_cl(wedge_cl(WRcl, WRcl), wedge_cl(WIcl, WIcl)))
print(f"  int theta^4 = {t4} (want 24)")
print(f"  int W_R^2   = {wr2} (want 8)")
print(f"  int W_I^2   = {wi2} (want 8)")
print(f"  int W_R W_I = {wrwi} (want 0)")
print(f"  int Om OmB  = {oom} (want 16)  [Omega OmegaBar = W_R^2 + W_I^2, cross term 0]")
assert t4 == 24 and wr2 == 8 and wi2 == 8 and wrwi == 0 and oom == 16
for j in (1, 2, 3, 4):
    v = int_cl(wedge_cl(WRcl, pow_cl(THETAd, j)))
    print(f"  int W_R theta^{j} = {v}")
    assert v == 0

print("\n== FM normalization + round trips (fmCl) ==")
pR = fm_cl(WRcl)
pI = fm_cl(WIcl)
print("  fm(W_R) == W_R (i.e. Phi_hat(W_R) = W_R-dual, coefficient 1):", pR == WRcl)
print("  fm(W_I) == W_I:", pI == WIcl)
print("  fm(fm(W_R)) == W_R:", fm_cl(pR) == WRcl)
print("  fm(fm(W_I)) == W_I:", fm_cl(pI) == WIcl)
assert pR == WRcl and pI == WIcl and fm_cl(pR) == WRcl and fm_cl(pI) == WIcl

# ---- the pair construction (mirrors task13d pair_check) ----
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

def instance(r, m, c1, c2m, gamma):
    eplus = ch_pair(r, c1, pair_c2p(m, c2m), pair_c3shift(c1, m), add_cl(gamma, pair_c4shift(c1, c2m, m)))
    eminus = ch_pair(r, c1, c2m, ZERO, gamma)
    qP = int_cl(wedge_cl(WRcl, pair_c2p(m, c2m)))
    qM = int_cl(wedge_cl(WRcl, c2m))
    chi_endp = chi_pp(eplus, ch_dual(eplus))
    chi_endm = chi_pp(eminus, ch_dual(eminus))
    chi_pxmv = chi_pp(eplus, ch_dual(eminus))
    d2 = add_cl(eplus['2'], smul_cl(Fr(-1), eminus['2']))
    d3 = add_cl(eplus['3'], smul_cl(Fr(-1), eminus['3']))
    d4 = add_cl(eplus['4'], smul_cl(Fr(-1), eminus['4']))
    return {
        'p2': d2 == smul_cl(Fr(m), WRcl),
        'p3': d3 == [], 'p4': d4 == [],
        'split': (qP - qM, -8 * m),
        't1': (chi_endp - chi_pxmv, 8 * m * m - m * qM),
        't2': (chi_pxmv - chi_endm, -m * qM),
        't3': (chi_endp - chi_endm, 8 * m * m - 2 * m * qM),
        'qP': qP, 'qM': qM,
    }

print("\n== W6 synthetic instances (purity + charge split + mixed-End table) ==")
cases = [("I1", 3, 1, ZERO, WRcl, ZERO), ("I2", 5, 2, ZERO, WRcl, ZERO),
         ("I3", 4, 1, THETAd, WRcl, ZERO), ("I4", 7, 3, THETAd, WRcl, [(Fr(5), VOL)])]
allok = True
for name, r, m, c1, c2m, gamma in cases:
    res = instance(r, m, c1, c2m, gamma)
    ok = (res['p2'] and res['p3'] and res['p4']
          and res['split'][0] == res['split'][1]
          and res['t1'][0] == res['t1'][1] and res['t2'][0] == res['t2'][1] and res['t3'][0] == res['t3'][1])
    allok = allok and ok
    print(f"  {name} (r={r}, m={m}, c1={'theta' if c1 else '0'}, gamma={gamma if gamma else '0'}): "
          f"pure={res['p2'] and res['p3'] and res['p4']} qP={res['qP']} qM={res['qM']} "
          f"split={res['split'][0]}=={res['split'][1]} t1={res['t1'][0]}=={res['t1'][1]} "
          f"t2={res['t2'][0]}=={res['t2'][1]} t3={res['t3'][0]}=={res['t3'][1]}  ALL={ok}")
    assert ok, f"instance {name} FAILED"

print("\n== carrier instance (F, O^r): q=0 slice recovers chi(End F) = 8 m^2 ==")
resC = instance(5, 1, ZERO, ZERO, ZERO)
print(f"  qM={resC['qM']} (want 0); qP={resC['qP']} (want -8); "
      f"t3={resC['t3'][0]}=={resC['t3'][1]} (want 8)")
assert resC['qM'] == 0 and resC['qP'] == -8 and resC['t3'][0] == 8

print("\n== linear detector instance (G = E-): chi(E+ x G) - chi(E- x G) = m <W_R, ch2(G)> ==")
r, m = 6, 2
eplus = ch_pair(r, ZERO, pair_c2p(m, WRcl), pair_c3shift(ZERO, m), add_cl(ZERO, pair_c4shift(ZERO, WRcl, m)))
eminus = ch_pair(r, ZERO, WRcl, ZERO, ZERO)
lhs = chi_pp(eplus, eminus) - chi_pp(eminus, eminus)
rhs = Fr(m) * int_cl(wedge_cl(WRcl, eminus['2']))
print(f"  lhs={lhs}; rhs={rhs}; match={lhs == rhs}")
assert lhs == rhs

print("\n== chi(End O^r) = 0 (Euler-zero carrier consistency) ==")
carO = ch_pair(5, ZERO, ZERO, ZERO, ZERO)
v = chi_pp(carO, ch_dual(carO))
print(f"  chi(End O^r) = {v}")
assert v == 0

print("\nALL MIRROR CHECKS GREEN — every Lean literal and decide target verified.")

# ============================================================================
# APPENDED (round 3): the ALL-INTEGER (Z-scaled) restatement of every decided
# proposition, mirroring the final GSTPairChannelWallsCertificate.lean exactly:
# integer coefficients; Newton conductors in numerator form; chi24 = 24*chi;
# the c_4 shift via -m*(c2M ^ W_R) + m^2*(W_R^2/2) with W_R^2/2 = 4 vol.
# Kernel idiom discipline: Nat/Int/List arithmetic only, no Rat evaluation.
# ============================================================================

WRz = [(1, 85), (-1, 90), (-1, 102), (-1, 105), (-1, 150), (-1, 153), (-1, 165), (1, 170)]
WIz = [(1, 86), (1, 89), (1, 101), (-1, 106), (1, 149), (-1, 154), (-1, 166), (-1, 169)]
THz = [(1, 3), (1, 12), (1, 48), (1, 192)]
HALFWR2 = [(1 * 4, VOL)]

def z_norm(c):
    return norm_cl([(Fr(a), m) for a, m in c])

def z_wedge(c1, c2):
    return wedge_cl([(Fr(a), m) for a, m in c1], [(Fr(b), m) for b, m in c2])

def z_mul(q, c): return z_norm([(q * a, m) for a, m in c])
def z_add(c1, c2): return z_norm([(a, m) for a, m in c1] + [(b, m) for b, m in c2])
def z_pow(c, k):
    r = z_norm([(Fr(1), 0)])
    for _ in range(k): r = z_wedge(r, c)
    return r
def z_int(c):
    for a, m in c:
        if m == VOL: return a
    return Fr(0)

print("\n== Z-model (round 3): W0 / periods / FM ==")
ok_w0 = all(z_wedge(z_pow(THz, j), Wc) == [] for j in (1, 2, 3) for Wc in (WRz, WIz))
ok_per = (z_int(z_pow(THz, 4)) == 24 and z_int(z_wedge(WRz, WRz)) == 8 and z_int(z_wedge(WIz, WIz)) == 8
          and z_int(z_wedge(WRz, WIz)) == 0 and z_int(z_add(z_wedge(WRz, WRz), z_wedge(WIz, WIz))) == 16
          and all(z_int(z_wedge(WRz, z_pow(THz, j))) == 0 for j in (1, 2, 3, 4)))
def z_fm(x): return z_norm([(a * wsign(bitlist(m), bitlist(255 ^ m)), 255 ^ m) for a, m in x])
ok_fm = z_fm(WRz) == WRz and z_fm(WIz) == WIz and z_fm(z_fm(WRz)) == WRz and z_fm(z_fm(WIz)) == WIz
print(f"  W0={ok_w0} periods={ok_per} fm={ok_fm}")
assert ok_w0 and ok_per and ok_fm

def ch2n(c1, c2): return z_add(z_pow(c1, 2), z_mul(-2, c2))
def ch3n(c1, c2, c3): return z_add(z_add(z_pow(c1, 3), z_mul(-3, z_wedge(c1, c2))), z_mul(3, c3))
def ch4n(c1, c2, c3, c4):
    return z_add(z_add(z_add(z_add(z_pow(c1, 4), z_mul(-4, z_wedge(z_pow(c1, 2), c2))),
        z_mul(2, z_pow(c2, 2))), z_mul(4, z_wedge(c1, c3))), z_mul(-4, c4))
def z_c2p(m, c2m): return z_add(c2m, z_mul(-m, WRz))
def z_c3s(c1, m): return z_wedge(c1, z_mul(-m, WRz))
def z_c4s(c2m, m): return z_add(z_mul(-m, z_wedge(c2m, WRz)), z_mul(m * m, HALFWR2))
def z_Eplus(r, c1, c2m, g, m):
    return (Fr(r), c1, ch2n(c1, z_c2p(m, c2m)), ch3n(c1, z_c2p(m, c2m), z_c3s(c1, m)),
            ch4n(c1, z_c2p(m, c2m), z_c3s(c1, m), z_add(g, z_c4s(c2m, m))))
def z_Eminus(r, c1, c2m, g):
    return (Fr(r), c1, ch2n(c1, c2m), ch3n(c1, c2m, []), ch4n(c1, c2m, [], g))
def z_dual(x): return (x[0], z_mul(-1, x[1]), x[2], z_mul(-1, x[3]), x[4])
def chi24(x, y):
    prod = z_add(z_mul(y[0], x[4]), z_add(z_mul(x[0], y[4]),
        z_add(z_mul(4, z_wedge(x[1], y[3])), z_add(z_mul(6, z_wedge(x[2], y[2])), z_mul(4, z_wedge(x[3], y[1]))))))
    return z_int(prod)
def zq(c2): return z_int(z_wedge(WRz, c2))

print("== Z-model (round 3): instances / carrier / detector (24-scaled table) ==")
for name, r, m, c1, c2m, g in [("I1",3,1,[],WRz,[]), ("I2",5,2,[],WRz,[]), ("I3",4,1,THz,WRz,[]), ("I4",7,3,THz,WRz,[(5,VOL)])]:
    ep, em = z_Eplus(r, c1, c2m, g, m), z_Eminus(r, c1, c2m, g)
    vals = (
        z_add(ep[2], z_mul(-1, em[2])) == z_mul(2 * m, WRz),
        z_add(ep[3], z_mul(-1, em[3])) == [],
        z_add(ep[4], z_mul(-1, em[4])) == [],
        zq(z_c2p(m, c2m)) - zq(c2m) == -8 * m,
        chi24(ep, z_dual(ep)) - chi24(ep, z_dual(em)) == 24 * (8 * m * m - m * zq(c2m)),
        chi24(ep, z_dual(em)) - chi24(em, z_dual(em)) == 24 * (-m * zq(c2m)),
        chi24(ep, z_dual(ep)) - chi24(em, z_dual(em)) == 24 * (8 * m * m - 2 * m * zq(c2m)))
    print(f"  {name}: {all(vals)} (qM={zq(c2m)})")
    assert all(vals)
carF, carO = z_Eplus(5, [], [], [], 1), z_Eminus(5, [], [], [])
cv = (zq([]) == 0, chi24(carO, z_dual(carO)) == 0, zq(z_c2p(1, [])) - zq([]) == -8,
      chi24(carF, z_dual(carF)) - chi24(carO, z_dual(carO)) == 24 * 8)
print(f"  carrier: {all(cv)}")
assert all(cv)
dep, dem = z_Eplus(6, [], WRz, [], 2), z_Eminus(6, [], WRz, [])
dv = chi24(dep, dem) - chi24(dem, dem) == 12 * 2 * z_int(z_wedge(WRz, dem[2]))
print(f"  detector: {dv}")
assert dv
print("Z-MODEL MIRROR GREEN — the final integer restatement fully verified.")
