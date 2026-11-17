#!/usr/bin/env python3
# field_letter_generation_round36_checks.py -- ROUND 36, THE NON-ELLIPTIC FACE STRIKE
# (the field-letter pairing-generation: R2' part (a) at the abelian-cyclotomic shapes)
#
# THE THEOREM CERTIFIED HERE (the finite shadow of the derivation
# GST_field_letter_generation_round36_2026_11_04.tex):
#   S14 the Field-Letter Descent Theorem: the descent relation
#      z_{tau U} = sigma_tau(z_U) * eps(tau,U); the compatibility theorem
#      (AND^{2p}K = the descent-compatible systems, by the dimension count);
#      the mixed-orbit kill; the stabilizer-eigen constraint; the full-descent
#      law dim(O) = |O|; the binomial law dim Hdg_{2p} = C(g,p) at the
#      primitive types; the calibrations (Rosati = g, the duality rows, the
#      product-world consistency).
#   S15 the Field-Letter Pairing-Generation Theorem: at EVERY committed
#      abelian-cyclotomic shape and EVERY CM-type class, the products of
#      divisor classes span the full Hodge space at degree 4 (span + membership
#      at every world), degree 6 (rank equality at every world + membership on
#      a bounded two-world sample, AUDIT-36 F1), and degree 8 (span receipts at
#      every octic world, AUDIT-36 F2): SURPLUS = 0 everywhere. The rank
#      receipts: 6/18/36 at the octic worlds, 3/9 at the sextic, 1 at the
#      quartic.
#   S16 the CM-Jacobian K-supply letter shadow: the graph graft propagates the
#      balance; the cross-stratum hostile fires.
#   V5 the operator's arity totals 4, 8, 24, 64, 208 (two algorithms at every
#      m <= 6, AUDIT-36 F5) + m=6 control (688, two algorithms) + the
#      cyclotomic product law -- the engine-continuity receipt.
#
# CONTRACT (SKILL sec.22 NO-OOM, stated BEFORE launch): cyclotomic shapes
# m in {3,4,5,6,8,12,7,9,15,16,20,24} (phi(m) <= 8); words <= C(8,4) = 70;
# AND-basis <= 70 elements; component matrices <= 272 x 70 (integer entries);
# type-class representatives <= 5 per world; per-class invariance members
# checked by the orbit-count algorithm only; random instances <= 48 per test;
# degree-6 membership sample (AUDIT-36 F1): 2 worlds, the first three triple
# products, the first 8 unbalanced 6-words; degree-8 span receipts (AUDIT-36
# F2): divisor multi-quadruple sample (repetitions allowed, cap 20) plus a
# 40-trial deterministic random-class pass per octic world; exact integer /
# fractions.Fraction arithmetic; ZERO floats; expected total runtime < 240 s;
# memory < 200 MB. Deterministic: xorshift64* seed
# 0xABCDEF9876543210 (distinct from every prior certificate: R33
# 0x9E3779B97F4A7C15, R34 0xC0FFEE123456789, R35 0xFEEDFACECAFEBEEF).
#
# LEDGER 107/109 DISCIPLINE: every ok() message states the predicate ACTUALLY
# tested; the mechanical vacuity scan (ledger 107's banned boolean-literal
# battery + the dead-conditional and self-comparison patterns) runs over this
# file's own source; every hostile control must FIRE with the predicted failure.

from fractions import Fraction
from math import gcd, comb
from itertools import combinations, permutations, combinations_with_replacement
import sys, time, hashlib

T0 = time.time()
SEED = 0xABCDEF9876543210
_rng_state = SEED & ((1 << 64) - 1)

def nxt():
    global _rng_state
    x = _rng_state
    x ^= (x << 13) & ((1 << 64) - 1)
    x ^= x >> 7
    x ^= (x << 17) & ((1 << 64) - 1)
    # xorshift64* multiplier
    _rng_state = x & ((1 << 64) - 1)
    return (_rng_state * 0x2545F4914F6CDD1D) & ((1 << 64) - 1)

CHECKS = 0
FAILS = 0
FAIL_LINES = []

def ok(msg):
    global CHECKS
    CHECKS += 1
    print(f"  ok {CHECKS:4d}  {msg}")

def bad(msg):
    global FAILS
    FAILS += 1
    FAIL_LINES.append(msg)
    print(f"  FAIL      {msg}")

def check(cond, msg):
    if cond:
        ok(msg)
    else:
        bad(msg)

# ================================================================ cyclotomic machinery

def poly_div_mod(num, den):
    num = list(num)
    q = [0] * max(0, len(num) - len(den) + 1)
    dn = len(den) - 1
    assert den[-1] == 1
    for i in range(len(num) - 1, dn - 1, -1):
        c = num[i]
        if c != 0:
            q[i - dn] = c
            for j in range(dn + 1):
                num[i - dn + j] -= c * den[j]
    while num and num[-1] == 0:
        num.pop()
    return q, num

_PHI_CACHE = {}
def cyclo(m):
    if m not in _PHI_CACHE:
        xs = [0] * (m + 1); xs[m] = 1; xs[0] -= 1
        for d in range(1, m):
            if m % d == 0:
                phid = cyclo(d)
                q, r = poly_div_mod(xs, phid)
                assert not r, (m, d, r)
                xs = q  # keep the QUOTIENT
        while len(xs) > 1 and xs[-1] == 0:
            xs.pop()
        _PHI_CACHE[m] = xs
    return _PHI_CACHE[m]

def power_reduce_table(m):
    phi = len(cyclo(m)) - 1  # the DEGREE of Phi_m
    cs = cyclo(m)
    red = []
    for e in range(phi):
        v = [0] * phi; v[e] = 1; red.append(v)
    for e in range(phi, m):
        v = [0] * phi
        # zeta^e = zeta^{e-phi} * zeta^phi = -sum_{j<phi} cs[j] * zeta^{e-phi+j}
        for j in range(phi):
            if cs[j]:
                for k in range(phi):
                    v[k] -= cs[j] * red[e - phi + j][k]
        red.append(v)
    return red, phi

def det_zeta(rows_exp, m, red, phi):
    """Determinant of a matrix whose entries are zeta^{e} (exponents mod m),
    as an exact integer vector in the power basis of Z[zeta]."""
    n = len(rows_exp)
    acc = [0] * phi
    for perm in permutations(range(n)):
        sgn = 1
        seen = [False] * n
        for i in range(n):
            if seen[i]:
                continue
            j = i; L = 0
            while not seen[j]:
                seen[j] = True; j = perm[j]; L += 1
            if L % 2 == 0:
                sgn *= -1  # even-length cycle contributes sign -1; odd contributes +1
        e = 0
        for a in range(n):
            e += rows_exp[a][perm[a]]
        e %= m
        v = red[e]
        for k in range(phi):
            if v[k]:
                acc[k] += sgn * v[k]
    return acc

# ================================================================ exact linear algebra

def rref_fraction(mat):
    if not mat:
        return []
    nrows = len(mat); ncols = len(mat[0])
    pivots = []
    r = 0
    for c in range(ncols):
        pr = None
        for rr in range(r, nrows):
            if mat[rr][c] != 0:
                pr = rr; break
        if pr is None:
            continue
        mat[r], mat[pr] = mat[pr], mat[r]
        pv = mat[r][c]
        mat[r] = [x / pv for x in mat[r]]
        for rr in range(nrows):
            if rr != r and mat[rr][c] != 0:
                f = mat[rr][c]
                mat[rr] = [a - f * b for a, b in zip(mat[rr], mat[r])]
        pivots.append(c)
        r += 1
        if r == nrows:
            break
    return pivots

def kernel_basis(mat_rows, ncols):
    mat = [[Fraction(x) for x in row] for row in mat_rows]
    piv = rref_fraction(mat)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * ncols
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -mat[i][f]
        basis.append(v)
    return basis, len(piv)

def rank_of(vectors, ncols):
    mat = [[Fraction(x) for x in v] for v in vectors]
    piv = rref_fraction(mat)
    return len(piv)

# ================================================================ the free-letter world

def group_units(m):
    return [a for a in range(1, m) if gcd(a, m) == 1]

def cm_types(m):
    G = group_units(m)
    c = (-1) % m
    pairs = []
    seen = set()
    for a in G:
        if a in seen:
            continue
        b = (a * c) % m
        pairs.append(tuple(sorted((a, b))))
        seen.add(a); seen.add(b)
    types = []
    for choice in range(1 << len(pairs)):
        Phi = sorted(pairs[i][choice >> i & 1] for i in range(len(pairs)))
        types.append(tuple(Phi))
    return types, pairs

def type_class_reps(m):
    """The G-orbit representatives of the CM types."""
    G = group_units(m)
    types, _ = cm_types(m)
    reps = []
    seen = set()
    for Phi in types:
        if Phi in seen:
            continue
        orb = set()
        for t in G:
            orb.add(tuple(sorted((t * a) % m for a in Phi)))
        seen |= orb
        reps.append(Phi)
    return reps

def orbit_words(m, U):
    G = group_units(m)
    out = set()
    for t in G:
        out.add(tuple(sorted((t * u) % m for u in U)))
    return sorted(out)

def word_balance(U, Phi):
    return sum(1 for u in U if u in Phi)

def orbit_count_dim(m, Phi, deg):
    """SECOND ALGORITHM for dim Hdg_{deg}: Theorem S14(iv) --
    the sum of |O| over pure-balanced G-orbits of deg-words."""
    G = group_units(m)
    p = deg // 2
    words = list(combinations(sorted(G), deg))
    seen = set()
    total = 0
    n_pure = 0
    for U in words:
        if U in seen:
            continue
        orb = orbit_words(m, U)
        seen |= set(orb)
        if all(word_balance(V, Phi) == p for V in orb):
            total += len(orb)
            n_pure += 1
    return total, n_pure

def analyze_world(m, Phi, degrees=(2, 4)):
    """The RREF computation of Hdg_{deg} kernels + the product spans."""
    G = group_units(m)
    g = len(G) // 2
    red, phi = power_reduce_table(m)
    res = {'m': m, 'phi': phi, 'g': g, 'Phi': Phi}
    hdg = {}
    for deg in degrees:
        p = deg // 2
        Is = list(combinations(range(phi), deg))
        Us = list(combinations(sorted(G), deg))
        unb = [U for U in Us if word_balance(U, Phi) != p]
        rows = []
        for U in unb:
            compU = {}
            for I in Is:
                matU = [[(u * i) % m for i in I] for u in U]
                compU[I] = det_zeta(matU, m, red, phi)
            for k in range(phi):
                rows.append([compU[I][k] for I in Is])
        basis, rank = kernel_basis(rows, len(Is))
        hdg[deg] = {'dim': len(basis), 'basis': basis, 'nwords': len(Us),
                    'nbal': len(Us) - len(unb), 'nunb': len(unb)}
    res['hdg'] = hdg
    if 4 in degrees and 2 in degrees:
        Is2 = list(combinations(range(phi), 2))
        Is4 = list(combinations(range(phi), 4))
        idx4 = {I: k for k, I in enumerate(Is4)}
        prod_vecs = []
        B2 = hdg[2]['basis']
        for a in range(len(B2)):
            for b in range(a, len(B2)):
                v = [Fraction(0)] * len(Is4)
                for i, I in enumerate(Is2):
                    qa = B2[a][i]
                    if qa == 0:
                        continue
                    for j, J in enumerate(Is2):
                        qb = B2[b][j]
                        if qb == 0:
                            continue
                        if set(I) & set(J):
                            continue
                        K4 = tuple(sorted(I + J))
                        seq = list(I) + list(J)
                        inv = sum(1 for x in range(len(seq))
                                  for y in range(x + 1, len(seq)) if seq[x] > seq[y])
                        sgn = -1 if inv % 2 else 1
                        v[idx4[K4]] += qa * qb * sgn
                prod_vecs.append(v)
        # membership: the products must satisfy the Hodge_4 kernel conditions
        rows4 = []
        Us4 = list(combinations(sorted(G), 4))
        unb4 = [U for U in Us4 if word_balance(U, Phi) != 2]
        comp4 = {}
        for U in unb4:
            comp4[U] = []
            for I in Is4:
                matU = [[(u * i) % m for i in I] for u in U]
                comp4[U].append(det_zeta(matU, m, red, phi))
        member_ok = True
        for v in prod_vecs:
            for U in unb4:
                acc = [0] * phi
                for idx, I in enumerate(Is4):
                    if v[idx] == 0:
                        continue
                    d = comp4[U][idx]
                    for k in range(phi):
                        if d[k]:
                            acc[k] += v[idx] * d[k]
                if any(x != 0 for x in acc):
                    member_ok = False
        res['product_member_4'] = member_ok
        pr = rank_of(prod_vecs, len(Is4))
        res['product_rank_4'] = pr
        res['surplus_4'] = hdg[4]['dim'] - pr
        res['n_prod_vecs'] = len(prod_vecs)
        res['divisor_basis_dim'] = len(B2)
        # proper-subspan hostile: products from only the first 2 divisor basis elements
        if len(B2) >= 3:
            sub_vecs = []
            for a in range(min(2, len(B2))):
                for b in range(a, min(2, len(B2))):
                    v = [Fraction(0)] * len(Is4)
                    for i, I in enumerate(Is2):
                        qa = B2[a][i]
                        if qa == 0:
                            continue
                        for j, J in enumerate(Is2):
                            qb = B2[b][j]
                            if qb == 0:
                                continue
                            if set(I) & set(J):
                                continue
                            K4 = tuple(sorted(I + J))
                            seq = list(I) + list(J)
                            inv = sum(1 for x in range(len(seq))
                                      for y in range(x + 1, len(seq)) if seq[x] > seq[y])
                            sgn = -1 if inv % 2 else 1
                            v[idx4[K4]] += qa * qb * sgn
                    sub_vecs.append(v)
            res['subspan_rank_4'] = rank_of(sub_vecs, len(Is4))
        # the mixed-orbit kill: the Hdg_4 basis components vanish on mixed orbits
        res['kill_check'] = kill_check_world(m, Phi, red, phi, hdg[4]['basis'], 4)
    # degree 6 and 8 product spans (octic worlds)
    if 6 in degrees and 2 in degrees and hdg[2]['basis']:
        Is2 = list(combinations(range(phi), 2))
        Is6 = list(combinations(range(phi), 6))
        if Is6:
            idx6 = {I: k for k, I in enumerate(Is6)}
            B2 = hdg[2]['basis']
            prod6 = []
            triples = list(combinations(range(len(B2)), 3)) if len(B2) >= 3 else []
            if not triples and len(B2) == 2:
                triples = []
            for (a, b, cc) in triples:
                v = [Fraction(0)] * len(Is6)
                # wedge of three pair-basis elements: accumulate via the flat products
                # d_a wedge d_b wedge d_c = sum over disjoint I,J,K
                for i, I in enumerate(Is2):
                    qa = B2[a][i]
                    if qa == 0: continue
                    for j, J in enumerate(Is2):
                        qb = B2[b][j]
                        if qb == 0: continue
                        if set(I) & set(J): continue
                        for k, K in enumerate(Is2):
                            qc = B2[cc][k]
                            if qc == 0: continue
                            if set(K) & set(I) or set(K) & set(J): continue
                            K6 = tuple(sorted(I + J + K))
                            seq = list(I) + list(J) + list(K)
                            inv = sum(1 for x in range(len(seq))
                                      for y in range(x + 1, len(seq)) if seq[x] > seq[y])
                            sgn = -1 if inv % 2 else 1
                            v[idx6[K6]] += qa * qb * qc * sgn
                prod6.append(v)
            if prod6:
                res['product_rank_6'] = rank_of(prod6, len(Is6))
            else:
                res['product_rank_6'] = 0
    return res

def kill_check_world(m, Phi, red, phi, Kb, deg):
    """The Hdg basis vectors' word-components vanish outside pure-balanced orbits."""
    G = group_units(m)
    p = deg // 2
    Us = list(combinations(sorted(G), deg))
    Is = list(combinations(range(phi), deg))
    # classify orbits
    seen = set()
    pure = set()
    for U in Us:
        if U in seen:
            continue
        orb = orbit_words(m, U)
        seen |= set(orb)
        if all(word_balance(V, Phi) == p for V in orb):
            pure |= set(orb)
    # components of each basis vector on each word
    for b, z in enumerate(Kb):
        for U in Us:
            if U in pure:
                continue
            acc = [0] * phi
            for idx, I in enumerate(Is):
                q = z[idx]
                if q == 0:
                    continue
                matU = [[(u * i) % m for i in I] for u in U]
                d = det_zeta(matU, m, red, phi)
                for k in range(phi):
                    if d[k]:
                        acc[k] += q * d[k]
            if any(x != 0 for x in acc):
                return False
    return True

# ================================================================ V1: the descent machinery

print("=" * 96)
print("V1 -- THE DESCENT MACHINERY (Theorem S14 (i)-(iv))")
print("=" * 96)

def descent_instance(m, Phi):
    """One instance check of z_{tau U} = sigma_tau(z_U) * eps(tau,U)."""
    G = group_units(m)
    red, phi = power_reduce_table(m)
    deg = 2
    Is = list(combinations(range(phi), deg))
    Us = list(combinations(sorted(G), deg))
    z = [Fraction((nxt() % 97) - 48, 1 + (nxt() % 7)) for _ in Is]
    def comp(U):
        acc = [0] * phi
        for idx, I in enumerate(Is):
            if z[idx] == 0:
                continue
            matU = [[(u * i) % m for i in I] for u in U]
            d = det_zeta(matU, m, red, phi)
            for k in range(phi):
                if d[k]:
                    acc[k] += z[idx] * d[k]
        return acc
    U = Us[nxt() % len(Us)]
    t = G[nxt() % len(G)]
    tU = tuple(sorted((t * u) % m for u in U))
    zU = comp(U); ztU = comp(tU)
    xs = [0] * phi
    for k in range(phi):
        if zU[k]:
            e = (t * k) % m
            for j in range(phi):
                xs[j] += zU[k] * red[e][j]
    seq = [(t * u) % m for u in U]
    tgt = list(tU)
    perm = [tgt.index(x) for x in seq]
    inv = sum(1 for a in range(len(perm)) for b in range(a + 1, len(perm)) if perm[a] > perm[b])
    sgn = -1 if inv % 2 else 1
    return all(xs[j] * sgn == ztU[j] for j in range(phi))

DESCENT_WORLDS = [(5, (1, 2)), (7, (1, 2, 3)), (15, (1, 2, 4, 7)), (24, (1, 5, 7, 11))]
for m, Phi in DESCENT_WORLDS:
    allok = True
    for i in range(12):
        if not descent_instance(m, Phi):
            allok = False
    check(allok, f"descent relation z_(tU)=sigma_t(z_U)*eps holds on 12 random AND^2K "
                 f"elements at m={m}, Phi={list(Phi)} (each element: random Q-coefficients "
                 f"over the power-basis wedges; the relation checked on a random (U,tau); "
                 f"the relation itself is type-independent -- the Phi names the world)")

# hostile: a WRONG sign must fail the relation (the control can fire)
def descent_wrong_sign_fires():
    m, Phi = 15, (1, 2, 4, 7)
    G = group_units(m)
    red, phi = power_reduce_table(m)
    deg = 2
    Is = list(combinations(range(phi), deg))
    Us = list(combinations(sorted(G), deg))
    z = [Fraction(1)] * len(Is)  # a fixed nontrivial element
    def comp(U):
        acc = [0] * phi
        for idx, I in enumerate(Is):
            matU = [[(u * i) % m for i in I] for u in U]
            d = det_zeta(matU, m, red, phi)
            for k in range(phi):
                if d[k]:
                    acc[k] += z[idx] * d[k]
        return acc
    # find a (U, t) where the sign matters (odd permutation)
    for U in Us:
        for t in G:
            tU = tuple(sorted((t * u) % m for u in U))
            seq = [(t * u) % m for u in U]
            tgt = list(tU)
            perm = [tgt.index(x) for x in seq]
            inv = sum(1 for a in range(len(perm)) for b in range(a + 1, len(perm)) if perm[a] > perm[b])
            if inv % 2 == 1:
                zU = comp(U); ztU = comp(tU)
                xs = [0] * phi
                for k in range(phi):
                    if zU[k]:
                        e = (t * k) % m
                        for j in range(phi):
                            xs[j] += zU[k] * red[e][j]
                if any(xs[j] != ztU[j] for j in range(phi)):
                    return True  # the WRONG (no-sign) relation differs: the sign is load-bearing
    return False
check(descent_wrong_sign_fires(), "the sign eps(tau,U) is load-bearing: an instance exists "
      "where sigma_t(z_U) != z_(tU) (the wrong-sign relation FAILS) at m=15, deg 2")

# the mixed-orbit kill + the full-descent law on the computed Hdg_4 kernels
WORLDS = [
    (3, (2,), "quadratic"), (4, (2,), "quadratic"), (6, (2,), "quadratic"),
    (5, (2, 4), "quartic"), (8, (2, 4), "quartic"), (12, (2, 4), "quartic"),
    (7, (2, 4, 6), "sextic"), (9, (2, 4, 6), "sextic"),
    (15, (2, 4, 6, 8), "octic"), (16, (2, 4, 6, 8), "octic"),
    (20, (2, 4, 6, 8), "octic"), (24, (2, 4, 6, 8), "octic"),
]

RESULTS = {}
for m, degrees, kind in WORLDS:
    reps = type_class_reps(m)
    for Phi in reps:
        res = analyze_world(m, Phi, degrees=degrees)
        RESULTS[(m, Phi)] = res
        # V1.2: the orbit-count (second algorithm) vs the RREF dim, at every degree
        for deg in degrees:
            oc, n_pure = orbit_count_dim(m, Phi, deg)
            check(oc == res['hdg'][deg]['dim'],
                  f"dim Hdg_{deg} at m={m} Phi={list(Phi)}: RREF kernel dim "
                  f"{res['hdg'][deg]['dim']} == orbit-count sum |O| over {n_pure} "
                  f"pure-balanced orbits = {oc} (two independent algorithms agree)")
        # V1.3: the mixed-orbit kill on the Hdg_4 basis
        if 4 in degrees:
            check(res.get('kill_check', None) is True,
                  f"the mixed-orbit kill at m={m} Phi={list(Phi)}: every Hdg_4 basis "
                  f"vector's word-components vanish on every mixed/unbalanced orbit word")

# ================================================================ V2: the character criterion

print("=" * 96)
print("V2 -- THE CHARACTER CRITERION + THE CALIBRATIONS (Theorem S14)")
print("=" * 96)

# (a) the Rosati/Hermitian calibration: Hdg_2 = g at the primitive types
PRIM_ROWS = [(5, (1, 2), 2), (7, (1, 2, 3), 3), (9, (1, 2, 4), 3),
             (15, (1, 2, 4, 7), 4), (16, (3, 5, 7, 15), 4),
             (20, (3, 7, 9, 19), 4), (24, (5, 7, 11, 23), 4)]
for m, Phi, g in PRIM_ROWS:
    r = RESULTS[(m, Phi)]
    check(r['hdg'][2]['dim'] == g,
          f"Rosati/Hermitian calibration at the primitive type m={m} Phi={list(Phi)}: "
          f"dim Hdg_2 = {r['hdg'][2]['dim']} == g = {g} (the classical NS dimension "
          f"K^+, the Rosati-fixed part)")

# (b) the duality rows at the octic worlds
for (m, Phi), r in RESULTS.items():
    if 6 in r['hdg'] and 8 in r['hdg']:
        check(r['hdg'][6]['dim'] == r['hdg'][2]['dim'],
              f"the duality row at m={m} Phi={list(Phi)}: dim Hdg_6 = "
              f"{r['hdg'][6]['dim']} == dim Hdg_2 = {r['hdg'][2]['dim']}")
        check(r['hdg'][8]['dim'] == 1,
              f"the top row at m={m} Phi={list(Phi)}: dim Hdg_8 = "
              f"{r['hdg'][8]['dim']} == 1 (the point class)")

# (c) the product-world consistency (the imprimitive values)
IMPRIM_ROWS = [
    (8, (1, 3), 4, 1), (12, (1, 5), 4, 1),
    (7, (3, 5, 6), 9, 9), (9, (1, 4, 7), 9, 9),
    (15, (1, 4, 7, 13), 16, 36), (16, (5, 7, 13, 15), 16, 36),
    (20, (1, 3, 7, 9), 16, 36), (24, (1, 5, 7, 11), 16, 36),
]
for m, Phi, d2, d4 in IMPRIM_ROWS:
    r = RESULTS[(m, Phi)]
    check(r['hdg'][2]['dim'] == d2 and r['hdg'][4]['dim'] == d4,
          f"the imprimitive-type product-world consistency at m={m} Phi={list(Phi)}: "
          f"dim Hdg_2 = {r['hdg'][2]['dim']} == {d2}, dim Hdg_4 = {r['hdg'][4]['dim']} "
          f"== {d4} (the Round-35 factor-letter values of the product worlds)")

# (d) the binomial law at the primitive types
BINOM_ROWS = [(5, (1, 2), [2, 1]), (7, (1, 2, 3), [3, 3, 1]), (9, (1, 2, 4), [3, 3, 1]),
              (15, (1, 2, 4, 7), [4, 6, 4, 1]), (16, (3, 5, 7, 15), [4, 6, 4, 1]),
              (20, (3, 7, 9, 19), [4, 6, 4, 1]), (24, (5, 7, 11, 23), [4, 6, 4, 1])]
for m, Phi, expected in BINOM_ROWS:
    r = RESULTS[(m, Phi)]
    g = r['g']
    actual = [r['hdg'][d]['dim'] for d in sorted(r['hdg'])]
    check(actual == expected,
          f"the binomial law at the primitive type m={m} Phi={list(Phi)}: "
          f"dim Hdg_{{2p}} = {actual} == C(g,p)-sequence {expected} with g = {g}")

# (e) the type-class invariance (all types within each class, by the orbit-count algorithm)
for m, degrees, kind in WORLDS:
    types, _ = cm_types(m)
    for Phi in types:
        for deg in degrees:
            oc, _ = orbit_count_dim(m, Phi, deg)
            repdim = None
            for (mm, PP), r in RESULTS.items():
                if mm == m:
                    # same class?
                    if tuple(sorted(PP)) in set(orbit_words(m, Phi)) or \
                       any(tuple(sorted((t * a) % m for a in PP)) == Phi for t in group_units(m)):
                        repdim = r['hdg'][deg]['dim']
                        break
            if repdim is not None:
                check(oc == repdim,
                      f"type-class invariance at m={m}: the orbit-count dim {oc} at "
                      f"Phi={list(Phi)} equals the class representative's dim {repdim} "
                      f"(degree {deg})")

# ================================================================ V3: the pairing-generation (THE CRUX)

print("=" * 96)
print("V3 -- THE FIELD-LETTER PAIRING-GENERATION (Theorem S15, THE CRUX)")
print("=" * 96)

for (m, Phi), r in sorted(RESULTS.items()):
    if 'product_rank_4' in r:
        check(r['product_rank_4'] == r['hdg'][4]['dim'],
              f"THE SPAN at m={m} Phi={list(Phi)}: rank of the divisor products "
              f"({r['n_prod_vecs']} two-fold products of the {r['divisor_basis_dim']}-dim "
              f"divisor basis) = {r['product_rank_4']} == dim Hdg_4 = {r['hdg'][4]['dim']} "
              f"-- SURPLUS = {r['surplus_4']}")
        check(r['product_member_4'],
              f"the products are Hodge at m={m} Phi={list(Phi)}: every two-fold product "
              f"vector satisfies the unbalanced-component vanishing (lies in Hdg_4)")
    if 'product_rank_6' in r and 6 in r['hdg']:
        if r['hdg'][6]['dim'] > 0:
            check(r['product_rank_6'] == r['hdg'][6]['dim'],
                  f"THE SPAN at degree 6 at m={m} Phi={list(Phi)}: the three-fold "
                  f"divisor products span Hdg_6: rank {r['product_rank_6']} == "
                  f"dim {r['hdg'][6]['dim']}")

# AUDIT-36 F1 REPAIR: the degree-6 product membership, bounded sample (2 worlds,
# the first three triple products, the first 8 unbalanced 6-words) -- the label
# states the sample; the rank equality above covers every world.
def product_member_6_sample(m, Phi, n_words=8):
    red, phi = power_reduce_table(m)
    G = group_units(m)
    r = RESULTS[(m, Phi)]
    B2 = r['hdg'][2]['basis']
    Is2 = list(combinations(range(phi), 2))
    Is6 = list(combinations(range(phi), 6))
    if not Is6 or len(B2) < 4:
        return None
    idx6 = {I: k for k, I in enumerate(Is6)}
    unb6 = [U for U in combinations(sorted(G), 6)
            if word_balance(U, Phi) != 3][:n_words]
    if not unb6:
        return None
    for (a, b, cc) in [(0, 1, 2), (0, 1, 3), (0, 2, 3)]:
        v = [Fraction(0)] * len(Is6)
        for i, I in enumerate(Is2):
            qa = B2[a][i]
            if qa == 0:
                continue
            for j, J in enumerate(Is2):
                qb = B2[b][j]
                if qb == 0:
                    continue
                if set(I) & set(J):
                    continue
                for k, K in enumerate(Is2):
                    qc = B2[cc][k]
                    if qc == 0:
                        continue
                    if set(K) & set(I) or set(K) & set(J):
                        continue
                    K6 = tuple(sorted(I + J + K))
                    seq = list(I) + list(J) + list(K)
                    inv = sum(1 for xx in range(len(seq))
                              for yy in range(xx + 1, len(seq)) if seq[xx] > seq[yy])
                    sgn = -1 if inv % 2 else 1
                    v[idx6[K6]] += qa * qb * qc * sgn
        if not any(q != 0 for q in v):
            continue  # a zero product carries no membership information
        for U in unb6:
            acc = [Fraction(0)] * phi
            for idx, I in enumerate(Is6):
                if v[idx] == 0:
                    continue
                matU = [[(u * i) % m for i in I] for u in U]
                d = det_zeta(matU, m, red, phi)
                for k in range(phi):
                    if d[k]:
                        acc[k] += v[idx] * d[k]
            if any(q != 0 for q in acc):
                return False
        return True
    return None

for m, Phi in [(15, (1, 2, 4, 7)), (16, (3, 5, 7, 15))]:
    mem6 = product_member_6_sample(m, Phi)
    check(mem6 is True,
          f"the degree-6 product membership (bounded sample, AUDIT-36 F1) at m={m} "
          f"Phi={list(Phi)}: the first nonzero triple product among the three "
          f"sampled triples of the divisor basis has VANISHING components on the "
          f"first 8 unbalanced 6-words (it lies in Hdg_6) -- the three-fold "
          f"product arithmetic is Hodge-faithful at the sampled worlds")

# AUDIT-36 F2 REPAIR: the degree-8 span receipts at every octic world (the
# header's degree-8 coverage claim now carried by checks): a nonzero four-fold
# divisor product exists (bounded MULTI-quadruple sample -- repetitions allowed,
# the cup-powers d^4 included -- early exit).
def degree8_span_receipt(m, Phi, cap_quads=20, n_rand=40):
    red, phi = power_reduce_table(m)
    if phi != 8:
        return None
    r = RESULTS[(m, Phi)]
    B2 = r['hdg'][2]['basis']
    if len(B2) < 4:
        return None
    Is2 = list(combinations(range(phi), 2))
    Is4 = list(combinations(range(phi), 4))
    idx4 = {I: k for k, I in enumerate(Is4)}

    def wedge_pair(va, vb):
        out = [Fraction(0)] * len(Is4)
        for i, I in enumerate(Is2):
            qa = va[i]
            if qa == 0:
                continue
            for j, J in enumerate(Is2):
                qb = vb[j]
                if qb == 0:
                    continue
                if set(I) & set(J):
                    continue
                seq = list(I) + list(J)
                inv = sum(1 for xx in range(len(seq))
                          for yy in range(xx + 1, len(seq)) if seq[xx] > seq[yy])
                sgn = -1 if inv % 2 else 1
                out[idx4[tuple(sorted(I + J))]] += qa * qb * sgn
        return out

    def top_pair(w1, w2):
        # the top (degree-8) component of w1 ^ w2: only disjoint 4-subsets
        # contribute (they union to the full 8-set)
        top = Fraction(0)
        for i1, I in enumerate(Is4):
            q1 = w1[i1]
            if q1 == 0:
                continue
            for i2, J in enumerate(Is4):
                q2 = w2[i2]
                if q2 == 0:
                    continue
                if set(I) & set(J):
                    continue
                seq = list(I) + list(J)
                inv = sum(1 for xx in range(len(seq))
                          for yy in range(xx + 1, len(seq)) if seq[xx] > seq[yy])
                sgn = -1 if inv % 2 else 1
                top += q1 * q2 * sgn
        return top

    quads = list(combinations_with_replacement(range(len(B2)), 4))[:cap_quads]
    for (a, b, c, d) in quads:
        w1 = wedge_pair(B2[a], B2[b])
        w2 = wedge_pair(B2[c], B2[d])
        top = top_pair(w1, w2)
        if top != 0:
            return ('multi-quadruple', (a, b, c, d))
    # the random-class pass: a deterministic pseudo-random Q-combination v of
    # the divisor basis; v is itself a divisor class, so v^4 (the cup power) is
    # a four-fold product of divisor classes -- the polarization-identity
    # receipt (a nonzero symmetric form fires on the diagonal).
    for trial in range(n_rand):
        coeffs = [Fraction((nxt() % 97) - 48, 1 + (nxt() % 7))
                  for _ in range(len(B2))]
        vv = [Fraction(0)] * len(Is2)
        for i, c_i in enumerate(coeffs):
            if c_i == 0:
                continue
            for j, I in enumerate(Is2):
                vv[j] += c_i * B2[i][j]
        w = wedge_pair(vv, vv)
        if top_pair(w, w) != 0:
            return ('random-class', trial)
    return None

for (m, Phi), r in sorted(RESULTS.items()):
    if 8 in r['hdg']:
        receipt = degree8_span_receipt(m, Phi)
        if receipt is None:
            desc = "NONE FOUND IN THE BOUNDED PASSES"
        else:
            desc = f"{receipt[0]} {receipt[1]}"
        check(receipt is not None,
              f"THE SPAN at degree 8 at m={m} Phi={list(Phi)}: a four-fold cup "
              f"product of divisor classes with NONZERO top component exists "
              f"(receipt: {desc} -- the multi-quadruple pass "
              f"(repetitions allowed, cap 20) or the deterministic random-class "
              f"pass (40 trials, xorshift64*, v^4 for a Q-combination v of the "
              f"divisor basis; v is itself a divisor class, so v^4 is a four-fold "
              f"product)) -- the four-fold divisor products span AND^8 K = "
              f"Hdg_8 (dim 1; membership automatic: the unique 8-word is "
              f"balanced) -- SURPLUS = 0")

# hostile: the proper-subspan sabotage must fire at the primitive octic
r = RESULTS[(15, (1, 2, 4, 7))]
subspan = r.get('subspan_rank_4', r['product_rank_4'])  # fail-closed default (AUDIT-36 F6)
check(subspan < r['product_rank_4'],
      f"the proper-subspan sabotage fires at m=15 Phi=[1,2,4,7]: products of only the "
      f"first 2 divisor basis elements give rank {subspan} < "
      f"{r['product_rank_4']} (the full span needs the whole divisor basis)")

# hostile: an unbalanced-supported combination is NOT Hodge
def unbalanced_control():
    m, Phi = 15, (1, 2, 4, 7)
    G = group_units(m)
    red, phi = power_reduce_table(m)
    Is = list(combinations(range(phi), 4))
    Us = list(combinations(sorted(G), 4))
    unb = [U for U in Us if word_balance(U, Phi) != 2]
    if not unb:
        return False
    U = unb[0]
    # the component vector of the basis wedge w_{(0,1,2,3)} on U -- nonzero
    matU = [[(u * i) % m for i in (0, 1, 2, 3)] for u in U]
    d = det_zeta(matU, m, red, phi)
    return any(x != 0 for x in d)
check(unbalanced_control(), "the unbalanced-word control fires: the basis wedge "
      "w_{(0,1,2,3)} has a NONZERO component on an unbalanced word at m=15 (a "
      "generic AND^4K element is not Hodge -- the kernel conditions are load-bearing)")

# ================================================================ V4: the S16 letter shadow

print("=" * 96)
print("V4 -- THEOREM S16's LETTER SHADOW (the graph graft)")
print("=" * 96)

def graft_check(m, Phi, n_instances=30):
    """The graft of a DIAGONAL pair (disjoint from W) onto a level-1-typed odd
    word preserves the level-1 typing exactly: |W'| = 2p+1 and |W' cap Phi| = p+1.
    The hostile: grafting two free Phi-letters breaks it (|W' cap Phi| = p+2)."""
    G = group_units(m)
    c = (-1) % m
    bal_ok = True
    hostile_ok = False
    for it in range(n_instances):
        p = 2
        words = [W for W in combinations(sorted(G), 2 * p - 1)
                 if word_balance(W, Phi) == p]
        if not words:
            return False, False
        W = words[nxt() % len(words)]
        Wset = set(W)
        # a fully free diagonal pair (both a and ca outside W)
        free_pairs = [a for a in G if a not in Wset and ((a * c) % m) not in Wset]
        if not free_pairs:
            bal_ok = False  # at the octic worlds a free pair always exists
            continue
        a = free_pairs[nxt() % len(free_pairs)]
        pair = tuple(sorted((a, (a * c) % m)))
        Wg = tuple(sorted(Wset | set(pair)))
        if not (len(Wg) == 2 * p + 1 and word_balance(Wg, Phi) == p + 1):
            bal_ok = False
        # the hostile: two free Phi-letters grafted instead of the diagonal pair
        free_phis = [x for x in Phi if x not in Wset]
        if len(free_phis) >= 2:
            Wb = tuple(sorted(Wset | set(free_phis[:2])))
            if len(Wb) == 2 * p + 1 and word_balance(Wb, Phi) == p + 2:
                hostile_ok = True
    return bal_ok, hostile_ok

GRAFT_WORLDS = [(15, (1, 2, 4, 7)), (16, (3, 5, 7, 15)),
                (20, (3, 7, 9, 19)), (24, (1, 5, 7, 11))]
for m, Phi in GRAFT_WORLDS:
    bal, host = graft_check(m, Phi)
    check(bal, f"the graph graft at m={m} Phi={list(Phi)}: grafting a DIAGONAL pair "
               f"{{a, ca}} (disjoint from W) onto 30 random level-1-typed odd words "
               f"(|W cap Phi| = p, |W| = 2p-1) gives exactly |W'| = 2p+1 and "
               f"|W' cap Phi| = p+1 -- the S5 type-chase's letter shadow")
    check(host, f"the hostile fires at m={m}: grafting two free Phi-letters instead "
                f"of the diagonal pair gives |W' cap Phi| = p+2 (level 3) -- the "
                f"diagonal-pair graft discipline is load-bearing")

# the non-diagonal pair carries no Hodge class at the primitive shapes:
# every non-diagonal balanced pair has a MIXED G-orbit there (the receipt that
# makes the Rosati calibration dim NS = g possible -- the off-diagonal supply is
# empty exactly at the simple CM worlds)
for m, Phi in [(5, (1, 2)), (7, (1, 2, 3)), (9, (1, 2, 4)), (15, (1, 2, 4, 7)),
               (16, (3, 5, 7, 15)), (20, (3, 7, 9, 19)), (24, (5, 7, 11, 23))]:
    G = group_units(m)
    c = (-1) % m
    allok = True
    found = 0
    for a in Phi:
        for b in G:
            if b in Phi:
                continue
            if b == (a * c) % m:
                continue  # skip the diagonal pair itself
            pair = tuple(sorted((a, b)))
            orb = orbit_words(m, pair)
            if all(word_balance(V, Phi) == 1 for V in orb):
                allok = False  # a pure-balanced off-diagonal orbit would break NS = g
            found += 1
    check(allok and found > 0,
          f"the non-diagonal pair hostile at the primitive m={m} Phi={list(Phi)}: "
          f"every off-diagonal balanced pair's G-orbit is MIXED (contains an "
          f"unbalanced pair) -- the off-diagonal pairing supply is empty at the "
          f"simple CM worlds (consistent with dim NS = g, the Rosati calibration)")

# the K-action letter preservation: sigma_a(alpha*x) = sigma_a(alpha)*sigma_a(x)
def zmul(a, b, m, phi):
    """The product of two Z[zeta]-elements (phi-length integer vectors), reduced
    iteratively into the power basis (zeta^phi = -sum_{j<phi} cs[j] zeta^j)."""
    raw = [0] * (2 * phi)
    for i in range(phi):
        if a[i]:
            for j in range(phi):
                if b[j]:
                    raw[i + j] += a[i] * b[j]
    cs = cyclo(m)
    for e in range(2 * phi - 1, phi - 1, -1):
        if raw[e]:
            for j in range(phi):
                if cs[j]:
                    raw[e - phi + j] -= raw[e] * cs[j]
            raw[e] = 0
    return raw[:phi]

def k_action_check(m, n_instances=10):
    red, phi = power_reduce_table(m)
    G = group_units(m)
    okall = True
    for it in range(n_instances):
        alpha = [(nxt() % 21) - 10 for _ in range(phi)]
        x = [(nxt() % 21) - 10 for _ in range(phi)]
        acc = zmul(alpha, x, m, phi)
        a = G[nxt() % len(G)]
        def sigma(y):
            out = [0] * phi
            for k in range(phi):
                if y[k]:
                    e = (a * k) % m
                    for j in range(phi):
                        out[j] += y[k] * red[e][j]
            return out
        sa = sigma(alpha); sx = sigma(x); saz = sigma(acc)
        prod2 = zmul(sa, sx, m, phi)
        if prod2 != saz:
            okall = False
    return okall

check(k_action_check(15), "the K-action letter preservation at m=15: for 10 random "
      "pairs (alpha, x) in Z[zeta]^phi and a random letter a, "
      "sigma_a(alpha*x) == sigma_a(alpha)*sigma_a(x) exactly (the endomorphism "
      "graphs act letterwise -- the S16 supply's letter shadow)")

# AUDIT-36 F4 REPAIR: the cross-stratum hostile recomputed as a REAL control
# (the prior version was a definitional tautology): in the product world
# m=5 x m=7 with the product type Phi1 U Phi2 on the disjoint letter sets,
# EVERY cross pair {a in G1, b in G2} has a MIXED (G1 x G2)-orbit (it contains
# an unbalanced word) -- no pure (1,1)-orbit crosses the non-isogenous fields.
def cross_field_check():
    m1, m2 = 5, 7
    Phi1, Phi2 = (1, 2), (1, 2, 3)
    G1 = group_units(m1)
    G2 = group_units(m2)
    Phi = set(('A', a) for a in Phi1) | set(('B', b) for b in Phi2)
    n_cross = 0
    n_pure = 0
    for a in G1:
        for b in G2:
            W = frozenset((('A', a), ('B', b)))
            orb = set()
            for t1 in G1:
                for t2 in G2:
                    orb.add(frozenset((('A', (t1 * a) % m1),
                                       ('B', (t2 * b) % m2))))
            if all(sum(1 for u in V if u in Phi) == 1 for V in orb):
                n_pure += 1
            n_cross += 1
    return n_cross, n_pure
n_cross, n_pure = cross_field_check()
check(n_pure == 0 and n_cross == 24,
      f"the cross-stratum hostile fires: at the product world m=5 x m=7 (the "
      f"type Phi_1 U Phi_2 on the disjoint letter sets), all {n_cross} cross "
      f"pairs {{a in G_1, b in G_2}} have MIXED (G_1 x G_2)-orbits ({n_pure} "
      f"pure-balanced) -- no pure (1,1) orbit crosses the non-isogenous CM "
      f"fields (Hom^0 = 0 transports nothing)")

# ================================================================ V5: the calibration anchor

print("=" * 96)
print("V5 -- THE CALIBRATION ANCHOR (the operator's arity totals, the engine continuity)")
print("=" * 96)

OPERATOR_TOTALS = {1: 4, 2: 8, 3: 24, 4: 64, 5: 208}

def cyclotomic_character_formula(m):
    """Algorithm (a): dim = (1/m)[2^{2m} + sum_{j=1}^{m-1} (1-(-1)^{L(j)})^{2 gcd(j,m)}],
    L(j) = m/gcd(j,m)."""
    from math import gcd as _gcd
    total = 2 ** (2 * m)
    for j in range(1, m):
        gj = _gcd(j, m)
        Lj = m // gj
        total += (1 - (-1) ** Lj) ** (2 * gj)
    return total // m

def brute_force_signed_exterior(m):
    """Algorithm (b): the brute-force signed exterior-algebra character sum over all
    2^{2m} letter subsets, deck = C_m acting by the cyclic letter rotation on 2m
    letters (two free orbits)."""
    n_letters = 2 * m
    # the rotation r: letter i -> i+2 mod n_letters on the first orbit,
    # i -> i+2+1?? -- the committed model: two free C_m-orbits of letters:
    # orbit A: letters 0..m-1 (r: i -> i+1 mod m), orbit B: letters m..2m-1
    # (r: i -> i+1 mod m within B). The sign of a permutation acting on a subset S:
    # the subset maps to r(S); the exterior sign = the parity of the bijection
    # S -> r(S) in the sorted order.
    # character: chi(r^k) = sum over subsets S with r^k(S) = S of (-1)^{perm(k,S)}
    # dim = (1/m) sum_{k=0}^{m-1} chi(r^k)
    chi = []
    for k in range(m):
        total = 0
        for S in range(1 << n_letters):
            # subset as tuple
            sub = [i for i in range(n_letters) if (S >> i) & 1]
            img = []
            for i in sub:
                if i < m:
                    img.append((i + k) % m)
                else:
                    img.append(m + ((i - m + k) % m))
            if sorted(img) == sorted(sub) and len(img) == len(set(img)):
                # fixed as a set: the sign of the induced permutation
                perm = [sorted(sub).index(x) for x in sub]
                # map: element sub[i] -> its image; compute the permutation parity of
                # the bijection S -> r^k(S) in the natural order
                pos = {x: j for j, x in enumerate(sorted(sub))}
                perm2 = [pos[img[i]] for i in range(len(sub))]
                inv = sum(1 for a in range(len(perm2)) for b in range(a + 1, len(perm2))
                          if perm2[a] > perm2[b])
                sgn = -1 if inv % 2 else 1
                total += sgn
        chi.append(total)
    return sum(chi) // m

for m in range(1, 6):
    v = OPERATOR_TOTALS[m]
    f = cyclotomic_character_formula(m)
    check(f == v, f"the operator's arity total at m={m}: the cyclotomic character "
                 f"formula gives {f} == {v}")
    if m <= 6:  # brute force bounded: 2^{2m} <= 4096 (AUDIT-36 F5: the two
        # largest committed totals now verified by BOTH algorithms)
        bf = brute_force_signed_exterior(m)
        check(bf == v, f"the operator's arity total at m={m}: the brute-force signed "
                       f"exterior character sum gives {bf} == {v}")

f6 = cyclotomic_character_formula(6)
check(f6 == 688, f"the m=6 agreement control: the cyclotomic character formula gives "
                 f"{f6} == 688 (the third committed value)")
bf6 = brute_force_signed_exterior(6)
check(bf6 == 688, f"the m=6 agreement control, second algorithm (AUDIT-36 F5): the "
                 f"brute-force signed exterior character sum gives {bf6} == 688")

# the cyclotomic product law, exact in Z[C_L]: det(I + C_L) = 1 - (-1)^L
for L in range(2, 13):
    # C_L the companion matrix of x^L - 1 (the L-cycle): det(I + C_L) via exact
    # integer determinant (Bareiss)
    n = L
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        M[i][(i + 1) % n] = 1  # the cycle
    # I + M
    A = [[(1 if i == j else 0) + M[i][j] for j in range(n)] for i in range(n)]
    # Bareiss exact determinant
    def bareiss(A):
        A = [row[:] for row in A]
        n = len(A)
        sign = 1
        prev = 1
        for k in range(n - 1):
            if A[k][k] == 0:
                # find a pivot row
                for i in range(k + 1, n):
                    if A[i][k] != 0:
                        A[k], A[i] = A[i], A[k]
                        sign = -sign
                        break
                else:
                    return 0
            for i in range(k + 1, n):
                for j in range(k + 1, n):
                    A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
                A[i][k] = 0
            prev = A[k][k]
        return sign * A[n - 1][n - 1]
    d = bareiss(A)
    check(d == 1 - (-1) ** L, f"the cyclotomic engine, exact: det(I + C_{L}) = {d} == "
                              f"1 - (-1)^{L} = {1 - (-1)**L} (exact Bareiss)")

# ================================================================ V6: the hostile battery + scans

print("=" * 96)
print("V6 -- THE HOSTILE BATTERY + THE SCANS")
print("=" * 96)

# H3: the fake-type control: a DIFFERENT type class gives DIFFERENT dims
r1 = RESULTS[(15, (1, 2, 4, 7))]
r2 = RESULTS[(15, (1, 4, 7, 13))]
check(r1['hdg'][4]['dim'] != r2['hdg'][4]['dim'],
      f"the fake-type control fires at m=15: the primitive class Phi=[1,2,4,7] has "
      f"dim Hdg_4 = {r1['hdg'][4]['dim']} != the E^4-class Phi=[1,4,7,13]'s "
      f"{r2['hdg'][4]['dim']} (the CM type is load-bearing -- the dims are not "
      f"type-blind)")

# H4: the garbage control: an INVALID CM type (both elements of one conjugate
# pair) produces different counts from every valid type -- the type-validity is
# load-bearing -- and every Phi actually used is valid (one per pair)
def type_valid(Phi, m):
    G = group_units(m)
    c = (-1) % m
    pairs = set()
    for a in G:
        pairs.add(tuple(sorted((a, (a * c) % m))))
    for pr in pairs:
        n_in = sum(1 for x in pr if x in Phi)
        if n_in != 1:
            return False
    return len(Phi) == len(G) // 2

for m, degrees, kind in WORLDS:
    for Phi in type_class_reps(m):
        check(type_valid(Phi, m), f"the input-validity control at m={m}: the type "
              f"Phi={list(Phi)} takes exactly one embedding per conjugate pair "
              f"(a valid CM type -- every world the certificate computes is valid)")

invalid_Phi = (1, 4)  # both elements of the pair {1,4} at m=5: NOT a CM type
oc_garbage, _ = orbit_count_dim(5, invalid_Phi, 2)
valid_dims = {orbit_count_dim(5, Phi, 2)[0] for Phi in type_class_reps(5)}
check(oc_garbage not in valid_dims,
      f"the garbage control fires at m=5: the invalid type (1,4) (both elements of "
      f"one conjugate pair) gives the degree-2 orbit-count {oc_garbage}, different "
      f"from every valid type's value {sorted(valid_dims)} -- the type-validity is "
      f"load-bearing")

# the mechanical vacuity scan (ledger 107): scan THIS file's own source,
# EXCLUDING the scan's own region (the sentinels) and with the banned literals
# built by concatenation so the scanner's own code cannot match them
# VACUITY-SCAN-REGION-START
def vacuity_scan():
    import re
    with open(__file__, 'r') as f:
        src_lines = f.readlines()
    # exclude the scan's own region
    out = []
    inside = False
    for ln in src_lines:
        if 'VACUITY-SCAN-REGION-START' in ln:
            inside = True
        if 'VACUITY-SCAN-REGION-END' in ln:
            inside = False
            continue
        if not inside:
            out.append(ln)
    src = ''.join(out)
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
check(len(hits) == 0, f"the mechanical vacuity scan (ledger 107) over this file's own "
                     f"source (the scan region excluded): {len(hits)} hits for the "
                     f"banned boolean-literal patterns")

# the self-comparison scan: no variable compared to itself within 3 lines of assignment
def self_comparison_scan():
    import re
    with open(__file__, 'r') as f:
        lines = f.readlines()
    hits = 0
    for i, line in enumerate(lines):
        mm = re.search(r'^\s*(\w+)\s*=\s*(.+)$', line)
        if mm:
            var, rhs = mm.group(1), mm.group(2)
            for j in range(i, min(i + 3, len(lines))):
                if re.search(rf'\b{re.escape(var)}\s*==\s*{re.escape(var)}\b', lines[j]):
                    hits += 1
    return hits

sc = self_comparison_scan()
check(sc == 0, f"the self-comparison scan (ledger 107): {sc} hits (no variable is "
               f"compared to itself within 3 lines of its assignment)")

# ================================================================ the result

print("=" * 96)
print(f"RESULT: {CHECKS} checks passed, {FAILS} failed")
if FAIL_LINES:
    for fl in FAIL_LINES:
        print(f"  FAILED: {fl}")
print(f"runtime: {time.time() - T0:.1f}s  (deterministic: xorshift64* seed "
      f"0x{SEED:X})", file=sys.stderr)
print("=" * 96)
sys.exit(0 if FAILS == 0 else 1)
