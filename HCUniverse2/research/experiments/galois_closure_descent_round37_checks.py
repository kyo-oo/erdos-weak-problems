#!/usr/bin/env python3
# =============================================================================
# ROUND 37 CERTIFICATE — THE GALOIS-CLOSURE DESCENT FAMILY (R2' face (a'))
# Target: S18/S19/S20 — the non-Galois CM shapes at the committed census.
#
# COVERAGE (the file's self-description, ledger-111 discipline — every claim
# below has a matching check in this file):
#   V1 the census: degree 4 COMPLETE (the 2-generation sweep of S_4, 5
#      transitive classes = the classical count); degree 6 COMPLETE (the
#      2-generation sweep of S_6, 16 classes = the classical count); degree 8:
#      the 5 regular worlds (all abstract groups of order 8) + the order-16
#      automorphism-split worlds over them (complete in the
#      containing-a-regular-subgroup class); every world with a central
#      fixed-point-free involution rho (the CM condition).
#   V2 the descent model at EVERY world: the exterior sign cocycle law; the
#      mixed-orbit kill receipts; the dimension by TWO algorithms (the
#      orbit-count law vs the exact blockwise RREF of the equivariance system)
#      agreeing everywhere (bounded: pure-words * |G| <= 2600).
#   V3 THE CRUX: the primitive/induced classifier; the calibrations (the
#      binomial law dim = C(g,p) at every primitive type of every world; NS = g
#      at primitive; the split law C(g,p)^2 at every QUADRATIC-INDUCIBLE type
#      (any index-2 inducing H', not only the maximal-subfield-2 ones); the
#      product-world law NS > g at the deeper-induced types; the palindrome
#      law; top = 1; Round 36's receipts 2 / 3-9 / 6-18-36 / 1 reproduced
#      through the new engine); the SURPLUS = dim - product-span-rank at EVERY
#      world, EVERY type orbit, EVERY degree 2..2g -- the degree-2 entries
#      computed as dim - #basis-systems, genuine (THE THEOREM: surplus = 0
#      everywhere); the deterministic random-class nondegeneracy pass
#      (v^p != 0); the product-equivariance spot checks (subsample disclosed).
#   V4 the E x A extension worlds (bounded: the quartic + sextic worlds
#      COMPLETE + the octic representatives -- the 5 regular worlds and 3
#      automorphism-split order-16 worlds; E-frame base worlds <= 17,
#      disjoint-CM and subfield-coupled): the Hom-formula
#      calibration dim Hdg_2(E x A) = 1 + NS(A) + 2*matches + surplus = 0.
#   V5 the calibration anchor: the operator's arity totals 4/8/24/64/208
#      (two algorithms at every m <= 5) + m = 6 control (688, both algorithms)
#      + the cyclotomic product law det(I + C_L) = 1 - (-1)^L (Bareiss,
#      L = 2..12).
#   V6 the hostile battery (every control FIRES with the predicted failure:
#      basis-generator deletion, the wrong-sign cocycle flip, the
#      type-validity battery -- double-letter, missing-pair, duplicate-letter,
#      empty, at a canary world AND adversarially at every world -- the
#      unbalanced-word INJECTION into the filter's input list, the
#      garbage-injection liveness, the census pair-generation and
#      generator-deletion) + the mechanical vacuity scan + the
#      self-comparison scan.
#
# Bounds: degree <= 8, |G| <= 48 at degrees 4/6, |G| <= 16 at degree 8, words
# <= C(8,4) = 70, E-frame base worlds <= 17, zero floats, exact integer /
# Fraction arithmetic, memory < 300 MB. Deterministic: xorshift64* seed
# 0xD15EA5E5BADF00D (distinct from R32 0x9E3779B97F4A7C15, R34
# 0xC0FFEE123456789, R35 0xFEEDFACECAFEBEEF, R36 0xABCDEF9876543210).
# Expected runtime ~2-5 min (dominated by the degree-6 completeness sweep
# and the octic E x A frames).
#
# LEDGER 107/109/111 DISCIPLINE: every ok() message states the predicate
# ACTUALLY tested; the header coverage claims match the check inventory; the
# span sampler covers the full quantifier domain (the iterate-basis
# S_p = span(S_{p-1} ^ NS) includes the diagonal/repetition products by
# construction); every hostile control must FIRE.
# =============================================================================
import sys, time, re
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product as iproduct
from math import gcd, comb

T0 = time.time()
SEED = 0xD15EA5E5BADF00D
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

# ================================================================ the engine
def perms_of(d):
    res = []; cur = list(range(d))
    def rec(k):
        if k == d:
            res.append(tuple(cur)); return
        for v in range(d):
            if v not in cur[:k]:
                cur[k] = v; rec(k+1)
    rec(0)
    return res

def pcomp(p, q):
    return tuple(p[q[i]] for i in range(len(p)))

def pinv_t(p):
    r = [0]*len(p)
    for i in range(len(p)): r[p[i]] = i
    return tuple(r)

def closure_tuples(gen_tuples, d):
    ident = tuple(range(d))
    have = {ident}; frontier = [ident]
    gens = list(gen_tuples)
    while frontier:
        newf = []
        for x in frontier:
            for g in gens:
                y = pcomp(g, x)
                if y not in have:
                    have.add(y); newf.append(y)
        frontier = newf
    return frozenset(have)

class GCtx:
    def __init__(self, elem_tuples, d):
        self.d = d
        self.elems = sorted(elem_tuples)
        self.n = len(self.elems)
        self.idx = {p: i for i, p in enumerate(self.elems)}
        self.comp = [[self.idx[pcomp(p, q)] for q in self.elems] for p in self.elems]
        self.ident = self.idx[tuple(range(d))]

def word_action(ctx, g, U):
    p = ctx.elems[g]
    img = [p[u] for u in U]
    s = 1
    for i in range(len(img)):
        for j in range(i+1, len(img)):
            if img[i] > img[j]: s = -s
    return tuple(sorted(img)), s

def group_center_ids(ctx):
    res = []
    for c in range(ctx.n):
        okc = True
        for g in range(ctx.n):
            if ctx.comp[c][g] != ctx.comp[g][c]:
                okc = False; break
        if okc: res.append(c)
    return res

def is_fpf(ctx, g):
    p = ctx.elems[g]
    return all(p[i] != i for i in range(ctx.d))

def is_involution(ctx, g):
    return ctx.comp[g][g] == ctx.ident

def is_abelian(ctx):
    for a in range(ctx.n):
        for b in range(ctx.n):
            if ctx.comp[a][b] != ctx.comp[b][a]:
                return False
    return True

def is_transitive(ctx):
    seen = {0}; frontier = [0]
    while frontier:
        newf = []
        for v in frontier:
            for g in range(ctx.n):
                y = ctx.elems[g][v]
                if y not in seen:
                    seen.add(y); newf.append(y)
        frontier = newf
    return len(seen) == ctx.d

# ------------------------- the census sweeps --------------------------------
def census_sweep(d):
    elems = perms_of(d)
    idx = {p: i for i, p in enumerate(elems)}
    n = len(elems)
    comp = [[idx[pcomp(p, q)] for q in elems] for p in elems]
    def closure_ids(gen_ids):
        have = {0}; frontier = [0]
        while frontier:
            newf = []
            for x in frontier:
                for g in gen_ids:
                    y = comp[x][g]
                    if y not in have:
                        have.add(y); newf.append(y)
            frontier = newf
        return frozenset(have)
    cyclic_rep = {}
    for e in range(n):
        cy = closure_ids([e])
        if cy not in cyclic_rep:
            cyclic_rep[cy] = e
    found = set()
    for a in sorted(cyclic_rep.values()):
        pa = elems[a]
        for b in range(n):
            pb = elems[b]
            seen = {0}; frontier = [0]
            while frontier:
                newf = []
                for v in frontier:
                    for p in (pa, pb):
                        y = p[v]
                        if y not in seen:
                            seen.add(y); newf.append(y)
                frontier = newf
            if len(seen) == d:
                found.add(closure_ids([a, b]))
    tup = {G: sorted(elems[p] for p in G) for G in found}
    def canon(G):
        best = None
        for g in range(n):
            ginv_t = pinv_t(elems[g])
            t = tuple(sorted(pcomp(pcomp(elems[g], p), ginv_t) for p in tup[G]))
            if best is None or t < best:
                best = t
        return frozenset(best)
    classes = {}
    for G in sorted(found, key=lambda GG: tup[GG]):
        cn = canon(G)
        if cn not in classes:
            classes[cn] = frozenset(tup[G])
    return list(classes.values())

def groups_of_order_8():
    out = []
    el = [k for k in range(8)]
    def m8(x, y): return (x + y) % 8
    out.append(("C8", el, m8))
    el = [(i, j) for i in range(4) for j in range(2)]
    def m42(x, y): return ((x[0]+y[0]) % 4, (x[1]+y[1]) % 2)
    out.append(("C4xC2", el, m42))
    el = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]
    def m2(x, y): return tuple((x[i]+y[i]) % 2 for i in range(3))
    out.append(("C2^3", el, m2))
    el = [(i, j) for j in range(2) for i in range(4)]
    def md4(x, y):
        i1, j1 = x; i2, j2 = y
        return (((i1 + (i2 if j1 == 0 else (-i2) % 4)) % 4, (j1+j2) % 2))
    out.append(("D4", el, md4))
    def mq(x, y):
        table = {(1,1):(1,1),(1,"i"):(1,"i"),(1,"j"):(1,"j"),(1,"k"):(1,"k"),
                 ("i",1):(1,"i"),("i","i"):(-1,1),("i","j"):(1,"k"),("i","k"):(-1,"j"),
                 ("j",1):(1,"j"),("j","i"):((-1),"k"),("j","j"):(-1,1),("j","k"):(1,"i"),
                 ("k",1):(1,"k"),("k","i"):(1,"j"),("k","j"):((-1),"i"),("k","k"):(-1,1)}
        sx, ux = x; sy, uy = y
        sgn, v = table[(ux, uy)]
        return (sx*sy*sgn, v)
    el = [(1,1), (1,"i"), (1,"j"), (1,"k"), (-1,1), (-1,"i"), (-1,"j"), (-1,"k")]
    out.append(("Q8", el, mq))
    return out

def regular_perms(el, mult):
    return [tuple(el.index(mult(g, x)) for x in el) for g in el]

def aut_perms(el, mult):
    import itertools
    d = len(el)
    idx = {e: i for i, e in enumerate(el)}
    res = []
    for cand in itertools.permutations(range(d)):
        if cand[0] != 0:
            continue
        okc = True
        for a in range(d):
            for b in range(d):
                if cand[idx[mult(el[a], el[b])]] != idx[mult(el[cand[a]], el[cand[b]])]:
                    okc = False; break
            if not okc: break
        if okc:
            res.append(tuple(cand))
    return res

# ------------------------- the descent model --------------------------------
def rho_pairs(ctx, rho):
    p = ctx.elems[rho]
    seen = set(); pairs = []
    for x in range(ctx.d):
        if x in seen: continue
        y = p[x]
        pairs.append((min(x, y), max(x, y)))
        seen.add(x); seen.add(y)
    return pairs

def cm_types(pairs):
    res = []
    for choice in iproduct(*[range(2)]*len(pairs)):
        res.append(tuple(sorted(pairs[i][choice[i]] for i in range(len(pairs)))))
    return res

def is_valid_type(ctx, rho, Phi):
    pairs = rho_pairs(ctx, rho)
    for pr in pairs:
        c = sum(1 for x in pr if x in set(Phi))
        if c != 1:
            return False
    return len(Phi) == len(pairs)

def type_orbit_reps(ctx, types):
    reps = []; seen = set()
    for t in types:
        if t in seen: continue
        orb = set()
        for g in range(ctx.n):
            img, _ = word_action(ctx, g, t)
            orb.add(img)
        seen |= orb
        reps.append(t)
    return reps

def balanced_words(ctx, Phi, p):
    PhiS = set(Phi)
    res = []
    for U in combinations(range(ctx.d), 2*p):
        if sum(1 for u in U if u in PhiS) == p:
            res.append(tuple(U))
    return res

def pure_balanced(ctx, words, Phi, p):
    PhiS = set(Phi)
    res = []
    for U in words:
        okp = True
        for g in range(ctx.n):
            img, _ = word_action(ctx, g, U)
            if sum(1 for u in img if u in PhiS) != p:
                okp = False; break
        if okp:
            res.append(U)
    return res

def word_orbits(ctx, words):
    ws = set(words)
    res = []; seen = set()
    for U in sorted(ws):
        if U in seen: continue
        orb = set()
        for g in range(ctx.n):
            img, _ = word_action(ctx, g, U)
            if img in ws:
                orb.add(img)
        seen |= orb
        stab = sum(1 for g in range(ctx.n) if word_action(ctx, g, U)[0] == U)
        res.append((tuple(sorted(orb)), stab))
    return res

def cocycle_check(ctx, degrees=(2, 4)):
    """s(gg',U) = s(g, g'U) * s(g',U) for all g,g' and all words at the degrees."""
    for pdeg in degrees:
        for U in combinations(range(ctx.d), pdeg):
            for g in range(ctx.n):
                for h in range(ctx.n):
                    gh = ctx.comp[g][h]
                    img1, s1 = word_action(ctx, h, U)
                    img2, s2 = word_action(ctx, g, img1)
                    img3, s3 = word_action(ctx, gh, U)
                    if img2 != img3 or s1 * s2 != s3:
                        return False
    return True

def _rref_rank(rows, ncols):
    M = [list(r) for r in rows]
    nr = len(M)
    if nr == 0: return 0
    rank = 0
    for col in range(ncols):
        piv = None
        for r in range(rank, nr):
            if M[r][col] != 0:
                piv = r; break
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        pv = M[rank][col]
        for r in range(rank+1, nr):
            if M[r][col] != 0:
                f = M[r][col]
                for c in range(col, ncols):
                    M[r][c] = M[r][c]*pv - M[rank][c]*f
        rank += 1
        if rank == nr: break
    return rank

def hdg_dim_rref(ctx, pureset_sorted, Phi, p):
    n = ctx.n
    pureset = set(pureset_sorted)
    orbits = word_orbits(ctx, pureset_sorted)
    total = 0
    for orb, stab in orbits:
        U0 = orb[0]
        var = {}
        for U in orb:
            for j in range(n):
                var[(U, j)] = len(var)
        nv = len(var)
        rows = []
        for g in range(n):
            gU, sgn = word_action(ctx, g, U0)
            if gU not in pureset:
                continue
            for j in range(n):
                row = [0]*nv
                row[var[(gU, j)]] += 1
                row[var[(U0, ctx.comp[j][g])]] -= sgn
                rows.append(row)
        rs = set()
        for r in rows:
            t = tuple(r)
            if any(t):
                rs.add(t)
        rank = _rref_rank(sorted(rs), nv)
        total += nv - rank
    return total

def _kernel(rows, ncols):
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
        den = 1
        for x in v:
            if x != 0:
                den = den * x.denominator // gcd(den, x.denominator)
        ker.append([int(x*den) for x in v])
    return ker

def degree2_basis(ctx, Phi):
    n = ctx.n
    words = balanced_words(ctx, Phi, 1)
    pure = pure_balanced(ctx, words, Phi, 1)
    pureset = set(pure)
    orbits = word_orbits(ctx, sorted(pureset))
    basis = []
    for orb, stab in orbits:
        U0 = orb[0]
        rows = []
        for h in range(n):
            hU, sh = word_action(ctx, h, U0)
            if hU != U0: continue
            for j in range(n):
                row = [0]*n
                row[j] += 1
                row[ctx.comp[j][h]] -= sh
                rows.append(row)
        ker = _kernel(rows, n)
        for v in ker:
            sysd = {U0: list(v)}
            for g in range(n):
                gU, sgn = word_action(ctx, g, U0)
                if gU in sysd or gU not in pureset:
                    continue
                gv = [0]*n
                for j in range(n):
                    gv[j] = v[ctx.comp[j][g]] * sgn
                sysd[gU] = gv
            basis.append(sysd)
    return basis

def shuffle_sign(U, V):
    lst = list(U) + list(V)
    inv = 0
    for a in range(len(lst)):
        for b in range(a+1, len(lst)):
            if lst[a] > lst[b]: inv += 1
    return tuple(sorted(lst)), (-1 if inv % 2 else 1)

def ext_product(A, B, n):
    res = {}
    for U, cU in A.items():
        for V, dV in B.items():
            if set(U) & set(V): continue
            W, s = shuffle_sign(U, V)
            prod = [cU[j]*dV[j] for j in range(n)]
            if W in res:
                rw = res[W]
                for j in range(n):
                    rw[j] += s*prod[j]
            else:
                res[W] = [s*prod[j] for j in range(n)]
    return res

def _gcd_list(v):
    g = 0
    for x in v:
        if x:
            g = gcd(g, abs(x))
            if g == 1:
                return 1
    return g or 1

class IntRank:
    """Incremental exact integer rank maintenance (gcd-scaled rows)."""
    def __init__(self, ncols):
        self.ncols = ncols
        self.rows = []   # list of (pivot_col, int_row)
    def add(self, v):
        """Add integer vector v; return True if rank increased."""
        v = list(v)
        g = _gcd_list(v)
        if g > 1:
            v = [x // g for x in v]
        for piv, row in self.rows:
            if v[piv] != 0:
                f = v[piv]; pv = row[piv]
                v = [v[c]*pv - row[c]*f for c in range(self.ncols)]
                g = _gcd_list(v)
                if g > 1:
                    v = [x // g for x in v]
        for c in range(self.ncols):
            if v[c] != 0:
                self.rows.append((c, v))
                return True
        return False
    def rank(self):
        return len(self.rows)

def product_span_rank(ctx, Phi, d2, p):
    """Span rank of the p-fold divisor products at degree 2p, via the
    iterate basis S_k = span(S_{k-1} ^ NS) at each degree 2k (its own pure
    word coordinate space per level).  Includes all with-replacement
    (diagonal) products by construction (s can equal d).  Early exit when
    the span fills the target space."""
    n = ctx.n
    cur_systems = list(d2)   # degree-2 level: the NS basis systems
    for k in range(2, p+1):
        words_k = balanced_words(ctx, Phi, k)
        pure_k = sorted(set(pure_balanced(ctx, words_k, Phi, k)))
        word_ix = {W: i for i, W in enumerate(pure_k)}
        ncols = len(pure_k)*n
        def to_vec(sysd):
            v = [0]*ncols
            for W, co in sysd.items():
                i = word_ix.get(W)
                if i is not None:
                    for j in range(n):
                        v[i*n + j] = co[j]
            return v
        rk = IntRank(ncols)
        target = len(pure_k)
        new_systems = []
        done = False
        for s in cur_systems:
            if done:
                break
            for dsys in d2:
                pr = ext_product(s, dsys, n)
                if not pr:
                    continue
                v = to_vec(pr)
                if any(v) and rk.add(v):
                    new_systems.append(pr)
                    if rk.rank() >= target:
                        done = True
                        break
        cur_systems = new_systems
        if not cur_systems:
            return 0
    return len(cur_systems)

def analyze_world(ctx, rho, label, rref_cap=2600, do_products=True,
                  anchor_expected=None):
    """Full analysis; returns dict. anchor_expected: optional {Phi: [dims]}."""
    n = ctx.n; d = ctx.d; g = d // 2
    pairs = rho_pairs(ctx, rho)
    types = cm_types(pairs)
    toreps = type_orbit_reps(ctx, types)
    H_order = sum(1 for h in range(n) if ctx.elems[h][0] == 0)
    res = {"label": label, "g": g, "n": n, "H": H_order, "rows": []}
    for Phi in toreps:
        dims = []; spans = []; surps = []
        d2 = None
        for p in range(1, g+1):
            words = balanced_words(ctx, Phi, p)
            if not words:
                dims.append(0); spans.append(0); surps.append(0); continue
            pure = pure_balanced(ctx, words, Phi, p)
            dim = len(pure)
            ps = sorted(set(pure))
            if p == 1:
                d2 = degree2_basis(ctx, Phi)
                # AUDIT-37 F3 repair: genuine -- the degree-2 span is the
                # number of constructed basis systems; if the basis
                # construction dropped content the surplus fires (the old
                # `span = dim` was definitional at every degree-2 entry)
                span = len(d2)
            elif do_products:
                span = product_span_rank(ctx, Phi, d2, p)
            else:
                span = None
            dims.append(dim); spans.append(span)
            surps.append(None if span is None else dim - span)
        res["rows"].append({"Phi": Phi, "dims": dims, "spans": spans,
                            "surps": surps, "d2": d2})
    return res

def right_action_rep(ctx):
    """For each letter x, a representative g_x with g_x * 0 = x (so the
    letter x is the coset g_x H).  The RIGHT H'-action on letters is
    x -> (g_x h') * 0."""
    rep = {}
    for g in range(ctx.n):
        x = ctx.elems[g][0]
        if x not in rep:
            rep[x] = g
    return rep

def induced_subfield(ctx, rho, Phi):
    """The inducing CM subfield classifier: Phi is induced from the subfield
    k = K~^H' (H < H' < G, rho notin H' so k is CM) iff Phi is a union of
    RIGHT H'-orbits of letters (the fibers of pi: G/H -> G/H').  Returns
    (best, quad): best = the max such [K':Q] = n/|H'| or None (primitive);
    quad = True iff SOME index-2 H' (order n/2) stabilizes Phi -- the
    QUADRATIC-INDUCIBLE marker, the split law's full domain (wider than the
    max-degree-2 class: order-refined types with a deeper maximal subfield
    still carry the split row)."""
    n = ctx.n
    H = frozenset(h for h in range(n) if ctx.elems[h][0] == 0)
    rep = right_action_rep(ctx)
    elems_out = [h for h in range(n) if h not in H]
    cands = set()
    for a in elems_out:
        cands.add(frozenset(closure_ids_in(ctx, list(H) + [a])))
    for a in elems_out:
        for b in elems_out:
            if b <= a: continue
            cands.add(frozenset(closure_ids_in(ctx, list(H) + [a, b])))
    best = None
    quad = False
    for Hpr in cands:
        if not (H < Hpr) or len(Hpr) >= n:
            continue
        if rho in Hpr:
            continue
        # Phi stable under the RIGHT H'-action: x -> (g_x h')*0
        stable = True
        for h in Hpr:
            for x in Phi:
                y = ctx.elems[ctx.comp[rep[x]][h]][0]
                if y not in set(Phi):
                    stable = False; break
            if not stable:
                break
        if stable:
            deg = n // len(Hpr)
            if deg == 2:
                quad = True
            if best is None or deg > best:
                best = deg
    return best, quad

def closure_ids_in(ctx, gen_ids):
    have = {ctx.ident}; frontier = [ctx.ident]
    while frontier:
        newf = []
        for x in frontier:
            for g in gen_ids:
                y = ctx.comp[x][g]
                if y not in have:
                    have.add(y); newf.append(y)
        frontier = newf
    return frozenset(have)

# ================================================================ V1: THE CENSUS
print("=" * 96)
print("V1 -- THE CENSUS (degrees 4 and 6 complete; degree 8: regular + aut16)")
print("=" * 96)

timer("building degree-4 sweep")
d4_classes = census_sweep(4)
check(len(d4_classes) == 5, f"degree-4 census: the 2-generation sweep finds "
      f"{len(d4_classes)} transitive classes == the classical count 5")

d4_worlds = []
for ci, G in enumerate(d4_classes):
    ctx = GCtx(G, 4)
    check(is_transitive(ctx), f"degree-4 class |G|={ctx.n}: transitive")
    Z = group_center_ids(ctx)
    rhos = [c for c in Z if is_involution(ctx, c) and is_fpf(ctx, c)]
    if rhos:
        check(len(Z) > 0, f"degree-4 class |G|={ctx.n}: center nontrivial "
              f"({len(Z)} elements), {len(rhos)} central fpf involutions")
    for ri, r in enumerate(rhos):
        d4_worlds.append((ctx, r, is_abelian(ctx), f"d4-G{ctx.n}c{ci}r{ri}"))

timer("building degree-6 sweep (the completeness receipt)")
d6_classes = census_sweep(6)
check(len(d6_classes) == 16, f"degree-6 census: the 2-generation sweep finds "
      f"{len(d6_classes)} transitive classes == the classical count 16 "
      f"(the completeness receipt: every transitive subgroup of S_6 is "
      f"2-generated, cross-validated by the classical count)")

d6_worlds = []
d6_orders_seen = set()
for ci, G in enumerate(d6_classes):
    ctx = GCtx(G, 6)
    check(is_transitive(ctx), f"degree-6 class |G|={ctx.n}: transitive")
    Z = group_center_ids(ctx)
    rhos = [c for c in Z if is_involution(ctx, c) and is_fpf(ctx, c)]
    d6_orders_seen.add(ctx.n)
    for ri, r in enumerate(rhos):
        d6_worlds.append((ctx, r, is_abelian(ctx), f"d6-G{ctx.n}c{ci}r{ri}"))
check(sorted(w[0].n for w in d6_worlds) == [6, 12, 24, 48],
      f"degree-6 rho-worlds: orders {sorted(w[0].n for w in d6_worlds)} == "
      f"[6, 12, 24, 48] (the abelian C6 plus the three non-abelian classes)")

timer("building degree-8 worlds")
d8_worlds = []
seen_sets = set()
order8_names = []
for name, el, mult in groups_of_order_8():
    order8_names.append(name)
    regp = regular_perms(el, mult)
    Nset = frozenset(regp)
    seen_sets.add(Nset)
    ctxN = GCtx(Nset, 8)
    Z = group_center_ids(ctxN)
    rhos = [c for c in Z if is_involution(ctxN, c) and is_fpf(ctxN, c)]
    check(len(rhos) >= 1, f"degree-8 regular {name}: central fpf rho exists "
          f"({len(rhos)} candidates)")
    ab = is_abelian(ctxN)
    for ri, r in enumerate(rhos):
        d8_worlds.append((ctxN, r, ab, f"d8-reg-{name}r{ri}"))
    autos = aut_perms(el, mult)
    n16 = 0
    x16 = 0
    for pm in autos:
        if pm in Nset:
            continue
        Gset = closure_tuples(list(Nset) + [pm], 8)
        if len(Gset) == 16 and Gset not in seen_sets:
            seen_sets.add(Gset)
            ctxG = GCtx(Gset, 8)
            Zg = group_center_ids(ctxG)
            rhosg = [c for c in Zg if is_involution(ctxG, c) and is_fpf(ctxG, c)]
            if rhosg:
                n16 += 1
                x16 += 1
                for ri, r in enumerate(rhosg):
                    d8_worlds.append((ctxG, r, False,
                                      f"d8-aut16-{name}x{x16}r{ri}"))
    check(n16 >= 1, f"degree-8 automorphism worlds over {name}: {n16} distinct "
          f"order-16 subgroups with central fpf rho")
check(len(order8_names) == 5, f"the regular worlds: all 5 abstract groups of "
      f"order 8 constructed ({order8_names}; the classical count)")
# the 5 groups are pairwise non-isomorphic: involution counts 1/3/7/5/1 with
# C8 vs Q8 distinguished by exponent
inv_counts = {}
for name, el, mult in groups_of_order_8():
    c = sum(1 for g in el if g != el[0] and mult(g, g) == el[0])
    inv_counts[name] = c
check(sorted(inv_counts.values()) == [1, 1, 3, 5, 7],
      f"the 5 regular groups are pairwise non-isomorphic: involution counts "
      f"{sorted(inv_counts.values())} == [1, 1, 3, 5, 7] (C8/Q8 split by "
      f"exponent: max element order 8 vs 4)")
maxord = {}
for name, el, mult in groups_of_order_8():
    mo = 1
    ident = el[0]
    for g in el:
        x = g; k = 1
        while x != ident:
            x = mult(x, g); k += 1
        mo = max(mo, k)
    maxord[name] = mo
check(maxord["C8"] == 8 and maxord["Q8"] == 4,
      f"C8 vs Q8 distinguished: max element orders {maxord['C8']} vs "
      f"{maxord['Q8']}")

ALL_WORLDS = [(ctx, r, ab, lab) for (ctx, r, ab, lab) in
              (d4_worlds + d6_worlds + d8_worlds)]
check(len(ALL_WORLDS) == len(d4_worlds) + len(d6_worlds) + len(d8_worlds),
      f"census totals: d4={len(d4_worlds)}, d6={len(d6_worlds)}, "
      f"d8={len(d8_worlds)}, all={len(ALL_WORLDS)} (G,rho)-worlds")
timer(f"census complete: {len(ALL_WORLDS)} worlds")

# ================================================================ V2: THE MODEL
print("=" * 96)
print("V2 -- THE DESCENT MODEL AT EVERY WORLD (cocycle; mixed-orbit kill; 2 algos)")
print("=" * 96)

RREF_CAP = 2600
rref_agree_worlds = 0
kill_receipts = 0
for wi, (ctx, rho, ab, label) in enumerate(ALL_WORLDS):
    g = ctx.d // 2
    pairs = rho_pairs(ctx, rho)
    types = cm_types(pairs)
    toreps = type_orbit_reps(ctx, types)
    # (a) the cocycle law at this world
    degs = tuple(sorted(set([2, min(4, 2*g)])))
    check(cocycle_check(ctx, degs),
          f"[{label}] the exterior sign cocycle s(gh,U)=s(g,hU)s(h,U) at "
          f"degrees {list(degs)} (all g,h in G, all words)")
    # (b) the mixed-orbit kill + the two-algorithm dims at every type orbit
    agree = True
    for Phi in toreps:
        for p in range(1, g+1):
            words = balanced_words(ctx, Phi, p)
            if not words:
                continue
            pure = pure_balanced(ctx, words, Phi, p)
            dim = len(pure)
            ps = sorted(set(pure))
            if len(ps)*ctx.n <= RREF_CAP:
                dim2 = hdg_dim_rref(ctx, ps, Phi, p)
                if dim2 != dim:
                    agree = False
                    bad(f"[{label}] type {list(Phi)} deg {2*p}: orbit law {dim} "
                        f"!= RREF {dim2}")
        # kill receipt: at least one world shows a killed (mixed) orbit
        if g >= 2:
            words2 = balanced_words(ctx, Phi, 1)
            pure2 = set(pure_balanced(ctx, words2, Phi, 1))
            for U in words2:
                if U not in pure2:
                    kill_receipts += 1
                    break
    if agree:
        rref_agree_worlds += 1
    check(agree, f"[{label}] the two-algorithm dimension agreement: orbit law "
          f"== blockwise RREF at every type orbit and degree (bounded "
          f"pure*|G| <= {RREF_CAP})")
check(kill_receipts > 0, f"the mixed-orbit kill receipts: {kill_receipts} "
      f"type-orbits with killed (mixed) balanced words across the census "
      f"(the kill is live, not vacuous)")
timer(f"V2 complete: two-algorithm agreement at {rref_agree_worlds}/{len(ALL_WORLDS)} worlds")

# ================================================================ V3: THE CRUX
print("=" * 96)
print("V3 -- THE CRUX: classifier, calibrations, SURPLUS at every world/type/degree")
print("=" * 96)

def binom_row(g):
    return [comb(g, p) for p in range(1, g+1)]

def split_row(g):
    return [comb(g, p)**2 for p in range(1, g+1)]

surpluses_total = 0
surpluses_nonzero = []
prim_count = 0
ind_count = 0
quad_count = 0
R36_RECEIPTS_SEEN = set()
for wi, (ctx, rho, ab, label) in enumerate(ALL_WORLDS):
    g = ctx.d // 2
    pairs = rho_pairs(ctx, rho)
    toreps = type_orbit_reps(ctx, cm_types(pairs))
    res = analyze_world(ctx, rho, label, rref_cap=RREF_CAP, do_products=True)
    for row in res["rows"]:
        Phi = row["Phi"]; dims = row["dims"]; surps = row["surps"]
        ind_deg, quad = induced_subfield(ctx, rho, Phi)
        pal = all(dims[i] == dims[g-2-i] for i in range(max(0, g-1)))
        check(pal, f"[{label}] type {list(Phi)}: the hard-Lefschetz palindrome "
              f"dim(2p) == dim(2g-2p) for 1 <= p <= g-1: dims {dims}")
        check(dims[-1] == 1, f"[{label}] type {list(Phi)}: the top degree "
              f"dim Hdg_(2g) = {dims[-1]} == 1 (the point class)")
        if ind_deg is None:
            prim_count += 1
            exp = binom_row(g)
            check(dims == exp, f"[{label}] PRIMITIVE type {list(Phi)}: the "
                  f"binomial law dims {dims} == C(g,p) row {exp} (Weil/Rosati: "
                  f"NS = {dims[0]} == g)")
        else:
            ind_count += 1
            if quad:
                # AUDIT-37 F2 repair: the split law checked at EVERY
                # quadratic-inducible orbit (any index-2 stabilizing H'),
                # not only the maximal-subfield-degree-2 ones
                quad_count += 1
                exp = split_row(g)
                check(dims == exp, f"[{label}] SPLIT (quadratic-inducible) "
                      f"type {list(Phi)}: the split law dims {dims} == "
                      f"C(g,p)^2 row {exp} (an index-2 H' stabilizes the "
                      f"type; maximal inducing degree {ind_deg})")
            else:
                check(dims[0] > g, f"[{label}] induced (degree {ind_deg} "
                      f"subfield, not quadratic-inducible) type {list(Phi)}: "
                      f"NS = {dims[0]} > g (the product-world value; "
                      f"dims {dims})")
        # THE SURPLUS
        for p in range(g):
            if surps[p] is None:
                continue
            surpluses_total += 1
            if surps[p] != 0:
                surpluses_nonzero.append((label, list(Phi), 2*(p+1), surps[p]))
        sall = [s for s in surps if s is not None]
        check(all(s == 0 for s in sall),
              f"[{label}] type {list(Phi)}: SURPLUS = 0 at every degree: "
              f"dims {dims} spans {row['spans']} (the divisor products span "
              f"the whole Hodge space)")
        # the R36 receipts through the new engine (label-free conditions)
        if ctx.d == 4 and dims == [2, 1] and ind_deg is None:
            R36_RECEIPTS_SEEN.add("quartic-1")
        if ctx.d == 6 and dims == [3, 3, 1] and ind_deg is None:
            R36_RECEIPTS_SEEN.add("sextic-3")
        if ctx.d == 6 and dims == [9, 9, 1]:
            R36_RECEIPTS_SEEN.add("sextic-9")
        if ctx.d == 8 and dims == [4, 6, 4, 1] and ind_deg is None:
            R36_RECEIPTS_SEEN.add("octic-6")
        if ctx.d == 8 and dims == [8, 18, 8, 1]:
            R36_RECEIPTS_SEEN.add("octic-18")
        if ctx.d == 8 and dims == [16, 36, 16, 1]:
            R36_RECEIPTS_SEEN.add("octic-36")

check(len(surpluses_nonzero) == 0,
      f"THE CENTRAL TABLE: {surpluses_total} (world, type, degree) surplus "
      f"entries computed (every degree 2..2g; the degree-2 entries as "
      f"dim - #basis-systems, genuine), {len(surpluses_nonzero)} nonzero -- "
      f"SURPLUS = 0 EVERYWHERE (S19 at the committed census)")
check(R36_RECEIPTS_SEEN == {"quartic-1", "sextic-3", "sextic-9",
                            "octic-6", "octic-18", "octic-36"},
      f"Round 36's receipts reproduced through the new engine: "
      f"{sorted(R36_RECEIPTS_SEEN)} == [octic-18, octic-36, octic-6, "
      f"quartic-1, sextic-3, sextic-9] (the 1/3/9/6/18/36 anchor set)")
check(prim_count > 0 and ind_count > 0 and quad_count > 0,
      f"the classifier is live: {prim_count} primitive type-orbits "
      f"(binomial law), {ind_count} induced type-orbits of which "
      f"{quad_count} quadratic-inducible (the split law C(g,p)^2, checked "
      f"at each) and {ind_count - quad_count} deeper-induced (the "
      f"product-world law NS > g) across the census")
timer(f"V3 complete: {surpluses_total} surplus entries, {len(surpluses_nonzero)} nonzero")

# the random-class nondegeneracy pass (ledger-111): v = a deterministic
# pseudo-random Q-combination of the divisor basis; v^p != 0 at every degree
print("-- the random-class nondegeneracy pass (v^p != 0 at every degree) --")
ndeg_worlds = 0
for wi, (ctx, rho, ab, label) in enumerate(ALL_WORLDS):
    g = ctx.d // 2
    toreps = type_orbit_reps(ctx, cm_types(rho_pairs(ctx, rho)))
    alive = True
    for Phi in toreps:
        d2 = degree2_basis(ctx, Phi)
        if not d2:
            # AUDIT-37 repair (the A2 caveat): fail-closed -- an empty
            # degree-2 basis contradicts NS >= 1; never silently alive
            alive = False
            continue
        # deterministic pseudo-random combination, with bounded retries:
        # a single draw can land on a degenerate combination (v^p = 0 for
        # special v even when the generic v is nonzero); the receipt is the
        # EXISTENCE of a deterministic nonzero draw (ledger-111 sampler
        # robustness: the claim is 'some v fires', not 'every v fires')
        def draw_v(trial):
            vv = {}
            for k, dsys in enumerate(d2):
                a = ((nxt() + trial * 7) % 19) - 9
                if a == 0:
                    a = 1 + (trial % 2)
                for W, co in dsys.items():
                    if W in vv:
                        for j in range(ctx.n):
                            vv[W][j] += a * co[j]
                    else:
                        vv[W] = [a * c for c in co]
            return vv
        def v_works(v):
            acc = v
            for p in range(2, g+1):
                words = balanced_words(ctx, Phi, p)
                if not words:
                    continue
                pure = pure_balanced(ctx, words, Phi, p)
                if not pure:
                    continue
                acc = ext_product(acc, v, ctx.n)
                if not acc or all(all(c == 0 for c in co) for co in acc.values()):
                    return False
            return True
        if not any(v_works(draw_v(t)) for t in range(4)):
            alive = False
    if alive:
        ndeg_worlds += 1
    check(alive, f"[{label}] the random-class pass: some deterministic draw "
          f"v (up to 4 retries, xorshift64*) has v^p != 0 at every degree "
          f"2..2g (the polarization-type nondegeneracy receipt)")
check(ndeg_worlds == len(ALL_WORLDS),
      f"the random-class nondegeneracy holds at all {ndeg_worlds}/"
      f"{len(ALL_WORLDS)} worlds")
timer("random-class pass complete")

# the product-equivariance spot check: products of solutions are solutions
print("-- the product-equivariance spot checks --")
peq_ok = True
peq_checked = 0
for wi, (ctx, rho, ab, label) in enumerate(ALL_WORLDS[:24]):
    g = ctx.d // 2
    toreps = type_orbit_reps(ctx, cm_types(rho_pairs(ctx, rho)))
    Phi = toreps[0]
    d2 = degree2_basis(ctx, Phi)
    if len(d2) < 2:
        continue
    peq_checked += 1
    pr = ext_product(d2[0], d2[1], ctx.n)
    # verify the equivariance: c_{gU} = g(c_U) * s(g,U) on the product support
    for g in range(ctx.n):
        for W in list(pr.keys())[:6]:
            cW = pr[W]
            if all(c == 0 for c in cW):
                continue
            gW, sgn = word_action(ctx, g, W)
            lhs = pr.get(gW)
            if lhs is None:
                peq_ok = False
                continue
            okg = True
            for j in range(ctx.n):
                want = sgn * cW[ctx.comp[j][g]]
                if lhs[j] != want:
                    okg = False
                    break
            if not okg:
                peq_ok = False
check(peq_ok, f"the product-equivariance spot checks ({peq_checked} of the "
      f"first 24 worlds actually checked -- worlds with < 2 basis systems "
      f"skipped; per world: the first type orbit, the d2[0]*d2[1] product, "
      f"the first 6 support words): products of descent systems satisfy the "
      f"equivariance relation c_(gU) = g(c_U) s(g,U) (the span computation's "
      f"basis)")
timer("product-equivariance spot checks complete")

# ================================================================ V4: E x A
print("=" * 96)
print("V4 -- THE E x A EXTENSION WORLDS (bounded; Hom-formula calibrations)")
print("=" * 96)

def disjoint_EA_world(ctxA, rhoA):
    """The product world C2 x G acting on 2+2g letters (E disjoint from A)."""
    d = ctxA.d
    letters = 2 + d
    sw = (1, 0)
    elems = []
    for a2 in (tuple(range(2)), sw):
        for g in ctxA.elems:
            perm = [0]*letters
            perm[0] = a2[0]; perm[1] = a2[1]
            for i in range(d):
                perm[2+i] = 2 + g[i]
            elems.append(tuple(perm))
    ctx = GCtx(elems, letters)
    rho_perm = [0]*letters
    rho_perm[0] = sw[0]; rho_perm[1] = sw[1]
    for i in range(d):
        rho_perm[2+i] = 2 + ctxA.elems[rhoA][i]
    rho = ctx.idx[tuple(rho_perm)]
    return ctx, rho

def coupled_EA_worlds(ctxA, rhoA, PhiA):
    """The joint G-action on G/H_k (E-letters) + G/H (A-letters), for each
    CM quadratic subfield k (H < H_k, rho notin H_k, |H_k| = |G|/2)."""
    n = ctxA.n; d = ctxA.d
    H = frozenset(h for h in range(n) if ctxA.elems[h][0] == 0)
    # coset structure: A-letters = G/H (points 0..d-1 of ctxA), letter i =
    # the coset of the element mapping 0 -> i
    rep = {}
    for g in range(n):
        i = ctxA.elems[g][0]
        if i not in rep:
            rep[i] = g
    res = []
    # candidate H_k: order n/2 subgroups containing H, not containing rho
    cands = set()
    for a in range(n):
        if a in H: continue
        cands.add(frozenset(closure_ids_in(ctxA, list(H) + [a])))
    for Hk in cands:
        if len(Hk) != n // 2 or not (H < Hk) or rhoA in Hk:
            continue
        # E-letters = cosets G/H_k: two of them; the joint action
        # E-letter for coset of g: g H_k; A-letter i for coset rep[i] H
        letters = 2 + d
        elems = []
        for g in range(n):
            perm = [0]*letters
            # E-part: g sends coset xHk -> gxHk; the two cosets represented
            # by e0 = identity and e1 = some element outside Hk
            e1 = None
            for x in range(n):
                if x not in Hk:
                    e1 = x; break
            # coset of identity = Hk; coset of e1
            # g * Hk:
            tgt0 = 0 if ctxA.comp[g][next(iter(Hk))] in Hk else 1
            tgt1 = 1 - tgt0
            perm[0] = tgt0; perm[1] = tgt1
            for i in range(d):
                perm[2+i] = 2 + ctxA.elems[g][i]
            elems.append(tuple(perm))
        ctxJ = GCtx(elems, letters)
        rho_perm = [0]*letters
        # rho acts on E-letters: rho*Hk = Hk iff rho in Hk (excluded) -> swaps
        rho_perm[0] = 1; rho_perm[1] = 0
        for i in range(d):
            rho_perm[2+i] = 2 + ctxA.elems[rhoA][i]
        rhoJ = ctxJ.idx[tuple(rho_perm)]
        # the projection pi: G/H -> G/H_k: letter x (coset rep[x]H) sits in
        # the H_k-coset of rep[x].  matches_for(PhiE): the A-letters of a
        # type that project to the CHOSEN E-letter.  E-letter 0 = the
        # identity H_k-coset; E-letter 1 = the other.  (Early-binding
        # factory: the closure must capture THIS Hk, not the loop's final
        # value -- the late-binding variant was this file's own F-class
        # defect, caught by the coupled-frame calibrations firing.)
        def _make_matches(_ctxA, _rep, _Hk):
            _hk_el = next(iter(_Hk))
            def matches_of(PhiE_letter, PhiA_letters):
                cnt = 0
                for x in PhiA_letters:
                    gx = _rep[x]
                    inHk = _ctxA.comp[gx][_hk_el] in _Hk
                    if (inHk and PhiE_letter == 0) or (not inHk and PhiE_letter == 1):
                        cnt += 1
                return cnt
            return matches_of
        res.append((ctxJ, rhoJ, _make_matches(ctxA, rep, Hk)))
    return res

ea_worlds_checked = 0
ea_surplus_nonzero = 0
# bounded E-frame base census (AUDIT-37 F1 repair): the quartic + sextic
# worlds COMPLETE + the octic representatives -- the first rho-world of each
# of the 5 regular base names and of the first 3 automorphism-split base
# names (x-index-disambiguated); base worlds <= 17
base_selection = []
for (ctx, r, ab, label) in d4_worlds + d6_worlds:
    base_selection.append((ctx, r, ab, label))
oct_reg_bases = []
oct_aut_bases = []
for (ctx, r, ab, label) in d8_worlds:
    base = label.rsplit("r", 1)[0]   # e.g. "d8-reg-C8" / "d8-aut16-C2^3x1"
    if base.startswith("d8-reg-"):
        if base not in [b for b, _ in oct_reg_bases]:
            oct_reg_bases.append((base, (ctx, r, ab, label)))
    else:
        gbase = base[:base.rfind("x")]   # the base GROUP (strip the G-set index)
        if gbase not in [b for b, _ in oct_aut_bases]:
            oct_aut_bases.append((gbase, (ctx, r, ab, label)))
for _b, w in oct_reg_bases:
    base_selection.append(w)
for _b, w in oct_aut_bases[:3]:
    base_selection.append(w)

for (ctxA, rhoA, ab, label) in base_selection:
    gA = ctxA.d // 2
    toreps = type_orbit_reps(ctxA, cm_types(rho_pairs(ctxA, rhoA)))
    # the disjoint E x A world
    ctxJ, rhoJ = disjoint_EA_world(ctxA, rhoA)
    pairsJ = rho_pairs(ctxJ, rhoJ)
    torepsJ = type_orbit_reps(ctxJ, cm_types(pairsJ))
    for PhiJ in torepsJ[:2]:
        resJ = analyze_world(ctxJ, rhoJ, f"EA-disj-{label}", rref_cap=RREF_CAP)
        for row in resJ["rows"][:2]:
            dims = row["dims"]; surps = [s for s in row["surps"] if s is not None]
            PhiA_part = tuple(x-2 for x in row["Phi"] if x >= 2)
            # expected NS: 1 + NS(A) + 0 (disjoint: no Hom)
            dA = len(pure_balanced(ctxA, balanced_words(ctxA, PhiA_part, 1),
                                   PhiA_part, 1)) if PhiA_part else 0
            check(dims[0] == 1 + dA,
                  f"[EA-disj-{label}] disjoint frame type {list(row['Phi'])}: "
                  f"dim Hdg_2 = {dims[0]} == 1 + NS(A)={dA} (the tensor law, "
                  f"no Hom)")
            check(all(s == 0 for s in surps),
                  f"[EA-disj-{label}] disjoint frame type {list(row['Phi'])}: "
                  f"SURPLUS = 0 at every degree (dims {dims})")
            ea_worlds_checked += 1
            if any(s != 0 for s in surps):
                ea_surplus_nonzero += 1
    # the coupled E x A worlds (where a CM quadratic subfield exists)
    PhiA0 = toreps[0]
    for (ctxC, rhoC, matches_of) in coupled_EA_worlds(ctxA, rhoA, PhiA0):
        pairsC = rho_pairs(ctxC, rhoC)
        torepsC = type_orbit_reps(ctxC, cm_types(pairsC))
        for PhiC in torepsC[:2]:
            # the A-part and E-part of the joint type
            PhiA_part = tuple(x-2 for x in PhiC if x >= 2)
            PhiE_part = tuple(x for x in PhiC if x < 2)
            if not PhiA_part or not PhiE_part:
                continue
            # the fiber rule (calibrated on E^3 = 9, E^4 = 16, the
            # different-CM products = 5): the A-type that is a FULL k-fiber
            # (over either k-letter) carries dimHom = 2*|Phi_A|; a
            # straddling type carries dimHom = 0 (no elliptic subvarieties
            # in the simple worlds; different CM fields in the split ones)
            m0 = matches_of(0, PhiA_part)
            m1 = matches_of(1, PhiA_part)
            full_fiber = (m0 == len(PhiA_part)) or (m1 == len(PhiA_part))
            mA = len(pure_balanced(ctxA, balanced_words(ctxA, PhiA_part, 1),
                                   PhiA_part, 1))
            if full_fiber:
                expNS = 1 + mA + 2*len(PhiA_part)
                why = (f"1 + NS(A)={mA} + 2*|Phi_A|={2*len(PhiA_part)} "
                       f"(the full-fiber Hom law: E x A = the E^{g+1}-world)")
            else:
                expNS = 1 + mA
                why = (f"1 + NS(A)={mA} + 0 (the straddling type: dimHom = 0, "
                       f"no elliptic subvarieties / different CM fields)")
            resC = analyze_world(ctxC, rhoC, f"EA-coup-{label}", rref_cap=RREF_CAP)
            for row in resC["rows"]:
                if tuple(x-2 for x in row["Phi"] if x >= 2) != PhiA_part:
                    continue
                dims = row["dims"]; surps = [s for s in row["surps"] if s is not None]
                check(dims[0] == expNS,
                      f"[EA-coup-{label}] coupled frame type {list(row['Phi'])}: "
                      f"dim Hdg_2 = {dims[0]} == {why}")
                check(all(s == 0 for s in surps),
                      f"[EA-coup-{label}] coupled frame type {list(row['Phi'])}: "
                      f"SURPLUS = 0 at every degree (dims {dims})")
                ea_worlds_checked += 1
                if any(s != 0 for s in surps):
                    ea_surplus_nonzero += 1
                break
            break
check(ea_worlds_checked >= 12,
      f"the E x A extension: {ea_worlds_checked} joint frames analyzed "
      f"(disjoint + coupled), Hom-formula calibrated")
check(ea_surplus_nonzero == 0,
      f"the E x A extension: SURPLUS = 0 at every joint frame "
      f"({ea_surplus_nonzero} nonzero)")
timer(f"V4 complete: {ea_worlds_checked} E x A frames")

# ================================================================ V5: THE ANCHOR
print("=" * 96)
print("V5 -- THE CALIBRATION ANCHOR (the operator's arity totals, engine continuity)")
print("=" * 96)

OPERATOR_TOTALS = {1: 4, 2: 8, 3: 24, 4: 64, 5: 208}

def cyclotomic_character_formula(m):
    from math import gcd as _gcd
    total = 2 ** (2 * m)
    for j in range(1, m):
        gj = _gcd(j, m)
        Lj = m // gj
        total += (1 - (-1) ** Lj) ** (2 * gj)
    return total // m

def brute_force_signed_exterior(m):
    n_letters = 2 * m
    chi = []
    for k in range(m):
        total = 0
        for S in range(1 << n_letters):
            sub = [i for i in range(n_letters) if (S >> i) & 1]
            img = []
            for i in sub:
                if i < m:
                    img.append((i + k) % m)
                else:
                    img.append(m + ((i - m + k) % m))
            if sorted(img) == sorted(sub) and len(img) == len(set(img)):
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
    check(f == v, f"the operator's arity total at m={m}: the cyclotomic "
          f"character formula gives {f} == {v}")
    bf = brute_force_signed_exterior(m)
    check(bf == v, f"the operator's arity total at m={m}: the brute-force "
          f"signed exterior character sum gives {bf} == {v}")

f6 = cyclotomic_character_formula(6)
check(f6 == 688, f"the m=6 agreement control: the cyclotomic character formula "
      f"gives {f6} == 688 (the third committed value)")
bf6 = brute_force_signed_exterior(6)
check(bf6 == 688, f"the m=6 agreement control, second algorithm: the "
      f"brute-force signed exterior character sum gives {bf6} == 688")

# the cyclotomic product law, exact: det(I + C_L) = 1 - (-1)^L
def bareiss_det(M):
    M = [list(r) for r in M]
    nn = len(M)
    if nn == 1:
        return M[0][0]
    sign = 1; prev = 1
    for i in range(nn - 1):
        if M[i][i] == 0:
            for r in range(i+1, nn):
                if M[r][i] != 0:
                    M[i], M[r] = M[r], M[i]
                    sign = -sign
                    break
            else:
                return 0
        for r in range(i+1, nn):
            for c in range(i+1, nn):
                M[r][c] = (M[r][c]*M[i][i] - M[r][i]*M[i][c]) // prev
        prev = M[i][i]
    return sign * M[nn-1][nn-1]

for L in range(2, 13):
    # companion matrix of x^L - 1 (the L-cycle)
    C = [[0]*L for _ in range(L)]
    for i in range(L - 1):
        C[i][i+1] = 1
    C[L-1][0] = 1
    IC = [[(1 if i == j else 0) + C[i][j] for j in range(L)] for i in range(L)]
    d = bareiss_det(IC)
    check(d == 1 - (-1) ** L, f"the cyclotomic engine, exact: det(I + C_{L}) "
          f"= {d} == 1 - (-1)^{L} = {1 - (-1)**L} (exact Bareiss)")
timer("V5 complete")

# ================================================================ V6: HOSTILE + SCANS
print("=" * 96)
print("V6 -- THE HOSTILE BATTERY (every control FIRES) + THE SCANS")
print("=" * 96)

# H1: basis-generator deletion -- the span must DROP
ctxH, rhoH, _, labH = d6_worlds[1] if len(d6_worlds) > 1 else d6_worlds[0]
torepsH = type_orbit_reps(ctxH, cm_types(rho_pairs(ctxH, rhoH)))
PhiH = None
for t in torepsH:
    d2 = degree2_basis(ctxH, t)
    pure1 = pure_balanced(ctxH, balanced_words(ctxH, t, 1), t, 1)
    if len(d2) == len(pure1) and len(d2) >= 2:
        PhiH = t; break
if PhiH is None:
    PhiH = torepsH[0]
d2H = degree2_basis(ctxH, PhiH)
pure4H = sorted(set(pure_balanced(ctxH, balanced_words(ctxH, PhiH, 2), PhiH, 2)))
true_rank = product_span_rank(ctxH, PhiH, d2H, 2)
true_dim = len(pure4H)
if len(d2H) >= 2:
    d2_del = d2H[:-1]
    del_rank = product_span_rank(ctxH, PhiH, d2_del, 2)
    check(del_rank < true_rank,
          f"H1 BASIS-DELETION FIRES: deleting one degree-2 basis generator "
          f"at {labH} drops the degree-4 span rank {true_rank} -> {del_rank} "
          f"(the span check is load-bearing, fail-closed)")
else:
    check(False, "H1 could not run (no world with >= 2 basis generators)")

# H2: the wrong-sign cocycle flip -- the block dimension must CHANGE
def hdg_dim_rref_flipped(ctx, pureset_sorted, Phi, p, flip_site):
    n = ctx.n
    pureset = set(pureset_sorted)
    orbits = word_orbits(ctx, pureset_sorted)
    total = 0
    for orb, stab in orbits:
        U0 = orb[0]
        var = {}
        for U in orb:
            for j in range(n):
                var[(U, j)] = len(var)
        nv = len(var)
        rows = []
        for g in range(n):
            gU, sgn = word_action(ctx, g, U0)
            if gU not in pureset:
                continue
            if (g, U0) == flip_site:
                sgn = -sgn
            for j in range(n):
                row = [0]*nv
                row[var[(gU, j)]] += 1
                row[var[(U0, ctx.comp[j][g])]] -= sgn
                rows.append(row)
        rs = set()
        for r in rows:
            t = tuple(r)
            if any(t):
                rs.add(t)
        rank = _rref_rank(sorted(rs), nv)
        total += nv - rank
    return total

# find a load-bearing flip site: an orbit with nontrivial stabilizer action
flip_found = False
flip_dim_true = None
flip_dim_bad = None
for (g0, U0c) in [(g0, U0c) for g0 in range(ctxH.n) for U0c in pure4H]:
    gU, _ = word_action(ctxH, g0, U0c)
    if gU in set(pure4H) and gU != U0c:
        d_true = hdg_dim_rref(ctxH, pure4H, PhiH, 2)
        d_flip = hdg_dim_rref_flipped(ctxH, pure4H, PhiH, 2, (g0, U0c))
        if d_flip != d_true:
            flip_found = True
            flip_dim_true = d_true
            flip_dim_bad = d_flip
            break
check(flip_found,
      f"H2 WRONG-SIGN FIRES: flipping the cocycle sign s(g,U0) at one "
      f"load-bearing site at {labH} changes the exact block dimension "
      f"{flip_dim_true} -> {flip_dim_bad} (the sign is load-bearing, "
      f"fail-closed)")

# H3: the fake type -- an invalid type (two letters from one rho-pair) must
# be REJECTED by the validity predicate
ctxF, rhoF, _, labF = d4_worlds[0]
pairsF = rho_pairs(ctxF, rhoF)
fake_Phi = tuple(sorted([pairsF[0][0], pairsF[0][1]]))
check(not is_valid_type(ctxF, rhoF, fake_Phi),
      f"H3 FAKE-TYPE FIRES: the invalid type {list(fake_Phi)} (both letters "
      f"of one rho-pair) is rejected by the type-validity predicate")
# H3b/H3c/H3d (AUDIT-37 S3b repair): the OTHER violation directions of the
# one-per-pair law -- missing-pair (under-length), duplicate-letter, empty --
# must each be REJECTED; and the adversarial battery runs at EVERY world (a
# lenient predicate in any single direction survives H3 alone: the planted-
# sabotage class the fresh agent demonstrated live)
validF = cm_types(pairsF)[0]
missing_Phi = validF[:-1]
dup_Phi = tuple(sorted(validF + (validF[0],)))
empty_Phi = ()
check(not is_valid_type(ctxF, rhoF, missing_Phi),
      f"H3b MISSING-PAIR FIRES: the under-length type {list(missing_Phi)} "
      f"(one rho-pair left unchosen) is rejected by the type-validity "
      f"predicate")
check(not is_valid_type(ctxF, rhoF, dup_Phi),
      f"H3c DUPLICATE-LETTER FIRES: the type {list(dup_Phi)} (a repeated "
      f"letter) is rejected by the type-validity predicate")
check(not is_valid_type(ctxF, rhoF, empty_Phi),
      f"H3d EMPTY-TYPE FIRES: the empty type () is rejected by the "
      f"type-validity predicate")
adv_bad = []
for (ctxV, rhoV, _, labV) in ALL_WORLDS:
    pairsV = rho_pairs(ctxV, rhoV)
    tv = cm_types(pairsV)[0]
    if is_valid_type(ctxV, rhoV, tuple(sorted([pairsV[0][0], pairsV[0][1]]))):
        adv_bad.append((labV, "double"))
    if is_valid_type(ctxV, rhoV, tv[:-1]):
        adv_bad.append((labV, "missing"))
    if is_valid_type(ctxV, rhoV, tuple(sorted(tv + (tv[0],)))):
        adv_bad.append((labV, "dup"))
    if is_valid_type(ctxV, rhoV, ()):
        adv_bad.append((labV, "empty"))
check(not adv_bad,
      f"H3-ADVERSARIAL: the one-per-pair predicate rejects all four "
      f"violation directions (double/missing/duplicate/empty) at every one "
      f"of the {len(ALL_WORLDS)} census worlds (accepted: {adv_bad[:4]})")

# H4 (AUDIT-37 F4 repair): the unbalanced word is INJECTED INTO the purity
# filter's input list -- it must be dropped while every balanced word
# survives (the old check tested exclusion from a list that never contained
# it: vacuous by construction)
wordsF = balanced_words(ctxH, PhiH, 2)
unb = None
for U in combinations(range(ctxH.d), 4):
    if U not in set(wordsF):
        unb = U
        break
pureF = set(pure_balanced(ctxH, wordsF, PhiH, 2))
pureF_inj = set(pure_balanced(ctxH, list(wordsF) + ([unb] if unb is not None else []),
                                PhiH, 2))
check(unb is not None and unb not in pureF_inj and pureF_inj == pureF,
      f"H4 UNBALANCED-INJECTION FIRES: the unbalanced word {list(unb)} "
      f"injected into the filter's input list is dropped by the purity "
      f"filter while all {len(pureF)} balanced words survive (the "
      f"mixed-orbit kill is live, fail-closed)")

# H5: the garbage-injection liveness -- a deliberately false predicate must
# be reported by the check framework (the bad() path fires and is retracted)
_g_pre_f = FAILS
_planted = (len(d2H) == len(d2H) + 1)
check(_planted,
      "H5 GARBAGE-LIVENESS: the planted false predicate was reported as a "
      "failure (the framework's failure path is live)")
_h5_fired = (FAILS == _g_pre_f + 1)
if _h5_fired:
    FAILS -= 1
    FAIL_LINES.pop()
check(_h5_fired,
      "H5 GARBAGE-LIVENESS FIRES: the planted false comparison was counted "
      "as a failure by the framework and retracted (the failure path is "
      "live, not decorative)")

# H6 (AUDIT-37 F5 repair): the census class is regenerated by a CERTIFIED
# generating pair (the 2-generation claim), and deleting either generator
# shrinks the closure.  The old check closed over the identity tuple alone
# (closure({id}) < |G| always: decorative).  The D4 class is non-cyclic, so
# neither single element regenerates it -- the check is genuine, fail-closed.
GD = d4_classes[2] if len(d4_classes) > 2 else d4_classes[0]
GDe = sorted(GD)
gen_pair = None
for ai in range(len(GDe)):
    for bi in range(ai + 1, len(GDe)):
        cl = closure_tuples([GDe[ai], GDe[bi]], 4)
        if frozenset(cl) == frozenset(GD):
            gen_pair = (GDe[ai], GDe[bi])
            break
    if gen_pair:
        break
check(gen_pair is not None,
      f"H6 PAIR-GENERATION: the census class (|G|={len(GD)}) is regenerated "
      f"exactly by a certified generating pair (the 2-generation closure "
      f"is load-bearing)")
if gen_pair is not None:
    sub_a = closure_tuples([gen_pair[0]], 4)
    sub_b = closure_tuples([gen_pair[1]], 4)
    check(len(sub_a) < len(GD) and len(sub_b) < len(GD),
          f"H6 GENERATOR-DELETION FIRES: deleting either generator of the "
          f"certified pair shrinks the group {len(GD)} -> {len(sub_a)} / "
          f"{len(sub_b)} (single-generation cannot regenerate the class)")

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
check(len(hits) == 0, f"the mechanical vacuity scan (ledger 107) over this "
      f"file's own source (the scan region excluded): {len(hits)} hits for "
      f"the banned boolean-literal patterns")

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
check(sc == 0, f"the self-comparison scan (ledger 107): {sc} hits (no "
      f"variable is compared to itself within 3 lines of its assignment)")

# the type-validity of every analyzed input
all_valid = True
for (ctx, rho, ab, label) in ALL_WORLDS:
    pairs = rho_pairs(ctx, rho)
    for t in cm_types(pairs):
        if not is_valid_type(ctx, rho, t):
            all_valid = False
check(all_valid, f"the type-validity consistency echo: all "
      f"{sum(len(cm_types(rho_pairs(c, r))) for (c, r, _, _l) in ALL_WORLDS)} "
      f"GENERATOR-produced types across the census pass the one-per-pair "
      f"predicate (a consistency echo of the generator; the adversarial "
      f"violation directions are the H3 battery above)")

# ================================================================ the result
print("=" * 96)
print(f"RESULT: {CHECKS} checks passed, {FAILS} failed")
if FAIL_LINES:
    for fl in FAIL_LINES:
        print(f"  FAILED: {fl}")
print(f"runtime: {time.time()-T0:.1f}s  (deterministic: xorshift64* seed "
      f"0x{SEED:X})", file=sys.stderr)
print(f"CHECKS={CHECKS} FAILS={FAILS}", file=sys.stderr)
sys.exit(0 if FAILS == 0 else 1)
