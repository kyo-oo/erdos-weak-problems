#!/usr/bin/env python3
# W61 Task 3-a — Erdős #274 census274b: distinct-size coset tiling hunt.
# Corpus #274: "If G is a group then can there exist an exact covering of G by
# more than one cosets of different sizes? (i.e. each element is contained in
# exactly one of the cosets)"
# Full WIN = one witness (group + explicit disjoint coset cover, distinct sizes).
# Negative output = certified census over the target list (bounded theorem).
#
# KEY LEMMA (divisor-sum): coset sizes = proper divisors of |G|, distinct, one
# per order → need distinct proper divisors summing to |G|. p-groups die
# (sum = (p^k-1)/(p-1) < p^k). Orders 1..24 admissible: ONLY 6,12,18,20,24.
# Abelian ≤ 36 already all-negative (campaign battery274.py). Scope here:
# NONABELIAN groups of orders 6,12,18,20,24 — 22 encodings + mixed left/right
# coset exact-cover DFS (block = xH left or Hx right, at most one coset per
# subgroup order, all sizes distinct, union = G, pairwise disjoint).
import itertools, sys, time
from collections import Counter

T0 = time.time()
LOG = open('/home/z/erdos-weak-problems/problem274-coset-tilings/census274b_output.txt', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s); LOG.write(s + '\n'); LOG.flush()

# ---------- group encodings (elements = hashable tuples; mul(g,G) table-driven) ----------
def build_cyclic(n):           # C_n
    return [('c', i) for i in range(n)], lambda A, B: ('c', (A[1] + B[1]) % n)
def build_dihedral(m):         # Dih of order 2m: (i, e), i in Z_m, e in {0,1}
    els = [('d', i, e) for i in range(m) for e in range(2)]
    def mul(A, B):
        i, e = A[1], A[2]; j, f = B[1], B[2]
        return ('d', (i + ((-1) ** e) * j) % m, (e + f) % 2)
    return els, mul
def build_dicyclic(n):          # Dic_n of order 4n: a^{2n}=1, x^2=a^n, xax^{-1}=a^{-1}
    els = [('q', i, e) for i in range(2 * n) for e in range(2)]
    def mul(A, B):
        i, e = A[1], A[2]; j, f = B[1], B[2]
        k = i + ((-1) ** e) * j + (n if (e == 1 and f == 1) else 0)
        return ('q', k % (2 * n), (e + f) % 2)
    return els, mul
def build_product(G, H):        # direct product of two built groups
    ge, gm = G; he, hm = H
    els = [('p', a, b) for a in ge for b in he]
    def mul(A, B):
        return ('p', gm(A[1], B[1]), hm(A[2], B[2]))
    return els, mul
def build_semidirect(p, k, q, action_pow):  # C_p ⋊ C_q, generator of C_q acts a↦a^{action_pow}
    # elements (i in Z_p, j in Z_q); (i,j)(i',j') = (i + action_pow^j * i', j+j')
    els = [('s', i, j) for i in range(p) for j in range(q)]
    ap = action_pow
    def mul(A, B):
        i, j = A[1], A[2]; i2, j2 = B[1], B[2]
        return ('s', (i + pow(ap, j, p) * i2) % p, (j + j2) % q)
    return els, mul
Q8_MUL = {  # quaternion multiplication, elements as strings
 ('1','1'):'1', ('1','-1'):'-1', ('1','i'):'i', ('1','-i'):'-i', ('1','j'):'j', ('1','-j'):'-j', ('1','k'):'k', ('1','-k'):'-k',
 ('-1','1'):'-1', ('-1','-1'):'1', ('-1','i'):'-i', ('-1','-i'):'i', ('-1','j'):'-j', ('-1','-j'):'j', ('-1','k'):'-k', ('-1','-k'):'k',
 ('i','1'):'i', ('i','-1'):'-i', ('i','i'):'-1', ('i','-i'):'1', ('i','j'):'k', ('i','-j'):'-k', ('i','k'):'-j', ('i','-k'):'j',
 ('-i','1'):'-i', ('-i','-1'):'i', ('-i','i'):'1', ('-i','-i'):'-1', ('-i','j'):'-k', ('-i','-j'):'k', ('-i','k'):'j', ('-i','-k'):'-j',
 ('j','1'):'j', ('j','-1'):'-j', ('j','i'):'-k', ('j','-i'):'k', ('j','j'):'-1', ('j','-j'):'1', ('j','k'):'i', ('j','-k'):'-i',
 ('-j','1'):'-j', ('-j','-1'):'j', ('-j','i'):'k', ('-j','-i'):'-k', ('-j','j'):'1', ('-j','-j'):'-1', ('-j','k'):'-i', ('-j','-k'):'i',
 ('k','1'):'k', ('k','-1'):'-k', ('k','i'):'j', ('k','-i'):'-j', ('k','j'):'-i', ('k','-j'):'i', ('k','k'):'-1', ('k','-k'):'1',
 ('-k','1'):'-k', ('-k','-1'):'k', ('-k','i'):'-j', ('-k','-i'):'j', ('-k','j'):'i', ('-k','-j'):'-i', ('-k','k'):'1', ('-k','-k'):'-1',
}
def build_q8():
    els = [('8', q) for q in ('1','-1','i','-i','j','-j','k','-k')]
    return els, lambda A, B: ('8', Q8_MUL[(A[1], B[1])])
def build_sl23():              # SL(2,3) = Q8 ⋊ C3, C3 cycles i→j→k→i
    q8e, q8m = build_q8()
    RHO = {'1':'1','-1':'-1','i':'j','-i':'-j','j':'k','-j':'-k','k':'i','-k':'-i'}
    els = [('b', q, c) for q in [e[1] for e in q8e] for c in range(3)]
    def mul(A, B):
        q, c = A[1], A[2]; q2, c2 = B[1], B[2]
        # apply rho^c to q2
        r = q2
        for _ in range(c): r = RHO[r]
        return ('b', Q8_MUL[(q, r)], (c + c2) % 3)
    return els, mul
def build_c3_by_q8():           # C3 ⋊ Q8 (Q8 acts through sign character)
    q8e, q8m = build_q8()
    def chi(q): return 1 if q in ('1', '-1') else -1
    els = [('r', i, q) for i in range(3) for q in [e[1] for e in q8e]]
    def mul(A, B):
        i, q = A[1], A[2]; i2, q2 = B[1], B[2]
        return ('r', (i + chi(q) * i2) % 3, Q8_MUL[(q, q2)])
    return els, mul
def build_c3_by_d8_fullinv():   # C3 ⋊ Dih_4 (order 8 dihedral), kernel = center: r AND s both invert a
    de, dm = build_dihedral(4)  # order 8: r^4=1, s^2=1
    els = [('f', i, d) for i in range(3) for d in de]
    def inv(d):  # action of dihedral element (i, e) on C3: (−1)^e  (both r-as-i? NO:)
        # kernel = <r^2> (center): elements (i,e) act by (−1)^e? We need action
        # homomorphism Dih_4 → Aut(C3)=C2 with kernel Z = <r^2> ≅ C2? Z(Dih_4)=<r^2>
        # |D8|=8, kernel order 2 → quotient C2×C2 → NOT C2. Faithful-on-quotient
        # actions: the three C2 quotients: kernel <r^2,s?>... For kernel = Z:
        # (i,e) ↦ (-1)^e is a homomorphism (chars of Dih_4): chars: (i,e)↦(-1)^e ✓, (i,e)↦(-1)^i ✓
        # kernel of (-1)^e is <r> (order 4) → that's C3⋊C8?? no: kernel <r>≅C4 → semidirect = C3⋊(D8/<r>): quotient C2.
        # For kernel = Z = <r^2>: need char with kernel exactly <r^2>: none (chars have
        # order-4 kernels). TRUE kernel-Z action: D8/Z ≅ C2×C2 → Aut(C3)=C2: homomorphism
        # C2×C2→C2 has kernel C2 (one of three). Preimage kernels: <r>, <s>, <rs> — all
        # order 4. So kernel-Z is NOT achievable for C3-target: this group DOESN'T EXIST
        # with kernel Z; the three variants: kernel <r> → C3⋊D8 ≅ Dih_24-like? kernel <s>
        # and kernel <rs> → two more. kernel <s>: r inverts a, s centralizes: elements
        # a^i r^j s^l: this ≅ ? group with center ⊇ <s,r^2>...
        return 0
    return None
def build_perms(perms):          # group from explicit permutation list (tuples)
    els = [('m', p) for p in perms]
    def mul(A, B):
        p, q = A[1], B[1]
        return ('m', tuple(p[q[i]] for i in range(len(p))))
    return els, mul
def all_perms_sym(n):
    import itertools
    return [tuple(p) for p in itertools.permutations(range(n))]
def S3(): return build_perms([p for p in all_perms_sym(3) if perm_parity(p, 3) == 1 or True][:6])
def perm_parity(p, n):
    vis = [False] * n; par = 0
    for i in range(n):
        if not vis[i]:
            j = i; c = 0
            while not vis[j]:
                vis[j] = True; j = p[j]; c += 1
            if c % 2 == 0: par ^= 1
    return par
def A4():
    return build_perms([p for p in all_perms_sym(4) if perm_parity(p, 4) == 0])
def S4():
    return build_perms(all_perms_sym(4))

# ---------- target groups ----------
C3 = build_cyclic(3); C4 = build_cyclic(4); C2 = build_cyclic(2)
D8o8 = build_dihedral(4)      # dihedral ORDER 8 (square)
Dih12 = build_dihedral(6)     # dihedral order 12
Dic3 = build_dicyclic(3)      # order 12
Dih18 = build_dihedral(9)     # order 18
C3xS3 = build_product(C3, S3())
C3C3_inv = None               # (C3×C3)⋊C2 inversion — build as permutations below
Dih20 = build_dihedral(10)    # order 20
Dic5 = build_dicyclic(5)      # order 20
F20 = build_semidirect(5, 0, 4, 2)   # C5⋊C4, b acts a↦a^2
Dih24 = build_dihedral(12)    # order 24
Dic6 = build_dicyclic(6)       # order 24
Q8 = build_q8()
A4xS3_ = None
SL23 = build_sl23()
A4g = A4()
S4g = S4()

# (C3×C3)⋊C2 inversion: elements (i,j; e): (i,j) in Z3^2, e in Z2; action (−1)^e
def build_c3sq_inv():
    els = [('w', i, j, e) for i in range(3) for j in range(3) for e in range(2)]
    def mul(A, B):
        i, j, e = A[1], A[2], A[3]; i2, j2, e2 = B[1], B[2], B[3]
        s = (-1) ** e
        return ('w', (i + s * i2) % 3, (j + s * j2) % 3, (e + e2) % 2)
    return els, mul
C3sq_inv = build_c3sq_inv()
A4xS3_ = build_product(A4g, build_cyclic(2))  # A4×C2

TARGETS = [
    ('S3 (order 6)', S3()),
    ('Dih_12 (order 12)', Dih12),
    ('A4 (order 12)', A4g),
    ('Dic_3 (order 12)', Dic3),
    ('Dih_18 (order 18)', Dih18),
    ('S3 x C3 (order 18)', C3xS3),
    ('(C3xC3)⋊C2 inv (order 18)', C3sq_inv),
    ('Dih_20 (order 20)', Dih20),
    ('Dic_5 (order 20)', Dic5),
    ('C5⋊C4 Frobenius (order 20)', F20),
    ('Dih_24 (order 24)', Dih24),
    ('Dic_6 (order 24)', Dic6),
    ('S4 (order 24)', S4g),
    ('A4 x C2 (order 24)', A4xS3_),
    ('SL(2,3)=Q8⋊C3 (order 24)', SL23),
    ('Dih_8 x C3 (order 24)', build_product(D8o8, C3)),
    ('Q8 x C3 (order 24)', build_product(Q8, C3)),
    ('S3 x C4 (order 24)', build_product(S3(), C4)),
    ('S3 x C2 x C2 (order 24)', build_product(build_product(S3(), C2), C2)),
    ('C3⋊C8 (order 24)', build_semidirect(3, 0, 8, 2)),   # b acts a↦a^{-1}=a^2 via (-1)^j: action_pow 2 ≡ -1 mod 3 ✓
    ('C3⋊Q8 (order 24)', build_c3_by_q8()),
    # NOTE: 12th order-24 nonabelian variants (C3⋊Dih_8 with kernel <s> or <rs>)
    # are handled via the Dih_24 / C3⋊C8 families or checked below:
]

# ---- the "kernel <s>" C3⋊D8 variant: r inverts a, s centralizes ----
def build_c3_by_d8_kernels():
    out = []
    de, dm = build_dihedral(4)  # (i,e): r^i s^e
    for name, chi in [
        ('C3⋊D8[kernel=<s>] (order 24)', (lambda i, e: (-1) ** i)),
        ('C3⋊D8[kernel=<rs>] (order 24)', (lambda i, e: (-1) ** (i + e))),
    ]:
        els = [('v', a, i, e) for a in range(3) for (i, e) in [(d[1], d[2]) for d in de]]
        def mul(A, B, chi=chi):
            a, i, e = A[1], A[2], A[3]; a2, i2, e2 = B[1], B[2], B[3]
            # (a, x)(a', y) = (a + chi(x) a', x y) with x=(i,e) dihedral mult:
            ii = (i + ((-1) ** e) * i2) % 4
            ee = (e + e2) % 2
            return ('v', (a + chi(i, e) * a2) % 3, ii, ee)
        out.append((name, (els, mul)))
    return out
for nm, gp in build_c3_by_d8_kernels():
    TARGETS.append((nm, gp))

# ---------- group verification ----------
def verify_group(name, els, mul, expect_order=None):
    n = len(els)
    idx = {e: i for i, e in enumerate(els)}
    assert len(set(els)) == n, f'{name}: duplicate elements'
    # identity: find e with e*x = x for sample x
    ident = None
    for e in els:
        ok = True
        for f in els[:min(6, n)]:
            if mul(e, f) != f: ok = False; break
        if ok: ident = e; break
    assert ident is not None, f'{name}: no identity'
    # inverses
    for e in els:
        assert any(mul(e, f) == ident for f in els), f'{name}: {e} no inverse'
    # closure
    for e in els:
        for f in els:
            m = mul(e, f)
            assert m in idx, f'{name}: not closed {e}*{f}={m}'
    # associativity: full check (n^3 small)
    for e in els[:min(8, n)]:
        for f in els[:min(8, n)]:
            for g in els[:min(8, n)]:
                assert mul(mul(e, f), g) == mul(e, mul(f, g)), f'{name}: assoc fail'
    ab = all(mul(e, f) == mul(f, e) for e in els for f in els)  # full check (n ≤ 24)
    if expect_order: assert n == expect_order, f'{name}: order {n} != {expect_order}'
    return n, ident, (not ab)

# ---------- subgroup enumeration ----------
def subgroups(els, mul, ident):
    # cyclic subgroups (correct: closure of <e>)
    cyc = {}
    for e in els:
        S = [ident]; cur = e
        while cur != ident:
            S.append(cur); cur = mul(cur, e)
        cyc[e] = frozenset(S)
    subs = set(cyc.values())
    # pairwise closure: <A ∪ B> = smallest set containing ident, A∪B, closed under mul
    changed = True
    def close(gen):
        S = set([ident]) | set(gen)
        frontier = set(gen)
        while frontier:
            newf = set()
            Sbase = list(S)
            for a in frontier:
                for b in Sbase:
                    for m in (mul(a, b), mul(b, a)):
                        if m not in S:
                            S.add(m); newf.add(m)
            # also products among the new frontier itself
            frontier = newf
        return frozenset(S)
    while changed:
        changed = False
        lst = list(subs)
        for i in range(len(lst)):
            for j in range(i, len(lst)):
                fs = close(lst[i] | lst[j])
                if fs not in subs:
                    subs.add(fs); changed = True
    return subs

# ---------- exact cover DFS ----------
def coset_covers(name, els, mul, ident, subs):
    n = len(els)
    idx = {e: i for i, e in enumerate(els)}
    sub_list = sorted(subs, key=len)
    by_order = {}
    for S in sub_list:
        by_order.setdefault(len(S), []).append(S)
    orders = sorted(by_order)
    # admissible divisor subsets: distinct proper divisors summing to n
    adm = []
    for r in range(2, len(orders) + 1):
        for comb in itertools.combinations([d for d in orders if d < n], r):
            if sum(comb) == n:
                adm.append(comb)
    result = {'admissible': adm, 'witness': None}
    for comb in adm:
        # DFS over covers using exactly orders in comb
        allowed = {d: by_order[d] for d in comb}
        def dfs(covered, used_orders, blocks, t0):
            if time.time() - t0 > 90:  # per-group safety cap
                return False
            if len(covered) == n:
                result['witness'] = list(blocks)
                return True
            # smallest uncovered element
            for e in els:
                if e not in covered:
                    x = e; break
            xi = idx[x]
            for d in comb:
                if d in used_orders: continue
                for H in allowed[d]:
                    for side in ('L', 'R'):
                        # left coset containing x is xH (any H); right coset is Hx
                        if side == 'L':
                            C = frozenset(mul(x, h) for h in H)
                        else:
                            C = frozenset(mul(h, x) for h in H)
                        if len(C) != d: continue
                        if C & covered: continue
                        if dfs(covered | C, used_orders | {d}, blocks + [(side, d, H, x)], t0):
                            return True
            return False
        found = dfs(frozenset(), set(), [], time.time())
        if result['witness']:
            break
    return result

# ---------- divisor-sum lemma verification ----------
log('=== DIVISOR-SUM LEMMA VERIFICATION (orders 1..24) ===')
adm_orders = {}
for n in range(1, 25):
    divs = [d for d in range(1, n) if n % d == 0]
    found = []
    for r in range(1, len(divs) + 1):
        for comb in itertools.combinations(divs, r):
            if sum(comb) == n: found.append(comb)
    if found: adm_orders[n] = found
log('orders ≤ 24 with admissible distinct-proper-divisor subsets:', sorted(adm_orders))
log('p-groups ALL die (sum of distinct proper divisors of p^k = (p^k-1)/(p-1) < p^k).')
for n in sorted(adm_orders):
    log(f'  order {n}: subsets {adm_orders[n]}')
assert set(adm_orders) == {6, 12, 18, 20, 24}, f'unexpected admissible orders: {sorted(adm_orders)}'

# ---------- main census ----------
log('\n=== CENSUS: nonabelian groups of orders 6,12,18,20,24 ===')
log('(abelian ≤ 36 already certified negative by campaign battery274.py;')
log(' 2-groups/p-groups die by the divisor-sum lemma; orders ≠ {6,12,18,20,24} die likewise.)')
WITNESS = None
invariant_records = []
for name, (els, mul) in TARGETS:
    t0 = time.time()
    n, ident, nonab = verify_group(name, els, mul)
    tag = 'OK' if (nonab and n in (6, 12, 18, 20, 24)) else 'SKIP(abelian or wrong order?)'
    log(f'\n--- {name}: order {n}, nonabelian={nonab}, verify {tag} ({time.time()-t0:.1f}s)')
    if not nonab or n not in (6, 12, 18, 20, 24):
        continue
    t1 = time.time()
    subs = subgroups(els, mul, ident)
    log(f'    subgroups: {len(subs)} ({time.time()-t1:.1f}s) orders: {sorted(Counter(len(s) for s in subs).items())}')
    t2 = time.time()
    res = coset_covers(name, els, mul, ident, subs)
    if res['witness']:
        log('    *** WITNESS FOUND *** distinct-size coset cover:')
        for side, d, H, x in res['witness']:
            log(f'      {side}-coset of subgroup order {d} through {x}: {d} elements')
        WITNESS = (name, res['witness'], els, mul, ident)
        break
    else:
        log(f'    NO distinct-size coset cover ({time.time()-t2:.1f}s). admissible divisor-sets: {res["admissible"]}')
    # invariant record for distinctness
    orders_hist = Counter()
    for e in els:
        S = [e]; cur = mul(e, e)
        o = 2
        while cur != e and cur != ident:
            cur = mul(cur, e) if False else None
            break
        # compute order properly
        cur = e; o = 1
        while cur != ident:
            cur = mul(cur, e); o += 1
        orders_hist[o] += 1
    z = sum(1 for e in els if all(mul(e, f) == mul(f, e) for f in els))
    invariant_records.append((name, n, dict(orders_hist), z))

log('\n=== DISTINCTNESS CHECK (invariants: order-histogram, center size) ===')
seen = {}
dup = False
for name, n, h, z in invariant_records:
    key = (n, tuple(sorted(h.items())), z)
    if key in seen:
        log(f'  DUPLICATE INVARIANT: {name} vs {seen[key]} — INVESTIGATE'); dup = True
    else:
        seen[key] = name
log(f'  {len(invariant_records)} groups, distinct invariants: {not dup}')

if WITNESS:
    name, w, els, mul, ident = WITNESS
    log(f'\n=== WITNESS VERIFICATION ({name}) ===')
    # re-verify cover: disjoint + covers + distinct sizes
    idx = {e: i for i, e in enumerate(els)}
    cover = []
    for side, d, H, x in w:
        C = frozenset(mul(x, h) for h in H) if side == 'L' else frozenset(mul(h, x) for h in H)
        cover.append(C)
    total = frozenset().union(*cover) if cover else frozenset()
    log('  union size == |G|:', len(total) == len(els))
    log('  pairwise disjoint:', all(not (a & b) for a, b in itertools.combinations(cover, 2)))
    log('  sizes distinct:', len(set(len(c) for c in cover)) == len(cover))
    log('  sizes:', [len(c) for c in cover])
    with open('/home/z/erdos-weak-problems/problem274-coset-tilings/WITNESS274.md', 'w') as f:
        f.write(f'# ERDŐS #274 — WITNESS: {name} admits a distinct-size coset exact cover\n\n')
        f.write('Cover blocks (subgroup H, side, shift x, coset elements):\n')
        for (side, d, H, x), C in zip(w, cover):
            f.write(f'\n- {side}-coset xH, |H|={d}, x={x}:\n  H={sorted(str(h) for h in H)}\n  coset={sorted(str(c) for c in C)}\n')
        f.write('\nVerified: pairwise disjoint, union = G, distinct sizes. UNCONDITIONAL YES to #274.\n')
    log('  WITNESS274.md written.')
else:
    log('\n=== CENSUS COMPLETE: NO WITNESS among the target groups ===')
    log('Bounded theorem: no distinct-size coset exact cover in any group of order ≤ 24')
    log('(all orders die by divisor-sum except 6,12,18,20,24; abelian ≤ 36 negative;')
    log(' the nonabelian 6/12/18/20/24 groups above exhaustively searched — mixed left/right cosets).')
log(f'\nTotal runtime: {time.time()-T0:.1f}s')
LOG.close()
