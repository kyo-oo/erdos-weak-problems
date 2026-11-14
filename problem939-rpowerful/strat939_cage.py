#!/usr/bin/env python3
# strat939_cage.py — W66-P939-S (STRATEGIST LANE): THE CONGRUENCE CAGE ANALYSIS.
#
# THE QUESTION: does the 4-powerful condition on c close a congruence cage that
# kills ALL pairwise-coprime triples UNCONDITIONALLY (for all bounds)?
#
# THE CAGE GEOMETRY (derived first, verified below):
#   * Coprimality -> at most one of a,b,c even (parity cage: EE lane DEAD:
#     gcd >= 2 trivially — the only cage that closes, and it is trivial).
#   * If a even -> 2^4 | a -> a = 0 mod 16 (EO lane); then c = a + b = b mod 16
#     (c odd). Necessary: (b, c) in the SAME mod-16 class.
#   * If a,b odd (OO lane) -> c even -> 2^4 | c (the K60 mod-16 obstruction)
#     -> b = -a mod 16.
#   * Per prime q: v_q(member) in {0} U [4, inf); a prime q of ONE member q^4
#     -divides that member only.
#   * Admissible residues mod q^b: units U {v_q >= 4} (v_q capped at b;
#     r = 0 mod q^b always admissible: n = q^(4k)).
#
# THE VERDICT (proven here in two independent ways):
#   THE CAGE IS OPEN. For EVERY modulus M there is a local coprime solution:
#   alpha = 0 mod 2^b(M), 1 mod odd part; beta = 1 mod M; gamma = 1 mod 2^b,
#   2 mod odd part; alpha + beta = gamma mod every prime power || M; no prime
#   of M divides two of them; AND each class is realized by a GENUINE
#   4-powerful number:
#     x = 2^(4*L) with L = lcm of ord_{q^c}(2) over odd prime powers q^c || M,
#         exponent >= b  (x = 0 mod 2^b, 1 mod odd part);
#     y = 1 (4-powerful, unit);
#     z = w^(1+3d) with d = ord_M(w) (pigeonhole: d <= M exists), w the CRT
#         class of gamma (z = w^(1+3d) is 4-powerful since exponent >= 4 and
#         z = w*(w^d)^3 = w mod M).
#   The achievement lemma (every unit class mod M contains a 4-powerful):
#     n = u^(1+3d), d = ord_M(u) — elementary (pigeonhole + unit
#     cancellation), NO Dirichlet / NO Euler totient needed.
# Hence NO fixed-modulus congruence argument can kill the coprime lane: the
# NO-direction of the full problem is not provable by congruences alone.
import sys, os, time, math
from sympy import primerange, factorint
from collections import Counter

T0 = time.time()
REPO = os.path.dirname(os.path.abspath(__file__))
LOG = None
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    if LOG is not None:
        LOG.write(s + '\n'); LOG.flush()

def iroot(n, k):
    if n < 2 or k == 1: return n
    if k == 2: return int(math.isqrt(n))
    x = int(round(n ** (1.0 / k)))
    if x < 1: x = 1
    while x ** k > n: x -= 1
    while (x + 1) ** k <= n: x += 1
    return x

def gen4(limit):
    r4 = iroot(limit, 4)
    P = list(primerange(2, r4 + 2))
    out = []
    ap = out.append
    def rec(i, val):
        ap(val)
        for j in range(i, len(P)):
            v = val * P[j] ** 4
            if v > limit: break
            while v <= limit:
                rec(j + 1, v)
                v *= P[j]
    rec(0, 1)
    out = [x for x in out if 1 < x <= limit]
    out.sort()
    return out

def is_r4(n):
    if n < 1: return False
    if n == 1: return True
    return all(e >= 4 for e in factorint(n).values())

def v_p(r, p):
    if r == 0: return None  # r = 0 mod M: valuation "at least" the modulus
    v = 0
    while r % p == 0:
        r //= p; v += 1
    return v

def crt(pairs):
    """pairs = [(r_i, m_i)] with m_i pairwise coprime; returns (r, M)."""
    r, M = 0, 1
    for ri, mi in pairs:
        # solve r + M*t = ri (mod mi): t = (ri - r) * M^{-1} mod mi
        Minv = pow(M, -1, mi)
        t = ((ri - r) * Minv) % mi
        r += M * t
        M *= mi
    return r % M, M

def mulord(u, m):
    """least d >= 1 with u^d = 1 mod m (u unit mod m); via the factorization
    of the group exponent candidates: d | phi(m) (Lagrange). Falls back to
    the pigeonhole loop for tiny m."""
    if m <= 1000:
        x = u % m; d = 1
        while x != 1:
            x = x * u % m; d += 1
        return d
    phi = 1
    for q, c in factorint(m).items():
        phi *= (q - 1) * q ** (c - 1)
    d = phi
    for r in factorint(phi):
        while d % r == 0 and pow(u, d // r, m) == 1:
            d //= r
    assert pow(u, d, m) == 1
    return d

# ----------------------------------------------------------------------------
# 1. Admissible-set A(M): empirical (from generated values) vs theoretical
# ----------------------------------------------------------------------------
def theoretical_A(M):
    """r in A(M) iff for every prime q^b || M: v_q(r) = 0 or (v_q(r) >= 4) or
    (r = 0 mod q^b with b <= 3 -> realized by q^(4k) = 0 mod q^b)."""
    fm = factorint(M)
    good = []
    for r in range(M):
        ok = True
        for q, b in fm.items():
            if r % q == 0:
                v = 0
                rr = r
                while rr % q == 0 and v < b:
                    rr //= q; v += 1
                # v is capped at b if r = 0 mod q^b
                if v == b:
                    v = None  # 'at least b': admissible (q^{4k})
                if not (v is None or v == 0 or v >= 4):
                    ok = False; break
        if ok:
            good.append(r)
    return set(good)

def empirical_A(M, values):
    return {v % M for v in values}

# ----------------------------------------------------------------------------
# 2. The achievement lemma receipts: u^(1+3d) is 4-powerful and = u mod M
# ----------------------------------------------------------------------------
def achieve(u, M):
    d = mulord(u, M)
    n = u ** (1 + 3 * d)
    assert n % M == u % M
    # n = u^(1+3d) with exponent >= 4: every prime p | u has
    # v_p(n) = v_p(u)*(1+3d) >= 4 — 4-powerful BY STRUCTURE (no big-int
    # factorization needed; u <= M is factored once if desired).
    fu = factorint(u) if u > 1 else {}
    assert all(e * (1 + 3 * d) >= 4 for e in [1] * 0) or True
    if u > 1:
        assert min(e * (1 + 3 * d) for e in fu.values()) >= 4
    return n, d

# ----------------------------------------------------------------------------
# 3. The local coprime triple per modulus (the EO-lane construction)
# ----------------------------------------------------------------------------
def local_eo_triple(M):
    """Returns (x, y, z, alpha, beta, gamma, checks) with:
    x, y, z genuine 4-powerful; x + y = z (mod M);
    no prime q | M divides two of x, y, z (mod-M coprimality);
    EO shape: x even (0 mod 2^b), y, z odd."""
    fm = factorint(M)
    b2 = fm.get(2, 0)
    # x = 2^(4L) with L = lcm(ord_{q^c}(2)) over odd prime powers q^c || M
    L = 1
    for q, c in fm.items():
        if q != 2:
            L = math.lcm(L, mulord(2 % (q ** c), q ** c))
    e4 = 4 * L
    while e4 < b2:          # ensure x = 0 mod 2^b
        e4 *= 2
    x = 2 ** e4
    # y = 1
    y = 1
    # gamma: 1 mod 2^b, 2 mod each odd q^c
    pairs = [(1 % (2 ** b2) if b2 else 0, 2 ** b2)] if b2 else []
    for q, c in fm.items():
        if q != 2:
            pairs.append((2 % (q ** c), q ** c))
    if not pairs:
        return None
    w, _ = crt(pairs)
    z, d = achieve(w, M)
    ok_sum = (x + y) % M == z % M
    # mod-M coprimality: for each prime q | M, count members divisible by q
    divi = {q: sum(1 for n in (x % M, y % M, z % M) if n % q == 0)
            for q in fm}
    ok_cop = all(v <= 1 for v in divi.values())
    return dict(x=x, y=y, z=z, gamma=w, ord=d, ok_sum=ok_sum,
                ok_cop=ok_cop, divi=divi,
                alpha=x % M, beta=y % M)

def local_oo_triple(M):
    """OO shape: a, b odd, c even: a = 1 mod 2^b, b = -1 mod 2^b, c = 0 mod
    2^b; a = b = 1, c = 2 mod odd q^c. c realized as 2^(4k)*u with u an odd
    4-powerful in the induced class (c even 4-powerful => 16 | c => 0 mod
    2^b for every b)."""
    fm = factorint(M)
    b2 = fm.get(2, 0)
    odd_part = math.prod(q ** c for q, c in fm.items() if q != 2)
    # a = 1 mod M (unit class): a = 1 (4-powerful)
    a = 1
    # b = -1 mod 2^b and 1 mod odd part (unit class mod M)
    pairs_b = [((-1) % (2 ** b2), 2 ** b2)] if b2 else []
    if odd_part > 1:
        pairs_b.append((1, odd_part))
    if not pairs_b:
        return None
    b_cls, _ = crt(pairs_b)
    b, db = achieve(b_cls, M)
    # c = a + b mod M: class c_cls; realize as 2^(4k) * u:
    #   c = 0 mod 2^b (automatic, k >= b/4); c = c_cls mod odd part:
    #   2^(4k) * u = c_cls mod odd part -> u = c_cls * 2^(-4k) mod odd part
    c_cls = (b_cls + 1) % M
    k = max(1, math.ceil(b2 / 4))
    if odd_part > 1:
        u_cls = (c_cls % odd_part) * pow(2 ** (4 * k), -1, odd_part) % odd_part
        u, dc = achieve(u_cls, odd_part)
        c = 2 ** (4 * k) * u
        d_info = f'dc={dc}'
    else:
        c = 2 ** (4 * k)
        d_info = 'dc=n/a'
    ok_sum = (a + b) % M == c % M
    divi = {q: sum(1 for n in (a % M, b % M, c % M) if n % q == 0)
            for q in fm}
    ok_cop = all(v <= 1 for v in divi.values())
    return dict(a=a, b=b, c=c, b_cls=b_cls, db=db, d_info=d_info,
                ok_sum=ok_sum, ok_cop=ok_cop, divi=divi)

# ----------------------------------------------------------------------------
def main():
    global LOG
    outfile = os.environ.get('OUTFILE', REPO + '/strat939_cage_output.txt')
    LOG = open(outfile, 'w')
    log(f'strat939_cage start; python {sys.version.split()[0]}')
    vals = gen4(10 ** 13)
    log(f'[CAGE] 4-powerful values <= 1e13: {len(vals)} '
        f'(generator validated vs the K60 Lean census row at 1e4: '
        f'{gen4(10**4) == [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000][1:]})')

    # ---- 1. A(M) sets ---------------------------------------------------------
    log('')
    log('=== 1. THE ADMISSIBLE-SET A(M) (empirical vs theoretical) ===')
    for M in (16, 32, 81, 625, 2401, 1296, 10000, 50625):
        Aem = empirical_A(M, vals)
        Ath = theoretical_A(M)
        cov = Aem == Ath
        log(f'[A({M})] |A| theoretical = {len(Ath)}; empirical coverage from '
            f'1e13 values = {len(Aem)}; FULL: {cov}')
        if not cov:
            missing = sorted(Ath - Aem)[:8]
            log(f'[A({M})]   missing (need the u^(1+3d) lift): {missing}')
            # the achievement lemma fills them:
            filled = []
            for r in missing:
                n, d = achieve(r, M)
                filled.append(n % M == r)
            log(f'[A({M})]   u^(1+3d) achievement covers the missing classes: '
                f'{all(filled)}')

    # odd-member classes mod 16 (the brief's census)
    log('')
    log('=== 2. THE ODD-MEMBER CLASSES MOD 16 ===')
    odd16 = Counter(v % 16 for v in vals if v & 1)
    log(f'[M16] odd 4-powerful classes mod 16: {dict(sorted(odd16.items()))}')
    log(f'[M16] even 4-powerful classes mod 16: '
        f'{dict(sorted(Counter(v % 16 for v in vals if not v & 1).items()))}')
    log(f'[M16] ALL 8 odd classes populated: {len(odd16) == 8}; even: only 0 '
        f'(16 | every even 4-powerful) — the mod-16 valuation cage')

    # ---- 3. local coprime triples --------------------------------------------
    log('')
    log('=== 3. THE CAGE-CLOSE TEST: local coprime EO/OO solutions per M ===')
    mods = [16, 81, 625, 2401, 1296, 10000, 50625,
            16 * 81 * 625 * 2401, 2 ** 16 * 3 ** 8, 2 ** 20 * 3 ** 12 * 5 ** 8]
    for M in mods:
        r = local_eo_triple(M)
        log(f'[EO M={M}] x=2^k (k={r["x"].bit_length()-1}) y=1 '
            f'z (bitlen {r["z"].bit_length()}) '
            f'(gamma={r["gamma"]}, ord={r["ord"]})')
        log(f'[EO M={M}]   x+y = z mod M: {r["ok_sum"]}; '
            f'mod-M coprime (per-prime divisors <= 1): {r["ok_cop"]} '
            f'{r["divi"]}')
        assert r['ok_sum'] and r['ok_cop']
        # 4-powerfulness by structure: x = 2^(4L') (single prime, exponent
        # >= 4); y = 1; z = w^(1+3d) (achieve: every prime exponent >= 4)
        assert r['x'].bit_length() - 1 >= 4 and is_r4(r['y'])
        if M <= 50625:
            r2 = local_oo_triple(M)
            log(f'[OO M={M}] a=1 b(bitlen {r2["b"].bit_length()}) '
                f'c(bitlen {r2["c"].bit_length()}) (b_cls={r2["b_cls"]}, '
                f'{r2["d_info"]})')
            log(f'[OO M={M}]   a+b = c mod M: {r2["ok_sum"]}; '
                f'mod-M coprime: {r2["ok_cop"]} {r2["divi"]}')
            assert r2['ok_sum'] and r2['ok_cop']
            # a = 1; b achieved (structure-checked inside achieve); c =
            # 2^(4k)*u with both parts 4-powerful
            assert is_r4(r2['a'])
            if M <= 1296:
                assert is_r4(r2['b']) and is_r4(r2['c'])
    log('')
    log('[VERDICT] THE CONGRUENCE CAGE IS OPEN: for every tested modulus M '
        '(and provably for every M by the CRT + order construction above), '
        'there are GENUINE 4-powerful x, y, z with x+y = z (mod M) and no '
        'prime of M dividing two members. NO fixed-modulus congruence '
        'argument can kill the pairwise-coprime lane.')
    log('')
    log('=== 4. THE NECESSARY-CONDITION PACKAGE (the exact cage geometry) ===')
    log('[CAGE] (i) parity: at most one of a,b,c even; EE pairs are dead '
        '(gcd >= 2) — the ONLY closed cage, and it is trivial.')
    log('[CAGE] (ii) EO: 16 | a (v_2 >= 4), c = b mod 16, b, c odd.')
    log('[CAGE] (iii) OO: 16 | c (the K60 theorem), b = -a mod 16.')
    log('[CAGE] (iv) per prime q: exactly one member may carry q, and then '
        'q^4 | that member: c = b mod rad4(a), c = a mod rad4(b), '
        'a = -b mod rad4(c) (rad4(x) = prod_{p | x} p^4).')
    log('[CAGE] (v) the c-side: c odd -> all primes odd, exponents >= 4 '
        '(c in the odd 4-powerful set: all 8 classes mod 16); c even -> '
        '16 | c. NO sparse-class forcing closes the cage (3 above).')
    log(f'strat939_cage total {time.time()-T0:.1f}s')
    LOG.close()

if __name__ == '__main__':
    main()
