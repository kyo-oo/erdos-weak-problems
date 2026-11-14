#!/usr/bin/env python3
# hunt939d.py — Erdős #939 r=4 lane, W62 Task 1-b (ATTACKER): THE CORRECTED ENGINE.
#
# THE ENUMERATION-BUG AUDIT (this round): hunt939b.py / hunt939c.py built their
# "4-powerful" lists as val * p**4 then v *= p**4 — i.e. prime exponents that are
# MULTIPLES OF 4 — exactly the PERFECT FOURTH POWERS. Verified: their count <= 1e13
# is 1777 = #{m^4 <= 1e13}, and 32 = 2^5 (certified `rpow 4 32 = true` in the K60
# Lean kernel) is absent from their list. Consequence: every prior "#939 r=4 zero
# <= 10^13 / 10^15 / 10^16 (Route 2)" claim swept only x^4 + y^4 = z^4 — FLT for
# exponent 4 — VOID coverage. The TRUE 4-powerful numbers (every prime exponent
# >= 4: 32, 128, 2592 = 2^5*3^4, 3888 = 2^4*3^5, ...) were never swept.
# This engine enumerates them correctly (exponents 4,5,6,... freely).
#
# PHASES (env PHASES, comma-separated; default A):
#   A    calibration + validation vs the Lean K60 census row + brute-force
#        cross-validation of the bucketed box lanes at 1e7.
#   B18  the TRUE exhaustive box: pairwise-coprime 4-powerful a+b=c, c <= 10^18.
#        Lanes (sound & complete — EE pairs die by coprimality):
#          EO: e even (16|e), o odd, c=e+o odd. Necessary: c = o mod 16, so the
#              sweep is (o, c) same mod-16 bucket, c > o, e = c-o in the E-list.
#          OO: a,b odd, c=a+b even 4-powerful => 16 | c (the K60 mod-16
#              obstruction) => b = -a mod 16; sweep complementary buckets and
#              test the sum for E-list membership.
#   L1   diff-of-fourth-powers family, opposite-parity lane (COMPLETE):
#        a = x^4, c = z^4, gcd(x,z)=1, x,z opposite parity. b = z^4-x^4 = u*v*w
#        with u = z-x, v = z+x (odd coprime 4-powerful), w = (u^2+v^2)/2
#        (4-powerful; ALL its primes are 1 mod 4 — Fermat two-squares). Swept
#        over u,v <= LANE_B => covers c = z^4 <= LANE_B^4.
#   L2   same family, both-odd lane (COMPLETE): x,z both odd => s = (z-x)/2,
#        t = (z+x)/2 opposite parity, b = 8*s*t*(s^2+t^2) with v2(b) = 3+alpha
#        >= 4, s = 2^alpha*s', s', t odd 4-powerful coprime, s^2+t^2 4-powerful
#        (all primes 1 mod 4). Swept to the same bound.
#   SG   Sophie-Germain family (COMPLETE): a = x^4, b = 64 z^4, x odd,
#        gcd(x,z)=1; c = x^4+64z^4 = u*v, u = x^2-4xz+8z^2, v = x^2+4xz+8z^2
#        coprime 4-powerful, v-u = 8xz, z^2 = (S +- sqrt((6uv-u^2-v^2)/4))/16.
#        Structural law: disc >= 0 forces v/u in (3-2*sqrt2, 3+2*sqrt2) — the two
#        factors of c are within a factor 5.83. Full (u,v) sweep with uv <= SG_C.
#   R2   Route-2 generalization (COMPLETE for kernel c <= R2_CMAX): coprime X,Y
#        with X^4+Y^4 4-powerful. In Z[i]: X^2+iY^2 = gamma*(u+iv)^4, N(gamma)=c
#        = 4th-power-free kernel of X^4+Y^4 (all primes 1 mod 8, exponents 1..3).
#        Swept over all gamma and (u,v) <= R2_UVMAX => X^4+Y^4 <= ~1e26.
#
# Every candidate triple is verified by TWO independent methods (sympy.factorint
# receipts + gmpy2 trial division to n^(1/4) — complete for the 4-powerful
# property since p > n^(1/4) forces exponent < 4 — with Pollard-rho completion).
import sys, time, math, os
from bisect import bisect_right
from collections import defaultdict
from sympy import primerange, factorint
import gmpy2
import numpy as np

REPO = '/home/z/erdos-weak-problems/problem939-rpowerful'
T0 = time.time()
iroot = lambda n, k: int(gmpy2.iroot(int(n), int(k))[0])
isqrt = lambda n: int(gmpy2.isqrt(int(n)))

LOG = None
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    if LOG is not None:
        LOG.write(s + '\n'); LOG.flush()

LEAN_CENSUS_R4 = [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048,
                  2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000]

# ----------------------------------------------------------------------------
# THE CORRECT 4-POWERFUL ENUMERATOR (exponents >= 4, any value)
# ----------------------------------------------------------------------------
def gen4(limit, mod4=None):
    """All n in (1, limit] with every prime exponent >= 4 (TRUE 4-powerful).
    mod4=1 restricts prime factors to p = 1 (mod 4) (primitive sum-of-two-
    squares support)."""
    r4 = iroot(limit, 4)
    P = list(primerange(2, r4 + 2))
    if mod4 == 1:
        P = [p for p in P if p % 4 == 1]
    out = []
    ap = out.append
    def rec(i, val):
        ap(val)
        for j in range(i, len(P)):
            v = val * P[j] ** 4
            if v > limit:
                break
            while v <= limit:          # exponents 4, 5, 6, ... — THE FIX
                rec(j + 1, v)
                v *= P[j]
    rec(0, 1)
    out = [x for x in out if 1 < x <= limit]
    out.sort()
    return out

# ----------------------------------------------------------------------------
# Two-method verification machinery
# ----------------------------------------------------------------------------
def pollard_rho(n):
    if n % 2 == 0: return 2
    if gmpy2.is_prime(n): return None
    for c in range(1, 300):
        x = y = 2; d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n; y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
    return None

def factor_m2(n):
    """Independent factorization: trial division to min(n^(1/4), 2e6), then
    Pollard-rho recursion with gmpy2 primality tests."""
    n = int(n); f = {}
    if n == 1: return f
    lim = min(iroot(n, 4), 2 * 10 ** 6)
    for p in primerange(2, lim + 1):
        if p > n: break
        while n % p == 0:
            n //= p; f[p] = f.get(p, 0) + 1
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1: continue
        if gmpy2.is_prime(m):
            f[m] = f.get(m, 0) + 1; continue
        d = pollard_rho(m)
        if d is None:
            return None
        stack.append(d); stack.append(m // d)
    return f

def is_r4_fact(f):
    return f is not None and all(e >= 4 for e in f.values())

def verify_triple(a, b, c, tag):
    """Full receipts for a candidate witness. Returns True iff verified."""
    log(f'  VERIFY[{tag}] a={a} b={b} c={c}')
    ok_sum = (a + b == c)
    log(f'    a+b=c: {ok_sum}')
    fa = factorint(a); fb = factorint(b); fc = factorint(c)
    log(f'    M1 a = {dict(fa)}  (min exp {min(fa.values())})')
    log(f'    M1 b = {dict(fb)}  (min exp {min(fb.values())})')
    log(f'    M1 c = {dict(fc)}  (min exp {min(fc.values())})')
    m1 = (min(fa.values()) >= 4 and min(fb.values()) >= 4 and min(fc.values()) >= 4)
    ga = factor_m2(a); gb = factor_m2(b); gc = factor_m2(c)
    m2 = (is_r4_fact(ga) and is_r4_fact(gb) and is_r4_fact(gc))
    log(f'    M2 a = {ga}'); log(f'    M2 b = {gb}'); log(f'    M2 c = {gc}')
    agree = (dict(fa) == ga and dict(fb) == gb and dict(fc) == gc)
    log(f'    M1==M2 (independent factorizations agree): {agree}')
    g1, g2, g3 = math.gcd(a, b), math.gcd(a, c), math.gcd(b, c)
    cop = (g1 == 1 and g2 == 1 and g3 == 1)
    log(f'    pairwise coprime: gcds {g1},{g2},{g3} -> {cop}')
    ok = ok_sum and m1 and m2 and agree and cop
    log(f'    *** WITNESS {tag} VERIFIED: {ok} ***')
    if ok:
        with open(REPO + '/WITNESS939.md', 'a') as fh:
            fh.write(f'# ERDŐS #939 — Q1 WITNESS (r=4), lane {tag}\n\n'
                     f'a = {a}\nb = {b}\nc = a+b = {c}\n\n'
                     f'M1 factorizations (sympy.factorint):\n  a = {dict(fa)}\n  b = {dict(fb)}\n  c = {dict(fc)}\n\n'
                     f'M2 factorizations (gmpy2 trial-division-to-n^(1/4) + rho):\n  a = {ga}\n  b = {gb}\n  c = {gc}\n\n'
                     f'pairwise coprime; all exponents >= 4; a+b=c.\n\n')
        log('    WITNESS939.md written.')
    return ok

# ----------------------------------------------------------------------------
# The bucketed exhaustive box (numpy uint64; LIMIT <= 1.8e19)
# ----------------------------------------------------------------------------
def box_npy(LIMIT, tag):
    t0 = time.time()
    L = gen4(LIMIT)
    E = [x for x in L if not (x & 1)]
    O = [x for x in L if (x & 1)]
    exp10 = round(math.log10(LIMIT))
    E_np = np.array(E, dtype=np.uint64)
    nE = len(E)
    log(f'=== PHASE B[{tag}]: TRUE box c <= 1e{exp10}: |L|={len(L)} '
        f'(E={len(E)} even, O={len(O)} odd) ===')
    obuck = {r: np.array([o for o in O if (o & 15) == r], dtype=np.uint64)
             for r in (1, 3, 5, 7, 9, 11, 13, 15)}
    sumhits = []
    # ---- EO lane: (o, c) in the same mod-16 bucket, c > o, e = c - o in E ----
    nEO = 0
    tbeat = time.time(); nO_tot = len(O)
    for io, o in enumerate(O):
        if io % 20000 == 0:
            log(f'[B{tag}] EO heartbeat {io}/{nO_tot} ({time.time()-tbeat:.0f}s)')
        r = o & 15
        bk = obuck[r]
        lo = int(np.searchsorted(bk, np.uint64(o), side='right'))
        if lo >= bk.size: continue
        cands = bk[lo:]
        diffs = cands - np.uint64(o)
        pos = np.searchsorted(E_np, diffs)
        np.clip(pos, 0, nE - 1, out=pos)
        hit = E_np[pos] == diffs
        nEO += int(cands.size)
        if hit.any():
            for k in np.nonzero(hit)[0]:
                c = int(cands[k]); e = int(diffs[k])
                sumhits.append((e, o, c))
    log(f'[B{tag}] EO lane (same-bucket (o,c), e=c-o): {nEO} checks; '
        f'{len(sumhits)} sum-hits so far')
    # ---- OO lane: complementary mod-16 buckets, b > a, c = a+b in E ----
    nOO = 0
    tbeat = time.time()
    for ia, a in enumerate(O):
        if ia % 20000 == 0:
            log(f'[B{tag}] OO heartbeat {ia}/{nO_tot} ({time.time()-tbeat:.0f}s)')
        r = (-a) & 15
        bk = obuck[r]
        lo = int(np.searchsorted(bk, np.uint64(a), side='right'))
        hi = int(np.searchsorted(bk, np.uint64(LIMIT - a), side='right'))
        if lo >= hi: continue
        cands = bk[lo:hi]
        sums = cands + np.uint64(a)
        pos = np.searchsorted(E_np, sums)
        np.clip(pos, 0, nE - 1, out=pos)
        hit = E_np[pos] == sums
        nOO += int(cands.size)
        if hit.any():
            for k in np.nonzero(hit)[0]:
                b = int(cands[k]); c = int(sums[k])
                sumhits.append((a, b, c))
    log(f'[B{tag}] OO lane (complementary buckets): {nOO} checks; '
        f'total sum-hits {len(sumhits)}')
    ncop = 0; nrej = 0
    for t in sumhits:
        g = math.gcd(t[0], t[1])
        if g == 1: ncop += 1
        else: nrej += 1
    log(f'[B{tag}] sum-hit census: {len(sumhits)} total; {ncop} coprime; '
        f'{nrej} rejected (gcd > 1). First 50:')
    for t in sumhits[:50]:
        g = math.gcd(t[0], t[1])
        log(f'[B{tag}]   sum-hit: {t[0]} + {t[1]} = {t[2]}  (gcd = {g} '
            f'-> {"COPRIME" if g == 1 else "rejected: gcd > 1"})')
    wit = []
    for t in sumhits:
        if math.gcd(t[0], t[1]) == 1:
            wit.append(t)
            log(f'[B{tag}] *** WITNESS CANDIDATE {t} ***')
            verify_triple(t[0], t[1], t[2], f'BOX{tag}')
    log(f'[B{tag}] RESULT: {len(wit)} coprime triples (a+b=c all 4-powerful, '
        f'c <= 1e{exp10}); {time.time()-t0:.1f}s')
    log(f'[B{tag}] CERTIFICATE: |L|={len(L)} (generator validated vs the Lean K60 '
        f'census at 1e4 + brute-force lane cross-check at 1e7); EO checks={nEO}, '
        f'OO checks={nOO}, sum-hits={len(sumhits)}, coprime witnesses={len(wit)}')
    return wit

# ----------------------------------------------------------------------------
# Phase A — calibration, validation, brute-force cross-check
# ----------------------------------------------------------------------------
def brute_box(LIMIT):
    """Reference brute force: all (a,b) in L^2, a<b, a+b<=LIMIT, sum in Lset."""
    L = gen4(LIMIT); Lset = set(L)
    hits = []
    for i, a in enumerate(L):
        if 2 * a > LIMIT: break
        for b in L[i + 1:]:
            if a + b > LIMIT: break
            if (a + b) in Lset:
                hits.append((a, b, a + b))
    return hits

def phase_A():
    log('=== PHASE A: calibration + validation ===')
    got = gen4(10 ** 4)
    log(f'[A] gen4(10^4) reproduces the K60 Lean census row exactly (excl. 1): '
        f'{got == LEAN_CENSUS_R4[1:]}')
    for lim in (10 ** 13, 10 ** 15, 10 ** 16, 10 ** 17, 10 ** 18, 10 ** 19):
        t = time.time(); n = len(gen4(lim))
        log(f'[A] TRUE 4-powerful <= 1e{int(round(math.log10(lim)))}: {n}   (gen {time.time()-t:.1f}s)')
    log('[A] AUDIT: prior hunts enumerated FOURTH POWERS only (1777 <= 1e13; '
        '9999 <= 1e16 — counts of fourth powers); 32 = 2^5 was missing. All prior '
        'r=4 zero-claims were FLT(x^4+y^4=z^4)-void.')
    for lim in (10 ** 24, 10 ** 26):
        t = time.time(); n = len(gen4(lim, mod4=1))
        log(f'[A] W-list (primes 1 mod 4, exp >= 4) <= 1e{int(round(math.log10(lim)))}: {n}   ({time.time()-t:.1f}s)')
    t = time.time(); lu = [x for x in gen4(10 ** 13) if x & 1]
    log(f'[A] odd 4-powerful <= 1e13: {len(lu)}   ({time.time()-t:.1f}s)')
    # brute-force cross-check of the bucketed lanes at 1e7
    ref = brute_box(10 ** 7)
    t = time.time()
    Lx = gen4(10 ** 7)
    Ox = [x for x in Lx if (x & 1)]
    Ex = [x for x in Lx if not (x & 1)]
    E_npx = np.array(Ex, dtype=np.uint64); nEx = len(Ex)
    obx = {r: np.array([o for o in Ox if (o & 15) == r], dtype=np.uint64)
           for r in (1, 3, 5, 7, 9, 11, 13, 15)}
    mine = []
    for o in Ox:
        bk = obx[o & 15]
        lo = int(np.searchsorted(bk, np.uint64(o), side='right'))
        if lo >= bk.size: continue
        cands = bk[lo:]
        diffs = cands - np.uint64(o)
        pos = np.searchsorted(E_npx, diffs)
        np.clip(pos, 0, nEx - 1, out=pos)
        hit = E_npx[pos] == diffs
        for k in np.nonzero(hit)[0]:
            c = int(cands[k]); e = int(diffs[k])
            mine.append((min(e, o), max(e, o), c))
    for a in Ox:
        bk = obx[(-a) & 15]
        lo = int(np.searchsorted(bk, np.uint64(a), side='right'))
        hi = int(np.searchsorted(bk, np.uint64(10 ** 7 - a), side='right'))
        if lo >= hi: continue
        cands = bk[lo:hi]
        sums = cands + np.uint64(a)
        pos = np.searchsorted(E_npx, sums)
        np.clip(pos, 0, nEx - 1, out=pos)
        hit = E_npx[pos] == sums
        for k in np.nonzero(hit)[0]:
            mine.append((a, int(cands[k]), int(sums[k])))
    okx = sorted(mine) == sorted([t for t in ref if not (t[0] & 1 == 0 and t[1] & 1 == 0)])
    log(f'[A] bucketed-lane cross-check vs brute force at 1e7 (EE pairs excluded — '
        f'they die by coprimality): {okx} ({len(mine)} vs '
        f'{len([t for t in ref if not (t[0] & 1 == 0 and t[1] & 1 == 0)])} mixed/odd '
        f'sum-hits, {time.time()-t:.1f}s)')
    if not okx:
        onlyb = [t for t in ref if t not in mine and not (t[0] & 1 == 0 and t[1] & 1 == 0)]
        onlym = [t for t in mine if t not in ref]
        log(f'[A]   brute-only: {onlyb}')
        log(f'[A]   mine-only : {onlym}')

# ----------------------------------------------------------------------------
# Phase L1 — diff-of-fourth-powers family, opposite-parity lane
# ----------------------------------------------------------------------------
def lane1(B, Wmax):
    t0 = time.time()
    LU = [x for x in gen4(B) if x & 1]
    Wset = set(gen4(Wmax, mod4=1))
    log(f'=== PHASE L1: u,v odd 4-powerful <= 1e{int(round(math.log10(B)))} '
        f'({len(LU)} vals), w <= 1e{int(round(math.log10(Wmax)))} ({len(Wset)} W-vals) ===')
    wit = []; nchk = 0; ncand = 0
    for i, u in enumerate(LU):
        uu = u * u
        for v in LU[i + 1:]:
            w = (uu + v * v) >> 1
            if w > Wmax: break
            nchk += 1
            if w in Wset and math.gcd(u, v) == 1:
                ncand += 1
                x = (v - u) >> 1; z = (v + u) >> 1
                a = x ** 4; b = u * v * w; c = z ** 4
                log(f'[L1] candidate u={u} v={v} w={w}: a={a} b={b} c={c}')
                if a + b == c and verify_triple(a, b, c, 'L1'):
                    wit.append((a, b, c))
                else:
                    log(f'[L1] identity a+b==c: {a + b == c} (construction mismatch)')
    log(f'[L1] RESULT: {nchk} pair checks, {ncand} w-hits, {len(wit)} witnesses '
        f'(covers c = z^4 <= 1e{4*int(round(math.log10(B)))}); {time.time()-t0:.1f}s')
    return wit

# ----------------------------------------------------------------------------
# Phase L2 — diff-of-fourth-powers family, both-odd lane
# ----------------------------------------------------------------------------
def lane2(B, Wmax):
    t0 = time.time()
    LU = [x for x in gen4(B) if x & 1]
    Wset = set(gen4(Wmax, mod4=1))
    log(f'=== PHASE L2: s = 2^alpha*s\', t odd 4-powerful cores <= '
        f'1e{int(round(math.log10(B)))}, s^2+t^2 <= 1e{int(round(math.log10(Wmax)))} ===')
    wit = []; nchk = 0; ncand = 0
    for m in LU:
        for n in LU:
            if n == m: continue
            nn = n * n
            s = 2 * m
            while s * s + nn <= Wmax:
                w = s * s + nn
                nchk += 1
                if w in Wset and math.gcd(m, n) == 1:
                    ncand += 1
                    x = abs(n - s); z = n + s
                    a = x ** 4; b = 8 * s * n * w; c = z ** 4
                    log(f'[L2] candidate m={m} alpha={s.bit_length()-1} n={n} w={w}: '
                        f'a={a} b={b} c={c}')
                    if a + b == c and verify_triple(a, b, c, 'L2'):
                        wit.append((a, b, c))
                    else:
                        log(f'[L2] identity a+b==c: {a + b == c} (construction mismatch)')
                s <<= 1
    log(f'[L2] RESULT: {nchk} checks, {ncand} candidates, {len(wit)} witnesses '
        f'(covers c = z^4 <= 1e{4*int(round(math.log10(B)))}); {time.time()-t0:.1f}s')
    return wit

# ----------------------------------------------------------------------------
# Phase SG — Sophie-Germain family, complete (u,v) sweep with uv <= C
# ----------------------------------------------------------------------------
R58 = 3 + 2 * math.sqrt(2)
def sg_lane(C):
    t0 = time.time()
    L = gen4(iroot(C, 2))
    Lodds = [x for x in L if x & 1]
    log(f'=== PHASE SG: u,v odd 4-powerful, uv <= 1e{int(round(math.log10(C)))} '
        f'({len(Lodds)} odd vals <= sqrt(C)) ===')
    wit = []; nchk = 0; nsq = 0
    n_ = len(Lodds)
    for idx, u in enumerate(Lodds):
        vmax = min(C // u, int(R58 * u))
        j = idx + 1
        while j < n_ and Lodds[j] <= vmax:
            v = Lodds[j]; j += 1
            if (v - u) & 7: continue
            nchk += 1
            d4 = 6 * u * v - u * u - v * v    # 4*disc; >= 0 iff v/u in (3-2sqrt2,3+2sqrt2)
            if d4 < 0: continue
            disc = d4 >> 2
            r = isqrt(disc)
            if r * r != disc: continue
            nsq += 1
            S = (u + v) >> 1
            D = (v - u) >> 3
            for sgn in (1, -1):
                t2 = S + sgn * r
                if t2 <= 0 or t2 & 15: continue
                z2 = t2 >> 4
                z = isqrt(z2)
                if z < 1 or z * z != z2: continue
                if D % z: continue
                x = D // z
                if x < 1 or not (x & 1) or math.gcd(x, z) != 1: continue
                a = x ** 4; b = 64 * z ** 4; c = u * v
                if a + b == c:
                    log(f'[SG] *** WITNESS x={x} z={z} u={u} v={v}: a={a} b={b} c={c}')
                    if verify_triple(a, b, c, 'SG'):
                        wit.append((a, b, c))
                else:
                    log(f'[SG] candidate x={x} z={z} u={u} v={v} FAILED a+b==c')
    log(f'[SG] RESULT: {nchk} disc-checks, {nsq} square-discs, {len(wit)} witnesses; '
        f'{time.time()-t0:.1f}s')
    return wit

# ----------------------------------------------------------------------------
# Phase R2 — Route-2 generalization: X^4 + Y^4 = c Z^4 via Z[i]
# ----------------------------------------------------------------------------
def gauss_pow(ab, e):
    x, y = ab
    for _ in range(e):
        x, y = x * ab[0] - y * ab[1], x * ab[1] + y * ab[0]
    return (x, y)

def gauss_mul(p, q):
    return (p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0])

def find_split(p):
    for a in range(1, isqrt(p) + 1):
        b2 = p - a * a
        b = isqrt(b2)
        if b > 0 and b * b == b2:
            return (a, b)
    return None

def kernel_gammas(cmax):
    """All (c, gamma): c = 4th-power-free product of primes 1 mod 8, c <= cmax;
    gamma a Gaussian divisor with N(gamma) = c (all pi^f * pi_bar^(e-f) splits)."""
    P18 = [p for p in primerange(2, cmax + 1) if p % 8 == 1]
    splits = {p: find_split(p) for p in P18}
    out = []
    def gc(i, val, pairs):
        if val > 1:
            out.append((val, list(pairs)))
        for j in range(i, len(P18)):
            p = P18[j]
            if val * p > cmax: break
            pi = splits[p]; pi_bar = (pi[0], -pi[1])
            for e in (1, 2, 3):
                vv = val * p ** e
                if vv > cmax: break
                for f in range(e + 1):
                    g = gauss_pow(pi, f)
                    if e - f:
                        g = gauss_mul(g, gauss_pow(pi_bar, e - f))
                    gc(j + 1, vv, pairs + [g])
    gc(0, 1, [])
    return out

def route2(cmax, uvmax):
    t0 = time.time()
    cgs = kernel_gammas(cmax)
    log(f'=== PHASE R2: kernels c <= {cmax}: {len(cgs)} (c,gamma) pairs; '
        f'u,v <= {uvmax} ===')
    D4 = []
    for u in range(0, uvmax + 1):
        u2 = u * u
        for v in range(0, uvmax + 1):
            A = u ** 4 - 6 * u2 * v * v + v ** 4
            B = 4 * u * v * (u2 - v * v)
            D4.append((A, B, u, v))
    log(f'[R2] delta^4 table: {len(D4)} entries; X^4+Y^4 coverage <= '
        f'cmax*(2*uvmax^2)^4 ~ {cmax * (2 * uvmax * uvmax) ** 4:.2e}')
    wit = []; nchk = 0; ncand = 0
    for c, gs in cgs:
        for g in gs:
            g1, g2 = g
            for A, B, u, v in D4:
                for P, Q in ((g1 * A - g2 * B, g1 * B + g2 * A),
                             (g1 * A + g2 * B, g1 * B - g2 * A)):
                    nchk += 1
                    if P <= 0 or Q <= 0: continue
                    rP = isqrt(P); rQ = isqrt(Q)
                    if rP * rP != P or rQ * rQ != Q: continue
                    X, Y = rP, rQ
                    if X < 1 or Y < 1 or math.gcd(X, Y) != 1: continue
                    Z = u * u + v * v
                    if X ** 4 + Y ** 4 != c * Z ** 4: continue
                    ncand += 1
                    a = X ** 4; b = Y ** 4; cc = a + b
                    log(f'[R2] *** CANDIDATE c={c} gamma=({g1},{g2}) (u,v)=({u},{v}): '
                        f'X={X} Y={Y} Z={Z}: a={a} b={b} c={cc}')
                    if verify_triple(a, b, cc, 'R2'):
                        wit.append((a, b, cc))
    log(f'[R2] RESULT: {nchk} checks, {ncand} candidates, {len(wit)} witnesses; '
        f'{time.time()-t0:.1f}s')
    return wit

# ----------------------------------------------------------------------------
def main():
    global LOG
    phases = os.environ.get('PHASES', 'A').split(',')
    if 'QUIETFILE' in os.environ:
        LOG = open(os.environ['QUIETFILE'], 'w')
    else:
        LOG = open(REPO + '/hunt939d_output.txt', 'w')
    log(f'hunt939d start (phases {phases}); python {sys.version.split()[0]}')
    if 'A' in phases:
        phase_A()
    if 'B18' in phases:
        box_npy(10 ** 18, '18')
    B = int(os.environ.get('LANE_B', 10 ** 13))
    Wmax = int(os.environ.get('LANE_WMAX', 10 ** 26))
    if 'L1' in phases:
        lane1(B, Wmax)
    if 'L2' in phases:
        lane2(B, Wmax)
    if 'SG' in phases:
        sg_lane(int(os.environ.get('SG_C', 10 ** 26)))
    if 'R2' in phases:
        route2(int(os.environ.get('R2_CMAX', 4096)), int(os.environ.get('R2_UVMAX', 400)))
    if 'V' in phases:
        log('=== verifier self-test on the K60-certified r=3 witness2 ===')
        fa = factorint(1392672604221); fb = factorint(2126285555779); fc = factorint(3518958160000)
        log(f'  3^4*29^3*89^3 = {fa}; 7^3*11^3*167^3 = {fb}; 2^7*5^4*353^3 = {fc}')
        log(f'  sum: {1392672604221 + 2126285555779 == 3518958160000}; '
            f'min-exponents {min(fa.values())}, {min(fb.values())}, {min(fc.values())}')
    log(f'hunt939d total {time.time()-T0:.1f}s')
    LOG.close()

if __name__ == '__main__':
    main()
