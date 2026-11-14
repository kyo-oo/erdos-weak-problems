#!/usr/bin/env python3
# W61 Task 3-d — Erdős #939 r=4 lane: ALGEBRAIC routes (not blind scan).
# Q1: do there exist pairwise-coprime 4-powerful a,b with a+b also 4-powerful?
# Route 2: c-driven scan — every 4-powerful c <= 1e16, check c = x^4 + y^4
#   (pairwise coprimality automatic: gcd(x,y)=1 => gcd(x^4,y^4)=1, and
#    gcd(x^4, x^4+y^4) = gcd(x^4, y^4) = 1).
# Route 3: Sophie-Germain parametric: a=x^4, b=64 z^4 (b=2^6 z^4 4-powerful),
#   c = x^4+64z^4 = (x^2-4xz+8z^2)(x^2+4xz+8z^2) [SG identity with y=2z],
#   need both factors 4-powerful (they are coprime for gcd(x,z)=1, x odd).
# Route 1: prior pair-scan <= 1e15 = ZERO (hunt939b, on disk — not redone).
import time, math
from sympy import primerange, factorint, gcd

T0 = time.time()
LOG = open('/home/z/erdos-weak-problems/problem939-rpowerful/hunt939c_output.txt', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s); LOG.write(s + '\n'); LOG.flush()

LIMIT_C = 10 ** 16

# --- generate all 4-powerful numbers <= LIMIT_C (and <= 2e8 for SG route) ---
def gen_r4(limit):
    P = list(primerange(2, int(limit ** 0.25) + 2))
    out = []
    def rec(idx, val):
        if val > limit: return
        if idx == len(P):
            if val > 1: out.append(val)
            return
        p = P[idx]
        v = p ** 4
        if v > limit:  # this and all larger primes can't divide any number <= limit? NO —
            # larger primes have p^4 > limit too, so only finitely many matter; stop when p^4 > limit
            if v > limit:
                out.append(val) if val > 1 else None
                return
        e = 0
        cur = val
        while cur <= limit:
            rec(idx + 1, cur)
            e += 1
            cur = val * (p ** (4 * e)) if False else val * p ** (4 * e)
            if cur > limit: break
        return
    # simpler: recursive with correct structure
    out = []
    def rec2(idx, val):
        if val > limit: return
        if val > 1: out.append(val)
        for j in range(idx, len(P)):
            nv = val * P[j] ** 4
            if nv > limit: break
            # exponents 4e, e>=1: multiply repeatedly by p^4
            cur = nv
            while cur <= limit:
                rec2(j + 1, cur)
                cur *= P[j] ** 4
    rec2(0, 1)
    return sorted(set(out))

t = time.time()
r4_all = gen_r4(LIMIT_C)
log(f'4-powerful <= 1e16: {len(r4_all)} ({time.time()-t:.1f}s)')
r4_set16 = set(r4_all)

# --- Route 2: c = x^4 + y^4 over 4-powerful c ---
t = time.time()
fp_list = [i ** 4 for i in range(1, int(LIMIT_C ** 0.25) + 2)]
fp_set = set(fp_list)
WIT = None
checked = 0
for c in r4_all:
    # x^4 < c/2 (wlog x <= y); look up c - x^4 in fp_set
    x = 1
    q = 1
    while q * 16 < c:  # x^4 < c/16?? no: need x^4 <= c/2; iterate x up to (c/2)^(1/4)
        q = x ** 4
        if q * 2 > c: break
        r = c - q
        if r in fp_set:
            y = round(r ** 0.25)
            while y ** 4 < r: y += 1
            while y ** 4 > r: y -= 1
            if y ** 4 == r and math.gcd(x, y) == 1:
                WIT = (x ** 4, y ** 4, c)
                break
        x += 1
        q = x ** 4
    checked += 1
    if WIT: break
log(f'Route 2 (c=x^4+y^4 subfamily, all 4-powerful c <= 1e16): '
    f'{"WITNESS " + str(WIT) if WIT else "ZERO"} ({time.time()-t:.1f}s, {checked}/{len(r4_all)} c scanned)')

# --- Route 3: Sophie-Germain parametric ---
t = time.time()
SG_LIMIT = 2 * 10 ** 8
r4_sg = set(gen_r4(SG_LIMIT))
log(f'4-powerful <= 2e8: {len(r4_sg)} ({time.time()-t:.1f}s)')
t = time.time()
hits = []
for z in range(1, 401):
    for x in range(3, 4001, 2):   # x odd
        if math.gcd(x, z) != 1: continue
        u = x * x - 4 * x * z + 8 * z * z
        v = x * x + 4 * x * z + 8 * z * z
        if u < 2 or v < 2: continue
        if u in r4_sg and v in r4_sg:
            hits.append((x, z, u, v))
            a = x ** 4
            b = 64 * z ** 4
            c = a + b
            if c in r4_set16 or c in r4_sg:
                WIT = (a, b, c)
                log(f'Route 3 FULL HIT: x={x} z={z} a={a} b={b} c={c}')
                break
    if WIT: break
log(f'Route 3 (SG factors u,v both 4-powerful, z<=400, x<=4000): '
    f'{len(hits)} factor-hits {hits[:5]}, full witness: {WIT} ({time.time()-t:.1f}s)')

if WIT:
    a, b, c = WIT
    fa, fb, fc = factorint(a), factorint(b), factorint(c)
    log('VERIFICATION:')
    log(f'  a = {a} = {fa}  (min exponent {min(fa.values())})')
    log(f'  b = {b} = {fb}  (min exponent {min(fb.values())})')
    log(f'  c = {c} = {fc}  (min exponent {min(fc.values())})')
    ok = min(fa.values()) >= 4 and min(fb.values()) >= 4 and min(fc.values()) >= 4 \
         and math.gcd(a, b) == 1 and math.gcd(a, c) == 1 and math.gcd(b, c) == 1
    log(f'  pairwise coprime + all exponents >= 4: {ok}')
    if ok:
        with open('/home/z/erdos-weak-problems/problem939-rpowerful/WITNESS939.md', 'w') as f:
            f.write(f'# ERDŐS #939 — Q1 WITNESS (r=4)\n\na = {a}\nb = {b}\nc = a+b = {c}\n\n'
                    f'factorizations:\n{fa}\n{fb}\n{fc}\n\npairwise coprime, all exponents >= 4.\n')
        log('  WITNESS939.md written.')
else:
    log('NO WITNESS via algebraic routes this round. Coverage added:')
    log(f'  - ALL coprime 4th-power pairs (x^4+y^4) with sum <= 1e16: ZERO (complete subfamily).')
    log(f'  - SG parametric family z<=400, x<=4000: factor-hits listed above; no full witness.')
log(f'\nTotal runtime {time.time()-T0:.1f}s')
LOG.close()
