#!/usr/bin/env python3
# validate939.py — W63-B1: THE ENUMERATOR DUAL-METHOD VALIDATION.
#
# The box certificates of hunt939d.py (B13..B20) rest on gen4() — the corrected
# 4-powerful enumerator (prime exponents >= 4). Per the verification law, the
# enumerator itself is validated by TWO INDEPENDENT CONSTRUCTIONS before any
# grind:
#   M1 (DFS generator, hunt939d.gen4): depth-first recursion over primes with
#       free exponents 4,5,6,...  — the engine the box lanes sweep with.
#   M2 (rad sieve, this file): a numpy sieve computes rad(n) = product of the
#       DISTINCT prime divisors of n for EVERY n <= N (a completely different
#       algorithm: no recursion, no prime-power enumeration); then
#       n is 4-powerful iff rad(n)^4 | n (n divided by rad exactly four
#       times) — because every prime exponent >= 4 iff rad^4 | n.
# Checks (receipts -> validate939_output.txt):
#   (1) M1 at 1e4 reproduces the K60 Lean census row (Erdos939R4.lean
#       census_r4_members, 25 values incl. 1) exactly, excluding the vacuous 1.
#   (2) M2 at 1e4 reproduces the SAME Lean census row exactly (so the Lean
#       literal is doubly matched).
#   (3) M2 list == M1 list EXACTLY at 1e7 (full set equality, all elements).
#   (4) audit anchors: 32 = 2^5, 2592 = 2^5*3^4, 3888 = 2^4*3^5 present;
#       factorization receipts via sympy.
#   (5) the true counts at 1e13..1e19 (M1; the box log re-derives them).
import os, sys, time
import numpy as np
from sympy import factorint

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hunt939d as H

REPO = H.REPO
OUTP = os.path.join(REPO, 'validate939_output.txt')

def rad_sieve_4powerful(N):
    """M2: independent construction. rad(n) via prime-sieve strided slices for
    every n in [0, N]; then 4-powerful iff rad(n)^4 | n. Returns bool mask."""
    t0 = time.time()
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for p in range(2, H.isqrt(N) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.nonzero(sieve)[0]
    rad = np.ones(N + 1, dtype=np.int64)
    for p in primes:
        rad[p::p] *= p          # rad(n) = prod of DISTINCT primes dividing n
    k = np.arange(N + 1, dtype=np.int64)
    ok = (k % rad == 0)             # first exact division (0,1 fixed below)
    k //= rad
    for _ in range(3):             # rad^4 | n iff four exact divisions by rad
        ok &= (k % rad == 0)
        k //= rad
    ok[:2] = False                 # 0,1 excluded (1 is vacuously rpow-4 per the
                                    # K60 kernel but outside both enumerations)
    print(f'    [M2] rad-sieve N={N}: {len(primes)} primes sieved, '
          f'{time.time()-t0:.1f}s', flush=True)
    return ok

def main():
    lines = []
    def log(s=''):
        print(s, flush=True); lines.append(str(s))
    log('=== validate939 — ENUMERATOR DUAL-METHOD VALIDATION (W63-B1) ===')
    log(f'python {sys.version.split()[0]}; numpy {np.__version__}; '
        f'gmpy2 {H.gmpy2.version()}')
    # (1) M1 census row at 1e4 vs the K60 Lean literal
    got = H.gen4(10 ** 4)
    ok1 = (got == H.LEAN_CENSUS_R4[1:])
    log(f'[1] M1 (DFS generator gen4) at 1e4 == K60 Lean census row '
        f'(excl. vacuous 1): {ok1}  ({len(got)} values vs {len(H.LEAN_CENSUS_R4)-1})')
    # (2) M2 census row at 1e4 vs the SAME Lean literal
    m4 = rad_sieve_4powerful(10 ** 4)
    sv4 = [i for i in range(2, 10 ** 4 + 1) if m4[i]]
    ok2 = (sv4 == H.LEAN_CENSUS_R4[1:])
    log(f'[2] M2 (independent rad-sieve) at 1e4 == K60 Lean census row '
        f'(excl. 1): {ok2}')
    # (3) full set equality M1 == M2 at 1e7
    m7 = rad_sieve_4powerful(10 ** 7)
    sv7 = [int(i) for i in np.nonzero(m7)[0]]
    g7 = H.gen4(10 ** 7)
    ok3 = (sv7 == g7)
    log(f'[3] M2 == M1 EXACT set equality at 1e7: {ok3}  '
        f'(|set| = {len(sv7)}; identical element-by-element)')
    if not ok3:
        log(f'    M2-only: {sorted(set(sv7) - set(g7))[:20]}')
        log(f'    M1-only: {sorted(set(g7) - set(sv7))[:20]}')
    # (4) audit anchors + factorization receipts
    log('[4] audit anchors (the values the prior fourth-power engines missed):')
    for v in (32, 2592, 3888, 614656, 1594323):
        f = factorint(v)
        log(f'    {v}: factors {dict(f)}, min exp {min(f.values())} '
            f'-> 4-powerful: {min(f.values()) >= 4}; in M1 list: {v in set(got) or v in set(g7)}')
    # (5) true counts 1e13..1e19 (M1)
    log('[5] TRUE 4-powerful counts (M1; re-derivation of the W62 audit rows):')
    for lim in (10 ** 13, 10 ** 15, 10 ** 16, 10 ** 17, 10 ** 18, 10 ** 19):
        t = time.time(); n = len(H.gen4(lim))
        log(f'    <= 1e{round(lim and len(str(lim)) - 1)}: {n}   '
            f'({time.time()-t:.1f}s)')
    okall = ok1 and ok2 and ok3
    log(f'=== validate939 VERDICT: {"ALL GREEN" if okall else "FAILURE — DO NOT GRIND"} ===')
    with open(OUTP, 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    print(f'receipts -> {OUTP}', flush=True)

if __name__ == '__main__':
    main()
