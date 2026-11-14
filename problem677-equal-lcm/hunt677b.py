#!/usr/bin/env python3
# W61 Task 3-b — Erdős #677 deep collision sweep.
# Corpus: "Let M(n,k) = lcm(n+1,...,n+k). Is it true that for all m >= n+k:
#          M(n,k) != M(m,k)?"  A same-k collision with gap >= k = FULL NO.
import time, math, sys
from math import gcd

T0 = time.time()
LOG = open('/home/z/erdos-weak-problems/problem677-equal-lcm/hunt677b_output.txt', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s); LOG.write(s + '\n'); LOG.flush()

def lcm(a, b):
    return a // gcd(a, b) * b

# k=2 lemma: M(n,2) = (n+1)(n+2) (consecutive -> gcd 1); x -> x(x+1) strictly
# increasing for x >= 1, hence injective: NO k=2 collision exists, for ALL n.
log('k=2 lemma: M(n,2)=(n+1)(n+2), x->x(x+1) strictly increasing => injective (no hunt needed).')

WITNESS = None
# budgets: (k, N) — N = max n scanned
plans = [(3, 800000), (4, 400000), (5, 200000), (6, 100000),
         (7, 60000), (8, 40000), (9, 20000), (10, 12000), (11, 8000), (12, 6000)]
for k, N in plans:
    if WITNESS: break
    t = time.time()
    first = {}          # value -> smallest n seen
    collisions = []
    # sliding window lcm via full recompute per n is O(k); use it (k small).
    vals = list(range(2, N + k + 2))   # will index n+1 .. n+k for n in [1, N]
    L = 1
    # initial window n=1: lcm(2..k+1)
    for v in range(2, k + 2): L = lcm(L, v)
    first[L] = 1
    for n in range(2, N + 1):
        # window n: lcm(n+1 .. n+k) = LCM of previous window with entering n+k, leaving n
        # cannot remove; recompute incrementally: maintain L_entering only works if
        # leaving element divides... do segment-free: maintain lcm of (n+1..n+k) via
        # prefix-lcm differences is unsafe. Direct method: L_new = lcm(L_old, n+k) then
        # divide by gcd contributions of n? UNSAFE. => maintain per-prime rolling counts
        # is heavy; use the standard trick: recompute every step (k small).
        L = 1
        base = n + 1
        for v in range(base, base + k):
            L = lcm(L, v)
        seen = first.get(L)
        if seen is None:
            first[L] = n
        elif n - seen >= k:
            collisions.append((seen, n, k, L))
            WITNESS = (seen, n, k)
            log(f'*** COLLISION with gap >= k: M({seen},{k}) = M({n},{k}) = {L}')
            break
        # near-miss log optional
    log(f'k={k}: n<= {N} scanned, distinct values {len(first)}, '
        f'collisions(gap>=k) {len(collisions)}, {time.time()-t:.1f}s')
    if not WITNESS:
        # report near-miss collisions (gap < k) count only
        nm = 0
        # (near-misses weren't stored; count same-value n-pairs cheaply skipped)
        log(f'  (same-value pairs with gap < k were overwritten by first-seen; only gap>=k tracked)')

if WITNESS:
    n0, n1, k = WITNESS
    a = 1
    for v in range(n0 + 1, n0 + k + 1): a = lcm(a, v)
    b = 1
    for v in range(n1 + 1, n1 + k + 1): b = lcm(b, v)
    log(f'VERIFY: M({n0},{k}) = {a}; M({n1},{k}) = {b}; equal = {a == b}')
    with open('/home/z/erdos-weak-problems/problem677-equal-lcm/WITNESS677.md', 'w') as f:
        f.write(f'# ERDŐS #677 — COLLISION WITNESS (FULL NO)\n\nM({n0},{k}) = M({n1},{k}) with m=n1 >= n0+k = {n0+k}.\n')
        f.write(f'window A = lcm({n0+1}..{n0+k}) = {a}\nwindow B = lcm({n1+1}..{n1+k}) = {b}\n')
    log('WITNESS677.md written.')
else:
    log('NO collision (gap>=k) in the scanned box. Certified: no same-k lcm-window')
    log('collision for k=3..12 with n <= N_k as tabulated above (k=2: injective lemma).')
log(f'Total runtime {time.time()-T0:.1f}s')
LOG.close()
