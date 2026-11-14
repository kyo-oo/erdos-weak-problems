#!/usr/bin/env python3
"""
THE READING RESOLUTION: does Fibonacci heal after removing {1,2}?
Fibonacci multiset: 1,1,2,3,5,8,13,21,...
Site claims Fibonacci shows (m,n)=(1,2). If every 2-removal breaks -> forall-reading consistent.
If some 2-removal heals (e.g. {1,2}) -> the site's claim requires the exists-reading.
Weak completeness up to bound B with infinite-tail safety: for Fibonacci, elements <= B
determine coverage up to B; we also verify the contiguity claim structurally.
"""
def fib_mult(n):
    a, b = 1, 1
    A = []
    while len(A) < n:
        A.append(a); a, b = b, a + b
    return A

def covered(A, B):
    cov = 1
    for x in A:
        if x <= B:
            cov |= cov << x
    return cov & ((1 << (B + 1)) - 1)

def report(A, B, name):
    cov = covered(A, B)
    holes = [n for n in range(0, B + 1) if not (cov >> n) & 1]
    # max hole:
    mh = max(holes) if holes else -1
    return cov, holes, mh

B = 3000
F = fib_mult(20)  # 1,1,2,3,5,...,4181
Fb = [x for x in F if x <= B]
print("Fibonacci elements <= B:", Fb)
cov, holes, mh = report(Fb, B, "F")
print(f"Fibonacci itself: holes up to {B}: {holes[:10]} ... maxhole={mh}")

import itertools
# 2-removals by position pairs, dedup by value-multiset
seen = {}
n = len(Fb)
for i, j in itertools.combinations(range(n), 2):
    Ax = Fb[:i] + Fb[i+1:j] + Fb[j+1:]
    key = tuple(sorted(Ax))
    if key in seen: continue
    cov, holes, mh = report(Ax, B, "")
    # completeness up to B: all n in [C, B] covered where C small
    tail_holes = [h for h in holes if h > 60]
    status = "HEALS(bounded holes)" if not tail_holes else f"BREAKS(holes at {tail_holes[:6]}...)"
    seen[key] = (Fb[i], Fb[j], status, mh, len([h for h in holes if h > 60]))
    print(f"remove {{{Fb[i]},{Fb[j]}}}: maxhole={mh}, holes>60: {len([h for h in holes if h>60])} -> {status}")
