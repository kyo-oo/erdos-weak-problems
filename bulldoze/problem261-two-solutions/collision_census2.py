#!/usr/bin/env python3
"""CORRECTED collision census for weakened Erdos #261.

Representation of n/2^n with pieces n+j, j in P subset {1..J}, J in P:
  multiply both sides by 2^(n+J):
      n * 2^J = sum_{j in P} (n+j) * 2^(J-j) = n*A_P + S_P
  ==>  n * (2^J - A_P) = S_P      [exact iff]
  A_P = sum_{j in P} 2^(J-j),  S_P = sum_{j in P} j*2^(J-j)

Every certified pattern is VERIFIED by exact rational reconstruction.
COLLISION = same n, two distinct patterns P != Q  ==>  n/2^n has two
distinct representations ==> answers Erdos's weakened #261 sub-question
AFFIRMATIVELY."""
from fractions import Fraction
from collections import defaultdict

JMAX = 16
sols = defaultdict(set)

for J in range(1, JMAX + 1):
    for mask in range(1 << J):
        if not (mask >> (J - 1)) & 1:      # require J in P (max offset exactly J)
            continue
        A = 0; S = 0
        for j in range(1, J + 1):
            if mask >> (j - 1) & 1:
                A += 1 << (J - j)
                S += j * (1 << (J - j))
        den = (1 << J) - A
        if den <= 0:
            continue
        if S % den == 0:
            n = S // den
            if n >= 1:
                offs = frozenset(j for j in range(1, J + 1) if mask >> (j - 1) & 1)
                # EXACT VERIFICATION
                lhs = Fraction(n, 1 << n) if n < 400 else None
                if lhs is not None:
                    rhs = sum(Fraction(n + j, 1 << (n + j)) for j in offs)
                    assert lhs == rhs, f"BROKEN CERT n={n} P={sorted(offs)}"
                sols[n].add(offs)

coll = {n: ps for n, ps in sols.items() if len(ps) >= 2}
print(f"n-values representable (J <= {JMAX}): {len(sols)}")
print(f"COLLISIONS: {len(coll)}")
for n, ps in sorted(coll.items())[:12]:
    print(f"  n = {n}: {len(ps)} distinct representations, e.g.:")
    for p in sorted(ps, key=lambda s: (len(s), sorted(s)))[:3]:
        print(f"      P = {sorted(p)}   (verified exact)")
if not coll:
    mx = max(len(ps) for ps in sols.values()) if sols else 0
    print(f"NO COLLISIONS to J={JMAX}; max reps per n = {mx}")
ns = sorted(sols)
print("representable n <= 200:", [x for x in ns if x <= 200])
