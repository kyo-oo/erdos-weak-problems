#!/usr/bin/env python3
# #396 hunt: for which k does there exist n with
#   P(k,n) = prod_{i=0}^{k} (n-i)  dividing  C(2n, n)?
# Case frontier extension: k = 0, 1, 2, ... — smallest witnesses n.
from math import comb

def divides_prod(k, n):
    """prod_{i=0}^{k} (n-i) | C(2n,n)?"""
    if n - k < 1:
        return False
    P = 1
    for i in range(0, k + 1):
        P *= (n - i)
    C = comb(2 * n, n)
    return C % P == 0

NMAX = 4000
best = {}   # k -> smallest n
for n in range(2, NMAX + 1):
    C = comb(2 * n, n)
    P = 1
    for k in range(0, n):
        if n - k < 1:
            break
        P *= (n - k)
        if C % P == 0:
            if k not in best:
                best[k] = n
        else:
            break

ks = sorted(best)
print("#396 witnesses: k -> smallest n with prod_{i=0}^{k}(n-i) | C(2n,n)")
line = []
for k in ks[:26]:
    line.append(f"k={k}: n={best[k]}")
    assert divides_prod(k, best[k]), (k, best[k])
print("  " + "; ".join(line))
print(f"frontier: k = 0..{ks[-1]} (all with witnesses <= {NMAX})" if ks else "none")
