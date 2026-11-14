#!/usr/bin/env python3
"""PASCAL 263 — fourth independent route for the three new #1063 witnesses:
C(n,k) built by the additive Pascal recurrence ONLY (no multiplications, no
divisions, no factorials), sliding a width-(k+1) row prefix from row 0 to row n.
Then the divisibility receipt (wcount, exempt position) is re-derived."""
import time
from gmpy2 import mpz, comb as gcomb
T0 = time.time()
def pascal_C(n, k):
    row = [mpz(1)] + [mpz(0)] * k      # prefix of row 0, width k+1
    for _ in range(n):                  # row r -> row r+1 (prefix only)
        for j in range(k, 0, -1):
            row[j] += row[j - 1]
    return row[k]
ok = True
for k, nk in ((18, 31110), (19, 612), (20, 67203)):
    c = pascal_C(nk, k)
    assert c == gcomb(mpz(nk), k), "PASCAL/GMP MISMATCH k=%d" % k
    wc = sum(1 for i in range(k) if c % (nk - i) == 0)
    misses = [i for i in range(k) if c % (nk - i) != 0]
    good = (wc == k - 1) and (len(misses) == 1)
    ok = ok and good
    print("k=%2d n_k=%6d: Pascal-additive C == GMP comb;  wcount=%d  exempt i=%s  %s"
          % (k, nk, wc, misses, "GREEN" if good else "RED"))
print("PASCAL 263 %s — %.1fs" % ("ALL GREEN" if ok else "RED", time.time() - T0))
