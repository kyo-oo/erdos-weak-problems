#!/usr/bin/env python3
# #686 k=3 square hunt: t^2 = (m+1)(m+2)(m+3) / ((n+1)(n+2)(n+3)),
# m >= n+3. The square-N residue front at k=3 (the S036 war's next step:
# t=99 and t=195 were the k=2 sporadics; now k=3).
# Method: for each n, the denominator D = (n+1)(n+2)(n+3); we need
# t^2 * D = (m+1)(m+2)(m+3) — walk m, keep a running product, test
# divisibility + square quotient.
import math

def is_square(x):
    if x < 0:
        return False
    r = math.isqrt(x)
    return r * r == x

NMAX = 40000   # n up to 40k, m up to n + window
hits = []
for n in range(0, NMAX):
    D = (n + 1) * (n + 2) * (n + 3)
    # running product of (m+1)(m+2)(m+3) as m advances:
    # start at m = n+3 (minimum), product over (n+4..n+6)
    lo = n + 4
    P = lo * (lo + 1) * (lo + 2)
    m = n + 3
    # advance m by 1: new product = old * (m+4)/m — maintain exactly
    while m < n + 3 + 20000:
        # P currently = (m+1)(m+2)(m+3)
        if P % D == 0:
            q = P // D
            if is_square(q):
                t = math.isqrt(q)
                hits.append((t, m, n))
                print(f"#686 k=3 SQUARE HIT: t={t} m={m} n={n}  "
                      f"(t^2 = {t*t})")
        # advance: P := (m+2)(m+3)(m+4) = P * (m+4) / (m+1)
        P = P // (m + 1) * (m + 4)
        m += 1

if not hits:
    print(f"#686 k=3: zero hits at n < {NMAX}, window 20000")
else:
    ts = sorted(set(h[0] for h in hits))
    print(f"#686 k=3 total hits: {len(hits)}; t values: {ts[:20]}")
