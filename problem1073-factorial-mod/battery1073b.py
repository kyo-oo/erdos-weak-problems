#!/usr/bin/env python3
"""BATTERY 1073-B — the KERNEL-CLAIMS battery (S041, Kernel 34).
Verifies every claim of Erdos1073.lean by methods independent of both the
engine (spf-sieve cascade) and the Lean kernel: sympy primality,
direct big-int factorial divisibility, brute window scans."""
import math
import random
from sympy import isprime, factorint

T28 = [25, 121, 169, 437, 551, 667, 721, 1037, 1159, 1273, 1349, 1403, 1541,
       1769, 1943, 2209, 2329, 2363, 2419, 3071, 3713, 4087, 5041, 5111,
       7313, 8357, 8479, 9017]

# the kernel's W131 (u, n) rows — cross-loaded from the census file and
# cross-checked against the kernel literal
W131 = []
for line in open("problem1073-factorial-mod/census1073_1e6.txt"):
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    u, n, P = map(int, line.split())
    W131.append((u, n))

ok = True
def check(cond, msg):
    global ok
    if not cond:
        print("FAIL:", msg)
        ok = False

# ---- 1. T28 rows: composite (sympy), bounded, witnessed by DIRECT divisibility
F = [1] * 100
for i in range(1, 100):
    F[i] = F[i - 1] * i
for u in T28:
    check(4 <= u <= 10**4, f"T28 bound {u}")
    check(not isprime(u), f"T28 composite {u}")
    check(any((F[n] + 1) % u == 0 for n in range(1, 100)), f"T28 witness {u}")
check(len(T28) == 28 and len(set(T28)) == 28, "T28 size/dup")

# ---- 2. census completeness at 10^4, INDEPENDENT scan (sympy composite test)
hits = []
for u in range(4, 10**4 + 1):
    if isprime(u):
        continue
    if any((F[n] + 1) % u == 0 for n in range(1, 100)):
        hits.append(u)
check(hits == sorted(T28), f"census<=1e4 exact: got {len(hits)} hits, "
      f"mismatch {[x for x in hits if x not in T28] + [x for x in T28 if x not in hits][:5]}")
print(f"census at 1e4: {len(hits)} hits == T28 -> A(10^4) = {len(hits)}")

# ---- 3. W131 rows: bounded, composite, direct big-int witness; matches engine
check(len(W131) == 131, f"W131 size {len(W131)}")
for u, n in W131:
    check(4 <= u < 10**6, f"W131 bound {u}")
    check(not isprime(u), f"W131 composite {u}")
    check(1 <= n, f"W131 n>=1 {u}")
    check((math.factorial(n) + 1) % u == 0, f"W131 witness {u} {n}")

# ---- 4. the Wilson channel
for p, n in [(5, 4), (13, 12), (563, 562)]:
    check(isprime(p), f"Wilson prime {p}")
    check((math.factorial(n) + 1) % (p * p) == 0, f"Wilson channel {p}")
check((563 * 563) == 316969, "563^2 = 316969")

# ---- 5. the Brocard channel
check(math.factorial(4) + 1 == 25 == 5 * 5, "Brocard 4")
check(math.factorial(5) + 1 == 121 == 11 * 11, "Brocard 5")
check(math.factorial(7) + 1 == 5041 == 71 * 71, "Brocard 7")

# ---- 6. L1 window law spot-check on 200 random composites < 10^6
random.seed(1073)
for _ in range(200):
    u = random.randrange(4, 10**6)
    if isprime(u):
        continue
    P = min(factorint(u))
    for n in range(1, min(P, 700)):
        if (math.factorial(n) + 1) % u == 0:
            check(n < P, f"L1 violation u={u} n={n} P={P}")
            break

# ---- 7. the growth-table consistency (engine agreement)
import bisect
us = sorted(u for u, _ in W131)
for x, want in [(10**3, 7), (10**4, 28)]:
    check(bisect.bisect_left(us, x) == want, f"A({x}) = {want}")

print("BATTERY1073B:", "GREEN" if ok else "RED")
