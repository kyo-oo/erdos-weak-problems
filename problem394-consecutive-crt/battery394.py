#!/usr/bin/env python3
"""BATTERY 394 — independent verification for the Erdos394 kernel (S034).

Method 1 (brute force): t_k(n) = least m with n | m(m+1)...(m+k-1), direct scan.
Method 2 (CRT): t_k(n) = min over ordered coprime factorizations of the
least positive solution of m = -i (mod d_i) — the characterization's oracle.

GREEN requires: (A) all agreements k=2..6, n<=300, (n,k!)=1;
(B) the four Lean tables (t2..t5) re-verified value by value;
(C) the showcase instances; (D) t_k(n) <= n.
"""
import sys
from math import gcd, factorial
from itertools import product as iproduct

def prod_cons(m, k):
    p = 1
    for i in range(k):
        p *= (m + i)
    return p

def t_brute(n, k):
    for m in range(1, n + 2):
        if prod_cons(m, k) % n == 0:
            return m
    return None

def prime_powers(n):
    pp, d = [], 2
    while d * d <= n:
        if n % d == 0:
            q = 1
            while n % d == 0:
                n //= d
                q *= d
            pp.append(q)
        d += 1
    if n > 1:
        pp.append(n)
    return pp

def crt_min(n, k):
    pp = prime_powers(n)
    best = None
    for assign in iproduct(range(k), repeat=len(pp)):
        d = [1] * k
        for q, pos in zip(pp, assign):
            d[pos] *= q
        r, M = 0, 1
        for i in range(k):
            m2 = d[i]
            r2 = (-i) % m2
            inv = pow(M, -1, m2)
            r = (r + M * ((r2 - r) * inv % m2)) % (M * m2)
            M *= m2
        assert M == n
        cand = r if r >= 1 else n
        if best is None or cand < best:
            best = cand
    return best

fails = 0

# (A) dual-method agreement
count = 0
for k in range(2, 7):
    KF = factorial(k)
    for n in range(2, 301):
        if gcd(n, KF) != 1:
            continue
        tb, tc = t_brute(n, k), crt_min(n, k)
        if tb != tc:
            print(f"MISMATCH k={k} n={n}: brute={tb} crt={tc}")
            fails += 1
        else:
            count += 1
print(f"(A) dual-method agreements k=2..6, n<=300: {count} (mismatches: {fails})")

# (B) the Lean tables
T2 = [2, 4, 6, 8, 10, 12, 5, 16, 18, 6, 22, 24, 26, 28, 30, 11, 14, 36, 12,
      40, 42, 9, 46, 48, 17, 52, 10, 18, 58, 60, 27, 25, 66, 23, 70, 72, 24,
      21, 78, 80, 82, 34, 29, 88, 13, 30, 19, 96, 44, 100]
N3 = [5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55,
      59, 61, 65, 67, 71, 73, 77, 79, 83, 85, 89, 91, 95, 97]
T3 = [3, 5, 9, 11, 15, 17, 21, 23, 27, 29, 5, 35, 39, 41, 45, 47, 51, 9, 57,
      59, 13, 65, 69, 71, 20, 77, 81, 15, 87, 12, 18, 95]
N4 = [5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55,
      59, 61, 65, 67, 71, 73, 77, 79, 83, 85, 89, 91, 95, 97]
T4 = [2, 4, 8, 10, 14, 16, 20, 22, 26, 28, 4, 34, 38, 40, 44, 46, 50, 8, 56,
      58, 10, 64, 68, 70, 11, 76, 80, 14, 86, 11, 17, 94]
N5 = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59, 61, 67, 71,
      73, 77, 79, 83, 89, 91, 97]
T5 = [3, 7, 9, 13, 15, 19, 25, 27, 33, 37, 39, 43, 45, 49, 55, 57, 63, 67,
      69, 7, 75, 79, 85, 10, 93]

tbad = 0
for j, n in enumerate(range(3, 102, 2)):
    if t_brute(n, 2) != T2[j]:
        print(f"T2 FAIL n={n}: got {t_brute(n,2)} want {T2[j]}")
        tbad += 1
for j, n in enumerate(N3):
    if t_brute(n, 3) != T3[j]:
        print(f"T3 FAIL n={n}: got {t_brute(n,3)} want {T3[j]}")
        tbad += 1
for j, n in enumerate(N4):
    if t_brute(n, 4) != T4[j]:
        print(f"T4 FAIL n={n}: got {t_brute(n,4)} want {T4[j]}")
        tbad += 1
for j, n in enumerate(N5):
    if t_brute(n, 5) != T5[j]:
        print(f"T5 FAIL n={n}: got {t_brute(n,5)} want {T5[j]}")
        tbad += 1
print(f"(B) Lean tables re-verified: 50+32+32+25 = 139 values (fails: {tbad})")
fails += tbad

# (C) showcase instances
shows = [(15, 2, 5), (35, 2, 14), (77, 2, 21), (35, 3, 5), (55, 3, 9),
         (77, 4, 11), (143, 5, 9)]
sbad = 0
for n, k, v in shows:
    got = t_brute(n, k)
    if got != v:
        print(f"SHOWCASE FAIL t_{k}({n}): got {got} want {v}")
        sbad += 1
print(f"(C) showcase instances: {len(shows)} (fails: {sbad})")
fails += sbad

# (D) t_k(n) <= n
dbad = 0
for k in range(1, 8):
    for n in range(1, 200):
        if t_brute(n, k) is None or t_brute(n, k) > n:
            print(f"BOUND FAIL t_{k}({n}) = {t_brute(n,k)} > {n}")
            dbad += 1
print(f"(D) t_k(n) <= n for k=1..7, n<200 (fails: {dbad})")
fails += dbad

if fails:
    print(f"ERDOS394_BATTERY_RED: {fails} failures")
    sys.exit(1)
print("ERDOS394_BATTERY_GREEN")
