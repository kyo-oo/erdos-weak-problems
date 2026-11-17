#!/usr/bin/env python3
"""SORTED-greedy Stanley A(t) — the Erdos-page convention.
a_0=0, a_1=t; candidates m > last, add iff no 3AP."""
import sys

def sorted_stanley(t, limit):
    S = [0, t]
    Sset = {0, t}
    for m in range(t + 1, limit):
        blocked = False
        for i in range(len(S)):
            for j in range(len(S)):
                if i == j: continue
                a, b = S[i], S[j]
                # (a, b, m): a + m = 2b
                if a + m == 2 * b:
                    blocked = True; break
            if blocked: break
        if not blocked:
            S.append(m); Sset.add(m)
    return S

def census(S, kmax=7):
    return [sum(1 for x in S if x < 3**k) for k in range(1, kmax + 1)]

def tern(n):  # ternary digits as string
    if n == 0: return "0"
    d = ""
    while n: d = str(n % 3) + d; n //= 3
    return d

print("=" * 76)
print("SORTED-GREEDY A(t) — THE ERDOS CONVENTION — FAMILY HUNT")
print("=" * 76)
LIMIT = 2200
targets = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
for t in targets:
    S = sorted_stanley(t, LIMIT)
    c = census(S)
    print(f"t={t:3d}  |A|={len(S):4d}  census={c}")
print()
for t in [1, 2, 3, 4, 6, 9]:
    S = sorted_stanley(t, LIMIT)
    print(f"A({t}) first 30: {S[:30]}")
    print(f"     ternary: {[tern(x) for x in S[:30]]}")
