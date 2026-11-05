#!/usr/bin/env python3
"""ERDOS #1108 — deep square census to max(S) <= 24 (Gray-code, exact).
Prefilter: square-residue set mod M = 2^6*3^2*5*7*11*13 = 2882880 (~0.88% pass),
then exact isqrt confirmation. Every hit re-verified through the FULL CASCADE LAW.
"""
from math import factorial, isqrt
import sys

N = 24
M = 64 * 63 * 65 * 11  # 2882880 = 2^6 * 3^2 * 5 * 7 * 11 * 13
facts = [factorial(b) for b in range(N + 1)]

def v2(n):
    c = 0
    while n % 2 == 0:
        n //= 2; c += 1
    return c

LAM = {}
def Lam(j):
    if j not in LAM: LAM[j] = v2(factorial(2 * j))
    return LAM[j]

def machine_v2(S):
    S = sorted(set(S))
    j0 = S[0] // 2
    L0 = Lam(j0)
    pairs = sorted(set(b // 2 for b in S))
    stack = [(Lam(j) - L0, sum(factorial(b) >> Lam(j) for b in S if b // 2 == j)) for j in pairs]
    nu = 0
    while True:
        d0, A0 = stack[0]
        if len(stack) == 1 or v2(A0) < stack[1][0]:
            return L0 + nu + v2(A0)
        d1 = stack[1][0]
        nu += d1
        newA = (A0 >> d1) + stack[1][1]
        stack = [(0, newA)] + [(d - d1, O) for (d, O) in stack[2:]]

print(f"square-residue set mod {M} ...", flush=True)
sq = set(r * r % M for r in range(M))
print(f"  {len(sq)} residues ({100.0*len(sq)/M:.2f}%)", flush=True)

print(f"Gray-code census over all 2^{N}-1 subsets of [1..{N}] ...", flush=True)
hits = []
cur = 0        # running sum
g = 0          # gray code = subset bitmask (bit t <-> element t+1)
cmod = 0       # running sum mod M
fmod = [f % M for f in facts]
k = 1
top = 1 << N
while k < top:
    t = (k & -k).bit_length() - 1
    g ^= (1 << t)
    e = t + 1
    if (g >> t) & 1:
        cur += facts[e]; cmod = (cmod + fmod[e]) % M
    else:
        cur -= facts[e]; cmod = (cmod - fmod[e]) % M
    if cmod in sq:
        r = isqrt(cur)
        if r * r == cur:
            S = [t + 1 for t in range(N) if (g >> t) & 1]
            hits.append((S, cur, r))
    k += 1

print(f"DONE: {len(hits)} square(s) among all subsets of [1..{N}]", flush=True)
for S, val, r in hits:
    mv = machine_v2(S)
    j0 = S[0] // 2
    lam = Lam(j0)
    ok = (mv == v2(val)) and (mv % 2 == 0) and (r * r == val)
    print(f"  S={S}  sum={val}  root={r}  v2={mv} (Lam({j0})={lam} + nu={mv-lam})  cascade+parity OK={ok}", flush=True)
maxes = sorted(set(S[-1] for S, _, _ in hits))
print(f"hit max-elements: {maxes}")
print(f"zero new squares for max in [16..{N}]: {all(m <= 15 for m in maxes)}")
