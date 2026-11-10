#!/usr/bin/env python3
"""Pool structure analysis for P273: how many fresh m (2m+1 prime, right parity)
divide a given modulus? Guides the tree-growth discipline."""
from sympy import factorint, isprime, primerange

def sieve_M(mlimit):
    N = 2*mlimit + 2
    sv = bytearray([1]) * N
    sv[0] = sv[1] = 0
    i = 2
    while i*i < N:
        if sv[i]:
            sv[i*i::i] = bytearray(len(range(i*i, N, i)))
        i += 1
    return set(m for m in range(2, mlimit) if sv[2*m+1])

def divisors_of(n):
    f = factorint(n)
    ds = [1]
    for q, e in f.items():
        ds = [d*q**k for d in ds for k in range(e+1)]
    return ds

mlimit = 1_000_000
M = sieve_M(mlimit)
E = set(m for m in M if m % 2 == 0)
O = set(m for m in M if m % 2 == 1)
print(f"|M|={len(M)} |E|={len(E)} |O|={len(O)}")

# probe: for various nu, count even-M / odd-M divisors
probes = [2, 6, 12, 24, 48, 120, 360, 720, 2520, 5040, 27720, 55440, 720720,
          3, 9, 15, 45, 105, 315, 945, 3465, 10395, 45045, 135135,
          2*45045, 4*45045, 8*45045, 16*45045, 64*45045,
          3**6*5**2*7, 3**6*5**3*7, 3**8*5**3*7, 3**8*5**3*7*11, 3**8*5**3*7*11*13,
          2**4*3**6*5**3*7, 2**6*3**6*5**3*7, 2**8*3**8*5**3*7*11]
for nu in probes:
    dv = divisors_of(nu)
    e = sum(1 for d in dv if d in E)
    o = sum(1 for d in dv if d in O)
    print(f"nu={nu:>14,d} d(nu)={len(dv):>5}  evenM={e:>4}  oddM={o:>4}")
