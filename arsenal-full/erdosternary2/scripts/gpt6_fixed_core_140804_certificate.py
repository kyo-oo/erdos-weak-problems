#!/usr/bin/env python3
"""Exact GST/Worldtrace 30-trit certificate through all 140804 cores.

Finite arithmetic only; the all-scale consequence uses two mathematical
lemmas: c_(s+1) = c_s + 3^(s+1)c_s^2 + 3^(2s+1)c_s^3, and the
GST tower digit projection d_3(4^(u*3^s), s+1+k)=d_3(u*c_s,k) (k<=s).
No random sampling, floating arithmetic, raw exponential expansion,
native_decide, or unverifiable search truncation.
"""
from time import perf_counter

MAX_CORE = 140804
DEPTH = 30
Q = 3**DEPTH
c = 1
for s in range(DEPTH-1):
    c = (c + 3**(s+1)*c*c + 3**(2*s+1)*c**3) % Q
assert Q == 205891132094649
assert c == 28881270545965

# Independent certificate structure: exhaustive pruning, not a sample.
survivors = list(range(1, MAX_CORE+2))
counts = []
for k in range(DEPTH):
    divisor = 3**k
    survivors = [u for u in survivors
                 if ((u*c//divisor)%3) != 2]
    counts.append(len(survivors))
assert len(counts)==DEPTH
assert survivors == [140805], (len(survivors),survivors[:10])
print("COEFF30",c)
print("MODULUS",Q)
print("FIRST_SURVIVOR_30",survivors[0])
print("CLEAN_COUNT_L28_L29_L30",counts[-3:])

# All s=0,...,28 have separate exact modular witnesses; we test a
# longer window than the final bound and prove the maximum hit offset.
checked = 0
maximum_offset = -1
max_case = None
started = perf_counter()
for s in range(DEPTH-1):
    window = s+60
    modulus = 3**window
    step = pow(4, 3**s, modulus)
    residue = 1
    for u in range(1, MAX_CORE+1):
        residue = (residue*step)%modulus
        K = u*3**s
        if K in (1, 4):
            continue
        checked += 1
        x = residue
        p = 0
        while x:
            x,digit = divmod(x,3)
            if digit==2:
                break
            p += 1
        else:
            raise AssertionError(("no witness within window",s,u,K))
        offset = p-s-1
        if offset>maximum_offset:
            maximum_offset=offset
            max_case=(s,u,p)
assert checked == (DEPTH-1)*MAX_CORE-2
assert checked == 4083314
assert maximum_offset == 41 and max_case == (19,102967,61)
print("LOW_SCALE_EXHAUSTIVE_CASES",checked)
print("MAX_RELATIVE_OFFSET",maximum_offset,max_case)
print("ALL_SCALES_FIXED_CORE_BOUND","1 <= u <= 140804; 4^(u*3^s) fires by row s+42")
print("GST_FIXED_CORE_140804_CERTIFICATE_PASS=1")
print("ELAPSED_SECONDS",round(perf_counter()-started,2))
