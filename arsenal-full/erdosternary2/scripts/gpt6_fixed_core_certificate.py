#!/usr/bin/env python3
"""Exact finite certificate for the GST/Worldtrace fixed-core infinite strip.

This program proves only finite arithmetic obligations. The passage from those
obligations to unbounded scales uses the separately proved GST LTE recurrence
and GSTTowerFire.tower_digit_read. No floats, random sampling or giant 4^K.
"""
from collections import Counter

DEPTH = 18
Q = 3**DEPTH
MAX_U = 566
C = 1
for n in range(17):
    C = (C + 3**(n+1)*C*C + 3**(2*n+1)*C*C*C) % Q
assert C == 235352482
INV = pow(C, -1, Q)
assert INV == 44359807 and (INV*C)%Q == 1

def digit(x, p):
    return (x//3**p)%3

def first_two(x, lo, hi):
    return next((p for p in range(lo, hi+1) if digit(x,p)==2), None)

# Every 18-trit Cantor residue; exact count is 2^18, no skipped words.
cantor = [0]
for j in range(DEPTH):
    power = 3**j
    cantor += [x+power for x in cantor]
assert len(cantor) == 2**DEPTH and len(set(cantor)) == len(cantor)
inverse_images = [(INV*x)%Q for x in cantor]
least_positive = min(v for v in inverse_images if v>0)
assert least_positive == 567
assert first_two((567*C)%Q, 0, 17) is None
hist = Counter()
for u in range(1, MAX_U+1):
    k = first_two((u*C)%Q, 0, 17)
    assert k is not None, u
    hist[k] += 1
assert sum(hist.values()) == MAX_U

# All initial scales, with the ACTUAL claimed row ceiling.
checked = 0
max_relative_offset = -1
max_case = None
for s in range(17):
    bound = s+22
    modulus = 3**(bound+1)
    for u in range(1, MAX_U+1):
        exponent = u*3**s
        if exponent in (1,4):
            continue
        checked += 1
        residue = pow(4, exponent, modulus)
        p = first_two(residue, 1, bound)
        assert p is not None, (s,u,exponent)
        if p-s-1 > max_relative_offset:
            max_relative_offset = p-s-1
            max_case = (s,u,p)
assert checked == 9620
assert max_relative_offset == 21 and max_case == (10,466,32)
print("GST_FIXED_CORE_Q", Q)
print("GST_FIXED_CORE_C17", C)
print("GST_FIXED_CORE_INVERSE", INV)
print("GST_FIXED_CORE_CANTOR_WORDS", len(cantor))
print("GST_FIXED_CORE_FIRST_WINDOW_SURVIVOR", least_positive)
print("GST_FIXED_CORE_MULTIPLIERS_PASSED", MAX_U)
print("GST_FIXED_CORE_LOW_SCALE_CASES", checked)
print("GST_FIXED_CORE_MAX_OFFSET", max_relative_offset, max_case)
print("GST_FIXED_CORE_CERTIFICATE_PASS=1")
