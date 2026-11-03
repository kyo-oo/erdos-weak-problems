import sys
sys.path.insert(0, '.')
from classifier import vp_fact, g_value
# Fast family scan: p=2, a=1..200, cap 2^16 -> separates small-g from deep(>=16)
deep, small = [], []
for a in range(1, 201):
    if (a+1) % 2 == 0:
        small.append((a, 0)); continue
    g, st = g_value(a, 2, max_bits=2**16)
    if st == 'BOUNDED': small.append((a, g))
    else: deep.append(a)
print("SMALL (g value):", small)
print("DEEP (g >= 16):", deep)
