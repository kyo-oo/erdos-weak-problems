#!/usr/bin/env python3
# Independent brute-force cross-validation of hunt850 at X=100000 (pure python, exact dict keys).
import os
from collections import defaultdict

OUT = "/home/z/erdos-weak-problems/problem850-radical-triple"
X = 100000
N = X + 2

# SPF sieve (Eratosthenes style: first prime to mark each index wins)
spf = [0] * (N + 1)
for i in range(2, N + 1):
    if spf[i] == 0:
        for j in range(i, N + 1, i):
            if spf[j] == 0:
                spf[j] = i

def rad(n):
    r = 1
    while n > 1:
        p = spf[n]
        r *= p
        while n % p == 0:
            n //= p
    return r

rads = [0] + [rad(n) for n in range(1, N + 1)]

g2 = defaultdict(list)
for x in range(1, X + 1):
    g2[(rads[x], rads[x + 1])].append(x)
l2 = sorted((a, b) for v in g2.values() for i, a in enumerate(v) for b in v[i + 1:])

g3 = defaultdict(list)
for x in range(1, X + 1):
    g3[(rads[x], rads[x + 1], rads[x + 2])].append(x)
l3 = sorted((a, b) for v in g3.values() for i, a in enumerate(v) for b in v[i + 1:])

print("python brute force (X=%d):" % X)
print("  L2 pairs:", l2)
print("  L3 pairs:", l3)

with open(os.path.join(OUT, "brute_l2.txt"), "w") as f:
    for a, b in l2:
        f.write("%d %d %d %d\n" % (a, b, rads[a], rads[a + 1]))
with open(os.path.join(OUT, "brute_l3.txt"), "w") as f:
    for a, b in l3:
        f.write("%d %d\n" % (a, b))

clines = [tuple(map(int, l.split())) for l in open(os.path.join(OUT, "length2_pairs.txt")) if l.strip()]
cpairs = sorted((a, b) for (a, b, r0, r1) in clines)
print("C-vs-python L2 pair list:", "MATCH" if cpairs == l2 else "MISMATCH")
if cpairs != l2:
    print("  C-only:", sorted(set(cpairs) - set(l2)))
    print("  py-only:", sorted(set(l2) - set(cpairs)))
print("C-vs-python L3 both empty:", "yes" if not l3 else "NO — python found: %s" % l3)
