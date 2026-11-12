import json, math
from math import gcd
# pal_dlog_full.json: list of [q, h, U, V, o2, o3]
full = json.load(open('../pal_dlog_full.json'))
print("palette entries:", len(full))
fam = json.load(open('../fam5040.json'))
famset = set(int(k) for k in fam)
# all primes with h | 5040
div5040 = [r for r in full if 5040 % r[1] == 0]
print("h | 5040 count:", len(div5040), " of which in fam:", sum(1 for r in div5040 if r[0] in famset))
extra = [r for r in div5040 if r[0] not in famset]
tot = sum(1.0/r[1] for r in div5040)
print("total budget all h|5040:", tot)
print("extra primes (h|5040, not in fam):")
for r in sorted(extra, key=lambda r: r[1]):
    inpal = r[0] in famset
    print(f"  q={r[0]:6d} h={r[1]:5d} U={r[2]:5d} V={r[3]:5d} o2={r[4]} o3={r[5]} 1/h={1.0/r[1]:.5f}")
# distribution of h in palette
from collections import Counter
c = Counter(r[1] for r in full)
print("h histogram (top):", sorted(c.items())[:20])
# primes with h | 2520 (smaller torus)
d2520 = [r for r in full if 2520 % r[1] == 0]
print("h | 2520 count:", len(d2520), "budget:", sum(1.0/r[1] for r in d2520))
