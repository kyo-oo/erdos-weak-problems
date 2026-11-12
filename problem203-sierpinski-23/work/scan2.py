import json
full = json.load(open('../pal_dlog_full.json'))
fam = json.load(open('../fam5040.json'))
famset = set(int(k) for k in fam)
for TOR in (10080, 5040*3, 5040*2*2*3*3*5*5*7*7, 27720, 55440):
    pass
def report(TOR, name):
    sel = [r for r in full if TOR % r[1] == 0]
    b = sum(1.0/r[1] for r in sel)
    print(f"torus {name} ({TOR}): primes with h|torus: {len(sel)}, budget {b:.4f}")
    new = [r for r in sel if 5040 % r[1] != 0]
    print("   new vs fam5040 (h not dividing 5040):")
    for r in sorted(new, key=lambda r: r[1]):
        print(f"     q={r[0]:6d} h={r[1]:5d} U={r[2]:5d} V={r[3]:5d} o2={r[4]} o3={r[5]}")
    return sel
report(10080, "10080")
report(27720, "27720=2^3*3^2*5*7*11")
report(55440, "55440")
report(83160, "83160=2^3*3^3*5*7*11")
report(110880, "110880")
report(166320, "166320=2^4*3^3*5*7*11")
report(332640, "332640=2^5*3^3*5*7*11")
# also: what's in palette at all with 32 | h?
h32 = [r for r in full if r[1] % 32 == 0]
print("\nall palette h divisible by 32:", sorted((r[1], r[0]) for r in h32)[:40])
h11 = [r for r in full if r[1] % 11 == 0]
print("all palette h divisible by 11:", sorted((r[1], r[0]) for r in h11)[:40])
