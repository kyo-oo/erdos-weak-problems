#!/usr/bin/env python3
# THE r30 WITNESS GENERATOR — fire rows for [1501, 3000], two-method verified.
# Method 1: modular exponentiation (pow(4, m, 3^(q+1)) // 3^q)
# Method 2: exact big-int ternary expansion (independent path)
import sys

POW3 = [1]
for _ in range(200):
    POW3.append(POW3[-1]*3)

def digit_of_pow4_mod(m, q):
    M = POW3[q+1]
    return pow(4, m, M) // POW3[q]

def ternary_digits(n):
    ds = []
    while n:
        ds.append(n % 3)
        n //= 3
    return ds

def digit_of_pow4_exact(m, q):
    ds = ternary_digits(4**m)
    return ds[q] if q < len(ds) else 0

def treeBad_mod(K, p):
    P = POW3[p]
    m = K % P
    d1 = digit_of_pow4_mod(m, p+1)
    d2 = digit_of_pow4_mod(m+1, p+1)
    trit = (K // P) % 3
    return (d1 == d2) and (trit == 2 - d1)

def treeBad_exact(K, p):
    P = POW3[p]
    m = K % P
    d1 = digit_of_pow4_exact(m, p+1)
    d2 = digit_of_pow4_exact(m+1, p+1)
    trit = (K // P) % 3
    return (d1 == d2) and (trit == 2 - d1)

def fire_row(K, maxp=140):
    for p in range(2, maxp):
        if treeBad_mod(K, p):
            return p
    return None

# cross-validate both methods on a sample
print("=== two-method cross-validation on [1501, 1600] ===")
mis = 0
for K in range(1501, 1600):
    for p in range(2, 60):
        if treeBad_mod(K, p) != treeBad_exact(K, p):
            mis += 1
            print("  MISMATCH", K, p)
print("mismatches:", mis)

print("=== fire rows [1501, 3000] ===")
rows = {}
mx = 0; amx = 0
for K in range(1501, 3001):
    r = fire_row(K)
    assert r is not None, f"NO FIRE at {K}"
    # verify with exact method at the fire row
    assert treeBad_exact(K, r), f"exact method disagrees at {K}, {r}"
    rows[K] = r
    if r > mx: mx = r; amx = K
print("all fire; max row:", mx, "at", amx)
import collections
hist = collections.Counter(rows.values())
print("histogram:", dict(sorted(hist.items())))

# also verify: the survivors {0..4,7} claim + [8,1500] all fire (engine-side sanity)
for K in [0,1,2,3,4,7]:
    assert fire_row(K) is None, f"survivor {K} fired?!"
for K in range(8, 1501):
    assert fire_row(K) is not None, f"NO FIRE at {K} in base!"
print("survivors {0..4,7} confirmed; [8,1500] all fire confirmed")

# emit the Lean witness list: pairs (K, r)
out = []
line = []
for K in range(1501, 3001):
    line.append(f"({K}, {rows[K]})")
    if len(line) == 8:
        out.append(", ".join(line))
        line = []
if line:
    out.append(", ".join(line))
with open("witness_rows_3000.txt", "w") as f:
    f.write("  " + ",\n  ".join(out))
print("witness list written:", sum(1 for _ in rows), "pairs")
