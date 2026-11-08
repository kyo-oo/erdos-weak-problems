import time
t0 = time.time()
print("=" * 70)
print("BATTERY 954: Erdos #954 Rosen sequence — INDEPENDENT DUAL-METHOD")
print("=" * 70)

def cnt(seq, n):
    """METHOD 1: direct double loop over the prefix."""
    c = 0
    for i in range(len(seq)):
        for j in range(i, len(seq)):
            if j >= 1 and seq[i] + seq[j] <= n:
                c += 1
    return c

def cnt2(seq, n):
    """METHOD 2: sum over j of the count of i <= j with seq[i] <= n - seq[j]."""
    c = 0
    for j in range(1, len(seq)):
        # count i in [0, j] with seq[i] + seq[j] <= n  (seq sorted)
        t = n - seq[j]
        # binary search (seq is strictly increasing)
        lo, hi = 0, j + 1
        while lo < hi:
            mid = (lo + hi) // 2
            if seq[mid] <= t:
                lo = mid + 1
            else:
                hi = mid
        c += lo
    return c

TAB = [0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45, 53, 61, 75, 87, 97, 112,
       124, 139, 147, 175, 182, 205, 219, 242, 265, 277, 309, 313, 349,
       378, 386, 430, 445, 478, 480, 546, 548, 603, 615, 669, 677, 718,
       769, 776, 836]

# 1. the table itself: strictly increasing, starts 0, 1
ok = TAB[0] == 0 and TAB[1] == 1 and all(TAB[i] < TAB[i+1] for i in range(len(TAB)-1))
print(f"  table sanity (starts 0,1; strictly increasing, 46 terms): {ok}")
print(f"  matches published prefix (0,1,3,5,9,13,17,24,31,38,45): {TAB[:11] == [0,1,3,5,9,13,17,24,31,38,45]}")

# 2. the construction property, dual-method: for each e in [2,45]:
#    cnt over prefix [0..e-1] at TAB[e] is < TAB[e]
okc = True
for e in range(2, 46):
    pre = TAB[:e]
    v1 = cnt(pre, TAB[e])
    v2 = cnt2(pre, TAB[e])
    if not (v1 == v2 and v1 < TAB[e]):
        okc = False
        print(f"  CONSTRUCTION FAIL e={e}: cnt={v1}/{v2} vs a_e={TAB[e]}")
print(f"  construction property (46 terms, dual-method): {okc}")

# 3. the count law on the kernel window: x in [1, 378), prefix 30 terms
okl = True
for x in range(1, 378):
    pre = TAB[:30]
    v1 = cnt(pre, x)
    v2 = cnt2(pre, x)
    if not (v1 == v2 and v1 >= x):
        okl = False
        print(f"  COUNT LAW FAIL x={x}: {v1}/{v2}")
print(f"  count law N(x) >= x for 1 <= x < 378 (30-term prefix, dual-method): {okl}")

# 4. the wider census (46-term prefix, x < 836) + deviation profile
okw = True
maxdev = 0
argx = 0
for x in range(1, 836):
    v = cnt(TAB[:45], x)
    if v < x:
        okw = False
        print(f"  WIDE LAW FAIL x={x}: {v}")
    if v - x > maxdev:
        maxdev = v - x
        argx = x
print(f"  wide count law (45-term prefix, x < 836): {okw}; max deviation {maxdev} at x={argx}")

if ok and okc and okl and okw:
    print("\nBATTERY954 GREEN: all dual-method checks passed.")
else:
    print("\nBATTERY954 RED: FAILURES ABOVE")
    raise SystemExit(1)
print(f"TOTAL: {time.time()-t0:.1f}s")
