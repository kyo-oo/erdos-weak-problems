#!/usr/bin/env python3
"""W64-F: verify the EXACT Lean theorem targets before authoring (dual-method).
Targets: (A) GrowthA criterion on w23 j (block order) all j<=12;
(B) level-4 decide box: every 2-position-removal survivor covers [0,61];
(C) general 2-removal: survivor covers [0, 2^{j+1}-1], all j<=9, all pairs;
(D) 3-kill: w23k j covers no odd, j<=9; (E) lsum closed form; (F) the delAt
decide statement mirror.
M1: python bitset. M2: structural criterion (Graham) + value-set parity."""
import itertools

def w23(j):  # block order: [1,1,1, 2,2,2, ..., 2^j x3]
    A = []
    for k in range(j + 1):
        A += [2 ** k] * 3
    return A

def w23k(j):  # the 3-kill survivor: blocks 1..j
    A = []
    for k in range(1, j + 1):
        A += [2 ** k] * 3
    return A

def covered(A, B):
    cov = 1
    for a in A:
        if a <= B:
            cov |= cov << a
    return cov & ((1 << (B + 1)) - 1)

def contiguous(cov, B):
    c = 0
    while c <= B and (cov >> c) & 1:
        c += 1
    return c

# (A) GrowthA criterion (snoc form): first element 1, each element <= 1 + prefix sum
print("A: GrowthA criterion on w23 j, j=0..12 (M2 structural)")
okA = True
for j in range(13):
    A = w23(j); s = 0; viol = None
    for i, a in enumerate(A):
        if i == 0:
            if a != 1: viol = i; break
        elif a > 1 + s:
            viol = i; break
        s += a
    okA = okA and viol is None
    assert s == 3 * (2 ** (j + 1) - 1), (j, s)
print("  all j<=12 PASS, lsum = 3(2^(j+1)-1) verified (E)")

# (B) level-4 box: 15 elements, C(15,2)=105 pairs, cover [0,61]
print("B: level-4 every-2-removal covers [0,61] (M1 bitset + M2 criterion)")
L4 = w23(4); assert len(L4) == 15 and sum(L4) == 93
okB = True
for i, jj in itertools.combinations(range(15), 2):
    Ax = L4[:i] + L4[i+1:jj] + L4[jj+1:]
    c = contiguous(covered(Ax, 93), sum(Ax))
    if c <= 61:
        okB = False; print("  FAIL pair", i, jj, c)
    # M2: criterion on sorted survivor
    s = 0; v = None
    for t, a in enumerate(sorted(Ax)):
        if t == 0:
            if a != 1: v = t; break
        elif a > 1 + s: v = t; break
        s += a
    assert v is None, (i, jj, v)
print("  105/105 pairs PASS bitset; criterion PASS")

# (C) general: every 2-removal survivor of w23 j covers [0, 2^{j+1}-1], j<=9
print("C: general 2-removal covers [0, 2^(j+1)-1], all pairs, j<=9")
okC = True
for j in range(10):
    A = w23(j); n = len(A); B = 2 ** (j + 1) - 1
    seen = set()
    for i, jj in itertools.combinations(range(n), 2):
        Ax = A[:i] + A[i+1:jj] + A[jj+1:]
        key = tuple(Ax)
        if key in seen: continue
        seen.add(key)
        c = contiguous(covered(Ax, B), B)
        if c <= B:
            okC = False; print("  FAIL", j, i, jj, c)
    print(f"  j={j}: {len(seen)} distinct survivors, all cover [0,{B}]")
okC2 = True  # M2: value-set: every power <= 2^j still present
for j in range(10):
    A = w23(j)
    for i, jj in itertools.combinations(range(len(A)), 2):
        Ax = A[:i] + A[i+1:jj] + A[jj+1:]
        for k in range(j + 1):
            if 2 ** k not in Ax:
                okC2 = False
print("  M2 value-set: every power survives, all pairs, j<=9:", okC2)

# (D) 3-kill: no odd covered, j<=9 (M1 bitset; M2 parity structural)
print("D: 3-kill survivor w23k j covers NO odd (j<=9)")
okD = True
for j in range(10):
    Ax = w23k(j); B = 3 * (2 ** (j + 1) - 1) if j >= 1 else 10
    cov = covered(Ax, min(B, 4000))
    odd = [x for x in range(1, min(B, 4000) + 1, 2) if (cov >> x) & 1]
    if odd: okD = False; print("  FAIL j", j, odd[:5])
    if any(a % 2 for a in Ax): okD = False
    # w23 j = [1,1,1] ++ w23k j structure check
    assert w23(j) == [1, 1, 1] + w23k(j)
print("  M1 no odd covered + M2 all-even + w23 j = blk0 ++ w23k j: PASS")

# (F) delAt mirror: exact Lean decide statement
print("F: delAt decide mirror (i<15, j<15, i<j, n<=61)")
def delAt(l, i):
    return l[:i] + l[i+1:]
fails = 0
for i in range(15):
    for jj in range(15):
        if i >= jj: continue
        Ax = delAt(delAt(L4, i), jj)
        for x in range(62):
            if not (covered(Ax, 61) >> x) & 1:
                fails += 1
print("  fails:", fails, "(expect 0)")

print("VERDICT:", "ALL GREEN" if (okA and okB and okC and okC2 and okD and fails == 0) else "BROKEN")
