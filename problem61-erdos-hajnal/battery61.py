#!/usr/bin/env python3
"""Battery 61: independent re-validation of the K67 kernel claims (python mirror)."""
import itertools

def pair_idx(n, i, j):
    if i > j: i, j = j, i
    # row-major upper triangle: positions before row i: sum_{r<i}(n-1-r) + (j-i-1)
    return sum(n-1-r for r in range(i)) + (j - i - 1)

def edge(mask, n, i, j):
    return (mask >> pair_idx(n, i, j)) & 1 == 1

def p4_patterns():
    pats = set()
    for perm in itertools.permutations(range(4)):
        a,b,c,d = perm
        edges = {(a,b),(b,c),(c,d)}
        bits = 0
        for k,(x,y) in enumerate(itertools.combinations(range(4),2)):
            if (x,y) in edges or (y,x) in edges: bits |= 1 << k
        pats.add(bits)
    return sorted(pats)

P4P = p4_patterns()
def subsets(n, m):
    return [ [i for i in range(n) if mask >> i & 1] for mask in range(2**n)
             if bin(mask).count('1') == m ]

def p4free(mask, n):
    for q in subsets(n, 4):
        a,b,c,d = q
        bits = (edge(mask,n,a,b)<<5)|(edge(mask,n,a,c)<<4)|(edge(mask,n,a,d)<<3)|(edge(mask,n,b,c)<<2)|(edge(mask,n,b,d)<<1)|edge(mask,n,c,d)
        if bits in P4P: return False
    return True

def p3free(mask, n):
    for q in subsets(n, 3):
        a,b,c = q
        e = edge(mask,n,a,b)+edge(mask,n,a,c)+edge(mask,n,b,c)
        if e == 2: return False
    return True

def trifree(mask, n):
    for q in subsets(n, 3):
        a,b,c = q
        if edge(mask,n,a,b) and edge(mask,n,a,c) and edge(mask,n,b,c): return False
    return True

def has_tri_or_ind3(mask, n):
    if not trifree(mask, n): return True
    for q in subsets(n, 3):
        a,b,c = q
        if not edge(mask,n,a,b) and not edge(mask,n,a,c) and not edge(mask,n,b,c): return True
    return False

ok = True
# R(3,3) = 6 upper: all 2^15 graphs
for m in range(2**15):
    if not has_tri_or_ind3(m, 6):
        print(f"FAIL R(3,3) at mask {m}"); ok = False; break
# C5 tightness
C5 = (1 << pair_idx(5,0,1)) | (1 << pair_idx(5,1,2)) | (1 << pair_idx(5,2,3)) | (1 << pair_idx(5,3,4)) | (1 << pair_idx(5,0,4))
assert trifree(C5, 5), "C5 has triangle"
assert all(any(edge(C5,5,a,b) or edge(C5,5,a,c) or edge(C5,5,b,c) for b,c in itertools.combinations([x for x in range(5) if x != a], 2)) for a in range(5))
for q in subsets(5, 3):
    a,b,c = q
    if not edge(C5,5,a,b) and not edge(C5,5,a,c) and not edge(C5,5,b,c):
        print("FAIL: C5 has independent 3"); ok = False; break
# K3 law n=5: every triangle-free has indep pair
for m in range(2**10):
    if trifree(m, 5):
        found = any(not edge(m,5,i,j) for i,j in itertools.combinations(range(5),2))
        if not found: print(f"FAIL K3 n=5 mask {m}"); ok = False; break
# P4 decomposition n=5 + omega-alpha shadow + P3 law
def connected(mask, n):
    seen = {0}; stack = [0]
    while stack:
        v = stack.pop()
        for w in range(n):
            if w != v and edge(mask, n, v, w) and w not in seen:
                seen.add(w); stack.append(w)
    return len(seen) == n

def has_clique3_or_ind3(mask, n):
    for q in subsets(n, 3):
        a,b,c = q
        if edge(mask,n,a,b) and edge(mask,n,a,c) and edge(mask,n,b,c): return True
        if not edge(mask,n,a,b) and not edge(mask,n,a,c) and not edge(mask,n,b,c): return True
    return False

for m in range(2**10):
    if p4free(m, 5):
        comp_mask = (2**10 - 1) - m
        if connected(m, 5) and connected(comp_mask, 5):
            print(f"FAIL P4 decomp mask {m}"); ok = False; break
        if not has_clique3_or_ind3(m, 5):
            print(f"FAIL P4 omega-alpha mask {m}"); ok = False; break
    if p3free(m, 5) and not has_clique3_or_ind3(m, 5):
        print(f"FAIL P3 law mask {m}"); ok = False; break
# tightness 2K2
twoK2 = (1 << pair_idx(4,0,1)) | (1 << pair_idx(4,2,3))
assert p3free(twoK2, 4) and p4free(twoK2, 4)
print("BATTERY61_ALL_GREEN" if ok else "BATTERY61_FAIL")
