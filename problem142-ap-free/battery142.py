#!/usr/bin/env python3
"""Battery 142: independent re-validation of every K66 kernel claim (python mirror)."""
import json, itertools

def aps(N, k):
    out = []
    for a in range(1, N+1):
        for d in range(1, N+1):
            if a + (k-1)*d > N: break
            out.append(tuple(a + i*d for i in range(k)))
    return out

def apfree(S, N, k):
    Ss = set(S)
    return all(not all(x in Ss for x in ap) for ap in aps(N, k))

def subsets(N, m):
    return [ [i+1 for i in range(N) if mask >> i & 1] for mask in range(2**N)
             if bin(mask).count('1') == m ]

def ternary_ok(n):
    while n:
        if n % 3 > 1: return False
        n //= 3
    return True

tables = json.load(open('problem142-ap-free/experiments/tables_rk.json'))
ok = True
# 1. exact values: r_3(9)=5, r_3(11)=6, r_3(13)=7
for N, v in [(9,5),(11,6),(13,7)]:
    t = tables['3'][str(N)]
    assert t['value'] == v, f"r_3({N}) != {v}"
    assert apfree(t['witness'] and [x+1 for x in t['witness']], N, 3) or apfree(t['witness'], N, 3), f"witness invalid {N}"
# 2. the upper direction: every (v+1)-subset contains a 3-AP
for N, v in [(9,5),(11,6),(13,7)]:
    for S in subsets(N, v+1):
        if apfree(S, N, 3):
            print(f"FAIL: AP-free {v+1}-subset of [{N}]: {S}"); ok = False
# 3. Stanley: 16 elements <= 81, 3-AP-free
stan = [n+1 for n in range(81) if ternary_ok(n)]
assert len(stan) == 16, f"stanley count {len(stan)}"
assert apfree(stan, 81, 3), "stanley not AP-free"
# 4. kernel witnesses
W = {
  (20,3): [2,4,7,8,13,15,16,20,21],
  (27,3): [1,2,5,7,11,16,18,19,23,24,26],
  (38,3): [1,2,4,8,9,13,21,23,26,27,30,32,35,36],
  (42,4): [1,2,3,5,6,8,9,10,16,18,19,21,22,24,30,31,33,34,35,38,39,40],
}
for (N,k), S in W.items():
    assert apfree(S, N, k), f"kernel witness invalid k={k} N={N}"
    t = tables[str(k)][str(N)]
    assert t['value'] == len(S), f"table mismatch k={k} N={N}: {t['value']} vs {len(S)}"
print("BATTERY142_ALL_GREEN" if ok else "BATTERY142_FAIL")
