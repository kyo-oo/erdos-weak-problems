#!/usr/bin/env python3
"""W2 phase 2: THEOREM U IS FALSE at large n. Extract the truth:
- deficient sets S at the failures, exact f(n,m) there
- minimal failing n (full small-m sweep n=17..45)
- max_m f(n,m) census (growth law)"""
import sys, time, random
from math import gcd
OUT = open("/home/z/my-project/repos/erdos-weak-problems/problem711-divisor-matching/w2_verify2_out.txt", "w", buffering=1)
random.seed(20260211)
def log(s=""):
    print(s); OUT.write(s + "\n")

def slot_masks(n, m, T):
    masks = {}
    for k in range(1, n + 1):
        start = (m + 1 + k - 1) // k * k
        msk = 0; x = start
        while x <= m + T:
            msk |= 1 << (x - m - 1); x += k
        masks[k] = msk
    return masks

def match_size(n, m, T):
    masks = slot_masks(n, m, T)
    adj = []
    for k in range(1, n + 1):
        lst = []; msk = masks[k]; p = 0
        while msk:
            if msk & 1: lst.append(p)
            msk >>= 1; p += 1
        adj.append(lst)
    match_slot = [-1] * T
    import sys as _s
    _s.setrecursionlimit(100000)
    def try_k(i, vis):
        for j in adj[i]:
            if not vis[j]:
                vis[j] = True
                if match_slot[j] == -1 or try_k(match_slot[j], vis):
                    match_slot[j] = i; return True
        return False
    cnt = 0
    for i in range(len(adj)):
        if try_k(i, [False] * T): cnt += 1
    return cnt

def max_deficiency(n, m, T):
    """max over S != empty of |S|-|N(S)|, via bitmask over 2^n (n<=26)."""
    masks = slot_masks(n, m, T)
    best = -10**9; bestS = None
    for sb in range(1, 1 << n):
        N = 0; s = 0; bb = sb
        for i in range(n):
            if bb & 1: N |= masks[i + 1]; s += 1
            bb >>= 1
        d = s - bin(N).count("1")
        if d > best:
            best = d; bestS = [i + 1 for i in range(n) if sb >> i & 1]
    return best, bestS

def f_exact(n, m, cap):
    for F in range(n + 1, cap + 1):
        if match_size(n, m, F - 1) == n: return F
    return None

log("=" * 78)
log("A. anatomy of the U-failures found in part 3")
for (n, m) in [(39, 821655575105), (60, 2256), (60, 2604), (100, 500), (100, 729), (100, 736)]:
    T = 2 * n - 2
    d, S = max_deficiency(n, m, T)
    fx = f_exact(n, m, 4 * n)
    log(f"  n={n} m={m}: max deficiency = {d} at S={S}; 2n-1={2*n-1}; exact f = {fx}")
    # is S saturated? (all k with M_k subset N(S))
    masks = slot_masks(n, m, T)
    N = 0
    for k in S: N |= masks[k]
    sat = [k for k in range(1, n + 1) if k not in S and (masks[k] & ~N) == 0]
    log(f"        (S saturated? extra keys with M_k within N(S): {sat})")

log("=" * 78)
log("B. minimal failing n: full small-m sweep m in [1, 5n^2], n = 17..45")
for n in range(17, 46):
    T = 2 * n - 2
    bad = []
    for m in range(1, 5 * n * n + 1):
        if match_size(n, m, T) < n:
            bad.append(m)
            if len(bad) >= 6: break
    if bad:
        d, S = max_deficiency(n, bad[0], T)
        fx = f_exact(n, bad[0], 4 * n)
        log(f"  n={n}: FIRST FAILURE at m={bad}  (deficiency {d}, S={S}, f={fx})  <-- U BROKEN")
        break
    else:
        log(f"  n={n}: no failure for m <= 5n^2 = {5*n*n}")

log("=" * 78)
log("C. max_m f(n,m) census (exact f, capped 3n): full sweep m<=4n^2 + adversarial + random")
def census_maxf(n):
    tests = set(range(1, 4 * n * n + 1))
    for k in range(max(2, n - 3), 3 * n + 2):
        for j in range(-2 * n, 2 * n + 1):
            if 1 <= k * k + j: tests.add(k * k + j)
    for M in [720720, 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29, 2 ** 21, 10 ** 9, 10 ** 12]:
        for t in range(0, 20):
            for j in range(-n, n + 1):
                if 1 <= M * t + j: tests.add(M * t + j)
    for _ in range(600): tests.add(random.randint(1, 10 ** 15))
    fmax = 0; arg = []
    for m in sorted(tests):
        F = f_exact(n, m, 3 * n)
        if F is None: F = 3 * n + 1
        if F > fmax: fmax = F; arg = [m]
        elif F == fmax and len(arg) < 8: arg.append(m)
    return fmax, arg
for n in [17, 20, 24, 30, 40, 60, 80, 100]:
    t0 = time.time()
    fmax, arg = census_maxf(n)
    log(f"  n={n:3d}: max f = {fmax}  [2n-1 = {2*n-1}, 3n/2 = {3*n//2}, n log n ~ {int(n*__import__('math').log(n))}]  argmax m ~ {arg}  ({time.time()-t0:.0f}s)")
log("W2 PHASE-2 COMPLETE")
OUT.close()
