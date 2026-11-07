import math, time, sys
from math import gcd
from functools import lru_cache
sys.setrecursionlimit(100000)
t0 = time.time()

print("="*72)
print("ENGINE 711-R2: FULL-PERIOD ADVERSARIAL AUDIT of the 2n-1 LAW")
print("  f(n,m) minimal F: (m, m+F) open interval contains distinct a_1..a_n, k | a_k")
print("  LAW: max_m f(n,m) = 2n-1, attained at m = (n-1)^2")
print("="*72)

def lcm_upto(n):
    L = 1
    for k in range(1, n+1):
        L = L*k//gcd(L,k)
    return L

def kuhn(n, m, win):  # win = number of integers in window (m+1 .. m+win)
    # keys 2..n (k=1 divides everything; handle separately)
    # generate adjacency on the fly; matchR[v] = key using v
    lo, hi = m+1, m+win
    matchR = {}
    def try_k(k, seen):
        # candidates: multiples of k in [lo, hi]
        start = ((lo + k - 1)//k)*k
        v = start
        while v <= hi:
            if v not in seen:
                seen[v] = True
                if v not in matchR or try_k(matchR[v], seen):
                    matchR[v] = k
                    return True
            v += k
        return False
    for k in range(n, 1, -1):
        if not try_k(k, {}):
            return None
    # k=1: any leftover integer
    for v in range(lo, hi+1):
        if v not in matchR:
            return {**{a: k for k in range(2, n+1) for a in [None]} , **{}, **matchR, 1: v}
    # build explicit assignment dict key->value
    assign = {}
    for v, k in matchR.items():
        assign[k] = v
    assign[1] = v
    return assign

def matchable(n, m, win):
    """Window (m, m+win+1) i.e. integers m+1..m+win. Return assignment or None.
    keys 1..n each need distinct multiple in window; 1 | everything."""
    lo, hi = m+1, m+win
    if win < n:  # not enough integers
        return None
    # greedy certificate first: k = n..2 take the largest free multiple; 1 takes leftover
    used = set()
    assign = {}
    ok = True
    for k in range(n, 1, -1):
        # largest multiple of k <= hi
        v = (hi//k)*k
        while v >= lo and v in used:
            v -= k
        if v < lo:
            ok = False
            break
        used.add(v); assign[k] = v
    if ok:
        # k=1: any free integer
        free = [v for v in range(lo, hi+1) if v not in used]
        if free:
            assign[1] = free[0]
            return assign
        ok = False
    # greedy failed -> exact Kuhn on keys 2..n then 1
    return kuhn(n, m, win)

def f711(n, m, cap=None):
    if cap is None: cap = n*n*m + n + 10
    F = n+1
    while F <= cap:
        if matchable(n, m, F-1) is not None:
            return F
        F += 1
    return None

print("\n--- PART A: FULL-PERIOD CENSUS n=2..12 (period L = lcm(1..n)) ---")
LAW_OK = True
for n in range(2, 13):
    L = lcm_upto(n)
    t = time.time()
    bad = []
    for m in range(1, L+1):
        if matchable(n, m, 2*n-2) is None:
            bad.append(m)
            if len(bad) >= 5: break
    stat = "ALL MATCHABLE (max_m f <= 2n-1 CONFIRMED)" if not bad else f"LAW BROKEN at m={bad}"
    if bad: LAW_OK = False
    print(f"  n={n:2d}  L={L:6d}  m swept 1..{L}  [{time.time()-t:6.1f}s]  {stat}")

print("\n--- PART B: the (n-1)^2 obstruction + exactness n=2..15 ---")
for n in range(2, 16):
    m = (n-1)*(n-1)
    a_low = matchable(n, m, 2*n-3)   # should be None (obstruction: f >= 2n-1)
    a_high = matchable(n, m, 2*n-2)  # should be an assignment (f <= 2n-1)
    # the forced-collision audit: multiples of n and n-1 in ((n-1)^2, n^2-2]
    lo, hi = (n-1)*(n-1)+1, n*n-2
    mult_n  = [v for v in range(lo, hi+1) if v % n == 0]
    mult_n1 = [v for v in range(lo, hi+1) if v % (n-1) == 0 and n >= 2]
    forced = (mult_n == [n*n-n]) and (mult_n1 == [n*n-n])
    ok = (a_low is None) and (a_high is not None) and forced
    if not ok: LAW_OK = False
    wit = " ".join(f"a_{k}={a_high[k]}" for k in sorted(a_high)) if a_high else "NONE"
    print(f"  n={n:2d} m={m:4d}: f({n},{m}) = 2n-1 = {2*n-1}: {'YES' if ok else 'NO!!!'} "
          f"(forced-collision {'OK' if forced else 'FAIL'}) witness: {wit}")

print("\n--- PART C: exact f(n,n) + periodicity spot-checks n=2..12 ---")
for n in range(2, 13):
    L = lcm_upto(n)
    fnn = f711(n, n)
    # periodicity: f(n, m) = f(n, m+L) for sample m
    per_ok = True
    for m in [1, 7, 40, 97, 233, 500, 997, 2003][:min(8, max(1,L))]:
        if m > L: continue
        if f711(n, m) != f711(n, m + L):
            per_ok = False
    print(f"  n={n:2d}: f(n,n) = {fnn}   periodicity(mod {L}): {'OK' if per_ok else 'FAIL'}")

print("\n--- PART D: complete small-n laws (all m in full period) ---")
for n in [2, 3]:
    L = lcm_upto(n)
    vals = {}
    for m in range(1, L+1):
        v = f711(n, m)
        vals[v] = vals.get(v, 0) + 1
    mx = max(vals)
    print(f"  n={n}: f(n,m) value histogram over full period {L}: {vals}; max = {mx} "
          f"{'= 2n-1 OK' if mx == 2*n-1 else 'NOT 2n-1!!!'}")

print("\n--- PART E: max_m f(n,m) exact + argmax, n=2..10 (full periods) ---")
for n in range(2, 11):
    L = lcm_upto(n)
    mx = 0; am = None
    for m in range(1, L+1):
        # f(n,m) > 2n-1 impossible per Part A; find exact f only up to 2n-1
        F = n+1
        while F <= 2*n-1:
            if matchable(n, m, F-1) is not None: break
            F += 1
        if F > mx: mx = F; am = m
    ok = (mx == 2*n-1) and (am == (n-1)*(n-1))
    if not ok: LAW_OK = False
    print(f"  n={n:2d}: max_m f = {mx} at m={am}  {'LAW OK (2n-1 at (n-1)^2)' if ok else 'DEVIATION'}")

print("\n" + ("="*72))
print("711 FULL-PERIOD LAW: " + ("CONFIRMED n=2..12 (parts A,B,E) + obstruction n<=15 (part B)" if LAW_OK else "BROKEN — SEE ABOVE"))
print(f"total time: {time.time()-t0:.1f}s")
