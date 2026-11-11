#!/usr/bin/env python3
"""W2 INDEPENDENT VERIFICATION BATTERY for Erdos #711 complete proof.
Conventions: window (m, m+F) = integers m+1..m+F-1.  f(n,m) = minimal F.
THEOREM U: f(n,m) <= 2n-1  <=>  Hall on W={m+1..m+2n-2}, keys 1..n.
Output saved to w2_verify_out.txt"""
import sys, time, random
from math import gcd
from itertools import combinations

random.seed(711711)
OUT = open("/home/z/my-project/repos/erdos-weak-problems/problem711-divisor-matching/w2_verify_out.txt", "w", buffering=1)
def log(s=""):
    print(s); OUT.write(s + "\n")

def lcm_upto(n):
    L = 1
    for k in range(1, n + 1): L = L * k // gcd(L, k)
    return L

# ---- bitmask machinery: window of T integers starting m+1 ----
def slot_masks(n, m, T, keys=None):
    """masks[k] = bitmask over positions 0..T-1 (value m+1+p) of multiples of k."""
    masks = {}
    for k in (keys if keys is not None else range(1, n + 1)):
        start = (m + 1 + k - 1) // k * k   # smallest multiple >= m+1
        msk = 0
        x = start
        while x <= m + T:
            msk |= 1 << (x - m - 1)
            x += k
        masks[k] = msk
    return masks

def match_size(n, m, T):
    """Kuhn matching keys 1..n vs slots m+1..m+T. Returns (size, assign)."""
    masks = slot_masks(n, m, T)
    adj = []
    for k in range(1, n + 1):
        lst = []
        msk = masks[k]; p = 0
        while msk:
            if msk & 1: lst.append(p)
            msk >>= 1; p += 1
        adj.append(lst)
    match_slot = [-1] * T
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
    return cnt, [None if match_slot[p] == -1 else match_slot[p] + 1 for p in range(T)]

def hall_ok(n, m):  # THEOREM U check at window 2n-2
    sz, _ = match_size(n, m, 2 * n - 2)
    return sz == n

# ============ PART 1: independent full-period U-verification n<=12 ============
log("=" * 78)
log("PART 1: THEOREM U independent full-period verification (matching-based)")
t0 = time.time(); allok = True
for n in range(2, 13):
    L = lcm_upto(n); bad = []
    for m in range(1, L + 1):
        if not hall_ok(n, m):
            bad.append(m)
            if len(bad) > 3: break
    ok = not bad
    allok &= ok
    log(f"  n={n:2d} period={L:6d}: Hall {'OK (0 violations)' if ok else 'FAILS at m=' + str(bad[:4])}")
log(f"PART 1 VERDICT: {'THEOREM U verified n=2..12 full periods, independent code' if allok else 'U BROKEN'} ({time.time()-t0:.1f}s)")

# ============ PART 2: extremal census |S| + |C| <= 2n-2, n=5..10 full periods ============
log("=" * 78)
log("PART 2: deficiency census over ALL subsets S (2^n), full periods n=5..10")
log("  deficiency d(S) = |S| - |N(S)| on window W (2n-2 ints). Hall <=> max d <= 0.")
for n in range(5, 11):
    L = lcm_upto(n); T = 2 * n - 2
    maxd = -99; worst = None; eqcases = {}
    for m in range(1, L + 1):
        masks = slot_masks(n, m, T)  # keys 1..n
        keys = list(range(1, n + 1))
        full = 0
        for k in keys: full |= masks[k]
        for sb in range(1, 1 << n):
            N = 0; s = 0
            bb = sb
            for i in range(n):
                if bb & 1:
                    N |= masks[i + 1]; s += 1
                bb >>= 1
            d = s - bin(N).count("1")
            if d > maxd:
                maxd = d; worst = (m, [i + 1 for i in range(n) if sb >> i & 1])
            if d == 0:
                S = tuple(i + 1 for i in range(n) if sb >> i & 1)
                eqcases[S] = eqcases.get(S, 0) + 1
    top = sorted(eqcases.items(), key=lambda kv: -kv[1])[:8]
    log(f"  n={n:2d} L={L:5d}: max deficiency = {maxd} (worst S at m={worst[0]})")
    log(f"        top equality S (d=0) counts: {top}")

# ============ PART 3: adversarial large-n U-check ============
log("=" * 78)
log("PART 3: THEOREM U adversarial+random m, n = 17..40 (plus 60, 100)")
def adversarial_tests(n):
    tests = set()
    for m in range(1, 2 * n * n + 2 * n + 1): tests.add(m)
    for k in range(max(2, n - 3), 4 * n + 2):
        for j in range(-2 * n, 2 * n + 1):
            if 1 <= k * k + j: tests.add(k * k + j)
    Ls = [lcm_upto(12), 720720, 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29,
          2 ** 21, 3 ** 11, 2 ** 6 * 3 ** 4 * 5 ** 3 * 7 ** 2, 10 ** 9, 10 ** 12, 10 ** 15]
    for M in Ls:
        for t in range(0, 30):
            for j in range(-2 * n, 2 * n + 1):
                if 1 <= M * t + j: tests.add(M * t + j)
    for _ in range(1500): tests.add(random.randint(1, 10 ** 12))
    for _ in range(800): tests.add(random.randint(1, 10 ** 18))
    return sorted(tests)
allok3 = True
for n in list(range(17, 41)) + [60, 100]:
    tests = adversarial_tests(n)
    bad = []
    for m in tests:
        if not hall_ok(n, m):
            bad.append(m)
            if len(bad) > 3: break
    ok = not bad
    allok3 &= ok
    log(f"  n={n:3d}: {len(tests):,} adversarial m: {'Hall OK' if ok else 'FAILS at ' + str(bad[:4])}")
log(f"PART 3 VERDICT: {'U CONFIRMED n=17..40,60,100 adversarial' if allok3 else 'U BROKEN'}")

# ============ PART 4: THEOREM N — exact f(n,n) + tight structure ============
log("=" * 78)
log("PART 4: THEOREM N: exact f(n,n) n=2..26; Hall census on window ceil(3n/2)")
def f_exact(n, m, cap):
    for F in range(n + 1, cap + 1):
        sz, _ = match_size(n, m, F - 1)
        if sz == n: return F
    return None
tbl = []
for n in range(2, 27):
    v = f_exact(n, n, 2 * n)
    tbl.append((n, v))
    log(f"  f({n:2d},{n:2d}) = {v}   [ceil(3n/2)+1 = {(3*n+1)//2+1 if (3*n)%2 else 3*n//2+1}, 2n-1={2*n-1}]")
log("  table: " + " ".join(f"{n}:{v}" for n, v in tbl))
# tight-set census for N-Hall at window size ceil(3n/2) (i.e., F = ceil(3n/2)+1)
log("  N-Hall equality census (window size ceil(3n/2), m=n):")
for n in range(6, 25):
    Tn = (3 * n + 1) // 2  # ceil(3n/2)
    masks = slot_masks(n, n, Tn)
    maxd = -99; worstS = None; eq = {}
    for sb in range(1, 1 << n):
        N = 0; s = 0
        bb = sb
        for i in range(n):
            if bb & 1: N |= masks[i + 1]; s += 1
            bb >>= 1
        d = s - bin(N).count("1")
        if d > maxd: maxd = d; worstS = [i + 1 for i in range(n) if sb >> i & 1]
        if d == 0:
            S = tuple(i + 1 for i in range(n) if sb >> i & 1)
            eq[S] = eq.get(S, 0) + 1
    top = sorted(eq.items(), key=lambda kv: -kv[1])[:5]
    log(f"    n={n:2d} T={Tn}: maxd={maxd} worstS={worstS}; top d=0 S: {top}")

# ============ PART 5: extremal-instance diagnostics (case A/B classification) ============
log("=" * 78)
log("PART 5: diagnostics of the tight instances (n=5..10, full period, antichain or not)")
for n in range(5, 11):
    L = lcm_upto(n); T = 2 * n - 2
    seen = {}
    for m in range(1, L + 1):
        masks = slot_masks(n, m, T)
        for sb in range(1, 1 << n):
            N = 0; s = 0
            bb = sb
            for i in range(n):
                if bb & 1: N |= masks[i + 1]; s += 1
                bb >>= 1
            if s - bin(N).count("1") == 0:
                S = tuple(i + 1 for i in range(n) if sb >> i & 1)
                # classify
                anti = all(not (a % b == 0) for i, a in enumerate(S) for j, b in enumerate(S) if i != j)
                lS = 1
                for k in S: lS = lS * k // gcd(lS, k)
                k1 = S[0]
                key = (S, anti, lS <= T, k1 * s <= T)
                seen[key] = seen.get(key, 0) + 1
    top = sorted(seen.items(), key=lambda kv: -kv[1])[:10]
    log(f"  n={n}: (S, antichain?, lcm<=T?, k1*s<=T?) -> count:")
    for (S, anti, caseA, lem5), c in top:
        log(f"    S={list(S)}  anti={anti}  caseA(lcm<=T)={caseA}  lem5={lem5}  x{c}")
log("W2 VERIFY COMPLETE")
OUT.close()
