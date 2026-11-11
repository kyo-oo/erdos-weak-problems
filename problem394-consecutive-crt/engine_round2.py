import math, time
from math import gcd, factorial
from itertools import product as iproduct
t0 = time.time()

print("="*72)
print("ENGINE 394-R2: the CRT LAW adversarial audit + certified table extraction")
print("  t_k(n) = least m >= 1 with n | m(m+1)...(m+k-1)")
print("  LAW: for (n, k!) = 1:  t_k(n) = min over ordered coprime factorizations")
print("       n = d_0 d_1 ... d_{k-1} of the least m > 0 with m = -i (mod d_i) for all i")
print("="*72)

def prod_cons(m, k):
    p = 1
    for i in range(k): p *= (m+i)
    return p

def t_brute(n, k, cap=None):
    if cap is None: cap = n + 2   # t_k(n) <= n always (first factor m=n)
    for m in range(1, cap+1):
        if prod_cons(m, k) % n == 0:
            return m
    return None

def prime_powers(n):
    pp = []
    d = 2
    while d*d <= n:
        if n % d == 0:
            q = 1
            while n % d == 0:
                n //= d; q *= d
            pp.append(q)
        d += 1
    if n > 1: pp.append(n)
    return pp

def crt_merge(pairs):  # pairs: list of (r_i, d_i) pairwise coprime
    r, M = 0, 1
    for (r2, m2) in pairs:
        g = gcd(M, m2)
        assert g == 1, "moduli not coprime"
        inv = pow(M, -1, m2)
        r = (r + M * ((r2 - r) * inv % m2)) % (M * m2)
        M *= m2
    return r % M, M

def crt_min(n, k):
    """min over ordered assignments of prime powers to k positions of the least
    positive solution of m = -i mod d_i."""
    pp = prime_powers(n)
    best = None
    for assign in iproduct(range(k), repeat=len(pp)):
        d = [1]*k
        for q, pos in zip(pp, assign):
            d[pos] *= q
        r, M = crt_merge([((-i) % d[i], d[i]) for i in range(k)])
        assert M == n
        cand = r if r >= 1 else n   # least positive: residue in [0, n); 0 -> n
        if best is None or cand < best:
            best = cand
    return best

print("\n--- PART A: dual-method agreement k=2..6, all (n,k!)=1, n <= 600 ---")
total_ok = 0; mismatches = []
for k in range(2, 7):
    KF = factorial(k)
    for n in range(2, 601):
        if gcd(n, KF) != 1: continue
        tb = t_brute(n, k)
        tc = crt_min(n, k)
        if tb != tc:
            mismatches.append((k, n, tb, tc))
        else:
            total_ok += 1
print(f"  agreements: {total_ok}   mismatches: {len(mismatches)}")
if mismatches:
    print("  MISMATCHES:", mismatches[:10])
    print("  LAW BROKEN")
else:
    print("  CRT LAW CONFIRMED (dual method: brute-force least-m == min-CRT-class)")

print("\n--- PART B: structure checks ---")
# (1) t_k(n) <= n always (first factor)
ok1 = all(t_brute(n, k) <= n for k in range(1, 8) for n in range(1, 400))
# (2) every valid m induces an assignment: prime powers land uniquely
ok2 = True
for k in range(2, 6):
    for n in range(2, 200):
        if gcd(n, factorial(k)) != 1: continue
        for m in range(1, n+1):
            if prod_cons(m, k) % n != 0: continue
            for q in prime_powers(n):
                # q must divide exactly one of m..m+k-1
                hits = [i for i in range(k) if (m+i) % q == 0]
                if len(hits) != 1:
                    ok2 = False
                    print(f"  UNIQUE-POSITION FAIL: n={n} k={k} m={m} q={q} hits={hits}")
print(f"  (1) t_k(n) <= n for k=1..7, n<400: {'OK' if ok1 else 'FAIL'}")
print(f"  (2) unique prime-power landing for all valid (n,k,m): {'OK' if ok2 else 'FAIL'}")

print("\n--- PART C: certified exact tables (for the Lean kernel) ---")
# t_2: odd n = 3..101
t2 = [(n, t_brute(n, 2)) for n in range(3, 102, 2)]
print("  t_2(odd n), n=3..101:")
print("   ", [v for _, v in t2])
# t_3: (n,6)=1, n=5..97
t3 = [(n, t_brute(n, 3)) for n in range(5, 98) if gcd(n, 6) == 1]
print(f"  t_3((n,6)=1), n=5..97 ({len(t3)} values):")
print("   ", [v for _, v in t3])
# t_4: (n,24)=1, n=5..99
t4 = [(n, t_brute(n, 4)) for n in range(5, 100) if gcd(n, 24) == 1]
print(f"  t_4((n,24)=1), n=5..99 ({len(t4)} values):")
print("   ", [v for _, v in t4])
# t_5: (n,120)=1, n=7..99
t5 = [(n, t_brute(n, 5)) for n in range(7, 100) if gcd(n, 120) == 1]
print(f"  t_5((n,120)=1), n=7..99 ({len(t5)} values):")
print("   ", [v for _, v in t5])

print("\n--- PART D: showcase instances (CRT law in action) ---")
for (n, k) in [(15, 2), (35, 2), (77, 2), (35, 3), (55, 3), (77, 4), (91, 4), (143, 5)]:
    print(f"  t_{k}({n}) = {t_brute(n, k)}   (CRT-min: {crt_min(n, k)})   agree: {t_brute(n, k) == crt_min(n, k)}")

print("\n" + "="*72)
print(f"394 CRT LAW: " + ("CONFIRMED — dual-method green, tables extracted" if not mismatches and ok1 and ok2 else "PROBLEM — SEE ABOVE"))
print(f"total time: {time.time()-t0:.1f}s")
