#!/usr/bin/env python3
"""
#396 k=3 witness sweep (S043): find n with
    (n)(n-1)(n-2)(n-3) | C(2n, n)        [k=3: four consecutive factors]
Prior art: k=0 n=2; k=1 n=2; k=2 n=2480 (kernelized, K35).

v_p(C(2n,n)) = 2 s_p(n) - s_p(2n)  (Legendre/Kummer) — computed per prime
p | prod_{i=0..3}(n-i). Trial division + Pollard rho for cofactors.
n from 4 upward; report the FIRST hit (minimal witness) and any hits.
"""
import sys, time

def sp(n, p):
    s = 0
    while n:
        s += n % p
        n //= p
    return s

def vp_central(n, p):
    # v_p(C(2n,n)) = (2 s_p(n) - s_p(2n)) / (p-1)   [Legendre: v_p(m!) = (m - s_p(m))/(p-1)]
    return (2 * sp(n, p) - sp(2 * n, p)) // (p - 1)

# --- Pollard rho (deterministic-ish, for cofactors) ---
def is_probable_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def pollard(n):
    if n % 2 == 0: return 2
    x = 2; y = 2; c = 1; d = 1
    while d == 1:
        x = (x*x + c) % n
        y = (y*y + c) % n; y = (y*y + c) % n
        d = __import__('math').gcd(abs(x - y), n)
        if d == n:
            c += 1; x = y = 2; d = 1
    return d

def factor(n):
    """yield (p, e)"""
    if n == 1: return
    stack = [n]; small = {}
    # trial small primes first
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        while stack and stack[-1] % p == 0 and stack[-1] != p:
            m = stack.pop(); e = 0
            while m % p == 0: m //= p; e += 1
            small[p] = small.get(p, 0) + e
            if m > 1: stack.append(m)
    # note: this mishandles pure powers; do simple per-item factoring instead
    res = dict(small)
    todo = stack
    # redo cleanly:
    res = {}
    todo = [n]
    while todo:
        m = todo.pop()
        if m == 1: continue
        if is_probable_prime(m):
            # extract
            e = 0
            # m is prime; but n may contain m multiple times — handled since
            # we factor n fully by splitting
            res[m] = res.get(m, 0) + 1
            continue
        d = pollard(m)
        todo.append(d); todo.append(m // d)
    # merge multiplicity correctly: the recursion splits distinct parts, but
    # repeated prime factors appear when d == m/p... pollard returns a
    # nontrivial divisor each time, so full factorization emerges.
    # However if n = p^e, pollard splits p^a -> p^b * p^c — fine.
    for p, e in res.items():
        pass
    return res

def factorize(n):
    """full factorization: dict p -> e"""
    f = {}
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97):
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        if n == 1: return f
    todo = [n]
    while todo:
        m = todo.pop()
        if m == 1: continue
        if is_probable_prime(m):
            f[m] = f.get(m, 0) + 1; continue
        d = pollard(m)
        todo.append(d); todo.append(m // d)
    return f

def check(n, k):
    """prod_{i=0..k}(n-i) | C(2n,n)?"""
    P = 1
    for i in range(k + 1):
        P *= (n - i)
    fac = factorize(P)
    for p, e in fac.items():
        if vp_central(n, p) < e:
            return False, (p, e, vp_central(n, p))
    return True, None

if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    nstart = int(sys.argv[2]) if len(sys.argv) > 2 else (4 if k == 3 else 100)
    nend = int(sys.argv[3]) if len(sys.argv) > 3 else 2_000_000
    t0 = time.time()
    hits = []
    # quick pre-filter: n(n-1)(n-2)(n-3) even-heavy; skip nothing, just run
    for n in range(max(nstart, k + 1), nend + 1):
        ok, fail = check(n, k)
        if ok:
            hits.append(n)
            print(f"#396 k={k} HIT: n={n}  ({time.time()-t0:.0f}s)", flush=True)
        if n % 200000 == 0:
            print(f"  n={n} ({time.time()-t0:.0f}s) hits={hits}", flush=True)
    print(f"#396 k={k} sweep {nstart}..{nend}: {len(hits)} hits: {hits[:20]}")
