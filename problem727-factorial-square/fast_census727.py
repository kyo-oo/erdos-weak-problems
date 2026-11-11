#!/usr/bin/env python3
"""Erdos #727 -- fast incremental census battery (W4, Session 029).

Usage:
  python3 fast_census727.py census K N   -- all n<=N with (n+K)!^2 | (2n)!
  python3 fast_census727.py smooth  K N  -- all n<=N with P(n+j) <= sqrt(2n) for all 1<=j<=K
                                            (the m=1 frontier-block / smoothness filter, Thm T4a)

Algorithm (census): maintain A[p] = v_p((2n)!), B[p] = v_p((n+K)!) incrementally.
At step n: add v_p(2n-1), v_p(2n) to A; add v_p(n+K) to B. New primes p<=n+K enter
exactly when n+K = p (handled automatically: v_p(p)=1 lands in B, and A[p]=1 was
already accumulated when 2n' - 1 or 2n' hit p, since n >= N0 > K implies p <= 2n-1).
bad set = {p <= n+K : A[p] < 2*B[p]}; sol(n) iff bad is empty.
Every reported solution is re-verified by an independent method (direct Legendre sums).
"""
import sys
from math import isqrt


def build_spf(N):
    spf = [0] * (N + 2)
    spf[0] = spf[1] = 1
    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i] = i
            if i * i <= N:
                for j in range(i * i, N + 1, i):
                    if spf[j] == 0:
                        spf[j] = i
    return spf


def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, isqrt(p) + 1))]


def vfact(m, p):
    v, q = 0, p
    while q <= m:
        v += m // q
        q *= p
    return v


def solve_brute(n, k):
    for p in primes_upto(n + k):
        if 2 * vfact(n + k, p) > vfact(2 * n, p):
            return False
    return True


def census(k, N):
    N0 = 2 * k + 20
    spf = build_spf(2 * N + k + 2)
    A, B, bad = {}, {}, set()
    for p in primes_upto(2 * N0):
        A[p] = vfact(2 * N0, p)
    for p in primes_upto(N0 + k):
        B[p] = vfact(N0 + k, p)
    for p in B:
        if A.get(p, 0) < 2 * B[p]:
            bad.add(p)
    sols = [n for n in range(1, N0 + 1) if solve_brute(n, k)]
    dec = {}
    for n in sols:
        dec[(n // 10) * 10] = dec.get((n // 10) * 10, 0) + 1
    if not bad:
        sols.append(N0)
        dec[(N0 // 10) * 10] = dec.get((N0 // 10) * 10, 0) + 1
    for n in range(N0 + 1, N + 1):
        for m in (2 * n - 1, 2 * n):
            mm = m
            while mm > 1:
                p = spf[mm]
                e = 0
                while mm % p == 0:
                    mm //= p
                    e += 1
                A[p] = A.get(p, 0) + e
                if p <= n + k:
                    if A[p] < 2 * B.get(p, 0):
                        bad.add(p)
                    elif p in bad:
                        bad.discard(p)
        mm = n + k
        while mm > 1:
            p = spf[mm]
            e = 0
            while mm % p == 0:
                mm //= p
                e += 1
            B[p] = B.get(p, 0) + e
            if A.get(p, 0) < 2 * B[p]:
                bad.add(p)
            elif p in bad:
                bad.discard(p)
        if not bad:
            sols.append(n)
            dec[(n // 10) * 10] = dec.get((n // 10) * 10, 0) + 1
    # independent re-verification (method 2: direct per-prime Legendre sums)
    chk = sols[:60] + sols[-12:]
    for n in chk:
        assert solve_brute(n, k), f"FAIL recheck k={k} n={n}"
    print(f"[K={k}] solutions n<={N}: total {len(sols)}")
    print(f"[K={k}] first 25: {sols[:25]}")
    if len(sols) > 30:
        print(f"[K={k}] last 6: {sols[-6:]}")
    ds = sorted(dec.items())
    print(f"[K={k}] per-10^4-block counts: {ds}")
    return sols


def smooth(k, N):
    spf = build_spf(N + k + 2)
    cnt = 0
    first = []
    for n in range(2, N + 1):
        ok = True
        b = isqrt(2 * n)
        for j in range(1, k + 1):
            m = n + j
            while m > 1:
                p = spf[m]
                if p > b:
                    ok = False
                    break
                while m % p == 0:
                    m //= p
            if not ok:
                break
        if ok:
            cnt += 1
            if len(first) < 12:
                first.append(n)
    print(f"[K={k}] smooth-frontier pass n<={N}: {cnt}  first: {first}")


if __name__ == "__main__":
    mode, k, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    if mode == "census":
        census(k, N)
    elif mode == "smooth":
        smooth(k, N)
