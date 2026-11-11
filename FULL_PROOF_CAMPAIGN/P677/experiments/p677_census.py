#!/usr/bin/env python3
"""P677 census engine — certified-complete collision scan for equal-lcm windows.

Problem (Erdos #677): M(n,k) = lcm{n+1,...,n+k}. Collision = pair n<m, m>=n+k
with M(n,k)=M(m,k). Engine: exact modular fingerprints of M(n,k) over ALL window
starts up to the rigorous m-bound (N+k)*mu_k, mu_k = D_max(k)^(1/k) (PROOF.md Thm E),
then exact big-integer re-verification of every duplicate candidate.

Dual method: (i) modular fingerprint scan (this file), (ii) exact bignum lcm dict
(brute, small range) — both must agree on the overlap of their ranges.
"""
import numpy as np
from math import gcd, floor, log
import sys, time, json

Q1 = 2147483647  # 2^31-1 Mersenne prime
Q2 = 2147483629  # prime

def primes_upto(n):
    sieve = bytearray([1])*(n+1); sieve[0]=sieve[1]=0
    for i in range(2, int(n**0.5)+1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(n+1) if sieve[i]]

def prime_powers_leq(x):
    """all prime powers p^a <= x (a>=1) as list of ints"""
    out = []
    for p in primes_upto(max(x, 2)):
        q = p
        while q <= x:
            out.append(q); q *= p
    return out

def D_table(k):
    """Exact D(r,k) for r in [0, Lambda): D = prod (n+i)/lcm; periodic mod Lambda.
    Returns (Lambda, list D[r]). c_p(r) = sum_a (cnt_{p^a}(r)-1)^+."""
    pps = prime_powers_leq(k-1)  # only these can contribute (span k-1)
    if not pps:
        return 1, [1]
    Lam = 1
    for q in pps: Lam = Lam*q//gcd(Lam, q)
    r = np.arange(Lam, dtype=np.int64)
    # c_p accumulation per prime
    from collections import defaultdict
    cexp = defaultdict(lambda: np.zeros(Lam, dtype=np.int64))
    for q in pps:
        p = 0
        for pp in primes_upto(q):
            if q % pp == 0: p = pp
        cnt = ((r + k)//q) - (r//q)              # exact multiples of q in window
        cexp[p] += np.maximum(cnt - 1, 0)
    Ds = [None]*Lam
    # exact big ints
    for i in range(Lam):
        v = 1
        for p, arr in cexp.items():
            v *= int(p)**int(arr[i])
        Ds[i] = v
    return Lam, Ds

def Dmax_of(k, Lam, Ds):
    return max(Ds)

def scan_k(k, N, chunk=2_000_000, verbose=True):
    """Scan all window starts n' in [0, Nmax] where Nmax = max(N, ceil((N+k)*mu_k)).
    Return list of exact-verified duplicate groups (value, [starts]) and stats."""
    Lam, Ds = D_table(k)
    Dmax = max(Ds)
    mu_k = Dmax ** (1.0/k)
    Nmax = int((N + k) * mu_k) + 2
    Nmax = max(Nmax, N + k + 1)
    if verbose:
        print(f"k={k}: D_max={Dmax} mu_k={mu_k:.4f} Lam={Lam} N={N} scan-to={Nmax}", flush=True)
    # inverse-D tables mod Q1,Q2 (D is k-smooth, k < Q, so invertible)
    invD1 = [pow(d % Q1, -1, Q1) for d in Ds]
    invD2 = [pow(d % Q2, -1, Q2) for d in Ds]
    invD1 = np.array(invD1, dtype=np.int64); invD2 = np.array(invD2, dtype=np.int64)
    keys = np.empty(Nmax+1, dtype=np.uint64)
    t0 = time.time()
    for lo in range(0, Nmax+1, chunk):
        hi = min(Nmax+1, lo+chunk)
        n = np.arange(lo, hi, dtype=np.int64)
        f1 = np.ones(hi-lo, dtype=np.int64); f2 = np.ones(hi-lo, dtype=np.int64)
        for i in range(1, k+1):
            f1 = (f1 * ((n + i) % Q1)) % Q1
            f2 = (f2 * ((n + i) % Q2)) % Q2
        r = n % Lam
        h1 = (f1 * invD1[r]) % Q1
        h2 = (f2 * invD2[r]) % Q2
        keys[lo:hi] = h1.astype(np.uint64) * np.uint64(Q1) + h2.astype(np.uint64)
        if verbose and (lo // chunk) % 5 == 0:
            print(f"  chunk {lo}-{hi} ({time.time()-t0:.1f}s)", flush=True)
    # sort in-place, find duplicates
    keys.sort()
    d = np.diff(keys)
    dupmask = d == 0
    ndup = int(dupmask.sum())
    stats = dict(k=k, N=N, Nmax=Nmax, Dmax=Dmax, mu_k=mu_k, dup_fingerprints=ndup,
                 seconds=time.time()-t0)
    results = []
    if ndup:
        dupvals = keys[1:][dupmask]
        dupvals = np.unique(dupvals)
        # locate: recompute keys chunk-wise and match
        want = set(int(x) for x in dupvals)
        pos = {}
        for lo in range(0, Nmax+1, chunk):
            hi = min(Nmax+1, lo+chunk)
            n = np.arange(lo, hi, dtype=np.int64)
            f1 = np.ones(hi-lo, dtype=np.int64); f2 = np.ones(hi-lo, dtype=np.int64)
            for i in range(1, k+1):
                f1 = (f1 * ((n + i) % Q1)) % Q1
                f2 = (f2 * ((n + i) % Q2)) % Q2
            r = n % Lam
            h1 = (f1 * invD1[r]) % Q1
            h2 = (f2 * invD2[r]) % Q2
            kk = h1.astype(np.uint64) * np.uint64(Q1) + h2.astype(np.uint64)
            for idx in np.nonzero(np.isin(kk, np.array(sorted(want), dtype=np.uint64)))[0]:
                pos.setdefault(int(kk[idx]), []).append(int(lo+idx))
        for val, starts in pos.items():
            # exact verification with bignums
            exact = {}
            for s in starts:
                L = 1
                for i in range(1, k+1):
                    g = gcd(L, s+i); L = L*(s+i)//g
                exact.setdefault(L, []).append(s)
            for L, ss in exact.items():
                if len(ss) >= 2:
                    results.append((str(L), ss))
    return results, stats

def brute_check(k, N):
    """Dual method: exact bignum lcm dict (small ranges only).
    Groups ALL starts by exact lcm value (multi-occurrences included)."""
    seen = {}
    for n in range(0, N+1):
        L = 1
        for i in range(1, k+1):
            g = gcd(L, n+i); L = L*(n+i)//g
        seen.setdefault(L, []).append(n)
    out = []
    for L, ss in seen.items():
        if len(ss) >= 2:
            for a in range(len(ss)):
                for b in range(a+1, len(ss)):
                    out.append((ss[a], ss[b]))
    return out

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "main"
    if mode == "selftest":
        # dual-method agreement: k=2..8, N=30000
        ok = True
        for k in range(2, 9):
            res, stats = scan_k(k, 30000, verbose=False)
            # collect all duplicate pairs from scan (with exact groups)
            scan_pairs = set()
            for L, ss in res:
                ss = sorted(ss)
                for a in range(len(ss)):
                    for b in range(a+1, len(ss)):
                        scan_pairs.add((ss[a], ss[b]))
            # NOTE: brute only covers pairs with BOTH <= N; scan covers starts <= Nmax
            bb = brute_check(k, 30000)
            bb2 = set((a,b) for (a,b) in bb if b <= 30000 and a <= 30000)
            # filter scan pairs to both <= 30000
            sc2 = set(p for p in scan_pairs if p[0] <= 30000 and p[1] <= 30000)
            if bb2 != sc2:
                print(f"MISMATCH k={k}: brute {sorted(bb2)} scan {sorted(sc2)}")
                ok = False
            else:
                print(f"k={k}: dual-method agree, {len(bb2)} duplicate pairs (incl overlaps)", flush=True)
        print("SELFTEST", "PASS" if ok else "FAIL")
    elif mode == "main":
        plan = []  # (k, N)
        for k in range(2, 13):  plan.append((k, 10_000_000))
        for k in range(13, 25): plan.append((k, 1_000_000))
        allres = {}
        for k, N in plan:
            res, stats = scan_k(k, N)
            coll = [(ss) for (L, ss) in res if any(ss[i+1] >= ss[i]+k for i in range(len(ss)-1))]
            stats["collision_groups"] = len(coll)
            stats["all_dup_groups"] = len(res)
            print(f"  => k={k}: dup_groups={len(res)} collisions(m>=n+k)={len(coll)} ({stats['seconds']:.0f}s)", flush=True)
            allres[k] = dict(stats=stats, groups=[[L, ss] for L, ss in res])
        with open("census_results.json", "w") as f:
            json.dump(allres, f)
        print("WROTE census_results.json")
