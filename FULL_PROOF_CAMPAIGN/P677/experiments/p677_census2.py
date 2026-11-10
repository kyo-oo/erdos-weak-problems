#!/usr/bin/env python3
"""P677 census engine v2 — memory-safe certified-complete collision scan.

Collision = n<m, m>=n+k, M(n,k)=M(m,k). Engine: exact modular fingerprints
M(n,k) mod (Q1*Q2) over ALL window starts up to the rigorous m-bound
Nmax = (N+k)*mu_k (PROOF.md Thm E, mu_k from the per-prime D-bound), computed
chunk-locally via prime-power counts (no giant period tables). Every duplicate
candidate is re-verified with exact big-integer lcm. Dual method: exact bignum
dict on small ranges (selftest).
"""
import numpy as np
from math import gcd, log
import sys, time, json

Q1 = 2147483647  # 2^31-1 Mersenne prime
Q2 = 2147483629  # prime
U31 = np.uint64(2147483647)

def primes_upto(n):
    sieve = bytearray([1])*(n+1); sieve[0]=sieve[1]=0
    for i in range(2, int(n**0.5)+1):
        if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(n+1) if sieve[i]]

def pp_groups(k):
    """prime powers p^a <= k-1, grouped: {p: [p, p^2, ...]} ; plus exponent bound E_p."""
    groups = {}
    for p in primes_upto(max(k-1, 2)):
        q = p; E = 0; qs = []
        while q <= k-1:
            qs.append(q); E += (k-1)//q; q *= p
        if qs: groups[p] = (qs, E)
    return groups

def D_bound(k):
    g = pp_groups(k)
    D = 1
    for p, (qs, E) in g.items(): D *= p**E
    return D

def scan_k(k, N, chunk=4_000_000, verbose=True):
    g = pp_groups(k)
    Db = D_bound(k)
    mu_k = Db ** (1.0/k)
    Nmax = int((N + k) * mu_k) + 2
    Nmax = max(Nmax, N + k + 1)
    if verbose:
        print(f"k={k}: D_bound={Db} mu_k={mu_k:.3f} N={N} scan-to={Nmax}", flush=True)
    # inverse-power tables per prime: t[e] = (p^-1)^e mod Q
    tabs1, tabs2 = {}, {}
    for p, (qs, E) in g.items():
        i1 = pow(p, -1, Q1); i2 = pow(p, -1, Q2)
        t1 = [1]*(E+1); t2 = [1]*(E+1)
        for e in range(1, E+1):
            t1[e] = t1[e-1]*i1 % Q1; t2[e] = t2[e-1]*i2 % Q2
        tabs1[p] = np.array(t1, dtype=np.int64); tabs2[p] = np.array(t2, dtype=np.int64)
    keys = np.empty(Nmax+1, dtype=np.uint64)
    t0 = time.time()
    for lo in range(0, Nmax+1, chunk):
        hi = min(Nmax+1, lo+chunk)
        n = np.arange(lo, hi, dtype=np.int64)
        f1 = np.ones(hi-lo, dtype=np.int64); f2 = np.ones(hi-lo, dtype=np.int64)
        for i in range(1, k+1):
            f1 = (f1 * ((n + i) % Q1)) % Q1
            f2 = (f2 * ((n + i) % Q2)) % Q2
        for p, (qs, E) in g.items():
            c = np.zeros(hi-lo, dtype=np.int64)
            for q in qs:
                c += np.maximum((n + k)//q - n//q - 1, 0)
            f1 = (f1 * tabs1[p][c]) % Q1
            f2 = (f2 * tabs2[p][c]) % Q2
        keys[lo:hi] = f1.astype(np.uint64)*U31 + f2.astype(np.uint64)
    keys.sort()
    # chunked duplicate detection
    ndup = 0
    dupvals = set()
    step = 8_000_000
    for lo in range(0, Nmax, step):
        seg = keys[lo:lo+step+1]
        d = np.diff(seg)
        m = d == 0
        ndup += int(m.sum())
        if m.any():
            dupvals.update(int(x) for x in seg[1:][m])
    stats = dict(k=k, N=N, Nmax=Nmax, D_bound=Db, mu_k=mu_k,
                 dup_fingerprints=ndup, seconds=time.time()-t0)
    results = []
    if ndup:
        want = np.array(sorted(dupvals), dtype=np.uint64)
        pos = {}
        for lo in range(0, Nmax+1, chunk):
            hi = min(Nmax+1, lo+chunk)
            n = np.arange(lo, hi, dtype=np.int64)
            f1 = np.ones(hi-lo, dtype=np.int64); f2 = np.ones(hi-lo, dtype=np.int64)
            for i in range(1, k+1):
                f1 = (f1 * ((n + i) % Q1)) % Q1
                f2 = (f2 * ((n + i) % Q2)) % Q2
            for p, (qs, E) in g.items():
                c = np.zeros(hi-lo, dtype=np.int64)
                for q in qs:
                    c += np.maximum((n + k)//q - n//q - 1, 0)
                f1 = (f1 * tabs1[p][c]) % Q1
                f2 = (f2 * tabs2[p][c]) % Q2
            kk = f1.astype(np.uint64)*U31 + f2.astype(np.uint64)
            sel = np.nonzero(np.isin(kk, want))[0]
            for idx in sel:
                pos.setdefault(int(kk[idx]), []).append(int(lo+idx))
        for val, starts in pos.items():
            exact = {}
            for s in starts:
                L = 1
                for i in range(1, k+1):
                    gg = gcd(L, s+i); L = L*(s+i)//gg
                exact.setdefault(L, []).append(s)
            for L, ss in exact.items():
                if len(ss) >= 2:
                    results.append((str(L), ss))
    del keys
    return results, stats

def brute_check(k, N):
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

def run_plan(plan, outfile="census_results.json"):
    allres = {}
    try:
        with open(outfile) as f: allres = json.load(f)
    except Exception: pass
    for k, N in plan:
        key = str(k)
        if key in allres and allres[key].get("stats", {}).get("N") == N:
            print(f"k={k}: already done", flush=True); continue
        res, stats = scan_k(k, N, verbose=False)
        coll = [ss for (L, ss) in res if any(ss[i+1] >= ss[i]+k for i in range(len(ss)-1))]
        stats["collision_groups"] = len(coll); stats["all_dup_groups"] = len(res)
        print(f"k={k}: N={N} scan-to={stats['Nmax']} dups={len(res)} COLLISIONS(m>=n+k)={len(coll)} ({stats['seconds']:.0f}s)", flush=True)
        if coll: print("  !!! COLLISION GROUPS:", coll, flush=True)
        allres[key] = dict(stats=stats, groups=[[L, ss] for L, ss in res])
        with open(outfile, "w") as f: json.dump(allres, f)

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if mode == "selftest":
        ok = True
        for k in range(2, 13):
            res, stats = scan_k(k, 30000, verbose=False)
            scan_pairs = set()
            for L, ss in res:
                ss = sorted(ss)
                for a in range(len(ss)):
                    for b in range(a+1, len(ss)):
                        scan_pairs.add((ss[a], ss[b]))
            bb = set(p for p in brute_check(k, 30000) if p[0] <= 30000 and p[1] <= 30000)
            sc2 = set(p for p in scan_pairs if p[0] <= 30000 and p[1] <= 30000)
            if bb != sc2:
                print(f"MISMATCH k={k}"); ok = False
            else:
                print(f"k={k}: dual-method agree ({len(bb)} dup pairs incl overlaps)", flush=True)
        print("SELFTEST", "PASS" if ok else "FAIL")
    else:
        phase = mode
        if phase == "A":   # deep: k=8..12 @ 1e7
            run_plan([(k, 10_000_000) for k in range(8, 13)])
        elif phase == "B": # k=13..24 @ 1e6
            run_plan([(k, 1_000_000) for k in range(13, 25)])
        elif phase == "C": # k=25..40 @ 1e6
            run_plan([(k, 1_000_000) for k in range(25, 41)])
        elif phase == "D": # k=2..7 @ 1e7 (re-run with v2 for uniform artifacts)
            run_plan([(k, 10_000_000) for k in range(2, 8)])
