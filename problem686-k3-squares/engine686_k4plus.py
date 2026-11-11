#!/usr/bin/env python3
"""
#686 THE MISSING-SQUARE k-SWEEP (S043): k = 4..10, the square classes the
k=2 family (t ≡ 2 mod 4, t >= 10, sporadic 99) and the k=3 census
(t in {3,4,70,1189,1798,4756}) do NOT cover: t = 2, odd t, t ≡ 0 (mod 4),
and t ≡ 2 (mod 4) with t < 10.

Problem shape (verbatim): N = prod_{1<=i<=k}(m+i) / prod_{1<=i<=k}(n+i),
k >= 2, m >= n+k, n >= 1. Square N = t^2:
    prod_{i=1..k}(m+i) = t^2 * prod_{i=1..k}(n+i).

Method: for each (k, n): D = prod(n+i) (incremental); for each missing t:
target = t^2 * D; m = round(D^{1/k} * t^{2/k}) (float root, error << 1);
verify window +-4 exactly with big ints. m >= n + k enforced.
"""
import math, sys, time

# --- the missing t set: not covered by k=2 family/census, not in k=3 six ---
def missing_ts(tmax):
    covered = set()
    for t in range(10, tmax + 1, 4):   # t == 2 mod 4, t >= 10
        covered.add(t)
    covered.add(99)                     # k=2 sporadic (within range)
    for t in (3, 4, 70, 1189, 1798, 4756):
        if t <= tmax:
            covered.add(t)              # k=3 classes
    return [t for t in range(2, tmax + 1) if t not in covered]

def run(k, nmax, tmax, t0=time.time()):
    ts = missing_ts(tmax)
    # precompute t^{2/k} per t
    tp = [(t, t ** (2.0 / k)) for t in ts]
    hits = []
    # incremental D for n: start n=1
    D = 1
    for i in range(2, 2 + k):           # prod_{i=1..k}(1+i) = (2)(3)...(k+1)
        D *= i
    for n in range(1, nmax + 1):
        if n > 1:
            D = D // n * (n + k)        # D(n) = D(n-1) * (n+k) / n
        rootD = D ** (1.0 / k)
        for t, f in tp:
            r = rootD * f
            m0 = int(r)
            lo = max(n + k, m0 - 4)
            hi = m0 + 4
            for m in range(lo, hi + 1):
                # P = (m+1)...(m+k)
                P = 1
                for i in range(1, k + 1):
                    P *= (m + i)
                if P == t * t * D:
                    hits.append((t, m, n, k))
                    print(f"#686 HIT: k={k} t={t} m={m} n={n}  "
                          f"(N = {t*t}, k-representation at k={k})", flush=True)
        if n % 5000 == 0:
            print(f"  k={k}: n={n}/{nmax}  hits={len(hits)}  "
                  f"({time.time()-t0:.0f}s)", flush=True)
    return hits

if __name__ == "__main__":
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    ks = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [4,5,6,7,8,9,10]
    allhits = []
    for k in ks:
        print(f"=== k={k} sweep: t missing <= {tmax}, n <= {nmax}", flush=True)
        allhits += run(k, nmax, tmax)
    if not allhits:
        print(f"#686 missing-square sweep: ZERO hits (k={ks}, t<={tmax}, n<={nmax})")
    else:
        print(f"#686 TOTAL: {len(allhits)} hits")
        for h in sorted(allhits):
            print("  ", h)
