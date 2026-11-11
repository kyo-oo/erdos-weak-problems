#!/usr/bin/env python3
"""
W2-P850: SEGMENTED BIG CENSUS for Erdos-Woods length-3 (corpus #850).

Certified statement produced: for all 1 <= x < y <= N (N = 10^9 default):
NO witness exists, i.e. there is no pair with supp(x+i) = supp(y+i), i=0,1,2.

Method (exact):
  Theorem A+B (see PROOF.md): a witness with top y REQUIRES R(y) < y where
  R(y) = rad(y(y+1)(y+2)). We compute rad(n) EXACTLY for every n <= N+1 via a
  segmented sieve (int64), find every y with R(y) < y (float prefilter with
  generous margin + exact integer recheck), and for each such y scan all
  x = y - m*R(y) >= 1 with exact check R(x) | m*R(y). If no y qualifies,
  there is no witness <= N. Quality/ratio landscape recorded as evidence.

Also verifies sieve correctness against trial division on samples per segment.
"""
import numpy as np, sys, time, math

T0 = time.time()
def log(msg): print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)

N  = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000_000
SEG = int(sys.argv[2]) if len(sys.argv) > 2 else 10_000_000
OUT = sys.argv[3] if len(sys.argv) > 3 else "big_census_results.txt"

# primes up to sqrt(N)+ via simple sieve
def simple_primes(B):
    is_p = np.ones(B+1, dtype=bool); is_p[:2] = False
    for p in range(2, int(B**0.5)+1):
        if is_p[p]: is_p[p*p::p] = False
    return np.nonzero(is_p)[0]

SQ = int(math.isqrt(N+2)) + 1
PRIMES = simple_primes(SQ)
log(f"N={N:,} SEG={SEG:,} primes<={SQ}: {len(PRIMES)}")

def rad_ref(n):
    r, d = 1, 2
    while d*d <= n:
        if n % d == 0:
            r *= d
            while n % d == 0: n //= d
        d += 1
    if n > 1: r *= n
    return r

LOG2 = math.log(2.0)
best_ratio = []   # (ratio, y) top-20 smallest R(y)/y
best_qual = []    # (q, n) top-20 largest qualities
cand_below = []   # all y with R(y) < y  (exact)
count_below2y = 0 # y with R(y) < 2y (exact)
n_windows = 0

results = []
def R_of(rad_y, rad_y1, rad_y2, y_even):
    return rad_y*rad_y1*rad_y2//(2 if y_even else 1)

# trial-division radical for isolated small x (candidate scan)
def rad_single(n):
    return rad_ref(n)

lo = 2  # y starts at 2
while lo <= N-2:
    hi = min(lo + SEG, N-1)          # y in [lo, hi-1]; need rad up to hi+1
    size = hi + 2 - lo               # cover n in [lo, hi+1]
    rad_seg = np.ones(size, dtype=np.int64)
    rem = np.arange(lo, hi+2, dtype=np.int64)
    for p in PRIMES:
        pk = int(p)
        # rad multiply once
        start = ((lo + pk - 1)//pk)*pk - lo
        if start < size:
            rad_seg[start::pk] *= pk
        # divide rem by p at every power level (each level divides by p ONCE)
        while pk <= hi + 1:
            start = ((lo + pk - 1)//pk)*pk - lo
            if start >= size: break
            rem[start::pk] //= p
            pk *= int(p)
    big = rem > 1
    rad_seg[big] *= rem[big]
    # exact spot-checks per segment
    for n in [lo+1, (lo+hi)//2, hi]:
        assert int(rad_seg[n-lo]) == rad_ref(n), (n, rad_seg[n-lo], rad_ref(n))
    # windows y in [lo, hi-1]
    ys = np.arange(lo, hi, dtype=np.int64)
    r0 = rad_seg[0:hi-lo].astype(np.float64)
    r1 = rad_seg[1:hi-lo+1].astype(np.float64)
    r2 = rad_seg[2:hi-lo+2].astype(np.float64)
    s = np.log(r0) + np.log(r1) + np.log(r2)
    s = s - np.where(ys % 2 == 0, LOG2, 0.0)
    n_windows += hi - lo
    # candidates R(y) < y (margin) and R(y) < 2y count
    ly = np.log(ys.astype(np.float64))
    candmask = s < ly + 0.001
    c2mask = s < ly + math.log(2.0) + 0.001
    for y in np.nonzero(candmask)[0]:
        y = int(ys[y])
        Ry = R_of(int(rad_seg[y-lo]), int(rad_seg[y+1-lo]), int(rad_seg[y+2-lo]), y % 2 == 0)
        if Ry < y:
            cand_below.append((y, Ry))
            log(f"!!! CANDIDATE TOP y={y} R(y)={Ry} ratio={Ry/y:.6f}")
        # exact count for 2y
    for y in np.nonzero(c2mask)[0]:
        y = int(ys[y])
        Ry = R_of(int(rad_seg[y-lo]), int(rad_seg[y+1-lo]), int(rad_seg[y+2-lo]), y % 2 == 0)
        if Ry < 2*y:
            count_below2y += 1
            best_ratio.append((Ry/y, y))
    # landscape: smallest ratios overall (float, rescan cheap)
    ratio = np.exp(s - ly)
    k = min(200, len(ratio))
    sel = np.argpartition(ratio, k-1)[:k]
    for i in sel:
        best_ratio.append((float(ratio[i]), int(ys[i])))
    best_ratio = sorted(best_ratio)[:400]
    # quality records: q = 2 ln(y+1)/ln R(y)
    with np.errstate(divide='ignore'):
        q = 2.0*np.log(ys+1)/s
    sel = np.argpartition(-q, min(200, len(q)-1))[:200]
    for i in sel:
        best_qual.append((float(q[i]), int(ys[i])+1))
    best_qual = sorted(best_qual, reverse=True)[:400]
    lo = hi
    if (lo//SEG) % 5 == 0:
        log(f"progress: y-window done to {lo:,}; min ratio so far {best_ratio[0] if best_ratio else None}")
        with open(OUT + ".partial", "w") as f:
            f.write(f"progress lo={lo}\ncand_below={cand_below}\ncount2y={count_below2y}\nbest_ratio={sorted(best_ratio)[:25]}\nbest_qual={sorted(best_qual, reverse=True)[:25]}\n")

log(f"scan complete: {n_windows:,} windows examined, y in [2, {N-2}]")
best_ratio = sorted(best_ratio)[:25]
best_qual = sorted(best_qual, reverse=True)[:25]
log(f"y with R(y) < y (EXACT): {cand_below if cand_below else 'NONE'}")
log(f"count y with R(y) < 2y (EXACT): {count_below2y}")
log("smallest R(y)/y: " + ", ".join(f"{y}:{r:.3f}" for r,y in best_ratio))
log("largest qualities (n^2-1,1,n^2): " + ", ".join(f"n={n}:q={q:.4f}" for q,n in best_qual))

# candidate scan: if any y with R(y) < y, check x = y - m R(y)
witnesses = []
for (y, Ry) in cand_below:
    m = 1
    while y - m*Ry >= 1:
        x = y - m*Ry
        Rx = rad_single(x)*rad_single(x+1)*rad_single(x+2)//(2 if x%2==0 else 1)
        if (m*Ry) % Rx == 0:
            witnesses.append((x, y))
            log(f"!!!! WITNESS FOUND: x={x} y={y}")
        m += 1
log(f"WITNESSES with max <= {N}: {witnesses if witnesses else 'NONE'}")

with open(OUT, "w") as f:
    f.write(f"N = {N}\nwindows scanned (y in [2,N-2]): {n_windows}\n")
    f.write(f"y with R(y)<y (exact): {cand_below}\n")
    f.write(f"count R(y)<2y: {count_below2y}\n")
    f.write(f"witnesses: {witnesses}\n")
    f.write("smallest ratios R(y)/y: " + repr(best_ratio) + "\n")
    f.write("top qualities (n^2-1,1,n^2): " + repr(best_qual) + "\n")
log(f"results written to {OUT}")
