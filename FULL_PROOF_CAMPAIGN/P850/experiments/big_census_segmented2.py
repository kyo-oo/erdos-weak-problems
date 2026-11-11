#!/usr/bin/env python3
"""
W2-P850: SEGMENTED BIG CENSUS for Erdos-Woods length-3 (corpus #850) — v2
(memory-safe: chunked window stage, float32 logs, resumable).

Certified statement: for all 1 <= x < y <= N: NO witness exists
(supp(x+i) = supp(y+i), i=0,1,2), via Theorems A+B (PROOF.md):
witness => R(y) < y, R(y) = rad(y(y+1)(y+2)) = rad((y+1)^2 - 1)*rad(y+1).
Scan all y in [LO_START, N-2] for R(y) < y (exact integer recheck of float
prefilter), then x = y - m*R(y) with exact R(x) | m*R(y) check.

Usage: big_census_segmented2.py N SEG OUT [LO_START]
"""
import numpy as np, sys, time, math, gc

T0 = time.time()
def log(msg): print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)

N  = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000_000
SEG = int(sys.argv[2]) if len(sys.argv) > 2 else 40_000_000
OUT = sys.argv[3] if len(sys.argv) > 3 else "big_census_results.txt"
LO_START = int(sys.argv[4]) if len(sys.argv) > 4 else 2

def simple_primes(B):
    is_p = np.ones(B+1, dtype=bool); is_p[:2] = False
    for p in range(2, int(B**0.5)+1):
        if is_p[p]: is_p[p*p::p] = False
    return np.nonzero(is_p)[0]

SQ = int(math.isqrt(N+2)) + 1
PRIMES = simple_primes(SQ)
log(f"N={N:,} SEG={SEG:,} LO_START={LO_START:,} primes<={SQ}: {len(PRIMES)}")

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
best_ratio, best_qual = [], []
cand_below = []
count_below2y = 0
n_windows = 0
CH = 10_000_000  # window-stage chunk

lo = max(2, LO_START)
while lo <= N-2:
    hi = min(lo + SEG, N-1)
    size = hi + 2 - lo
    rad_seg = np.ones(size, dtype=np.int64)
    rem = np.arange(lo, hi+2, dtype=np.int64)
    for p in PRIMES:
        p = int(p)
        start = ((lo + p - 1)//p)*p - lo
        if start < size:
            rad_seg[start::p] *= p
        pk = p
        while pk <= hi + 1:
            start = ((lo + pk - 1)//pk)*pk - lo
            if start >= size: break
            rem[start::pk] //= p
            pk *= p
    big = rem > 1
    rad_seg[big] *= rem[big]
    del big
    # exact spot-checks
    for n in {lo+1, (lo+hi)//2, hi, hi+1}:
        assert int(rad_seg[n-lo]) == rad_ref(n), (n, rad_seg[n-lo], rad_ref(n))
    del rem; gc.collect()
    # window stage in chunks of CH (y in [lo, hi-1])
    c0 = lo
    while c0 < hi:
        c1 = min(c0 + CH, hi)
        L = c1 - c0
        r0 = np.log(rad_seg[c0-lo : c1-lo].astype(np.float32)).astype(np.float32)
        r1 = np.log(rad_seg[c0+1-lo : c1+1-lo].astype(np.float32)).astype(np.float32)
        r2 = np.log(rad_seg[c0+2-lo : c1+2-lo].astype(np.float32)).astype(np.float32)
        s = r0 + r1 + r2
        ys = np.arange(c0, c1, dtype=np.int64)
        s -= np.where(ys % 2 == 0, np.float32(LOG2), np.float32(0.0))
        ly = np.log(ys.astype(np.float32))
        n_windows += L
        candmask = s < ly + np.float32(0.001)
        c2mask = s < ly + np.float32(math.log(2.0) + 0.001)
        for k in np.nonzero(candmask)[0]:
            y = int(ys[k])
            Ry = int(rad_seg[y-lo])*int(rad_seg[y+1-lo])*int(rad_seg[y+2-lo])//((2 if y % 2 == 0 else 1))
            if Ry < y:
                cand_below.append((y, Ry))
                log(f"!!! CANDIDATE TOP y={y} R(y)={Ry} ratio={Ry/y:.6f}")
        for k in np.nonzero(c2mask)[0]:
            y = int(ys[k])
            Ry = int(rad_seg[y-lo])*int(rad_seg[y+1-lo])*int(rad_seg[y+2-lo])//((2 if y % 2 == 0 else 1))
            if Ry < 2*y:
                count_below2y += 1
                best_ratio.append((Ry/y, y))
        ratio = np.exp(s - ly)
        kk = min(200, L)
        sel = np.argpartition(ratio, kk-1)[:kk]
        for i in sel:
            best_ratio.append((float(ratio[i]), int(ys[i])))
        best_ratio = sorted(best_ratio)[:400]
        with np.errstate(divide='ignore'):
            q = (2.0*np.log((ys+1).astype(np.float32))).astype(np.float32)/s
        sel = np.argpartition(-q, min(200, L-1))[:200]
        for i in sel:
            best_qual.append((float(q[i]), int(ys[i])+1))
        best_qual = sorted(best_qual, reverse=True)[:400]
        c0 = c1
        del r0, r1, r2, s, ys, ly, ratio, q
    lo = hi
    log(f"progress: y done to {lo:,}; min ratio {best_ratio[0] if best_ratio else None}; cands={len(cand_below)}")
    with open(OUT + ".partial", "w") as f:
        f.write(f"progress lo={lo}\ncand_below={cand_below}\ncount2y={count_below2y}\nbest_ratio={sorted(best_ratio)[:25]}\nbest_qual={sorted(best_qual, reverse=True)[:25]}\n")

log(f"scan complete: {n_windows:,} windows; y in [{max(2,LO_START)}, {N-2}]")
best_ratio = sorted(best_ratio)[:25]
best_qual = sorted(best_qual, reverse=True)[:25]
log(f"y with R(y) < y (EXACT): {cand_below if cand_below else 'NONE'}")
log(f"count y with R(y) < 2y (EXACT): {count_below2y}")
log("smallest R(y)/y: " + ", ".join(f"{y}:{r:.3f}" for r,y in best_ratio))
log("largest qualities (n^2-1,1,n^2): " + ", ".join(f"n={n}:q={q:.4f}" for q,n in best_qual))

witnesses = []
for (y, Ry) in cand_below:
    m = 1
    while y - m*Ry >= 1:
        x = y - m*Ry
        Rx = rad_ref(x)*rad_ref(x+1)*rad_ref(x+2)//(2 if x%2==0 else 1)
        if (m*Ry) % Rx == 0:
            witnesses.append((x, y))
            log(f"!!!! WITNESS FOUND: x={x} y={y}")
        m += 1
log(f"WITNESSES with max <= {N} (in scanned range): {witnesses if witnesses else 'NONE'}")

with open(OUT, "w") as f:
    f.write(f"N = {N}\nlo_start = {LO_START}\nwindows scanned: {n_windows}\n")
    f.write(f"y with R(y)<y (exact): {cand_below}\n")
    f.write(f"count R(y)<2y: {count_below2y}\n")
    f.write(f"witnesses: {witnesses}\n")
    f.write("smallest ratios R(y)/y: " + repr(best_ratio) + "\n")
    f.write("top qualities (n^2-1,1,n^2): " + repr(best_qual) + "\n")
log(f"results written to {OUT}")
