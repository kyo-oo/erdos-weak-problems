#!/usr/bin/env python3
"""ladder_k21.py — same-phase alpha-ladder & growth stats for the k=21 census
re-run (task Q2, 2026-11-04; re-runs the wiped session's census).

Usage: ladder_k21.py c21 [b1 b2]     (b1,b2 = block split of scale 21)
Writes the growth_a4.txt-format row for k=21 plus the ladder/fit tables that
go into A4_STATUS.md §10 and analysis/growth_k21_a4.txt.
"""
import sys, math

ck = [1, 1, 4, 9, 19, 37, 79, 147, 266, 476, 919, 1790, 3210, 5425, 9093,
      19206, 38367, 65794, 108103, 177194, 347370]   # k=0..20 certified
c21 = int(sys.argv[1]); ck.append(c21)
ln3 = math.log(3)
LOG32 = math.log(2) / ln3          # log_3 2 = 0.6309...

print(f"c_21 = {c21}")
# ---- growth_a4.txt row (established format: k c_k r_k localexp cumexp 2c-c) ----
r = c21 / ck[20]
print(f"GROWTHROW 21 {c21} {r:.4f} {math.log(r)/ln3:.4f} "
      f"{math.log(c21)/(21*ln3):.4f} {2*ck[20]-c21}")

print("\ncumulative alpha_k = ln c_k/(k ln3):")
for k in range(10, 22):
    print(f"  k={k:2d}  {math.log(ck[k])/(k*ln3):.4f}")

for phase, ks in ((1, [11, 16, 21]), (0, [10, 15, 20])):
    a = [math.log(ck[k]) / (k * ln3) for k in ks]
    print(f"\nsame-phase k≡{phase} (mod 5): " +
          " -> ".join(f"a_{k}={v:.4f}" for k, v in zip(ks, a)))
    print("  declines: " + ", ".join(f"{a[i+1]-a[i]:+.4f}" for i in range(len(a)-1)) +
          f"   | gap to log3(2)={LOG32:.4f}: " +
          ", ".join(f"{LOG32-v:.4f}" for v in a))

print("\n5-scale marginal exponents ln(c_k/c_{k-5})/(5 ln3):")
for lo, hi in ((5, 9), (10, 14), (15, 19), (12, 16), (17, 21)):
    print(f"  k={lo}..{hi}: {math.log(ck[hi]/ck[lo-1])/(5*ln3):.4f}")

print("\nType-1 normalizer c_k/2^k (Type-1 needs -> const>0; it collapses):")
print("  " + " ".join(f"{ck[k]/2**k:.4f}" for k in range(8, 22)))
print("Type-2 normalizer c_k/(3^(k/2)*sqrt(k)) (Type-2 needs bounded band):")
print("  " + " ".join(f"{ck[k]/(3**(k/2)*math.sqrt(k)):.4f}" for k in range(8, 22)))

def lsq2(pts):                      # y = p + q x  -> (p, q, R2)
    n = len(pts); sx = sum(x for x, y in pts); sy = sum(y for x, y in pts)
    sxx = sum(x*x for x, y in pts); sxy = sum(x*y for x, y in pts)
    q = (n*sxy - sx*sy) / (n*sxx - sx*sx); p = (sy - q*sx) / n
    my = sy/n
    ssr = sum((y - (p + q*x))**2 for x, y in pts)
    sst = sum((y - my)**2 for x, y in pts)
    return p, q, 1 - ssr/sst

def lsq3(pts):                      # y = p + q x1 + s x2 -> (p, q, s, R2)
    n = len(pts)
    A = [[1, x1, x2] for x1, x2, y in pts]
    b = [y for x1, x2, y in pts]
    # normal equations M z = c
    M = [[sum(A[i][r]*A[i][c2] for i in range(n)) for c2 in range(3)] for r in range(3)]
    c = [sum(A[i][r]*b[i] for i in range(n)) for r in range(3)]
    # 3x3 solve (Gauss, no pivot needed here)
    for col in range(3):
        piv = M[col][col]
        for r2 in range(3):
            if r2 != col:
                f = M[r2][col]/piv
                for c2 in range(3): M[r2][c2] -= f*M[col][c2]
                c[r2] -= f*c[col]
    p, q, s = (c[0]/M[0][0], c[1]/M[1][1], c[2]/M[2][2])
    my = sum(b)/n
    ssr = sum((y - (p + q*x1 + s*x2))**2 for x1, x2, y in pts)
    sst = sum((y - my)**2 for x1, x2, y in pts)
    return p, q, s, 1 - ssr/sst

print("\nLSQ fits of ln c_k = lnC + a*(k ln3) + b*ln k:")
for lo in (8, 10, 13):
    pts = [(k*ln3, math.log(ck[k]) - 0.5*math.log(k)) for k in range(lo, 22)]
    p, q, r2 = lsq2(pts)
    print(f"  fixed b=1/2, k in [{lo},21]: a={q:.4f} C={math.exp(p):.4f} R2={r2:.5f}")
for lo in (8, 10):
    pts = [(k*ln3, math.log(k), math.log(ck[k])) for k in range(lo, 22)]
    p, q, s, r2 = lsq3(pts)
    print(f"  free (a,b),  k in [{lo},21]: a={q:.4f} b={s:.4f} C={math.exp(p):.4f} R2={r2:.5f}")

# same-phase alpha prediction of the pure Type-2 fit through k<=21 vs observed
pts = [(k*ln3, math.log(ck[k]) - 0.5*math.log(k)) for k in range(8, 22)]
p, q, r2 = lsq2(pts)
C = math.exp(p); a = q
print(f"\nType-2 fit (b=1/2, k in [8,21]): C={C:.4f} a={a:.4f}")
for k in (22, 25):
    print(f"  predicted c_{k} = {C*3**(a*k)*math.sqrt(k):.3e}")
t1 = c21 / 2**21
print(f"Type-1 frozen at k=21 (c_k/2^k={t1:.4f}): "
      f"c_22={t1*2**22:.3e} c_25={t1*2**25:.3e}")
ak = lambda k: a + (math.log(C) + 0.5*math.log(k))/(k*ln3)
print(f"same-phase (k≡1) declines predicted by this fit: "
      f"a16-a11={ak(16)-ak(11):+.4f} a21-a16={ak(21)-ak(16):+.4f} a26-a21={ak(26)-ak(21):+.4f}")

if len(sys.argv) > 3:
    b1, b2 = int(sys.argv[2]), int(sys.argv[3])
    b0 = ck[20]
    print(f"\nblock split scale 21: b0={b0} b1={b1} b2={b2} "
          f"(b1/c20={b1/b0:.4f} b2/c20={b2/b0:.4f})")
    print(f"leading-digit-2 fraction of 21-digit members: {b2/(c21-b0):.4f} "
          f"(phase law k≡1: peak; k=16 value was 0.726)")
