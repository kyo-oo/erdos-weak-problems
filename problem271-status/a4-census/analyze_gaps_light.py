#!/usr/bin/env python3
"""WAR-271 task 1-c: light completion of the A(4) analysis (gaps, overlap,
digit-uniformity tests, period-5 phase table, Type-2 fit + projections).
Trivial compute: reads only existing census dumps. No census generation."""
import math, os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
A4 = [int(x) for x in open(os.path.join(HERE, 'data/a4_members_3k20.txt'))]
A2 = [int(x) for x in open(os.path.join(HERE, 'data/a2_members_3k13.txt'))]
OUT = []
def p(s=""):
    print(s); OUT.append(s)
def ter(n):
    if n == 0: return "0"
    d = ""
    while n: d = str(n % 3) + d; n //= 3
    return d

# sanity: counts
c4 = []
for k in range(21):
    lo, hi = 0, len(A4)
    while lo < hi:
        mid = (lo+hi)//2
        if A4[mid] < 3**k: lo = mid+1
        else: hi = mid
    c4.append(lo)
assert c4 == [1,1,4,9,19,37,79,147,266,476,919,1790,3210,5425,9093,19206,38367,65794,108103,177194,347370], c4
p("[sanity] c_k from a4_members_3k20.txt matches counts_a4.txt exactly; |A4|=%d" % len(A4))

L3 = math.log(3)
p("\n===== (A) GAPS (the missing section f) =====")
g = [A4[i+1]-A4[i] for i in range(len(A4)-1)]
p("gaps: n=%d min=%d max=%d distinct=%d" % (len(g), min(g), max(g), len(set(g))))
cnt = Counter(g)
p("gap histogram (value:count), all gaps with count>=1000, sorted by value:")
p("  " + ", ".join(f"{v}:{c}" for v, c in sorted(cnt.items()) if c >= 1000))
p("small-gap counts: 1:%d  2:%d  3:%d  4:%d  5:%d" % (cnt[1], cnt[2], cnt[3], cnt[4], cnt[5]))
big = sorted(range(len(g)), key=lambda i: -g[i])[:12]
p("12 largest gaps (between a_i and a_{i+1}; a_i in ternary):")
for i in big:
    p("  i=%d gap=%d a_i=%d (%s_3) a_{i+1}=%d (%s_3)" % (i, g[i], A4[i], ter(A4[i]), A4[i+1], ter(A4[i+1])))
p("max gap within [0,3^k) for k=2..20: " + ", ".join(
    f"3^{k}:{max(g[:c4[k]-1]) if c4[k]>1 else 0}" for k in range(2, 21)))

def gamma_fit(imin, imax):
    # local slope of ln gap vs ln index over index window (median-binned)
    xs, ys = [], []
    B = 40
    idx = list(range(imin, min(imax, len(g))))
    step = max(1, len(idx)//B)
    for b in range(0, len(idx), step):
        w = idx[b:b+step]
        xs.append(math.log(sum(i for i in w)/len(w)))
        ys.append(math.log(sum(g[i-1] for i in w)/len(w)))
    n = len(xs); mx = sum(xs)/n; my = sum(ys)/n
    sxx = sum((x-mx)**2 for x in xs); sxy = sum((x-mx)*(y-my) for x, y in zip(xs, ys))
    return sxy/sxx
p("gap scaling exponent gamma = d ln(gap)/d ln(index) (Type-1 -> 0.585, Type-2 m^2/logm -> 1.0 with log correction):")
for lo_, hi_ in [(30000, 347370), (100000, 347370), (200000, 347370), (5000, 50000)]:
    p("  indices %6d..%6d: gamma = %.4f" % (lo_, hi_, gamma_fit(lo_, hi_)))

p("\n===== (B) A(4) vs A(2) overlap + family membership =====")
s2 = set(A2); s4 = set(A4)
p("|A(4) ∩ A(2) ∩ [0,3^13)| = %d  (A(2) has %d members there; A(4) has %d)" % (
    len(s4 & s2), len(A2), c4[13]))
fam = [(4*3**j in s4, 2*3**j in s4, 3**j in s4) for j in range(13)]
p("membership in A(4): 4*3^j: %s" % ["Y" if a else "n" for a, _, _ in fam])
p("                      2*3^j: %s" % ["Y" if b else "n" for _, b, _ in fam])
p("                       3^j : %s" % ["Y" if c else "n" for _, _, c in fam])

p("\n===== (C) DIGIT UNIFORMITY (interior digits) =====")
bysize = {}
for n in A4:
    if n == 0: continue
    bysize.setdefault(len(ter(n)), []).append(n)
for d in [16, 18, 20]:
    ns = bysize[d]
    p("d=%d (n=%d): per-position digit frequencies P(0)/P(1)/P(2), positions 0..%d:" % (d, len(ns), d-1))
    row = []
    for pos in range(d):
        c0 = c1 = c2 = 0
        for n in ns:
            m = n
            for _ in range(pos): m //= 3
            r = m % 3
            if r == 0: c0 += 1
            elif r == 1: c1 += 1
            else: c2 += 1
        row.append("%.3f/%.3f/%.3f" % (c0/len(ns), c1/len(ns), c2/len(ns)))
    p("  " + " | ".join(row))
# pooled interior positions (0..d-4) for d=20
ns = bysize[20]; tot = [0, 0, 0]; N = 0
for n in ns:
    m = n
    for pos in range(17):   # exclude top 3 positions
        r = m % 3; tot[r] += 1; m //= 3; N += 1
p("d=20 pooled interior positions 0..16: P(0)=%.5f P(1)=%.5f P(2)=%.5f  (uniform = 0.33333)" %
  (tot[0]/N, tot[1]/N, tot[2]/N))
# adjacent independence: P(2 at pos i AND 2 at pos i+1), i in 1..15, d=20
both = single = 0
for n in ns:
    m = n
    digs = [m % 3]; mm = m // 3
    for _ in range(19):
        digs.append(mm % 3); mm //= 3
    for i in range(1, 16):
        if digs[i+1] == 2:
            single += 1
            if digs[i] == 2: both += 1
p("d=20 adjacent-digit check: P(pos_i=2 | pos_{i+1}=2) = %.5f  (independence -> 0.33333)" % (both/single))
# #2s distribution vs Binomial(20,1/3)
binom = [math.comb(20, j)*(1/3)**j*(2/3)**(20-j) for j in range(21)]
obs = Counter()
for n in ns:
    m = n; k2 = 0
    for _ in range(20):
        if m % 3 == 2: k2 += 1
        m //= 3
    obs[k2] += 1
mean = sum(k*v for k, v in obs.items())/len(ns)
var = sum((k-mean)**2*v for k, v in obs.items())/len(ns)
p("d=20 #2s per member: mean=%.4f (binom 20/3=%.4f)  var=%.4f (binom=%.4f)" %
  (mean, 20/3, var, 20*(1/3)*(2/3)))
p("d=20 #2s distribution obs%% vs Binomial(20,1/3)%% (j: obs, binom):")
p("  " + "; ".join("j=%d: %.2f/%.2f" % (j, 100*obs.get(j, 0)/len(ns), 100*binom[j]) for j in range(4, 13)))

p("\n===== (D) PERIOD-5 PHASE STRUCTURE =====")
p("r_k = c_k/c_{k-1} by k mod 5 (k=5..20):")
for ph in range(5):
    vals = [(k, c4[k]/c4[k-1]) for k in range(5, 21) if k % 5 == ph]
    p("  k mod 5 = %d: %s" % (ph, ", ".join("k=%d: %.4f" % kv for kv in vals)))
p("alpha_k by k mod 5 (cumulative exponent):")
for ph in range(5):
    vals = [(k, math.log(c4[k])/(k*L3)) for k in range(10, 21) if k % 5 == ph]
    p("  k mod 5 = %d: %s" % (ph, ", ".join("k=%d: %.4f" % kv for kv in vals)))
p("same-phase alpha declines: a10->a15: %+.4f  a15->a20: %+.4f" % (
    math.log(c4[15])/(15*L3)-math.log(c4[10])/(10*L3),
    math.log(c4[20])/(20*L3)-math.log(c4[15])/(15*L3)))
p("5-scale block marginal exponents: k=5..9: %.4f  k=10..14: %.4f  k=15..19: %.4f" % (
    math.log(c4[9]/c4[4])/(5*L3), math.log(c4[14]/c4[9])/(5*L3), math.log(c4[19]/c4[14])/(5*L3)))
# leading-digit-2 fraction n_k^{(top=2)}/n_k by scale
p("leading-digit-2 fraction among k-digit members (from data):")
for k in range(11, 21):
    ns = bysize[k]
    f2 = sum(1 for n in ns if (n // 3**(k-1)) == 2) / len(ns)
    p("  k=%2d: %.4f" % (k, f2))

p("\n===== (E) TYPE-2 FIT AND PROJECTIONS =====")
p("c_k/2^k (Type-1 normalizer; must -> const if Type-1):")
p("  " + ", ".join("k=%d: %.4f" % (k, c4[k]/2**k) for k in range(8, 21)))
p("c_k/(3^(k/2)*sqrt(k)) (Type-2 k^2/logk normalizer; must -> const if Type-2):")
p("  " + ", ".join("k=%d: %.4f" % (k, c4[k]/(3**(k/2)*math.sqrt(k))) for k in range(8, 21)))
p("c_k/3^(k/2) (pure alpha=1/2 normalizer):")
p("  " + ", ".join("k=%d: %.4f" % (k, c4[k]/3**(k/2)) for k in range(8, 21)))

def lsq(pts):
    n = len(pts); mx = sum(x for x, _ in pts)/n; my = sum(y for _, y in pts)/n
    sxx = sum((x-mx)**2 for x, _ in pts); sxy = sum((x-mx)*(y-my) for x, y in pts)
    b = sxy/sxx; a = my - b*mx
    r2 = 1 - sum((y-(a+b*x))**2 for x, y in pts)/sum((y-my)**2 for _, y in pts)
    return a, b, r2
# fixed-beta fit: ln c_k - 0.5 ln k = lnC + alpha*k*ln3
for lo_, hi_, beta in [(10, 20, 0.5), (13, 20, 0.5), (8, 20, 0.5), (10, 20, 1.0), (13, 20, 1.0)]:
    pts = [(k*L3, math.log(c4[k]) - beta*math.log(k)) for k in range(lo_, hi_+1)]
    a, b, r2 = lsq(pts)
    p("fixed-beta fit k in [%d,%d], beta=%.1f: alpha = %.5f  C = e^%.4f = %.4f  R2 = %.6f" %
      (lo_, hi_, beta, b/L3*0+b, a, math.exp(a), r2) )
    # NOTE: slope b is per unit of (k*ln3), so alpha = b directly in ln c = lnC + alpha*(k ln3)
for lo_, hi_, beta in [(10, 20, 0.5), (13, 20, 0.5)]:
    pts = [(k*L3, math.log(c4[k]) - beta*math.log(k)) for k in range(lo_, hi_+1)]
    a, b, r2 = lsq(pts)
    p("  -> k in [%d,%d] beta=%.1f: alpha = %.5f  C = %.4f  R2 = %.6f" % (lo_, hi_, beta, b, math.exp(a), r2))
# residuals of alpha_k vs Type-2 form alpha_k = 1/2 + (lnC + 0.5 ln k)/(k ln3), C=1.3162
C = c4[20]/(3**10*math.sqrt(20))
p("Type-2 form with single C = %.4f (fitted at k=20): predicted vs observed alpha_k:" % C)
for k in range(10, 21):
    pred = 0.5 + (math.log(C) + 0.5*math.log(k))/(k*L3)
    obs_ = math.log(c4[k])/(k*L3)
    p("  k=%2d: pred %.4f  obs %.4f  resid %+.4f" % (k, pred, obs_, obs_-pred))
p("Type-1 form c_k = C'*2^k with C' = %.4f (fitted at k=20): predicted vs observed alpha_k:" % (c4[20]/2**20))
C1 = c4[20]/2**20
for k in range(10, 21):
    pred = math.log(2)/L3 + math.log(C1)/(k*L3)
    obs_ = math.log(c4[k])/(k*L3)
    p("  k=%2d: pred %.4f  obs %.4f  resid %+.4f" % (k, pred, obs_, obs_-pred))
# projections
p("PROJECTIONS:")
a2C = C
p("  Type-2 (alpha=1/2, beta=1/2, C=%.4f): c_21=%.3e  c_22=%.3e  c_25=%.4e  c_30=%.4e" % (
    a2C, a2C*3**10.5*math.sqrt(21), a2C*3**11*math.sqrt(22), a2C*3**12.5*math.sqrt(25), a2C*3**15*math.sqrt(30)))
marg = math.log(c4[19]/c4[14])/(5*L3)
p("  marginal-alpha frozen at 5-block mean %.4f (k=15..19): c_25 = %.4e  c_30 = %.4e" % (
    marg, c4[20]*3**(marg*5), c4[20]*3**(marg*10)))
p("  Type-1 (c_k/2^k = %.4f frozen): c_25 = %.4e  c_30 = %.4e" % (
    C1, C1*2**25, C1*2**30))
p("  predicted alpha_25 under Type-2 fit: %.4f ; under frozen-marginal: %.4f ; Type-1 requires >= 0.5806 rising" % (
    0.5 + (math.log(a2C)+0.5*math.log(25))/(25*L3), math.log(c4[20]*3**(marg*5))/(25*L3)))
# member-growth consistency constant
p("member-growth: implied a_m ~ K*m^2/ln(a_m) with K = 1/C^2/ln(3)... check at m=340000:")
m = 340000; am = A4[m-1]
p("  a_340000 = %d ; Type-2 fit c(x)=C*sqrt(x*k), k=ln x/ln3 -> x = m^2/(C^2*ln x); solve: x = %.4e (obs %.4e, ratio %.3f)" % (
    am, m*m/(C*C*math.log(am)), am, am/(m*m/(C*C*math.log(am)))))
p("  a_m*ln(m)/m^2 at m=340000: %.5f (table value 0.37957)" % (am*math.log(m)/m**2))

with open(os.path.join(HERE, 'analysis_light_output.txt'), 'w') as f:
    f.write('\n'.join(OUT) + '\n')
p("\n[written: analysis_light_output.txt]")
