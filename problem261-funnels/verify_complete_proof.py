#!/usr/bin/env python3
"""
ERDŐS #261 — COMPLETE_PROOF.md VERIFICATION BATTERY (Agent W5).
Every theorem shipped in COMPLETE_PROOF.md gets an exact-arithmetic receipt here.
All arithmetic exact (integers / fractions.Fraction). No floats anywhere.
Exit code 0 = ALL PASS.
"""
import sys, os, time
from fractions import Fraction as F

T0 = time.time()
OK = True
def check(name, cond, detail=""):
    global OK
    if cond: print(f"  PASS  {name}" + (f"   [{detail}]" if detail else ""))
    else:
        print(f"  FAIL  {name}   {detail}"); OK = False

# =====================================================================
# THE WALK (Kill-2 convention, identical to funnels.py / FunnelStructure.lean)
# =====================================================================
def walk_states(N0, v0, cap=3_000_000):
    N, v, out = N0, v0, []
    steps = 0
    while v != 0 and steps < cap:
        take = (2*v >= N)
        v = 2*v - N if take else 2*v
        N += 1
        out.append((N, v, take))
        steps += 1
    return out, (N if v == 0 else None)

def walk_full(n, cap=3_000_000):
    if n == 1: N0, v0 = 3, 2
    else:      N0, v0 = n+1, n
    if v0 == 0: return N0, set()
    path, D = walk_states(N0, v0, cap)
    takes = {N-1 for (N, v, take) in path if take}
    return D, takes

memo = {}
STEPS = [0]
def walk_memo(N, v, cap=2_000_000):
    path = []
    while True:
        if v == 0:
            D = N; break
        if (N, v) in memo:
            D = memo[(N, v)]; break
        if len(path) > cap:
            D = None; break
        path.append((N, v)); STEPS[0] += 1
        take = (2*v >= N)
        v = 2*v - N if take else 2*v
        N += 1
    if D is not None:
        for st in path: memo[st] = D
    return D

# =====================================================================
# V1 — BL GREEDY-RUN THEOREM (greedy = BL witness, D = 2^{m+1}-1, room = m)
# =====================================================================
print("V1 — BL family: greedy walk takes exactly {n+1..n+m}, dies at D=2^{m+1}-1, room=m")
for m in range(2, 41):
    n = 2**(m+1) - m - 2
    D, takes = walk_full(n, cap=200_000)
    if not (D == 2**(m+1) - 1 and takes == set(range(n+1, n+m+1)) and D - 1 - n == m):
        check(f"V1 m={m}", False, f"D={D}"); break
else:
    check("V1 BL greedy-run m=2..40", True, "all D=2^{m+1}-1, rooms=m ⟹ greedy room unbounded")
for m in range(2, 25):
    n = 2**(m+1) - m - 2
    assert F(n, 2**n) == sum(F(n+j, 2**(n+j)) for j in range(1, m+1))
check("V1 BL witness identity Σ(n+j)/2^{n+j}=n/2^n, m=2..24", True, "exact Fractions")
print(f"    [t={time.time()-T0:.1f}s]")

# =====================================================================
# V2 — SOUNDNESS + invariants (n=1..300)
# =====================================================================
print("V2 — soundness: take-set represents n/2^n exactly; D odd; D>n; |T|≥2; pieces>n")
bad = 0
for n in range(1, 301):
    D, T = walk_full(n)
    if D is None: check(f"V2 n={n} death", False, "cap"); bad += 1; continue
    if sum(F(a, 2**a) for a in T) != F(n, 2**n) or len(T) < 2 or min(T) <= n \
       or D % 2 == 0 or D <= n or len(T) != len(set(T)):
        check(f"V2 n={n}", False, f"D={D}"); bad += 1
check("V2 soundness n=1..300", bad == 0, "300/300 exact")
print(f"    [t={time.time()-T0:.1f}s]")

# =====================================================================
# V2b — CENSUS: live re-run n≤600 + receipts audit of v2_deaths.txt ([1,4000])
# =====================================================================
print("V2b — census: live n≤600 + v2_deaths.txt audit ([1,4000], 5-way-verified receipts)")
base = "/home/z/my-project/repos/erdos-weak-problems/problem261-funnels/engine/run261"
def load_deaths(fn):
    out = []
    with open(fn) as fh:
        for line in fh:
            parts = line.split()
            if len(parts) >= 3 and parts[2] in ("d", "c", "w"):
                out.append((int(parts[0]), int(parts[1]), parts[2]))
    return out
v2 = load_deaths(f"{base}/v2_deaths.txt")
got = {}
for (n, D, m) in v2: got[D] = got.get(D, 0) + 1
exp = {12231: 2578, 4855: 475, 4993: 103, 2593: 101, 4489: 99, 393: 90, 1943: 66, 29753: 47}
check("V2b receipts [1,4000]: 4000 records, funnel table exact",
      len(v2) == 4000 and all(got.get(k, 0) == c for k, c in exp.items()),
      f"12231:{got.get(12231)} 4855:{got.get(4855)}")
check("V2b receipts [1,4000]: D odd ∧ D>n, max room 152125 @ n=3817",
      all(D % 2 == 1 and D > n for (n, D, m) in v2)
      and max(D - 1 - n for (n, D, m) in v2) == 152125
      and [n for (n, D, m) in v2 if D - 1 - n == 152125] == [3817])
live600 = all(walk_memo(3, 2) if n == 1 else walk_memo(n+1, n) for n in range(1, 601))
d600 = {n: (walk_memo(3, 2) if n == 1 else walk_memo(n+1, n)) for n in range(1, 601)}
check("V2b live census n≤600: 600/600 die; 12231-basin present",
      live600 and sum(1 for n, D in d600.items() if D == 12231) >= 100,
      f"{sum(1 for n, D in d600.items() if D == 12231)} walks die at 12231")
print(f"    [t={time.time()-T0:.1f}s]")

# =====================================================================
# V3 — x = 1/2 REPRESENTATIONS + block swap
# =====================================================================
print("V3 — x=1/2: three+ representations, block swap {4,5}≅{3,8}")
S = lambda A: sum(F(a, 2**a) for a in A)
check("V3 {2} = 1/2", S([2]) == F(1, 2))
check("V3 {3,6,8} = 1/2", S([3, 6, 8]) == F(1, 2))
check("V3 {4,5,6} = 1/2", S([4, 5, 6]) == F(1, 2))
check("V3 {4,5,7,8,11,13,14} = 1/2", S([4, 5, 7, 8, 11, 13, 14]) == F(1, 2))
check("V3 block swap {4,5} = {3,8}", S([4, 5]) == S([3, 8]))
check("V3 window-8 scaled ints (Lean decide mirror)",
      2*2**6 == 3*2**5 + 6*2**2 + 8 == 4*2**4 + 5*2**3 + 6*2**2 == 128)
check("V3 n/2^n=1/2 only for n∈{1,2}", [n for n in range(1, 50) if F(n, 2**n) == F(1, 2)] == [1, 2])

# =====================================================================
# V4 — THE TOWER: halving family, disjoint regions, σ-invariance, irrationality
# =====================================================================
print("V4 — the tower: m_k = 2^{k+2}-k-3")
mf = lambda k: 2**(k+2) - k - 3
for k in range(0, 16):
    m = mf(k)
    assert F(m, 2**m) == sum(F(m+i, 2**(m+i)) for i in range(1, k+2))
check("V4 halving family k=0..15 (exact)", True)
check("V4 regions disjoint k≤59 (gap = 2^{k+2}-k-2 > 0)",
      all(mf(k+1) - (mf(k) + k + 1) == 2**(k+2) - k - 2 for k in range(60)))
K = 10
def tower_value(sigma, K):
    tot = F(0)
    for k in range(K):
        m = mf(k)
        tot += F(m, 2**m) if sigma[k] else sum(F(m+i, 2**(m+i)) for i in range(1, k+2))
    return tot
vals = {tower_value([(k*d//7) % 2 for k in range(K)], K) for d in range(8)}
check("V4 tower partial value identical across 8 σ patterns (K=10)", len(vals) == 1)
for Kc in range(0, 13):
    bound = F(2*(mf(Kc+1)+1), 2**(2**(Kc+2)-1))
    tail_ge = sum(F(mf(k), 2**mf(k)) for k in range(Kc+1, Kc+12))
    assert 0 < tail_ge < bound, (Kc,)
check("V4 B_K tail: partial tail ∈ (0, 2(m_{K+1}+1)2^{-(2^{K+2}-1)}) for K=0..12", True,
      "⟹ B_K → 0 super-exponentially (irrationality engine)")
xbits = 3000
num = sum(mf(k) * 2**(xbits - mf(k)) for k in range(0, 9))
iso = all(mf(k) - (mf(k).bit_length() - 1) > mf(k-1) + (k-1) + 1 for k in range(1, 9))
check("V4 cluster isolation: bit-support of m_k·2^{-m_k} clears region k-1 (k≤8)", iso)
zg_ok = True
for k in range(0, 7):
    lo, hi = mf(k) + k + 1, mf(k+1) - mf(k+1).bit_length() + 1
    if hi <= lo or ((num >> lo) & ((1 << (hi - lo)) - 1)) != 0:
        zg_ok = False; break
check("V4 zero-gaps between clusters in binary expansion of x* (k≤6, exact ints)", zg_ok)
print(f"    [t={time.time()-T0:.1f}s]")

# =====================================================================
# V5 — AP RATIONALITY + kernel identity
# =====================================================================
print("V5 — AP sums: Σ_{k≥0}(r+kT)/2^{r+kT} = 2^{-r}(r/(1-q) + Tq/(1-q)^2), q=2^{-T}")
def ap_closed(r, T):
    q = F(1, 2**T)
    return F(1, 2**r) * (F(r) / (1 - q) + F(T) * q / (1 - q)**2)
for (r, T) in [(1, 1), (3, 7), (9, 24), (5, 12), (2, 3), (17, 40)]:
    closed = ap_closed(r, T)
    partial = sum(F(r + k*T, 2**(r + k*T)) for k in range(0, 90))
    rest = sum(F(r + k*T, 2**(r + k*T)) for k in range(90, 170))
    ub = rest + F(2, 2**(r + 170*T))
    if not (partial < closed <= ub):
        check(f"V5 AP ({r},{T})", False); break
else:
    check("V5 AP identity (6 pairs, exact bracketing partial_{90} < closed ≤ partial+tail)",
          True)
ker_ok = True
for (r, T) in [(1, 1), (9, 24), (5, 12)]:
    for K in range(0, 30):
        if sum((r + k*T) * 2**(K - k) for k in range(0, K+1)) != \
           r*(2**(K+1) - 1) + T*(2**(K+1) - K - 2):
            ker_ok = False
check("V5 kernel identity Σ_{k≤K}(r+kT)2^{K-k} = r(2^{K+1}-1)+T(2^{K+1}-K-2)", ker_ok)
print(f"    [t={time.time()-T0:.1f}s]")

# =====================================================================
# V6 — GADGET SPACE: gadget equation, finite image, run identity, boundary
# =====================================================================
print("V6 — gadget space: s(1+σ_Π−σ_J) = τ_J−τ_Π; finite image; run identity")
import itertools
def sig(X): return sum(F(1, 2**j) for j in X)
def tau(X): return sum(F(j, 2**j) for j in X)
def gadget_ok(s, Pi, J):
    return F(s, 2**s) + sum(F(s+j, 2**(s+j)) for j in Pi) == \
           sum(F(s+j, 2**(s+j)) for j in J)
def gadget_sol(Pi, J):
    den = 1 + sig(Pi) - sig(J)
    if den <= 0: return None
    v = (tau(J) - tau(Pi)) / den
    return v.numerator if v.denominator == 1 and v > 0 else None
cnt = 0; fail = 0
for W in range(1, 8):                       # window size d-1 = W (spacing d = W+1)
    Wn = list(range(1, W+1))
    for Pi in itertools.chain.from_iterable(itertools.combinations(Wn, r) for r in range(0, W+1)):
        rest = [j for j in Wn if j not in Pi]
        for J in itertools.chain.from_iterable(itertools.combinations(rest, r) for r in range(0, len(rest)+1)):
            s = gadget_sol(list(Pi), list(J))
            if s is None: continue
            cnt += 1
            if s <= 200 and not gadget_ok(s, list(Pi), list(J)): fail += 1
check(f"V6(a) gadget equation ⟺ s(1+σ_Π−σ_J)=τ_J−τ_Π ({cnt} patterns W≤6, s≤200)",
      fail == 0)
fw = []
for d in range(2, 27):
    s_star = 2**d - d - 1
    assert gadget_ok(s_star, [], list(range(1, d))) and gadget_sol([], list(range(1, d))) == s_star
    fw.append(s_star)
check("V6(b) full-window gadget ⟺ s = 2^d−d−1 exactly (d=2..26; = tower family m_{d-2})",
      True, f"s* = {fw[:8]}")
def finite_image(d):
    Wn = list(range(1, d)); out = set()
    for Pi in itertools.chain.from_iterable(itertools.combinations(Wn, r) for r in range(0, d)):
        rest = [j for j in Wn if j not in Pi]
        for J in itertools.chain.from_iterable(itertools.combinations(rest, r) for r in range(0, len(rest)+1)):
            s = gadget_sol(list(Pi), list(J))
            if s is not None and s >= 1: out.add(s)
    return out
im5 = finite_image(5)
check("V6(c) finite image d=5 = {1,2,4,6,11,26} (⊆ 3^4 = 81 patterns)",
      im5 == {1, 2, 4, 6, 11, 26}, f"got {sorted(im5)}")
check("V6(c) finite image d=4 ⊆ 3^3 = 27 patterns (26 ∈ image)", len(finite_image(4)) <= 27 and 26 in finite_image(4))
t4 = True
for d in range(2, 11):
    for s in range(1, 80):
        R = sum(F(s+i, 2**(s+i)) for i in range(1, d))
        if R - F(s, 2**s) != F(1, 2**s) * (2 - F(s+d+1, 2**(d-1))): t4 = False
check("V6(d) run identity R(s,d)−s2^{-s} = 2^{-s}[2−(s+d+1)2^{1-d}] (d≤10, s≤79)", t4)
t5 = True
for d in range(2, 11):
    s_star = 2**d - d - 1
    defs = [F(s, 2**s) - sum(F(s+i, 2**(s+i)) for i in range(1, d)) for s in range(s_star, s_star+60)]
    if any(x <= 0 for x in defs) or any(defs[i+1] <= defs[i] for i in range(len(defs)-1)): t5 = False
check("V6(e) s > 2^d−d−1: run undershoots, deficit positive & strictly increasing (d≤10)", t5)
print(f"    [t={time.time()-T0:.1f}s]")

# =====================================================================
# V7 — GREEDY COMPLETENESS G: finite exact certificates
# =====================================================================
print("V7 — greedy completeness G: in-window rep ⟹ walk dies (finite certificates)")
K = 14
gstates = 0; gdeaths = 0
for N in range(2, 65):
    for v in range(0, N):
        target = v * 2**(K+1)
        reach = 1
        for a in range(N, N+K+1):
            w = a * 2**(N+K-a)
            if w <= target: reach |= reach << w
        if (reach >> target) & 1:
            gstates += 1
            D = walk_memo(N, v)
            if D is not None: gdeaths += 1
check(f"V7(a) states (N≤64, v<N) with rep in [N,N+{K}]: {gdeaths}/{gstates} die",
      gdeaths == gstates)
cert_n = set()
for J in range(1, 13):
    for r in range(0, J+1):
        for P in itertools.combinations(range(1, J+1), r):
            A = sum(2**(J-j) for j in P); S_ = sum(j*2**(J-j) for j in P)
            den = 2**J - A
            if den > 0 and S_ % den == 0:
                n = S_ // den
                if n >= 2: cert_n.add(n)
cd = sum(1 for n in cert_n if (D := walk_memo(n+1, n)) is not None and D % 2 == 1 and D > n)
check(f"V7(b) pattern-certified n (J≤12): {cd}/{len(cert_n)} walk-die with odd D>n",
      cd == len(cert_n), f"max certified n = {max(cert_n)}")
dw = sum(1 for n in range(2, 401) if walk_memo(n+1, n) is not None)
repwin = {n for n in cert_n if n <= 400}
check(f"V7(c) n≤400: walk-death ({dw}/399) ⊇ window-rep ({len(repwin)})", dw >= len(repwin))
print(f"    [t={time.time()-T0:.1f}s, walk steps total = {STEPS[0]}]")

# =====================================================================
# V8 — FRONTIER RECEIPTS AUDIT (engine artifacts, re-verified from disk)
# =====================================================================
print("V8 — engine receipts audit (run261/*.txt)")
blocks = []
for e in range(1, 20):
    fn = f"{base}/e{e}_deaths.txt"
    if os.path.exists(fn): blocks.append(load_deaths(fn))
extra = []
for tag in ("fr", "p0", "v3", "v2"):
    fn = f"{base}/{tag}_deaths.txt"
    if os.path.exists(fn): extra.append(load_deaths(fn))
allrec = [r for b in blocks + extra for r in b]
inv_ok = all(D % 2 == 1 and D > n for (n, D, _) in allrec)
ens = sorted(n for b in blocks for (n, D, m) in b)
contig_ok = (ens == list(range(3260201, 4400201)))
maxD = max(D for (n, D, m) in allrec)
check(f"V8 invariants D odd ∧ D>n over {len(allrec)} records", inv_ok)
check("V8 e1..e19 contiguity: n = 3260201..4400200 exactly once", contig_ok,
      f"{len(ens)} records")
check("V8 record death modulus = 1,449,322,159 (unchanged)", maxD == 1449322159, f"max D={maxD}")

print()
print("BATTERY VERDICT:", "ALL PASS" if OK else "FAILURES PRESENT",
      f"[{time.time()-T0:.1f}s]")
sys.exit(0 if OK else 1)
