#!/usr/bin/env python3
"""W66-P306-D — THE OBSTRUCTION FRAME (analysis engine).

Question: which of the 8-12 near-unit remainders are STRUCTURALLY impossible
under the campaign's D-class law (denominators p*q, p<q primes, distinct),
and which are merely engine-hard?

Layers computed here (all python-verified):
  L0  the 2-term kill re-derivation (kernel's quarter_kill, independent)
  L1  the general SQUAREFREE-B LAW (any term count): reduced denominator of
      any distinct-D-class reciprocal sum is squarefree  ->  the complete
      impossible family inside b<=30 is exactly the non-squarefree-b box
  L2  the PRIME-ANCHOR LAW: every prime r | b divides some denominator
      (mod-r argument on the lcm equation)  ->  verified on every audited
      receipt; necessary condition for the remainders
  L3  the 2-ADIC PARITY LAW for even b (the count of even denominators mod 2)
  L4  the AMICABLE-TRIPLE BANK: all (u,v,w), u<v<w primes, u*v*w = x(u+v+w)
      for x <= 30 — the disjoint 1/x inventory for the peel machinery
  L5  the DENSITY CAGE: window pair-density D(X); for each near-unit target
      the minimal window with D(X) >= T; complement granularity feasibility
      (complement value >= smallest window pair value)
  L6  the PEEL STARVATION CAGE: fresh-chunk prime budget required per piece
      vs the global availability  ->  which near-units cannot close via
      disjoint-window peels and WHY
"""
import json, re
from fractions import Fraction
from math import gcd, isqrt, prod
from sympy import primerange

PRIMES = list(primerange(2, 2000))
PSET = set(PRIMES)

def trial_factors(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f.append(n)
    return f

def squarefree(n):
    f = trial_factors(n)
    return len(f) == len(set(f))

def divisors(n):
    ds = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            ds.append(d)
            if d != n // d:
                ds.append(n // d)
    return sorted(ds)

# ---------------- receipts (all audited + banked so far) ----------------
def load_receipts():
    rec = {}
    for line in open("../EVIDENCE_306.txt"):
        m = re.match(r"^(\d+)/(\d+)\s*=\s*(.+)$", line.strip())
        if not m:
            continue
        rec[(int(m.group(1)), int(m.group(2)))] = [int(x) for x in re.findall(r"1/(\d+)", m.group(3))]
    try:
        w63 = json.load(open("EVIDENCE_306_W63.json"))
        for k, v in w63["done"].items():
            a, b = map(int, k.split("/"))
            rec.setdefault((a, b), v)
    except Exception:
        pass
    try:
        w66 = json.load(open("EVIDENCE_306_W66D.json"))
        for k, v in w66["done"].items():
            a, b = map(int, k.split("/"))
            rec[(a, b)] = v
    except Exception:
        pass
    return rec

R = load_receipts()
print(f"[receipts loaded] {len(R)}")

# ---------------- L0: the two-term kill, independent ----------------
print("\n=== L0: two-term kills (independent re-derivation) ===")
for (a, b) in [(1, 4), (3, 4), (1, 2), (1, 8), (3, 8)]:
    sols = []
    # a/b = 1/n + 1/m  <=>  a*n*m = b*(n+m)
    # for a=1,b=4: (n-4)(m-4)=16 ; general: multiply out
    for n in range(2, 4000):
        # a/b - 1/n = (a*n - b)/(b*n) = 1/m  =>  m = b*n/(a*n - b)
        num = a * n - b
        if num <= 0:
            continue
        if (b * n) % num == 0:
            m = (b * n) // num
            if m > n:
                f = trial_factors(m)
                if len(f) == 2 and f[0] != f[1] and m != n:
                    fn = trial_factors(n)
                    if len(fn) == 2 and fn[0] != fn[1]:
                        sols.append((n, m))
    print(f"  {a}/{b}: 2-term distinct D-class solutions: {sols if sols else 'NONE'}")

# ---------------- L1: the general squarefree-b law ----------------
print("\n=== L1: general squarefree-b law (computational) ===")
import random
random.seed(306)
ok = True
for trial in range(2000):
    k = random.randint(1, 6)
    dens = random.sample([p * q for i, p in enumerate(PRIMES[:40]) for q in PRIMES[:40][i + 1:]], k)
    s = sum(Fraction(1, n) for n in dens)
    if not squarefree(s.denominator):
        ok = False
        print("  COUNTEREXAMPLE", dens, s)
        break
print(f"  2000 random distinct-D-class sums: reduced denominator squarefree: {ok}")
non_sf = []
for b in range(2, 31):
    if squarefree(b):
        continue
    for a in range(1, b):
        if gcd(a, b) == 1:
            non_sf.append((a, b))
print(f"  non-squarefree-b reduced fractions <= 30 (the impossible family): "
      f"{len(non_sf)} e.g. {non_sf[:8]} ... incl. 1/4, 3/4")
sf = [(a, b) for b in range(2, 31) if squarefree(b) for a in range(1, b) if gcd(a, b) == 1]
print(f"  squarefree-b box (the reachable universe at b<=30): {len(sf)}")
assert len(sf) == 181

# ---------------- L2: the prime-anchor law ----------------
print("\n=== L2: prime-anchor law on all audited receipts ===")
viol = []
for (a, b), dens in R.items():
    for r in set(trial_factors(b)):
        if not any(n % r == 0 for n in dens):
            viol.append((a, b, r))
            break
print(f"  receipts checked: {len(R)}; anchor violations: {len(viol)} {viol[:5]}")
if not viol:
    print("  LAW HOLDS on every receipt: for each prime r | b, some denominator is r-divisible.")

# ---------------- L3: the 2-adic parity law ----------------
print("\n=== L3: 2-adic parity law (even b receipts) ===")
viol3 = []
for (a, b), dens in R.items():
    if b % 2:
        continue
    L = b
    for n in dens:
        L = L * n // gcd(L, n)
    even_ct = sum(1 for n in dens if n % 2 == 0)
    if even_ct % 2 != (a * (L // b)) % 2:
        viol3.append((a, b))
print(f"  even-b receipts checked: {sum(1 for (a, b) in R if b % 2 == 0)}; "
      f"parity violations: {len(viol3)} {viol3[:5]}")

# ---------------- L4: the amicable-triple bank ----------------
print("\n=== L4: amicable-triple bank (u<v<w primes, uvw = x(u+v+w)) ===")
BANK = {}
for x in range(2, 31):
    trs = []
    for u in [p for p in PRIMES if p < 60]:
        for v in [p for p in PRIMES if u < p < 200]:
            # w = x(u+v)/(uv - x)
            den = u * v - x
            if den <= 0:
                continue
            num = x * (u + v)
            if num % den:
                continue
            w = num // den
            if v < w and w in PSET:
                trs.append((u, v, w))
    if trs:
        BANK[x] = trs
for x in sorted(BANK):
    print(f"  1/{x}: {len(BANK[x])} triples: {BANK[x][:6]}{' ...' if len(BANK[x]) > 6 else ''}")
print(f"  x values with triples: {sorted(BANK)}")

# ---------------- L5: the density cage ----------------
print("\n=== L5: window density cage D(X) = sum 1/(pq) over pairs of primes<=X ===")
def D(X):
    W = [p for p in PRIMES if p <= X]
    s = Fraction(0)
    for i in range(len(W)):
        for j in range(i + 1, len(W)):
            s += Fraction(1, W[i] * W[j])
    return s
DTAB = {X: D(X) for X in [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]}
for X, d in DTAB.items():
    print(f"  D({X}) = {float(d):.4f}   ({len([p for p in PRIMES if p <= X])} primes, "
          f"{len([p for p in PRIMES if p <= X]) * (len([p for p in PRIMES if p <= X]) - 1) // 2} pairs)")

NEAR = [(9, 10), (10, 11), (12, 13), (13, 14), (14, 15), (15, 17), (16, 17),
        (16, 19), (17, 19), (18, 19), (19, 21), (20, 21), (28, 29), (29, 30), (22, 23)]
print("\n  near-unit cage check: minimal window with D(X) >= T; complement granularity:")
for (a, b) in NEAR:
    T = Fraction(a, b)
    need = None
    for X in sorted(DTAB):
        if DTAB[X] >= T and (X >= max(trial_factors(b))):
            need = X
            break
    if need is None:
        print(f"  {a}/{b}: NO window <= 71 hosts it (T={float(T):.4f} > D(71)) — peel-only")
        continue
    W = [p for p in PRIMES if p <= need]
    L = prod(W)
    total = DTAB[need] * L
    C = total - T * L
    minval = min(L // (W[i] * W[j]) for i in range(len(W)) for j in range(i + 1, len(W)))
    print(f"  {a}/{b} (T={float(T):.4f}): min window X={need}, complement C={float(C/L):.5f}·L "
          f"({'GRANULAR OK' if C >= minval else 'COMPLEMENT BELOW MIN PAIR (too small: no subset)'})")

# ---------------- L6: peel starvation cage ----------------
print("\n=== L6: peel starvation (fresh chunk budget per 1/b piece) ===")
def chunk_budget(b):
    """max number of pairwise-disjoint fresh chunks whose window
    primes(b)+chunk has pair density >= 1/b (coarse analytic bound)."""
    bs = trial_factors(b)
    cross = sum(Fraction(1, r) for r in set(bs))
    chunks, used = [], []
    pool = [p for p in PRIMES if p not in set(bs)]
    # greedy: take primes in order into chunks of 6
    idx = 0
    while idx + 6 <= len(pool) and len(chunks) < 30:
        ch = pool[idx:idx + 6]
        u = sum(Fraction(1, p) for p in ch)
        dens = (cross + u) * u  # ~ (sum)^2 - sq terms, generous
        if dens / 2 + cross * u >= Fraction(1, b):
            chunks.append(ch)
        used.append(ch)
        idx += 6
    return len(chunks)
for b in [10, 11, 13, 14, 15, 17, 19, 21, 23, 29, 30]:
    print(f"  1/{b}-piece: ~{chunk_budget(b)} disjoint fresh chunks rich enough (analytic "
          f"coarse bound; a-1..a pieces needed for (b-1)/b targets)")

print("\n[obstruction frame computations complete]")
