# P939 STRIKE A — witness certification + census growth law + the vacuous-sweep audit.
# (1) certify the r=3 witness 19902511 + 756249048 = 776151559 (full factorization,
#     exponent audit, pairwise-gcd audit, kernel decomposition display);
# (2) census growth law N_4(10^k), k = 8..15 + C4 fit;
# (3) consecutive 4-powerful pairs <= 10^15 (the a=1 lane);
# (4) audit the OLD vacuous sweeps (10^13: 1777 = #4th-powers; 10^15: 5622).
import time
from sympy import primerange, factorint, isprime

t0 = time.time()

# ---------- (1) r=3 witness certification ----------
A, B, C = 19902511, 756249048, 776151559
fa, fb, fc = factorint(A), factorint(B), factorint(C)
print("=== r=3 WITNESS CERTIFICATION ===")
print(f"{A} = " + " * ".join(f"{p}^{e}" for p, e in sorted(fa.items())))
print(f"{B} = " + " * ".join(f"{p}^{e}" for p, e in sorted(fb.items())))
print(f"{C} = " + " * ".join(f"{p}^{e}" for p, e in sorted(fc.items())))
r3_ok = (A + B == C
         and all(e >= 3 for e in fa.values()) and all(e >= 3 for e in fb.values())
         and all(e >= 3 for e in fc.values())
         and not (set(fa) & set(fb)) and not (set(fa) & set(fc)) and not (set(fb) & set(fc)))
print(f"sum check: {A} + {B} = {A+B} == {C}: {A+B == C}")
print(f"all exponents >= 3: {all(e>=3 for e in fa.values())}, {all(e>=3 for e in fb.values())}, {all(e>=3 for e in fc.values())}")
print(f"pairwise coprime: {not (set(fa)&set(fb))}, {not (set(fa)&set(fc))}, {not (set(fb)&set(fc))}")
print(f"VERDICT r3 witness: {'CERTIFIED' if r3_ok else 'FAILED'}")
# kernel decomposition (r=3): n = s * m^3, s cube-free, rad(s)|m
def kernel3(n, f):
    s, m = 1, 1
    for p, e in f.items():
        t = e % 3
        s *= p ** t
        m *= p ** ((e - t) // 3)
    return s, m
for name, n, f in (("a", A, fa), ("b", B, fb), ("c", C, fc)):
    s, m = kernel3(n, f)
    assert s * m ** 3 == n
    print(f"  {name} = {n} = kernel {s} * ({m})^3   (kernel primes {sorted(factorint(s))})")

# ---------- (2) census growth law ----------
LIMIT = 10 ** 15
primes = list(primerange(2, int(LIMIT ** 0.25) + 2))
vals = []
def gen(idx, val):
    if val > 1:
        vals.append(val)
    for i in range(idx, len(primes)):
        p = primes[i]
        v = val * p ** 4
        if v > LIMIT:
            break
        while v <= LIMIT:
            gen(i + 1, v)
            v *= p
gen(0, 1)
vals.sort()
print("\n=== CENSUS GROWTH LAW (4-powerful) ===")
print(f"N_4(10^15) = {len(vals)}  (gen {time.time()-t0:.1f}s)")
for k in range(8, 16):
    X = 10 ** k
    # count via generator is already all <= 10^15; use bisect
    import bisect
    n = bisect.bisect_right(vals, X)
    print(f"  N_4(10^{k}) = {n:7d}   N/X^(1/4) = {n / X**0.25:.4f}")
n4 = len(vals)
print(f"C4 (fit at 10^15) = {n4 / LIMIT**0.25:.4f}")
n4th = sum(1 for v in vals if round(v ** 0.25) ** 4 == v)
print(f"perfect 4th powers inside census: {n4th} (old vacuous census claimed 5622)")

# ---------- (3) consecutive 4-powerful pairs ----------
print("\n=== a=1 LANE: consecutive 4-powerful pairs <= 10^15 ===")
gaps1 = [(vals[i], vals[i+1]) for i in range(len(vals)-1) if vals[i+1] - vals[i] == 1]
print(f"count: {len(gaps1)}", gaps1[:5])

# ---------- (4) old sweep audit ----------
print("\n=== OLD SWEEP AUDIT ===")
for X, claim in ((10**13, 1777), (10**15, 5622)):
    m = int(X ** 0.25)
    while m ** 4 > X: m -= 1
    n_th = m - 1  # m = 2..m  (excluding 1)
    print(f"  claimed {claim} '4-powerfuls' <= 10^{int(round(__import__('math').log10(X)))}: "
          f"true count of PERFECT 4TH POWERS m^4 (m>=2): {n_th}  -> VACUOUS: {n_th == claim}")
print(f"total {time.time()-t0:.1f}s")
