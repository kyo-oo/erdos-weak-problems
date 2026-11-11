# #939 r=4 escalation: a+b=c all 4-powerful, pairwise coprime — hunt to 10^15.
# Escalation of hunt939.py (10^13, zero). Bitmask coprimality + sorted-pair scan.
import sys, time
from sympy import primerange, factorint

LIMIT = 10 ** 15
t0 = time.time()

# 4-powerful numbers: n = prod p^(4 e_p), e_p >= 1  (i.e. powerful-of-order-4)
primes = list(primerange(2, int(LIMIT ** 0.25) + 2))
pid = {p: i for i, p in enumerate(primes)}

rpow = []
masks = []


def gen(idx, val, mask):
    if val > LIMIT:
        return
    if val > 1:
        rpow.append(val)
        masks.append(mask)
    for i in range(idx, len(primes)):
        p = primes[i]
        q = p ** 4
        if val * q > LIMIT:
            break
        m = mask | (1 << i)
        v = val * q
        while v <= LIMIT:
            gen(i + 1, v, m)
            v *= q


gen(0, 1, 0)
order = sorted(range(len(rpow)), key=lambda i: rpow[i])
rpow = [rpow[i] for i in order]
masks = [masks[i] for i in order]
rpset = set(rpow)
print(f"{len(rpow)} 4-powerful numbers <= 10^15 (gen {time.time()-t0:.1f}s)", flush=True)

hits = []
n = len(rpow)
checked = 0
for i in range(n):
    a = rpow[i]
    ma = masks[i]
    if a * 2 > LIMIT:
        break
    for j in range(i + 1, n):
        b = rpow[j]
        c = a + b
        if c > LIMIT:
            break
        if ma & masks[j]:
            continue
        checked += 1
        if c in rpset:
            # gcd(c,a)=gcd(a+b,a)=gcd(b,a)=1 — pairwise automatic
            hits.append((a, b, c))
            print(f"HIT: {a} + {b} = {c}", flush=True)
print(f"coprime pairs summed: {checked}")
print(f"HITS: {len(hits)}")
print("HUNT939B:", "WITNESS" if hits else "ZERO <= 10^15", flush=True)
print(f"total {time.time()-t0:.1f}s")
