# P939 engine: CORRECT census + pairwise-coprime sum search for r-powerful numbers.
# Fixes the vacuous hunt939b.py (which only enumerated exponents == 0 mod 4,
# i.e. perfect r-th powers -> for r=4 it merely re-proved Fermat n=4).
#
# Usage: python3 hunt939c.py <r> <limit>
import sys, time
import numpy as np
from sympy import primerange

r = int(sys.argv[1]) if len(sys.argv) > 1 else 4
LIMIT = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 15
t0 = time.time()

# --- generate ALL r-powerful numbers <= LIMIT (every exponent e_p >= r) ---
primes = list(primerange(2, int(LIMIT ** (1.0 / r)) + 2))
vals = []       # value
psets = []      # tuple of dense prime indices

def gen(idx, val, ps):
    if val > 1:
        vals.append(val)
        psets.append(tuple(ps))
    for i in range(idx, len(primes)):
        p = primes[i]
        v = val * p ** r
        if v > LIMIT:
            break
        ps.append(i)
        while v <= LIMIT:
            gen(i + 1, v, ps)
            v *= p
        ps.pop()

gen(0, 1, [])
order = sorted(range(len(vals)), key=lambda i: vals[i])
vals = [vals[i] for i in order]
psets = [psets[i] for i in order]
N = len(vals)
V = np.array(vals, dtype=np.int64)
print(f"[{r}={r}] {N} r-powerful numbers <= {LIMIT}  (gen {time.time()-t0:.1f}s)", flush=True)
if r == 4:
    n4 = int((LIMIT) ** 0.25)
    print(f"  (perfect 4th powers alone: {n4 - 1 if int(round(n4**4))>LIMIT else n4}; "
          f"OLD vacuous census claimed 5622)", flush=True)

# --- prime -> sorted array of value-indices divisible by it ---
maxp = max((max(s) for s in psets if s), default=-1)
divlists = [None] * (maxp + 1)
for pid in range(maxp + 1):
    divlists[pid] = np.array([j for j in range(N) if pid in psets[j]], dtype=np.int64)

hits = []
coprime_pairs = 0
total_pairs = 0
for i in range(N):
    a = vals[i]
    if 2 * a > LIMIT:
        break
    cutoff = int(np.searchsorted(V, LIMIT - a, side='right'))
    if cutoff <= i + 1:
        continue
    mask = np.ones(cutoff, dtype=bool)
    mask[: i + 1] = False
    for pid in psets[i]:
        dl = divlists[pid]
        dl = dl[dl < cutoff]
        mask[dl] = False
    idx = np.flatnonzero(mask)
    total_pairs += cutoff - (i + 1)
    coprime_pairs += len(idx)
    if len(idx) == 0:
        continue
    sums = V[idx] + a
    pos = V.searchsorted(sums)
    pos[pos >= N] = 0
    ok = V[pos] == sums
    if ok.any():
        for j, s in zip(idx[ok], sums[ok]):
            hits.append((a, int(vals[j]), int(s)))
            print(f"HIT: {a} + {int(vals[j])} = {s}", flush=True)

print(f"pairs with sum<={LIMIT}: {total_pairs}, coprime: {coprime_pairs}")
print(f"HITS: {len(hits)}")
print(f"VERDICT[{r},{LIMIT}]: " + ("WITNESS FOUND" if hits else "ZERO"), flush=True)
print(f"total {time.time()-t0:.1f}s")
