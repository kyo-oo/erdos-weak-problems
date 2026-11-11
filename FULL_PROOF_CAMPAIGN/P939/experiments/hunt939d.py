# P939 STRIKE C — the r=4 ESCALATION to 10^16 (the corrected engine, fast divlists),
# + decade-level pair/expectation stats + the numeric receipts of the algebraic lane.
# Engine = hunt939c.py with the divlist construction inverted (O(N*omega) not O(P*N)).
import time, math, bisect
import numpy as np
from sympy import primerange

t0 = time.time()
LIMIT = 10 ** 16
r = 4

primes = list(primerange(2, int(LIMIT ** (1.0 / r)) + 2))
vals, psets = [], []
def gen(idx, val, ps):
    if val > 1:
        vals.append(val); psets.append(tuple(ps))
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
vals = [vals[i] for i in order]; psets = [psets[i] for i in order]
N = len(vals)
V = np.array(vals, dtype=np.int64)
print(f"[r=4] {N} 4-powerful numbers <= 10^16  (gen {time.time()-t0:.1f}s)", flush=True)

# decade counts + densities
K = 16
Ndec = [bisect.bisect_right(vals, 10 ** k) for k in range(0, K + 1)]
dens = np.zeros(K)
for k in range(K):
    dens[k] = (Ndec[k + 1] - Ndec[k]) / (10 ** (k + 1) - 10 ** k)
print("decade counts:", " ".join(f"{k}:{Ndec[k]}" for k in range(10, K + 1)), flush=True)

# fast inverted divlists
maxp = max(max(s) for s in psets if s) + 1
div = [[] for _ in range(maxp)]
for j, ps in enumerate(psets):
    for pid in ps:
        div[pid].append(j)
dl = [np.array(d, dtype=np.int64) for d in div]

hits = []
coprime_pairs = 0
total_pairs = 0
E_unif = 0.0
E_dec = np.zeros(K)
pairs_dec = np.zeros(K)
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
        d = dl[pid]
        d = d[d < cutoff]
        mask[d] = False
    idx = np.flatnonzero(mask)
    total_pairs += cutoff - (i + 1)
    if len(idx) == 0:
        continue
    coprime_pairs += len(idx)
    sums = V[idx] + a
    dec = np.minimum(np.floor(np.log10(sums.astype(np.float64))), K - 1).astype(np.int64)
    dc = dens[dec]
    E_unif += float(dc.sum())
    E_dec += np.bincount(dec, weights=dc, minlength=K)
    pairs_dec += np.bincount(dec, minlength=K)
    pos = V.searchsorted(sums)
    pos[pos >= N] = 0
    ok = V[pos] == sums
    if ok.any():
        for j, s in zip(idx[ok], sums[ok]):
            hits.append((a, int(vals[j]), int(s)))
            print(f"HIT: {a} + {int(vals[j])} = {s}", flush=True)

print(f"pairs with sum<=10^16: {total_pairs:,}, coprime: {coprime_pairs:,}")
print(f"HITS: {len(hits)}")
print(f"VERDICT[4,10^16]: " + ("WITNESS FOUND" if hits else "ZERO"), flush=True)
print(f"E_unif(<=10^16, decade densities) = {E_unif:.4f}")
print("E by decade k=2..15:", " ".join(f"{k}:{E_dec[k]:.4f}" for k in range(2, 16)))
print("coprime pairs by decade k=2..15:", " ".join(f"{k}:{int(pairs_dec[k]):,}" for k in range(2, 16)))
print(f"total {time.time()-t0:.1f}s", flush=True)

# ---- numeric receipts of the algebraic lane (Template A + the r=3 kernel equation) ----
print("\n=== TEMPLATE A WIRING RECEIPT (2-covering of the square-hypotenuse sub-case) ===")
# d1 x^4 + d2 y^4 = z^2  -->  E_{d1d2}: V^2 = U^3 - 4 d1 d2 U,  U = 2(v + u^2), V = 2uU
d1, d2, x, y, z, u, v = 1, 8, 1, 1, 3, 1, 3
U, V = 2 * (v + u * u), 2 * u * 2 * (v + u * u)
ok_quartic = d1 * x ** 4 + d2 * y ** 4 == z * z
ok_curve = V * V == U ** 3 - 4 * d1 * d2 * U
print(f"quartic {d1}*{x}^4 + {d2}*{y}^4 = {z}^2 : {ok_quartic}")
print(f"E_{{{d1*d2}}}: V^2 = U^3 - {4*d1*d2}U at (U,V)=({U},{V}): "
      f"{V}^2 = {V*V} vs {U}^3 - {4*d1*d2}*{U} = {U**3 - 4*d1*d2*U} : {ok_curve}")
print("=== r=3 KERNEL EQUATION RECEIPT (the certified witness, kernel triple (1,9,1)) ===")
print(f"271^3 + 9*438^3 = {271**3} + {9*438**3} = {271**3 + 9*438**3} = 919^3 : "
      f"{271**3 + 9*438**3 == 919**3}")
