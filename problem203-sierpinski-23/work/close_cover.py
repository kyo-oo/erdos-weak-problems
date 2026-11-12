"""Close the Sierpinski 2*3 covering over Z_L^2 (L=10080) via greedy coset layers.

Family: famL10080.json [q, h, U, V] — primes dividing gcd(2^L-1, 3^L-1).
Greedy: order primes by 1/h desc; per prime pick the coset W maximizing newly
covered mass; iterate until uncovered = 0. Output: the certificate layers.
Then CRT m (m = -g^{-W} mod q per prime; m = 1 mod 6; m > max q) and verify.
"""
import json, math, time
import numpy as np

L = 10080
fam = json.load(open("famL10080.json"))
fam = [(int(q), int(h), int(U), int(V)) for (q, h, U, V) in fam]
# keep only pairwise-coprime moduli bases? For CRT we need pairwise coprime q's
# (distinct prime powers of same base p are coprime only if consecutive powers
# are not both used). Filter: one entry per prime base (highest power wins ties
# by budget). Actually fam entries are q = p^e for distinct p mostly; check.
bases = {}
for (q, h, U, V) in fam:
    # find the prime base by trial division (q itself prime or prime power)
    p = q
    for d in range(2, int(q**0.5) + 1):
        if q % d == 0:
            p = d
            break
    if p not in bases or 1.0 / h > 1.0 / bases[p][1]:
        bases[p] = (q, h, U, V)
fam = sorted(bases.values(), key=lambda r: (-1.0 / r[1], r[0]))
print(f"family (distinct bases): {len(fam)} primes, budget={sum(1.0/r[1] for r in fam):.4f}")

ks = np.arange(L, dtype=np.int64)
# coverage bitmap over (k, l) in [0,L)^2 -- chunked over k to save memory
CH = 512
layers = []   # (q, h, U, V, W)
uncovered_cols = [np.ones(L, dtype=bool) for _ in range(0)]  # placeholder

def col_chunk_indices():
    for a in range(0, L, CH):
        yield a, min(a + CH, L)

def count_per_W(h, U, V):
    """for each W in [0,h): count of uncovered cells (Uk+Vl=W mod h)"""
    counts = np.zeros(h, dtype=np.int64)
    for a, b in col_chunk_indices():
        kc = ks[a:b]
        r = kc % h
        # table T[s] = (U*r + V*s) mod h over l mod h -- for each row k, the
        # cells' values are (U*r + V*s) mod h for s in [0,h); full l in [0,L)
        # each s repeats L//h times
        rep = L // h
        s = np.arange(h, dtype=np.int64)
        base = (U * r[:, None] + V * s[None, :]) % h  # (chunk, h)
        # uncovered mask for this chunk: shape (chunk, L)
        um = unc[a:b, :]
        # count uncovered cells by value: for each row, expand over l
        vals = np.repeat(base, rep, axis=1)  # (chunk, h*rep) = (chunk, L)
        # order: s-major repeat; vals[:, j] corresponds to l = j (since
        # l = s*rep + t? NO -- l in [0,L): l % h = l // (L/h)? careful:
        # l ranges [0,L); l mod h cycles with period h, NOT blocked.
        # Redo: vals must be (U*(k%h) + V*(l%h)) % h with l%h = l mod h.
        # Correct expansion: for l in [0,L): l % h = (l % h). Build directly.
        lmod = ks % h  # (L,) value l mod h
        vals2 = (U * r[:, None] + V * lmod[None, :]) % h  # (chunk, L)
        # mask by uncovered
        m = vals2[um]
        counts += np.bincount(m, minlength=h)
    return counts

# full uncovered bitmap (L, L) bool = 10080^2 = 100MB -- ok
unc = np.ones((L, L), dtype=bool)
total = L * L
t0 = time.time()
for (q, h, U, V) in fam:
    if not unc.any():
        break
    counts = count_per_W(h, U, V)
    W = int(np.argmax(counts))
    if counts[W] == 0:
        continue
    layers.append((q, h, U, V, W))
    # apply the chosen coset: mark covered
    for a, b in col_chunk_indices():
        kc = ks[a:b]
        r = kc % h
        lmod = ks % h
        vals = (U * r[:, None] + V * lmod[None, :]) % h
        unc[a:b, :][vals == W] = False
    print(f"  layer q={q:6d} h={h:5d} W={W:5d} newly covered {counts[W]:10d} "
          f"remaining {int(unc.sum()):10d} ({time.time()-t0:.0f}s)")

rem = int(unc.sum())
print(f"REMAINING UNCOVERED: {rem}")
if rem == 0:
    print("COVERING CLOSED with", len(layers), "layers")
    json.dump(layers, open("covering_closed.json", "w"))
else:
    # fall back: try also merging the fam5040 extra primes
    print("NOT closed — needs family extension")
    json.dump(layers, open("covering_partial.json", "w"))
