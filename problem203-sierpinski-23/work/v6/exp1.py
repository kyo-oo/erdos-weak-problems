"""exp1.py — the 5040-core (pure-prime) greedy experiment + residual structure.

Fact: the L=55440 family = 31 pure primes (h | 5040, no 11-part) + 21 with
11 | h. The pure primes carve the SAME coset in every 11-fiber; the core
cover problem (cover (Z_5040)^2 by the 31 pure cosets, budget 1.0214) is the
crux. This experiment: greedy (several orders) + residual histograms.
"""
import json, time, sys
import numpy as np

W6 = "/home/z/waves/w66-p203-k/problem203-sierpinski-23/work/v6/"
pal = json.load(open("/home/z/waves/w66-p203-k/problem203-sierpinski-23/pal_dlog_full.json"))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3]), int(r[4]), int(r[5])) for r in pal]

L = 5040
fam = [r for r in pal if L % r[1] == 0]
fam.sort(key=lambda r: -1.0 / r[1])
print(f"pure family (h|5040): {len(fam)} primes, budget {sum(1.0/r[1] for r in fam):.4f}")

ks = np.arange(L, dtype=np.int64)

def count_per_W(unc, h, U, V):
    """counts[W] = #uncovered cells (k,l) with (U*k+V*l)%h == W."""
    lmod = ks % h
    vals = (U * (ks % h)[:, None] + V * lmod[None, :]) % h   # (L,L)
    counts = np.bincount(vals.ravel()[unc.ravel()], minlength=h)
    return counts.astype(np.int64)

def apply_coset(unc, h, U, V, Wv):
    g = int(np.gcd(V, h)); hg = h // g
    rhs = (Wv - U * ks) % h
    ok = (rhs % g == 0) if g > 1 else np.ones(L, dtype=bool)
    if hg > 1:
        Vg = (V // g) % hg
        inv = pow(int(Vg), -1, int(hg))
    for k in np.nonzero(ok)[0]:
        l0 = ((int(rhs[k]) // g) * inv) % hg if hg > 1 else 0
        unc[k, l0::hg] = False

def greedy(order, tag):
    unc = np.ones((L, L), dtype=bool)
    layers = []
    t0 = time.time()
    for (q, h, U, V, o2, o3) in order:
        counts = count_per_W(unc, h, U, V)
        Wv = int(np.argmax(counts))
        if counts[Wv] == 0:
            layers.append((q, h, U, V, -1))
            continue
        apply_coset(unc, h, U, V, Wv)
        layers.append((q, h, U, V, Wv))
    rem = int(unc.sum())
    print(f"[{tag}] residual {rem} / {L*L} = {rem/(L*L)*100:.3f}%  ({time.time()-t0:.0f}s)")
    return layers, unc

# order 1: density-desc (the classic)
layers1, unc1 = greedy(fam, "density-desc")

# order 2: density-asc (small cosets first)
layers2, unc2 = greedy(list(reversed(fam)), "density-asc")

# residual structure histogram of the best
best_unc = unc1 if unc1.sum() <= unc2.sum() else unc2
rem = int(best_unc.sum())
print(f"\nbest residual {rem} ({rem/(L*L)*100:.3f}%)")

# per-component histograms of the residual
comps = [(2, 4), (3, 2), (5, 1), (7, 1)]
for (p, a) in comps:
    m = p ** a
    km = ks % m
    H = np.zeros((m, m), dtype=np.int64)
    idx = np.nonzero(best_unc)
    Hn = np.bincount(km[idx[0]] * m + km[idx[1]], minlength=m*m).reshape(m, m)
    print(f"residual histogram mod {m}^2 (rows k%{m}, cols l%{m}):")
    print(Hn)
    print(f"  min/max cell: {Hn.min()} {Hn.max()}   expected-if-uniform {rem/(m*m):.0f}")
