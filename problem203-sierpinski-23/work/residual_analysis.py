"""Residual structure analysis for the L=55440 greedy covering.

The greedy placed all 52 members (1.063% residual, 32.68M cells).
The budget saturates ~1.25 at every L — more members won't close the tail.
This pass: WHERE do the uncovered cells live? Distribution over small
residue classes (k mod d, l mod d) for d | 55440, per-member reach.
"""
import json
import numpy as np

L = 55440
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
unc = np.load(W + "unc55440.npy")
bits = np.unpackbits(unc, bitorder='little')[: L * L].reshape(L, L)
res_mask = bits.view(bool)
total = int(res_mask.sum())
print(f"residual: {total} ({total/L/L*100:.3f}%)", flush=True)

ks = np.arange(L, dtype=np.int64)

for d in [2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 22, 35, 55, 77]:
    if L % d != 0:
        continue
    km = (ks % d)
    # per (k mod d, l mod d) residual density
    grid = np.zeros((d, d), dtype=np.int64)
    tot = np.zeros((d, d), dtype=np.int64)
    CH = 4096
    for a in range(0, L, CH):
        b = min(a + CH, L)
        kc = km[a:b]
        lm = km
        sub = res_mask[a:b, :]
        for i in range(d):
            for j in range(d):
                sel = sub[(kc == i)][:, lm == j]
                grid[i, j] += int(sel.sum())
                tot[i, j] += sel.size
    frac = np.where(tot > 0, grid / np.maximum(tot, 1), 0.0)
    # which cells are over/under-represented
    hot = np.argwhere(frac > 2.0 * total / (L * L))
    cold = np.argwhere(frac < 0.2 * total / (L * L))
    print(f"d={d:3d}: max {frac.max():.3f}, min {frac.min():.3f}, hot classes {len(hot)}/{d*d}, cold {len(cold)}/{d*d}", flush=True)
    if d in (4, 9, 11):
        print(frac.round(3).tolist(), flush=True)
