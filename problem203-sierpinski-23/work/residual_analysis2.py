"""Residual structure analysis v2 — chunked bincount (one pass per d)."""
import numpy as np

L = 55440
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
unc = np.load(W + "unc55440.npy")
ks = np.arange(L, dtype=np.int64)
CH = 1024
overall = 1.063 / 100.0

for d in [4, 9, 11, 5, 7]:
    if L % d:
        continue
    km = (ks % d).astype(np.int16)
    grid = np.zeros(d * d, dtype=np.int64)
    tot = np.zeros(d * d, dtype=np.int64)
    for a in range(0, L, CH):
        b = min(a + CH, L)
        kc = km[a:b]
        code = (kc[:, None].astype(np.int32) * d + km[None, :].astype(np.int32)).astype(np.int32)
        seg = unc[a * L // 8:(b * L + 7) // 8]
        bits = np.unpackbits(seg, bitorder='little')[: (b - a) * L].reshape(b - a, L)
        resw = bits.ravel().astype(np.int32)  # 0/1 int32
        grid += np.bincount(code.ravel(), weights=resw, minlength=d * d).astype(np.int64)
        tot += np.bincount(code.ravel(), minlength=d * d).astype(np.int64)
        del code, bits, resw
    frac = (grid / np.maximum(tot, 1)).reshape(d, d)
    print(f"d={d}: overall {grid.sum()/tot.sum():.5f}")
    for i in range(d):
        print("  ", " ".join(f"{frac[i,j]:.4f}" for j in range(d)))
    hot = frac.max(); cold = frac.min()
    print(f"  max {hot:.4f} ({hot/overall:.1f}x) min {cold:.4f} ({cold/overall:.2f}x)")
