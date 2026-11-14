"""validate_v6.py — cross-check the v6 fiber engine against the KNOWN residual.

state27720all.json: 35 layers [q,h,U,V,W] at L=27720, the banked anneal state,
residual EXACTLY 218794308 (verify_v5_preflight.log, count-map ground truth).
The v6 engine (CORE=2520, P=11) must reproduce this number exactly.
"""
import json, sys
import numpy as np

W_DIR = "/home/z/waves/w66-p203-k/problem203-sierpinski-23/work/v6/"
sys.path.insert(0, W_DIR)
L = 27720
P = 11
CORE = L // P  # 2520

layers = json.load(open("/home/z/waves/w66-p203-k/problem203-sierpinski-23/work/state27720all.json"))
layers = [tuple(l) for l in layers]
core_layers = [l for l in layers if CORE % l[1] == 0]
p_layers = [l for l in layers if l[1] % P == 0 and CORE % (l[1] // P) == 0]
print(f"35 layers -> {len(core_layers)} core + {len(p_layers)} p-primes")

ks = np.arange(CORE, dtype=np.int64)

def coset_row_indices(h, U, V, Wv):
    g = int(np.gcd(V, h)); hg = h // g
    rhs = (Wv - U * ks) % h
    ok = (rhs % g == 0) if g > 1 else np.ones(CORE, dtype=bool)
    if hg > 1:
        Vg = (V // g) % hg
        inv = pow(int(Vg), -1, int(hg))
    else:
        inv = 0
    for a in np.nonzero(ok)[0]:
        l0 = ((int(rhs[a]) // g) * inv) % hg if hg > 1 else 0
        yield int(a), l0, hg

def carve_bool(Z, h, U, V, Wv):
    for a, l0, hg in coset_row_indices(h, U, V, Wv):
        Z[a, l0::hg] = False

core_count = np.zeros((CORE, CORE), dtype=np.int8)
for (q, h, U, V, Wv) in core_layers:
    for a, l0, hg in coset_row_indices(h, U, V, Wv):
        core_count[a, l0::hg] += 1

pchoice = {}
for (q, h, U, V, Wv) in p_layers:
    m = h // P
    pchoice[q] = (Wv % m, Wv % P)

Z = (core_count == 0)
total = 0
for j1 in range(P):
    for j2 in range(P):
        Zj = Z.copy()
        for (q, h, U, V, Wv) in p_layers:
            m = h // P
            w0, w11 = pchoice[q]
            if (U * j1 + V * j2) % P == w11:
                carve_bool(Zj, m, U, V, w0)
        total += int(Zj.sum())
print(f"v6 fiber residual: {total}")
print(f"expected (banked): 218794308")
print("MATCH" if total == 218794308 else "MISMATCH")
