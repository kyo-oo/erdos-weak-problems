#!/usr/bin/env python3
"""w66_feas.py v2 — THE FORCED-OVERLAP FEASIBILITY LAW + SUBSET-SCAN (W66).

LAW (pair level): for primes p,q with cosets C_p, C_q (cosets of ker phi_p,
index h_p), C_p ∩ C_q is a coset of Lambda_p ∩ Lambda_q, NONEMPTY iff
(W_p, W_q) ∈ image(phi_p, phi_q) — and |image| = h_p h_q / s with
s = [Z^2 : Lambda_p + Lambda_q] = gcd of the six 2x2 minors of the 2x4
generator matrix.  s = 1  <=>  EVERY (W_p, W_q) compatible  <=>  the pair
ALWAYS overlaps by exactly 1/(h_p h_q) of the torus: FORCED waste.

LAW (waste floor, rigorous): waste = sum_x (c(x) - 1) over cells, c = cover
count.  waste = S_pairs - S_triples + S_quads - ... >= S_pairs - S_triples
>= W_forced - T_max, where T_max = sum over ALL triples of the maximal
triple-intersection size 1/[Z^2 : Lambda_i ∩ Lambda_j ∩ Lambda_k].

VERDICT: covering exists => waste <= budget - 1 = slack.  Hence
    W_forced(S) - T_max(S) > budget(S) - 1  =>  NO COVERING for subset S.
The SUBSET-SCAN greedily maximizes margin(S) = budget-1 - W_forced + T_max
over subsets S of each frame's family (drop the forced-waste-heavy primes).
max over S of margin(S) <= 0 => the whole free-coset frame is DEAD.
"""
import json, math, os, sys, itertools
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w66_lib import kernel_lattice, hnf_rows, lat_intersect, lat_index, six_minor_s

HERE = os.path.dirname(os.path.abspath(__file__))

def gen_and_dlogs(q, o2, o3, h):
    H = {1: (0, 0)}
    seen = {1}
    stack = [1 % q]
    while stack:
        v = stack.pop()
        for base, d in ((2, (1, 0)), (3, (0, 1))):
            w = v * base % q
            if w not in seen:
                seen.add(w)
                H[w] = (H[v][0] + d[0], H[v][1] + d[1])
                stack.append(w)
    if len(seen) != h:
        return None
    fh = {}
    x = h
    d = 2
    while d * d <= x:
        while x % d == 0:
            fh[d] = fh.get(d, 0) + 1
            x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        fh[x] = fh.get(x, 0) + 1
    for v in H:
        if v == 1:
            continue
        o = h
        for p in fh:
            while o % p == 0 and pow(v, o // p, q) == 1:
                o //= p
        if o == h:
            tbl = {}
            cur = 1
            for i in range(h):
                tbl[cur] = i
                cur = cur * v % q
            if 2 % q in tbl and 3 % q in tbl:
                return (q, h, tbl[2 % q], tbl[3 % q], o2, o3)
    return None

def frame_analysis(L, verbose=True):
    pal = {int(k): v for k, v in json.load(open(os.path.join(HERE, "w66_deep.json"))).items()}
    rows = [r for r in pal.values() if L % r[3] == 0]
    full = []
    for r in rows:
        q, o2, o3, h, src = r
        f = gen_and_dlogs(q, o2, o3, h)
        if f is None:
            print(f"  !! no generator for q={q} h={h}")
            continue
        full.append(f)
    n = len(full)
    h_arr = np.array([r[1] for r in full], dtype=np.float64)
    h_inv = 1.0 / h_arr
    B = float(h_inv.sum())
    lats = [hnf_rows(list(kernel_lattice(r[2], r[3], r[1])[0]),
                     list(kernel_lattice(r[2], r[3], r[1])[1])) for r in full]
    # pair table: s_{ij}, forced weights
    SP = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        Li = lats[i]
        bi = kernel_lattice(full[i][2], full[i][3], full[i][1])
        for j in range(i + 1, n):
            bj = kernel_lattice(full[j][2], full[j][3], full[j][1])
            s = six_minor_s(bi[0], bi[1], bj[0], bj[1])
            SP[i, j] = SP[j, i] = s
    hh = np.outer(h_arr, h_arr)
    FORCEDW = np.where(SP == 1, 1.0 / np.maximum(hh, 1), 0.0)
    np.fill_diagonal(FORCEDW, 0.0)
    Wforced_full = float(FORCEDW.sum() / 2)
    # triple table: 1/index3 for all triples (max triple-intersection size)
    T3 = np.zeros((n, n, n), dtype=np.float64)
    for i in range(n):
        for j in range(i + 1, n):
            Lij = lat_intersect(lats[i], lats[j])
            for k in range(j + 1, n):
                Lijk = lat_intersect(Lij, lats[k])
                w3 = 1.0 / lat_index(Lijk)
                T3[i, j, k] = T3[i, k, j] = T3[j, i, k] = T3[j, k, i] = \
                T3[k, i, j] = T3[k, j, i] = w3
    Tmax_full = float(T3.sum() / 6)
    if verbose:
        print(f"L={L}: fam={n} budget={B:.4f} slack={B-1:.4f}")
        print(f"  W_forced={Wforced_full:.4f}  T_max={Tmax_full:.4f}  floor={Wforced_full-Tmax_full:.4f}")
        dead = (Wforced_full - Tmax_full) > (B - 1)
        print(f"  full-family verdict: {'RIGOROUSLY DEAD' if dead else 'inconclusive (pair floor below slack)'}")
    # ---------------- SUBSET SCAN: maximize margin ----------------
    # margin(S) = (B(S)-1) - W_forced(S) + T_max(S); incremental greedy.
    mask = np.zeros(n, dtype=bool)
    marg = -1.0
    order = sorted(range(n), key=lambda i: -1.0 / full[i][1])

    def deltas(c, msk):
        """(dB, dW, dT) of ADDING c to the masked set."""
        dB = 1.0 / full[c][1]
        dW = float(FORCEDW[msk, c].sum())
        dT = float(msk @ T3[:, :, c] @ msk) / 2.0
        return dB, dW, dT

    for _ in range(600):
        improved = False
        # ADD phase: best candidate by delta margin
        best = None
        for c in order:
            if mask[c]:
                continue
            dB, dW, dT = deltas(c, mask)
            dm = dB - dW + dT
            if dm > 1e-12 and (best is None or dm > best[0]):
                best = (dm, c)
        if best:
            mask[best[1]] = True
            marg += best[0]
            improved = True
        # PRUNE phase: remove if margin improves
        for c in range(n):
            if not mask[c]:
                continue
            m2 = mask.copy()
            m2[c] = False
            dB, dW, dT = deltas(c, m2)   # what adding c BACK would give
            # margin(S - c) = margin(S) - (dB - dW + dT)
            dm = dB - dW + dT
            if marg - dm > marg + 1e-12:
                mask[c] = False
                marg -= dm
                improved = True
        if not improved:
            break
    S = [i for i in range(n) if mask[i]]
    best_margin = marg
    if verbose:
        b_S = float(h_inv[S].sum()) if len(S) else 0.0
        idxs = sorted(S)
        w_S = FORCEDW[np.ix_(idxs, idxs)].sum() / 2 if len(idxs) > 1 else 0.0
        t_S = T3[np.ix_(idxs, idxs, idxs)].sum() / 6 if len(idxs) >= 3 else 0.0
        print(f"  BEST SUBSET: |S|={len(S)} budget={b_S:.4f} (slack {b_S-1:.4f}) "
              f"W_forced={w_S:.4f} T_max={t_S:.4f} => margin={best_margin:+.4f}")
        print(f"  members: {[(full[i][0], full[i][1]) for i in idxs]}")
        verdict = "ALIVE SUBSET FOUND" if best_margin > 0 else "no alive subset (frame class DEAD)"
        print(f"  SUBSET VERDICT: {verdict}")
    return {"L": L, "n": n, "budget": B, "W_forced": Wforced_full,
            "T_max": Tmax_full, "best_margin": best_margin,
            "best_subset": sorted(S)}

if __name__ == "__main__":
    out = []
    for L in (27720, 55440, 720720, 2162160, 12252240):
        out.append(frame_analysis(L))
        print()
    json.dump(out, open(os.path.join(HERE, "w66_feas.json"), "w"), default=int)
    print("wrote w66_feas.json")
