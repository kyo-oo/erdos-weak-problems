#!/usr/bin/env python3
"""#708 W63-D1 census grinder v2: all 4-subsets A of [2..M2] with
max(A) = M in [M1..M2], windows t = 1..T, EXACT worst minB.
Chunk-safe: per-batch checkpoints (L75), resume. Window factorizations
cached per (M,t) — shared across all A with the same max.

Usage: census2 M1 M2 T [BATCH]
"""
import sys, json, os, time, math
from itertools import combinations

sys.set_int_max_str_digits(100000)
OUT = "/home/z/waves/w63-d1-p708/problem708-product-divisibility"
CKPT = os.path.join(OUT, "g4_census2_ckpt.json")


def factorize(n):
    fac = {}
    if n < 2:
        return fac
    d = 2
    while d * d <= n:
        while n % d == 0:
            fac[d] = fac.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fac[n] = fac.get(n, 0) + 1
    return fac


FCACHE = {}


def window_factors(M, t):
    key = (M, t)
    if key not in FCACHE:
        lo, hi = t + 1, t + M
        FCACHE[key] = [factorize(b) for b in range(lo, hi + 1)]
    return FCACHE[key]


def minB_from_wf(A, wfac):
    """Exact min |B| from precomputed window factorizations (DP take/skip)."""
    D = {}
    for a in A:
        for p, c in factorize(a).items():
            D[p] = D.get(p, 0) + c
    ps = sorted(D)
    k = len(ps)
    e = tuple(D[p] for p in ps)
    idx = {p: i for i, p in enumerate(ps)}
    cur = {e: 0}
    zero = (0,) * k
    for fb in wfac:
        v = [0] * k
        for p, c in fb.items():
            i = idx.get(p)
            if i is not None:
                v[i] = min(c, e[i])
        v = tuple(v)
        if not any(v):
            continue
        nxt = dict(cur)
        for s, c in cur.items():
            s2 = tuple(max(0, s[i] - v[i]) for i in range(k))
            if s2 == s:
                continue
            old = nxt.get(s2)
            if old is None or c + 1 < old:
                nxt[s2] = c + 1
        cur = nxt
    return cur[zero] if zero in cur else len(wfac) + 1


def main(M1, M2, T, BATCH=400):
    state = {"done": [], "rows": [], "max": 0, "maxA": None, "hist5": []}
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            state = json.load(f)
        print(f"[census2] resume: {len(state['done'])} batches done, "
              f"rows={len(state['rows'])} max={state['max']}", flush=True)
    t_start = time.time()
    for M in range(M1, M2 + 1):
        As = [sorted(S + (M,)) for S in combinations(range(2, M), 3)]
        for bi in range(0, len(As), BATCH):
            tag = f"{M}:{bi}"
            if tag in state["done"]:
                continue
            batch = As[bi:bi + BATCH]
            t0 = time.time()
            for A in batch:
                worst, wt = 0, None
                for t in range(1, T + 1):
                    wfac = window_factors(M, t)
                    s = minB_from_wf(A, wfac)
                    if s > worst:
                        worst, wt = s, t
                state["rows"].append({"A": A, "worst": worst, "t": wt})
                if worst > state["max"]:
                    state["max"] = worst
                    state["maxA"] = [A, wt]
                if worst >= 5:
                    state["hist5"].append([A, wt, worst])
                    print(f"[census2] !!! FORCING-{worst} FOUND: A={A} t={wt}",
                          flush=True)
            state["done"].append(tag)
            with open(CKPT, "w") as f:
                json.dump(state, f)
            print(f"[census2] M={M} batch {bi}:{bi+len(batch)}: "
                  f"{time.time()-t0:.1f}s (elapsed {time.time()-t_start:.0f}s) "
                  f"rows={len(state['rows'])} max={state['max']}", flush=True)
    dist = {}
    for r in state["rows"]:
        dist[r["worst"]] = dist.get(r["worst"], 0) + 1
    print(f"[census2] DONE: {len(state['rows'])} 4-sets, "
          f"worst-dist {dict(sorted(dist.items()))}")
    print(f"[census2] GLOBAL MAX over box (max(A) in [{M1},{M2}], t=1..{T}): "
          f"{state['max']} at {state['maxA']}")
    if state["hist5"]:
        print("[census2] g(4)>=5 WITNESSES:")
        for A, wt, w in state["hist5"]:
            print(f"   A={A} t={wt}: worst = {w}")


if __name__ == "__main__":
    M1 = int(sys.argv[1]); M2 = int(sys.argv[2]); T = int(sys.argv[3])
    B = int(sys.argv[4]) if len(sys.argv) > 4 else 400
    main(M1, M2, T, B)
