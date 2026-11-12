"""L=27720 ANNEALING engine — count-map + delta moves (S054).

The greedy stalled at 98.42% (1.58% residual) and single-moves found
zero gains (locally optimal). The annealer: int8 count-map (772MB),
moves = member W-changes evaluated by COSET-LOCAL deltas (no full scans):
  delta = +(cells leaving count==1 in old coset) - (cells at count==0 in new coset)
Accept if improves (greedy anneal; temperature rounds later if needed).
State: state27720all.json (layers) + count27720.npy (int8 map).
"""
import json, time, random
import numpy as np

L = 27720
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
pal = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/pal_dlog_full.json"))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]
fam = [r for r in pal if L % r[1] == 0]
fam.sort(key=lambda r: -1.0 / r[1])
FAM = {q: (h, U, V) for (q, h, U, V) in fam}

layers = json.load(open(W + "state27720all.json"))
wmap = {l[0]: l[4] for l in layers}

import os
if os.path.exists(W + "count27720.npy"):
    count = np.load(W + "count27720.npy")
    print("resumed count-map", flush=True)
else:
    count = np.zeros((L, L), dtype=np.int8)

    def add_coset(h, U, V, Wv, delta):
        # cells: U*k + V*l == Wv (mod h); row-wise arithmetic progressions
        g = np.gcd(V, h)
        step = h // g.item() if hasattr(g, 'item') else h // g
        # V*l === Wv - U*k (mod h) solvable iff g | (Wv - U*k)
        ks = np.arange(L, dtype=np.int64)
        rhs = (Wv - U * ks) % h
        ok = (rhs % g == 0) if g > 1 else np.ones(L, dtype=bool)
        # V/g invertible mod h/g
        Vg = (V // g) % (h // g)
        hg = h // g
        # inverse of Vg mod hg
        inv = pow(int(Vg), -1, int(hg)) if hg > 1 else 0
        idx_k = np.nonzero(ok)[0]
        for k in idx_k:
            l0 = ((rhs[k] // g) * inv) % hg if hg > 1 else 0
            row = count[k]
            ls = np.arange(l0, L, hg)
            row[ls] += delta
        return

    t0 = time.time()
    for l in layers:
        if l[4] >= 0:
            q, h, U, V, Wv = l
            add_coset(h, U, V, Wv, 1)
    print(f"count-map built: {time.time()-t0:.0f}s, residual {(count==0).sum()}", flush=True)
    np.save(W + "count27720.npy", count)

res0 = int((count == 0).sum())
print(f"residual: {res0} ({res0/L/L*100:.3f}%)", flush=True)
if res0 == 0:
    print("COVERING ALREADY CLOSED")
    raise SystemExit

def coset_cells(h, U, V, Wv):
    """yield (k, ls-array) rows of the coset."""
    g = int(np.gcd(V, h))
    hg = h // g
    ks = np.arange(L, dtype=np.int64)
    rhs = (Wv - U * ks) % h
    ok = (rhs % g == 0) if g > 1 else np.ones(L, dtype=bool)
    Vg = (V // g) % hg if hg > 1 else 0
    inv = pow(int(Vg), -1, int(hg)) if hg > 1 else 0
    idx_k = np.nonzero(ok)[0]
    for k in idx_k:
        l0 = ((int(rhs[k]) // g) * inv) % hg if hg > 1 else 0
        ls = np.arange(l0, L, hg)
        yield k, ls

def delta_eval(h, U, V, Wold, Wnew):
    """energy delta of switching member from Wold to Wnew."""
    d = 0
    # cells leaving old coset: count==1 there -> become uncovered
    for k, ls in coset_cells(h, U, V, Wold):
        row = count[k]
        d += int((row[ls] == 1).sum())
    # cells entering new coset: count==0 there -> become covered
    for k, ls in coset_cells(h, U, V, Wnew):
        row = count[k]
        d -= int((row[ls] == 0).sum())
    return d

def apply_switch(h, U, V, Wold, Wnew):
    for k, ls in coset_cells(h, U, V, Wold):
        count[k][ls] -= 1
    for k, ls in coset_cells(h, U, V, Wnew):
        count[k][ls] += 1

t0 = time.time()
random.seed(42)
BUDGET_S = 480
moves = tried = 0
members = [l for l in layers if l[4] >= 0]
while time.time() - t0 < BUDGET_S:
    l = random.choice(members)
    q, h, U, V, Wold = l
    Wnew = random.randrange(h)
    if Wnew == Wold:
        continue
    tried += 1
    d = delta_eval(h, U, V, Wold, Wnew)
    if d < 0:
        apply_switch(h, U, V, Wold, Wnew)
        l[4] = Wnew
        moves += 1
        res = int((count == 0).sum())
        print(f"MOVE q={q} h={h} W {Wold}->{Wnew} d={d} residual {res} ({res/L/L*100:.3f}%) ({time.time()-t0:.0f}s)", flush=True)
        json.dump(layers, open(W + "state27720all.json", "w"))
        np.save(W + "count27720.npy", count)
        if res == 0:
            print("COVERING CLOSED")
            json.dump({"L": L, "layers": [x for x in layers if x[4] >= 0]},
                      open(W + "covering_closed_27720anneal.json", "w"))
            break

res = int((count == 0).sum())
print(f"== anneal pass: tried {tried}, moves {moves}, residual {res} ({res/L/L*100:.3f}%) ({time.time()-t0:.0f}s)", flush=True)
if res == 0:
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [x for x in layers if x[4] >= 0]},
              open(W + "covering_closed_27720anneal.json", "w"))
