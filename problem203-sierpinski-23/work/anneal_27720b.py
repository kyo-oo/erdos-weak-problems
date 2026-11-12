"""L=27720 ANNEALING v2 — TEMPERATURE (S056 round 3).

The greedy single-switch annealer plateaued (round 1: 18 moves; round 2:
ZERO moves — local optimum). Per the no-re-roll law the mechanism changes:
CLASSIC SIMULATED ANNEALING — accept worsening moves with temperature-
scaled probability (escape energy wells), track best-seen separately.

State: state27720all.json = BEST config (canonical, only advances);
count27720.npy = count-map of the LIVE config (rebuilt on resume from
live json). Live config: state27720live.json.
"""
import json, time, random, math
import numpy as np

L = 27720
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
pal = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/pal_dlog_full.json"))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]
fam = [r for r in pal if L % r[1] == 0]
fam.sort(key=lambda r: -1.0 / r[1])
FAM = {q: (h, U, V) for (q, h, U, V) in fam}

# canonical best state
best_layers = json.load(open(W + "state27720all.json"))

# live state: start from best (round 3 launch)
import os
if os.path.exists(W + "state27720live.json"):
    live = json.load(open(W + "state27720live.json"))
    print("resumed LIVE config", flush=True)
else:
    live = [list(l) for l in best_layers]
    json.dump(live, open(W + "state27720live.json", "w"))

def build_count(layers):
    count = np.zeros((L, L), dtype=np.int8)
    def add_coset(h, U, V, Wv, delta):
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
            row = count[k]
            ls = np.arange(l0, L, hg)
            row[ls] += delta
    for l in layers:
        if l[4] >= 0:
            q, h, U, V, Wv = l
            add_coset(h, U, V, Wv, 1)
    return count

def coset_cells(h, U, V, Wv):
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

count = build_count(live)
res_live = int((count == 0).sum())
best_res = int((np.zeros(1) * 0).sum())  # placeholder, set below
best_res = res_live
if os.path.exists(W + "bestres27720.txt"):
    best_res = int(open(W + "bestres27720.txt").read().strip())
print(f"live residual: {res_live} ({res_live/L/L*100:.3f}%), best banked: {best_res}", flush=True)

def delta_eval(h, U, V, Wold, Wnew):
    d = 0
    for k, ls in coset_cells(h, U, V, Wold):
        row = count[k]
        d += int((row[ls] == 1).sum())
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
random.seed(88)
BUDGET_S = 470
T0, T1 = 600.0, 0.5  # temperature ramp down
members = [l for l in live if l[4] >= 0]
acc = tried = 0
improve = 0
while time.time() - t0 < BUDGET_S:
    frac = (time.time() - t0) / BUDGET_S
    T = T0 * (T1 / T0) ** frac  # geometric ramp
    l = random.choice(members)
    q, h, U, V, Wold = l
    Wnew = random.randrange(h)
    if Wnew == Wold:
        continue
    tried += 1
    d = delta_eval(h, U, V, Wold, Wnew)
    if d < 0 or (d > 0 and random.random() < math.exp(-d / T)):
        apply_switch(h, U, V, Wold, Wnew)
        l[4] = Wnew
        acc += 1
        res = int((count == 0).sum())
        if res < best_res:
            best_res = res
            improve += 1
            json.dump(live, open(W + "state27720all.json", "w"))  # new BEST = canonical
            open(W + "bestres27720.txt", "w").write(str(best_res))
            print(f"BEST res {res} ({res/L/L*100:.3f}%) T={T:.1f} ({time.time()-t0:.0f}s)", flush=True)
    # periodic live-state save (L80)
    if tried % 200 == 0:
        json.dump(live, open(W + "state27720live.json", "w"))

res_live = int((count == 0).sum())
json.dump(live, open(W + "state27720live.json", "w"))
print(f"== temper pass: tried {tried}, accepted {acc}, improvements {improve}, live res {res_live} ({res_live/L/L*100:.3f}%), best {best_res} ({best_res/L/L*100:.3f}%) ({time.time()-t0:.0f}s)", flush=True)
if best_res == 0:
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [x for x in live if x[4] >= 0]},
              open(W + "covering_closed_27720anneal.json", "w"))
