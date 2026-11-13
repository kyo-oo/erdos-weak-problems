"""L=27720 ANNEALING v3 — PAIR-MOVES (S057 round 11+; rewritten after the
platform directory-swap of S057 — remote is truth, fetch+reset recovers).

The single-switch landscape is exhausted (greedy: 18 then 0; temper
T0=600: 7+7+1 then 0+0+0 — three consecutive zero-move rounds = the
stuck trigger). Per the no-re-roll law the mechanism escalates: PAIR
switches (two members moved simultaneously — escapes the 1-move local
optimum), sequential-delta evaluation (switch2 evaluated on the map
after switch1 — exact residual bookkeeping), temperature on the pair
delta, single-moves still mixed in (50/50).

State: state27720all.json = BEST (canonical); state27720live.json =
live; count27720.npy = live count-map; bestres27720.txt = best residual.
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

best_layers = json.load(open(W + "state27720all.json"))
live = json.load(open(W + "state27720live.json"))
best_res = int(open(W + "bestres27720.txt").read().strip())

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
random.seed(90210)
BUDGET_S = 460
T0, T1 = 300.0, 0.4
members = [l for l in live if l[4] >= 0]
tried = acc_single = acc_pair = improve = 0
while time.time() - t0 < BUDGET_S:
    frac = (time.time() - t0) / BUDGET_S
    T = T0 * (T1 / T0) ** frac
    if random.random() < 0.5 or len(members) < 2:
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
            acc_single += 1
            res = int((count == 0).sum())
            if res < best_res:
                best_res = res; improve += 1
                json.dump(live, open(W + "state27720all.json", "w"))
                open(W + "bestres27720.txt", "w").write(str(best_res))
                print(f"BEST res {res} ({res/L/L*100:.3f}%) [single] T={T:.1f} ({time.time()-t0:.0f}s)", flush=True)
    else:
        i1, i2 = random.sample(range(len(members)), 2)
        l1, l2 = members[i1], members[i2]
        q1, h1, U1, V1, Wold1 = l1
        q2, h2, U2, V2, Wold2 = l2
        Wnew1 = random.randrange(h1)
        if Wnew1 == Wold1:
            continue
        tried += 1
        d1 = delta_eval(h1, U1, V1, Wold1, Wnew1)
        apply_switch(h1, U1, V1, Wold1, Wnew1)
        Wnew2 = random.randrange(h2)
        d2 = 0
        moved2 = Wnew2 != Wold2
        if moved2:
            d2 = delta_eval(h2, U2, V2, Wold2, Wnew2)
        d_total = d1 + d2
        if d_total < 0 or (d_total > 0 and random.random() < math.exp(-d_total / T)):
            if moved2:
                apply_switch(h2, U2, V2, Wold2, Wnew2)
                l2[4] = Wnew2
            l1[4] = Wnew1
            acc_pair += 1
            res = int((count == 0).sum())
            if res < best_res:
                best_res = res; improve += 1
                json.dump(live, open(W + "state27720all.json", "w"))
                open(W + "bestres27720.txt", "w").write(str(best_res))
                print(f"BEST res {res} ({res/L/L*100:.3f}%) [pair] T={T:.1f} ({time.time()-t0:.0f}s)", flush=True)
        else:
            apply_switch(h1, U1, V1, Wnew1, Wold1)
    if tried % 200 == 0:
        json.dump(live, open(W + "state27720live.json", "w"))

res_live = int((count == 0).sum())
json.dump(live, open(W + "state27720live.json", "w"))
print(f"== pair pass: tried {tried}, acc single {acc_single}, acc pair {acc_pair}, improvements {improve}, live res {res_live} ({res_live/L/L*100:.3f}%), best {best_res} ({best_res/L/L*100:.3f}%) ({time.time()-t0:.0f}s)", flush=True)
if best_res == 0:
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [x for x in live if x[4] >= 0]},
              open(W + "covering_closed_27720anneal.json", "w"))
