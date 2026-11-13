"""L=27720 ANNEALING v4 — RESTART-DIVERSIFICATION (S057 round 12+).

v3 pair-pass diagnosis (this bank): tried 746, accepted 0, improvements 0
— the pair landscape from the banked basin is FROZEN, and v3's FIXED seed
(90210) on an unchanged live state makes re-runs replay the identical
rejected walk (provably futile). Two concrete pathologies:
  (a) v3's acceptance rule rejects d==0 moves -> plateau travel impossible;
  (b) no restart diversity: same basin, same walk, forever.

ONE mechanism escalation: ILS-style RESTART DIVERSIFICATION —
  * time-varying seed (each call is a genuinely new walk);
  * KICK: K_PAIRS forced pair switches (delta ignored, sequential-delta
    bookkeeping preserved) -> jump to a neighboring basin;
  * TEMPER from the kicked state, single/pair mix as v3 but NEUTRAL
    d==0 moves ACCEPTED (plateau walking), T: 600 -> 0.4;
  * BASIN MEMORY: a restart ending worse than the banked best resets
    live INCREMENTALLY to best (exact switch-backs, no count rebuild);
  * banking protocol unchanged: every improvement immediately writes
    state27720all.json + bestres27720.txt, verified by a full count
    scan before banking (no fabricated numbers).

Invocation: python3 anneal_27720d.py   (no args; state on disk).
State: state27720all.json = BEST (canonical); state27720live.json =
live; count bookkeeping in-memory only; bestres27720.txt = best residual.
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

live = json.load(open(W + "state27720live.json"))
best_layers = [list(x) for x in json.load(open(W + "state27720all.json"))]
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

def full_res():
    return int(L * L - np.count_nonzero(count))

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

res_live = full_res()
print(f"live residual: {res_live} ({res_live/L/L*100:.3f}%), best banked: {best_res}", flush=True)

seed = int(time.time() * 1000) % (2 ** 31)
random.seed(seed)
print(f"v4 restart-diversification seed: {seed}", flush=True)

t0 = time.time()
BUDGET_S = 420
T0R, T1R = 600.0, 0.4     # temper schedule per restart
TW = 110.0                 # temper window seconds per restart
K_PAIRS = 3                # forced pair switches per kick

members = [l for l in live if l[4] >= 0]
tried = acc = acc_neut = acc_up = seen_neg = improve = restarts = 0

def bank():
    json.dump(live, open(W + "state27720all.json", "w"))
    open(W + "bestres27720.txt", "w").write(str(best_res))

def reset_to_best():
    """Incremental exact switch-back of every live member to banked best W."""
    n = 0
    for i in range(min(len(live), len(best_layers))):
        ll, bb = live[i], best_layers[i]
        if ll[4] >= 0 and bb[4] >= 0 and ll[4] != bb[4]:
            q, h, U, V, Wcur = ll
            apply_switch(h, U, V, Wcur, bb[4])
            ll[4] = bb[4]
            n += 1
    return n

if res_live > best_res:
    n = reset_to_best()
    res_live = full_res()
    print(f"startup reset to best: {n} switchbacks, res {res_live}", flush=True)

while time.time() - t0 < BUDGET_S - 25:
    restarts += 1
    # --- KICK: forced pair switches (delta ignored; sequential application) ---
    k2 = 2 * min(K_PAIRS, len(members) // 2)
    if k2 >= 2:
        idxs = random.sample(range(len(members)), k2)
        for j in range(0, k2, 2):
            for l in (members[idxs[j]], members[idxs[j + 1]]):
                q, h, U, V, Wcur = l
                Wnew = random.randrange(h)
                if Wnew != Wcur:
                    apply_switch(h, U, V, Wcur, Wnew)
                    l[4] = Wnew
    res_cur = full_res()
    print(f"[restart {restarts}] kick res {res_cur} ({res_cur/L/L*100:.3f}%), d_vs_best {res_cur - best_res}", flush=True)
    # --- TEMPER: single/pair mix, NEUTRAL moves accepted (plateau walk) ---
    t_r = time.time()
    while time.time() - t_r < TW and time.time() - t0 < BUDGET_S:
        frac = min((time.time() - t_r) / TW, 1.0)
        T = T0R * (T1R / T0R) ** frac
        if random.random() < 0.5 or len(members) < 2:
            l = random.choice(members)
            q, h, U, V, Wold = l
            Wnew = random.randrange(h)
            if Wnew == Wold:
                continue
            tried += 1
            d = delta_eval(h, U, V, Wold, Wnew)
            if d < 0:
                seen_neg += 1
            if d <= 0 or (d > 0 and random.random() < math.exp(-d / T)):
                apply_switch(h, U, V, Wold, Wnew)
                l[4] = Wnew
                acc += 1
                if d == 0:
                    acc_neut += 1
                elif d > 0:
                    acc_up += 1
                res_cur += d
                if res_cur < best_res:
                    r_true = full_res()
                    res_cur = r_true
                    if r_true < best_res:
                        best_res = r_true
                        improve += 1
                        best_layers = [list(x) for x in live]
                        bank()
                        print(f"BEST res {best_res} ({best_res/L/L*100:.3f}%) [v4 r{restarts}, single] T={T:.1f} ({time.time()-t0:.0f}s)", flush=True)
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
            if d_total < 0:
                seen_neg += 1
            if d_total <= 0 or (d_total > 0 and random.random() < math.exp(-d_total / T)):
                if moved2:
                    apply_switch(h2, U2, V2, Wold2, Wnew2)
                    l2[4] = Wnew2
                l1[4] = Wnew1
                acc += 1
                if d_total == 0:
                    acc_neut += 1
                elif d_total > 0:
                    acc_up += 1
                res_cur += d_total
                if res_cur < best_res:
                    r_true = full_res()
                    res_cur = r_true
                    if r_true < best_res:
                        best_res = r_true
                        improve += 1
                        best_layers = [list(x) for x in live]
                        bank()
                        print(f"BEST res {best_res} ({best_res/L/L*100:.3f}%) [v4 r{restarts}, pair] T={T:.1f} ({time.time()-t0:.0f}s)", flush=True)
            else:
                apply_switch(h1, U1, V1, Wnew1, Wold1)
        if tried % 300 == 0 and tried > 0:
            json.dump(live, open(W + "state27720live.json", "w"))
    # --- end of temper: verify, log, basin memory ---
    r_end = full_res()
    if r_end != res_cur:
        print(f"[restart {restarts}] DRIFT warn: tracked {res_cur} vs scan {r_end}", flush=True)
        res_cur = r_end
    print(f"[restart {restarts}] temper end res {r_end} ({r_end/L/L*100:.3f}%), cum tried {tried}, acc {acc} (neutral {acc_neut}, uphill {acc_up}), neg proposals {seen_neg}", flush=True)
    if r_end > best_res:
        n = reset_to_best()
        print(f"[restart {restarts}] basin failed -> {n} switchbacks to best", flush=True)
    json.dump(live, open(W + "state27720live.json", "w"))

res_live = full_res()
json.dump(live, open(W + "state27720live.json", "w"))
print(f"== v4 restart-div pass: restarts {restarts}, tried {tried}, acc {acc} (neutral {acc_neut}, uphill {acc_up}), neg-props {seen_neg}, improvements {improve}, live res {res_live} ({res_live/L/L*100:.3f}%), best {best_res} ({best_res/L/L*100:.3f}%) ({time.time()-t0:.0f}s)", flush=True)
if best_res == 0:
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [x for x in live if x[4] >= 0]},
              open(W + "covering_closed_27720anneal.json", "w"))
