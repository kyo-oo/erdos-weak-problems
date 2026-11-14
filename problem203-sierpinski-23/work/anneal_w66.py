#!/usr/bin/env python3
"""C-203 W66 ANNEALER at L=27720 — THE ENLARGED-PALETTE INTENSIFICATION.

Built on the W65 v5.1 frame (anneal_27720f.py: 1-pair kicks + exhaustive
sweep-recovery tempering + Metropolis polish with graded moves), escalated:
  * PALETTE GROWTH: the layer set = the W65 banked state (35 layers,
    bestres 218,794,308 = 28.4741%) + ALL missing full-family members —
    the W66 complete 42-prime family for L=27720 (budget 1.056421 vs the
    1.056313 baseline scan family; the missing 7 layers include the
    deep-tier prime p=18481 with h=9240 > the old 4998 scan cap) — each
    new layer placed greedily (argmax gain) at startup;
  * MORE RESTARTS: kick sizes alternate 1-pair / 2-pair / 3-member;
  * BETTER COOLING: sweep budget 300s (was 230), polish 240s (was 150),
    reheat 3e4 -> 300 (was 400) with a longer low-T plateau;
  * banking: every improvement -> bestres27720_w66.txt +
    state27720all_w66.json + w66_anneal.log (atomic writes).

The count map is the EXACT int8 cover multiplicity map (27720^2 = 768MB) —
every switch delta is exact (this is the frame the 55440 torus cannot
afford in RAM; see close_w66_55440.py for the sound bitmap design there).
"""
import json, os, time, math, random, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..")
L = 27720
MODE = sys.argv[1] if len(sys.argv) > 1 else "cycle"
CYCLES = int(sys.argv[2]) if len(sys.argv) > 2 else 10
CH = 1024
KICK_CAP = 12_000_000
SWEEP_BUDGET = 300.0
POLISH_BUDGET = 240.0
CKPT_EVERY = 60.0
T1 = 300.0
P_NEAR, P_FAR = 0.60, 0.15
LOG = os.path.join(HERE, "w66_anneal.log")

def logline(s):
    with open(LOG, "a") as f: f.write(s + "\n")
    print(s, flush=True)

def atomic_json(obj, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f); f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)

def atomic_txt(s, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        f.write(s); f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)

# ---------- state: W65 bank + enlarged family ----------
best_layers = json.load(open(os.path.join(HERE, "state27720all_base.json")))
best_res = int(open(os.path.join(HERE, "bestres27720_base.txt")).read().strip())
state_qs = {l[0] for l in best_layers}

pal66 = json.load(open(os.path.join(OUT, "pal_dlog_w66.json")))
fam27 = [(int(r[0]), int(r[1]), int(r[2]), int(r[3]))
         for r in pal66 if L % int(r[1]) == 0]
# dedup by base prime keep min-h (prime powers excluded from the layer set)
bases = {}
for (q, h, U, V) in fam27:
    p = q; d = 2
    while d * d <= q:
        if q % d == 0: p = d; break
        d += 1
    if p not in bases or 1.0 / h > 1.0 / bases[p][1]:
        bases[p] = (q, h, U, V)
fam27 = sorted(bases.values(), key=lambda r: -1.0 / r[1])
missing = [r for r in fam27 if r[0] not in state_qs]
budget_all = sum(1.0 / r[1] for r in fam27)
logline(f"[w66-27720] full family: {len(fam27)} primes budget {budget_all:.6f}; "
        f"banked layers {len(best_layers)} (res {best_res}); "
        f"NEW layers to add: {[r[0] for r in missing]}")

live = [list(x) for x in best_layers]
for (q, h, U, V) in missing:
    live.append([q, h, U, V, -1])

# ---------- count map ----------
ks = np.arange(L, dtype=np.int64)

def build_count(layers):
    count = np.zeros((L, L), dtype=np.int8)
    def add_coset(h, U, V, Wv, delta):
        g = int(np.gcd(V, h))
        hg = h // g
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

t0 = time.time()
count = build_count(live)
build_s = time.time() - t0

def full_res():
    return int(L * L - np.count_nonzero(count))

res_live = full_res()
logline(f"[w66 {MODE}] build {build_s:.0f}s; banked-state residual {res_live} "
        f"({res_live/L/L*100:.4f}%); best banked {best_res}")

members = [l for l in live if l[4] >= 0]
MINFO = []
for l in members:
    q, h, U, V, Wv = l
    g = int(np.gcd(V, h))
    hg = h // g
    MINFO.append({"g": g, "hg": hg, "srange": max(2, h // 12), "h": h})

def coset_cells(h, U, V, Wv):
    g = int(np.gcd(V, h))
    hg = h // g
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

# ---------- greedy placement of the NEW layers ----------
improve = 0
def bank(res_true, tag):
    global best_res, best_layers, improve
    best_res = res_true
    best_layers = [list(x) for x in live]
    atomic_json(best_layers, os.path.join(HERE, "state27720all_w66.json"))
    atomic_txt(f"{best_res}\n", os.path.join(HERE, "bestres27720_w66.txt"))
    atomic_json({
        "L": L, "engine": "anneal_w66.py (enlarged 42-family v5.1 escalation)",
        "residual": best_res, "residual_pct": best_res / L / L * 100.0,
        "layers": best_layers, "improvements": improve,
        "banked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tag": tag,
    }, os.path.join(HERE, "best27720_w66.json"))
    logline(f"BANK res {best_res} ({best_res/L/L*100:.4f}%) [tag {tag}]")

def kill_check():
    if full_res() == 0:
        atomic_json({"L": L, "layers": [list(x) for x in live]},
                    os.path.join(HERE, "covering_closed_27720_w66.json"))
        logline("=== KILL: COVERING CLOSED at L=27720 ===")
        sys.exit(0)

# greedy-init the new layers via the exhaustive gain histogram (argmax_W)
for i in range(len(live)):
    if live[i][4] < 0:
        q, h, U, V, Wv = live[i]
        ks = np.arange(L, dtype=np.int64)
        Vb = ((V * ks) % h).astype(np.int64)
        G = np.zeros(h, dtype=np.int64)
        for a0 in range(0, L, CH):
            a1 = min(a0 + CH, L)
            rowmask = count[a0:a1] == 0
            if not rowmask.any():
                continue
            ai, bi = np.nonzero(rowmask)
            Ua = (U * (a0 + ai)) % h
            vals = (Ua + Vb[bi]) % h
            G += np.bincount(vals, minlength=h)
            del rowmask, ai, bi, Ua, vals
        W = int(np.argmax(G))
        if G[W] > 0:
            for k, ls in coset_cells(h, U, V, W):
                count[k][ls] += 1
            live[i][4] = W
            r = full_res()
            logline(f"[greedy-new] q={q} h={h} W={W} gain {int(G[W])} -> res {r} "
                    f"({r/L/L*100:.4f}%)")
            members.append(live[i])
            g = int(np.gcd(V, h)); hg = h // g
            MINFO.append({"g": g, "hg": hg, "srange": max(2, h // 12), "h": h})
            if r < best_res:
                improve += 1
                bank(r, "greedy new layer")
                kill_check()
        else:
            logline(f"[greedy-new] q={q} h={h}: no gain (skipped)")

res_cur = full_res()
logline(f"[startup] enlarged-family residual: {res_cur} ({res_cur/L/L*100:.4f}%)")

# ---------- sweep machinery (exhaustive coordinate descent) ----------
def gain_dist(i):
    q, h, U, V, Wv = members[i]
    Vb = ((V * ks) % h).astype(np.int64)
    G = np.zeros(h, dtype=np.int64)
    for a0 in range(0, L, CH):
        a1 = min(a0 + CH, L)
        rowmask = count[a0:a1] == 0
        if not rowmask.any():
            continue
        ai, bi = np.nonzero(rowmask)
        Ua = (U * (a0 + ai)) % h
        vals = (Ua + Vb[bi]) % h
        G += np.bincount(vals, minlength=h)
        del rowmask, ai, bi, Ua, vals
    return G

def loss_of(i):
    q, h, U, V, Wold = members[i]
    d = 0
    for k, ls in coset_cells(h, U, V, Wold):
        row = count[k]
        d += int((row[ls] == 1).sum())
    return d

stats = {"tried": 0, "acc": 0, "acc_neut": 0, "acc_up": 0, "near": 0, "far": 0,
         "pair": 0, "neg_props": 0, "sweep_switches": 0, "sweep_gain": 0}

def save_ckpt(phase, extra=None):
    atomic_json(live, os.path.join(HERE, "state27720live_w66.json"))
    obj = {
        "cycle": cycle_n, "phase": phase, "mode": MODE,
        "res_cur": res_cur, "best": best_res, "stats": stats,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if extra:
        obj.update(extra)
    atomic_json(obj, os.path.join(HERE, "ckpt_w66.json"))

def sweep_passes(cycle_no, budget):
    global res_cur
    t_sw = time.time()
    last_save = time.time()
    passes = 0
    while time.time() - t_sw < budget and passes < 12:
        passes += 1
        sw = 0
        g_tot = 0
        for i in range(len(members)):
            if time.time() - t_sw > budget:
                break
            q, h, U, V, Wold = members[i]
            G = gain_dist(i)
            w_best = int(np.argmax(G))
            g_best = int(G[w_best])
            if g_best == 0:
                continue
            loss = loss_of(i)
            if g_best > loss:
                d = loss - g_best
                apply_switch(h, U, V, Wold, w_best)
                members[i][4] = w_best
                res_cur += d
                sw += 1
                g_tot += (g_best - loss)
                stats["sweep_switches"] += 1
                stats["sweep_gain"] += (g_best - loss)
                logline(f"[sweep c{cycle_no} p{passes}] q={q} W {Wold}->{w_best} "
                        f"gain {g_best} loss {loss} d {d:+d} res {res_cur} "
                        f"({res_cur/L/L*100:.4f}%)")
                if res_cur < best_res:
                    r_true = full_res()
                    if r_true < best_res:
                        res_cur = r_true
                        improve += 1
                        bank(r_true, f"sweep c{cycle_no} p{passes}")
                        kill_check()
                    else:
                        res_cur = r_true
            if (i % 7 == 0) and (time.time() - last_save > CKPT_EVERY):
                save_ckpt("sweep", {"pass": passes})
                last_save = time.time()
        logline(f"[sweep c{cycle_no}] pass {passes}: {sw} switches, net {g_tot:+d}, "
                f"res {res_cur} ({res_cur/L/L*100:.4f}%) ({time.time()-t_sw:.0f}s)")
        if sw == 0:
            break
        save_ckpt("sweep", {"pass": passes})
    kill_check()

def polish(cycle_no):
    global res_cur
    def near_W(i, Wcur):
        m = MINFO[i]
        s = random.randint(1, m["srange"])
        if random.random() < 0.5:
            s = -s
        return (Wcur + m["g"] * s) % m["h"]
    t_p = time.time()
    T0P = 3.0e4
    while time.time() - t_p < POLISH_BUDGET:
        frac = min((time.time() - t_p) / POLISH_BUDGET, 1.0)
        T = T0P * (T1 / T0P) ** frac
        r = random.random()
        if r < P_NEAR or len(members) < 2:
            i = random.randrange(len(members))
            q, h, U, V, Wold = members[i]
            Wnew = near_W(i, Wold)
            if Wnew == Wold:
                continue
            stats["near"] += 1; stats["tried"] += 1
            d = delta_eval(h, U, V, Wold, Wnew)
            if d < 0: stats["neg_props"] += 1
            if d <= 0 or (d > 0 and random.random() < math.exp(-d / T)):
                apply_switch(h, U, V, Wold, Wnew)
                members[i][4] = Wnew
                stats["acc"] += 1
                if d == 0: stats["acc_neut"] += 1
                elif d > 0: stats["acc_up"] += 1
                res_cur += d
                if res_cur < best_res:
                    r_true = full_res()
                    if r_true < best_res:
                        res_cur = r_true
                        improve += 1
                        bank(r_true, f"polish c{cycle_no}")
                        kill_check()
                    else:
                        res_cur = r_true
        elif r < P_NEAR + P_FAR:
            i = random.randrange(len(members))
            q, h, U, V, Wold = members[i]
            Wnew = random.randrange(h)
            if Wnew == Wold:
                continue
            stats["far"] += 1; stats["tried"] += 1
            d = delta_eval(h, U, V, Wold, Wnew)
            if d < 0: stats["neg_props"] += 1
            if d <= 0 or (d > 0 and random.random() < math.exp(-d / T)):
                apply_switch(h, U, V, Wold, Wnew)
                members[i][4] = Wnew
                stats["acc"] += 1
                if d == 0: stats["acc_neut"] += 1
                elif d > 0: stats["acc_up"] += 1
                res_cur += d
                if res_cur < best_res:
                    r_true = full_res()
                    if r_true < best_res:
                        res_cur = r_true
                        improve += 1
                        bank(r_true, f"polish far c{cycle_no}")
                        kill_check()
                    else:
                        res_cur = r_true
        else:
            i1, i2 = random.sample(range(len(members)), 2)
            l1, l2 = members[i1], members[i2]
            q1, h1, U1, V1, Wold1 = l1
            q2, h2, U2, V2, Wold2 = l2
            Wnew1 = near_W(i1, Wold1)
            if Wnew1 == Wold1:
                continue
            stats["pair"] += 1; stats["tried"] += 1
            d1 = delta_eval(h1, U1, V1, Wold1, Wnew1)
            apply_switch(h1, U1, V1, Wold1, Wnew1)
            Wnew2 = near_W(i2, Wold2) if random.random() < 0.7 else random.randrange(h2)
            moved2 = Wnew2 != Wold2
            d2 = 0
            if moved2:
                d2 = delta_eval(h2, U2, V2, Wold2, Wnew2)
            d_total = d1 + d2
            if d_total < 0: stats["neg_props"] += 1
            if d_total <= 0 or (d_total > 0 and random.random() < math.exp(-d_total / T)):
                if moved2:
                    apply_switch(h2, U2, V2, Wold2, Wnew2)
                    l2[4] = Wnew2
                l1[4] = Wnew1
                stats["acc"] += 1
                if d_total == 0: stats["acc_neut"] += 1
                elif d_total > 0: stats["acc_up"] += 1
                res_cur += d_total
                if res_cur < best_res:
                    r_true = full_res()
                    if r_true < best_res:
                        res_cur = r_true
                        improve += 1
                        bank(r_true, f"polish pair c{cycle_no}")
                        kill_check()
                    else:
                        res_cur = r_true
            else:
                apply_switch(h1, U1, V1, Wnew1, Wold1)

# ---------- cycles: kick (graded) + sweep + polish ----------
seed = int(time.time() * 1000) % (2 ** 31)
random.seed(seed)
cycle_n = 0
for cyc in range(CYCLES):
    if MODE != "cycle":
        break
    cycle_n = cyc + 1
    # graded kick: 1-pair, 2-pair, or 3-member random W re-assignments
    kick_mode = cyc % 3
    n_kick = 2 if kick_mode == 0 else (4 if kick_mode == 1 else 3)
    trial = []
    for j in range(min(n_kick, len(members))):
        i = random.randrange(len(members))
        q, h, U, V, Wcur = members[i]
        Wnew = random.randrange(h)
        if Wnew != Wcur:
            apply_switch(h, U, V, Wcur, Wnew)
            members[i][4] = Wnew
            trial.append((i, h, U, V, Wcur, Wnew))
    res_kick = full_res()
    kick_excess = res_kick - best_res
    if kick_excess > KICK_CAP and trial:
        for (i, h, U, V, Wcur, Wnew) in reversed(trial):
            apply_switch(h, U, V, Wnew, Wcur)
            members[i][4] = Wcur
        res_kick = full_res()
    res_cur = res_kick
    logline(f"[cycle {cycle_n}] KICK mode {kick_mode} -> res {res_kick} "
            f"({res_kick/L/L*100:.4f}%), excess {res_kick-best_res:+d}, seed {seed}")
    save_ckpt("sweep", {"kick_excess": res_kick - best_res})
    sweep_passes(cycle_n, SWEEP_BUDGET)
    polish(cycle_n)
    r_end = full_res()
    if r_end != res_cur:
        logline(f"[cycle {cycle_n}] DRIFT {res_cur} vs {r_end}; adopting scan")
        res_cur = r_end
    kill_check()
    if r_end > best_res:
        # revert: rebuild the count map from the banked best layers
        count = build_count(best_layers)
        live = [list(x) for x in best_layers]
        members = [l for l in live if l[4] >= 0]
        MINFO = []
        for l in members:
            q, h, U, V, Wv = l
            g = int(np.gcd(V, h)); hg = h // g
            MINFO.append({"g": g, "hg": hg, "srange": max(2, h // 12), "h": h})
        res_cur = best_res
        logline(f"[cycle {cycle_n}] basin failed -> rebuild to best {best_res}")
    elif r_end == best_res:
        logline(f"[cycle {cycle_n}] ended AT best (plateau)")
    save_ckpt("done")
    logline(f"== w66 cycle {cycle_n} done: best {best_res} "
            f"({best_res/L/L*100:.4f}%), improvements {improve}, "
            f"sweep switches {stats['sweep_switches']} (net {stats['sweep_gain']:+d}), "
            f"wall {time.time()-t0:.0f}s")

logline(f"== anneal_w66 FINISHED: best {best_res} ({best_res/L/L*100:.4f}%) "
        f"after {CYCLES} cycles, wall {time.time()-t0:.0f}s")
