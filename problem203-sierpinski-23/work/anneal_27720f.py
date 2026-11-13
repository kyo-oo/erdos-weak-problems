"""C-203 v5.1 ANNEALER — 1-PAIR KICKS + SWEEP-RECOVERY TEMPERING (W59-T5).

v5.0 (anneal_27720e.py) evidence, 2 cycles: the reheated Metropolis temper
DOES climb back from kicks (cycle 1: recovered 26.3M of +29.9M excess —
v4's T=600 walks recovered nothing), but it stalls in the moat ~+400k above
the bank (cycle 2 ended +415k, basin-failed). The moat is where stochastic
recovery dies; the exhaustive per-coordinate greedy sweep is not.

v5.1 mechanism (escalated recovery engine inside the v5 kick/temper frame):
  * KICK: ONE pair (2 forced far W-switches), excess capped <= 12M;
  * SWEEP RECOVERY: per member i, G_i(W) = #{residual cells in coset(W)}
    computed EXACTLY by one chunked bincount over the count==0 mask
    (serves ALL W simultaneously); LOSS_i = #{coset(W_old) ∩ count==1}
    (the two cosets are disjoint for W != W_old, so the switch delta is
    LOSS - G with no cross terms). Switch iff max_W G_i(W) > LOSS_i ->
    argmax. Passes repeat until a pass makes zero switches
    (coordinate-optimum). This is the 300-400s tempering cycle's
    recovery phase, done deterministically;
  * POLISH: Metropolis with graded near-moves (W -> W + g*s = exact
    l-translation of the coset), far moves, near-pair moves; T reheat
    3e4 -> 400; neutral moves accepted (plateau walking);
  * banking/checkpoint/kill laws unchanged (every improvement + ~60s
    atomic writes; residual 0 -> covering_closed_27720v5.json + STOP).

Modes: `python3 anneal_27720f.py bank`  = no kick, sweep from the bank
        (validation: bank claimed coordinate-optimal; argmax is
        exhaustive, unlike the earlier 40-sample delta scans).
        default = kick + sweep + polish cycle.
"""
import json, os, time, math, random, sys
import numpy as np

L = 27720
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
MODE = sys.argv[1] if len(sys.argv) > 1 else "cycle"
CH = 1024
KICK_CAP = 12_000_000
SWEEP_BUDGET = 230.0     # seconds for the sweep phase
POLISH_BUDGET = 150.0    # seconds for the Metropolis polish phase
CKPT_EVERY = 60.0
T1 = 400.0
P_NEAR, P_FAR = 0.60, 0.15
LOG = W + "v5rounds.log"

def logline(s):
    with open(LOG, "a") as f:
        f.write(s + "\n")
    print(s, flush=True)

def atomic_json(obj, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)

def atomic_txt(s, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        f.write(s)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)

# ---------- state ----------
best_layers = json.load(open(W + "state27720all.json"))
try:
    live = json.load(open(W + "state27720live.json"))
except Exception:
    live = None
best_res = int(open(W + "bestres27720.txt").read().strip())
try:
    ckpt = json.load(open(W + "ckpt_v5.json"))
    cycle_n = int(ckpt.get("cycle", 0))
    stats0 = ckpt.get("stats", {})
except Exception:
    ckpt = None
    cycle_n = 0
    stats0 = {}

if live is None or len(live) != len(best_layers) or any(l[4] < 0 for l in live):
    live = [list(x) for x in best_layers]

# ---------- count map ----------
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

t0 = time.time()
count = build_count(live)
build_s = time.time() - t0

def full_res():
    return int(L * L - np.count_nonzero(count))

res_live = full_res()
logline(f"[v5.1 {MODE}] build {build_s:.0f}s; live residual {res_live} "
        f"({res_live/L/L*100:.4f}%); best banked {best_res} ({best_res/L/L*100:.4f}%)")

members = [l for l in live if l[4] >= 0]
ks = np.arange(L, dtype=np.int64)
MINFO = []
for l in members:
    q, h, U, V, Wv = l
    g = int(np.gcd(V, h))
    hg = h // g
    MINFO.append({"g": g, "hg": hg, "srange": max(2, h // 12), "h": h})

def coset_cells(h, U, V, Wv):
    g = int(np.gcd(V, h))
    hg = h // g
    ks_ = np.arange(L, dtype=np.int64)
    rhs = (Wv - U * ks_) % h
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

# ---------- banking ----------
improve = 0
def bank(res_true, tag):
    global best_res, best_layers, improve
    best_res = res_true
    best_layers = [list(x) for x in live]
    atomic_json(best_layers, W + "state27720all.json")
    atomic_txt(str(best_res), W + "bestres27720.txt")
    atomic_json({
        "L": L, "engine": "anneal_27720f.py (v5.1: 1-pair kicks + sweep-recovery temper)",
        "residual": best_res, "residual_pct": best_res / L / L * 100.0,
        "layers": best_layers, "cycle": cycle_n, "improvements": improve,
        "banked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tag": tag,
    }, W + "best.json")
    logline(f"BANK res {best_res} ({best_res/L/L*100:.4f}%) [cycle {cycle_n}, {tag}]")

def kill_check():
    if full_res() == 0:
        atomic_json({"L": L, "layers": [list(x) for x in live]},
                    W + "covering_closed_27720v5.json")
        atomic_json(live, W + "state27720live.json")
        logline("=== KILL: COVERING CLOSED ===")
        sys.exit(0)

if res_live < best_res:
    improve += 1
    bank(res_live, "posthumous bank from resumed live")
    kill_check()

# ---------- sweep machinery ----------
def gain_dist(i):
    """G[W] = number of residual (count==0) cells in coset(W), all W at once."""
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
         "pair": 0, "neg_props": 0, "sweep_switches": 0, "sweep_gain": 0,
         "min_delta": 10**9, "max_delta": -10**9}
for k in stats:
    if k in stats0:
        stats[k] = stats0[k]
res_cur = res_live

def save_ckpt(phase, extra=None):
    atomic_json(live, W + "state27720live.json")
    obj = {
        "cycle": cycle_n, "phase": phase, "mode": MODE,
        "res_cur": res_cur, "best": best_res, "stats": stats,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if extra:
        obj.update(extra)
    atomic_json(obj, W + "ckpt_v5.json")

seed = int(time.time() * 1000) % (2 ** 31)
random.seed(seed)

# ---------- basin memory: reset live to best ----------
if MODE == "cycle":
    n_back = 0
    for i in range(len(live)):
        if live[i][4] != best_layers[i][4]:
            q, h, U, V, Wcur = live[i]
            apply_switch(h, U, V, Wcur, best_layers[i][4])
            live[i][4] = best_layers[i][4]
            n_back += 1
    if n_back:
        r_chk = full_res()
        if r_chk != best_res:
            logline(f"[startup] WARN reset drift {r_chk} vs best {best_res}")
        res_cur = best_res
        logline(f"[startup] basin memory: {n_back} switch-backs to best")

# ---------- KICK (cycle mode only) ----------
kick_excess = 0
if MODE == "cycle":
    for attempt in range(6):
        i1, i2 = random.sample(range(len(members)), 2)
        trial = []
        for i in (i1, i2):
            q, h, U, V, Wcur = members[i]
            Wnew = random.randrange(h)
            if Wnew != Wcur:
                apply_switch(h, U, V, Wcur, Wnew)
                members[i][4] = Wnew
                trial.append((i, h, U, V, Wcur, Wnew))
        res_kick = full_res()
        kick_excess = res_kick - best_res
        if kick_excess <= KICK_CAP or attempt == 5:
            break
        for (i, h, U, V, Wcur, Wnew) in reversed(trial):
            apply_switch(h, U, V, Wnew, Wcur)
            members[i][4] = Wcur
    res_cur = res_kick
    logline(f"[cycle {cycle_n+1}] KICK 1-pair members {members[i1][0]},{members[i2][0]} "
            f"-> res {res_kick} ({res_kick/L/L*100:.4f}%), excess {kick_excess:+d} "
            f"(tries {attempt+1}), seed {seed}")
    save_ckpt("sweep", {"kick_excess": kick_excess})

# ---------- SWEEP RECOVERY ----------
t_sw = time.time()
last_save = time.time()
passes = 0
while time.time() - t_sw < SWEEP_BUDGET and passes < 8:
    passes += 1
    sw = 0
    g_tot = 0
    for i in range(len(members)):
        if time.time() - t_sw > SWEEP_BUDGET:
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
            logline(f"[sweep c{cycle_n+1} p{passes}] member q={q} W {Wold}->{w_best} "
                    f"gain {g_best} loss {loss} d {d:+d} res {res_cur} ({res_cur/L/L*100:.4f}%)")
            if res_cur < best_res:
                r_true = full_res()
                if r_true < best_res:
                    res_cur = r_true
                    improve += 1
                    bank(r_true, f"sweep p{passes}")
                    kill_check()
                else:
                    res_cur = r_true
                    logline(f"[sweep] scan-corrected to {r_true}")
        if (i % 7 == 0) and (time.time() - last_save > CKPT_EVERY):
            save_ckpt("sweep", {"pass": passes})
            last_save = time.time()
    logline(f"[sweep c{cycle_n+1}] pass {passes}: {sw} switches, net gain {g_tot:+d} cells, "
            f"res {res_cur} ({res_cur/L/L*100:.4f}%) ({time.time()-t_sw:.0f}s)")
    if sw == 0:
        break
    save_ckpt("sweep", {"pass": passes})
kill_check()

# ---------- POLISH (Metropolis, graded moves, reheated) ----------
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
        stats["min_delta"] = min(stats["min_delta"], d)
        stats["max_delta"] = max(stats["max_delta"], d)
        if d < 0:
            stats["neg_props"] += 1
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
                    bank(r_true, "polish near")
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
        stats["min_delta"] = min(stats["min_delta"], d)
        stats["max_delta"] = max(stats["max_delta"], d)
        if d < 0:
            stats["neg_props"] += 1
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
                    bank(r_true, "polish far")
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
        stats["min_delta"] = min(stats["min_delta"], d_total)
        stats["max_delta"] = max(stats["max_delta"], d_total)
        if d_total < 0:
            stats["neg_props"] += 1
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
                    bank(r_true, "polish pair")
                    kill_check()
                else:
                    res_cur = r_true
        else:
            apply_switch(h1, U1, V1, Wnew1, Wold1)
    if time.time() - last_save >= CKPT_EVERY:
        r_now = full_res()
        if r_now != res_cur:
            logline(f"[ckpt] DRIFT tracked {res_cur} vs scan {r_now}; adopting scan")
            res_cur = r_now
        save_ckpt("polish")
        last_save = time.time()

# ---------- endgame ----------
r_end = full_res()
if r_end != res_cur:
    logline(f"[end] DRIFT tracked {res_cur} vs scan {r_end}; adopting scan")
    res_cur = r_end
kill_check()
if r_end > best_res:
    n_back = 0
    for i in range(len(live)):
        if live[i][4] != best_layers[i][4]:
            q, h, U, V, Wcur = live[i]
            apply_switch(h, U, V, Wcur, best_layers[i][4])
            live[i][4] = best_layers[i][4]
            n_back += 1
    logline(f"[cycle {cycle_n+1}] basin failed -> {n_back} switch-backs to best {best_res}")
elif r_end == best_res:
    logline(f"[cycle {cycle_n+1}] ended AT best (plateau)")
atomic_json(live, W + "state27720live.json")
atomic_json({
    "cycle": cycle_n + 1, "phase": "done", "mode": MODE,
    "res_cur": best_res if r_end > best_res else r_end, "best": best_res,
    "stats": stats,
    "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
}, W + "ckpt_v5.json")
logline(f"== v5.1 {MODE} cycle {cycle_n+1} done: best {best_res} ({best_res/L/L*100:.4f}%), "
        f"improvements {improve}, sweep switches {stats['sweep_switches']} "
        f"(net {stats['sweep_gain']:+d}), polish tried {stats['tried']}, "
        f"wall {(time.time()-t0):.0f}s")
