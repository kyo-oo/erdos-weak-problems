"""C-203 v5 ANNEALER — 1-PAIR KICKS + REHEATED 300-400s TEMPERING (W59-T5).

v4 diagnosis (this bank): kick-recovery mismatch — 3-pair kicks land
10^6-10^7 cells uphill while the fixed temper T0=600 sits FAR below the
median single-move delta (+542358), so the climb back is never accepted;
every restart ends worse, resets, and replays a frozen walk. v5 mechanism
(three coordinated fixes, one escalation):

  * KICK SHRUNK to ONE pair (2 forced W-switches) — neighbor-basin hop;
  * TEMPER WIDENED to 360s with ACCEPTANCE REHEATING: per-cycle T0 sized
    to the kick excess (clamped [3e5, 4e6]) -> geometric cool to 400;
  * GRADED PROPOSALS: near-moves W -> W + g*s (g = gcd(V,h), s small) are
    exact l-TRANSLATIONS of the member's coset (proof: V*t = g*s (mod h)
    is solved by t = s*(V/g)^{-1} mod h/g, so the new coset = old coset
    shifted by t in l) — deltas are boundary effects, the graded descent
    class the v1-v4 uniform-W samplers never had. Far moves + near-pair
    moves mixed in; neutral d==0 accepted (plateau walking).

Checkpoint law (reaper-safe): every improvement AND every ~60s -> live
state + ckpt JSON to disk (atomic tmp+rename); a fresh invocation
resumes the interrupted temper from the checkpoint. Cycle end: basin
memory (exact switch-backs to best if the restart failed).
KILL law: residual == 0 -> covering_closed_27720v5.json + STOP.

Invocation: python3 anneal_27720e.py    (one cycle ~380s per call).
Bank: state27720all.json (best) + bestres27720.txt + best.json + v5rounds.log.
"""
import json, os, time, math, random, sys
import numpy as np

L = 27720
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
BUDGET_TEMPER = 380.0          # v5 route: 300-400s tempering
KICK_CAP = 12_000_000         # 1-pair kicks capped: excess the temper can digest
CKPT_EVERY = 60.0              # reaper law: periodic checkpoint
T1 = 400.0                     # cold end of temper
T0_MIN, T0_MAX = 3.0e5, 4.0e6  # reheat clamp
P_NEAR, P_FAR = 0.60, 0.15     # rest = pair moves
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

# ---------- state load ----------
best_layers = json.load(open(W + "state27720all.json"))
try:
    live = json.load(open(W + "state27720live.json"))
except Exception:
    live = None
best_res = int(open(W + "bestres27720.txt").read().strip())
try:
    ckpt = json.load(open(W + "ckpt_v5.json"))
except Exception:
    ckpt = None

if live is None or len(live) != len(best_layers):
    live = [list(x) for x in best_layers]
if any(l[4] < 0 for l in live):
    logline("[startup] FATAL: live state has inactive members — engine invariant broken")
    sys.exit(1)

# ---------- count map (exact, rebuilt each invocation; ~7-12s) ----------
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
logline(f"[startup] build {build_s:.0f}s; live residual {res_live} ({res_live/L/L*100:.4f}%); "
        f"best banked {best_res} ({best_res/L/L*100:.4f}%); ckpt phase "
        f"{ckpt['phase'] if ckpt else 'none'}")

# ---------- member geometry (cached per member) ----------
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
cycle_n = (ckpt["cycle"] if ckpt else 0)

def bank(res_true, tag):
    global best_res, best_layers, improve
    best_res = res_true
    best_layers = [list(x) for x in live]
    atomic_json(best_layers, W + "state27720all.json")
    atomic_txt(str(best_res), W + "bestres27720.txt")
    atomic_json({
        "L": L, "engine": "anneal_27720e.py (v5: 1-pair kicks + reheated temper)",
        "residual": best_res, "residual_pct": best_res / L / L * 100.0,
        "layers": best_layers, "cycle": cycle_n, "improvements": improve,
        "banked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "tag": tag,
    }, W + "best.json")
    logline(f"BANK res {best_res} ({best_res/L/L*100:.4f}%) [cycle {cycle_n}, {tag}] "
            f"({time.strftime('%H:%M:%S')})")

if res_live < best_res:
    # improvement was found by a killed predecessor but not banked
    improve += 1
    bank(res_live, "posthumous bank from resumed live")

if res_live == 0:
    atomic_json({"L": L, "layers": [list(x) for x in live]},
                W + "covering_closed_27720v5.json")
    logline("=== KILL: COVERING CLOSED (startup scan) ===")
    sys.exit(0)

# ---------- proposal samplers ----------
def near_W(i, Wcur):
    m = MINFO[i]
    s = random.randint(1, m["srange"])
    if random.random() < 0.5:
        s = -s
    return (Wcur + m["g"] * s) % m["h"]

def far_W(i):
    return random.randrange(MINFO[i]["h"])

# ---------- checkpoint writer ----------
stats = {"tried": 0, "acc": 0, "acc_neut": 0, "acc_up": 0, "near": 0, "far": 0,
         "pair": 0, "neg_props": 0, "min_delta": 10**9, "max_delta": -10**9}
if ckpt and "stats" in ckpt:
    for k in stats:
        stats[k] = ckpt["stats"].get(k, stats[k])
res_cur = res_live
walk_min = res_cur

def save_ckpt(phase, temper_elapsed, T0=None):
    atomic_json(live, W + "state27720live.json")
    atomic_json({
        "cycle": cycle_n, "phase": phase, "temper_elapsed": temper_elapsed,
        "T0": T0, "res_cur": res_cur, "best": best_res,
        "stats": stats, "walk_min": walk_min,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }, W + "ckpt_v5.json")

# ---------- resume or new cycle ----------
seed = int(time.time() * 1000) % (2 ** 31)
random.seed(seed)

resuming = (ckpt is not None and ckpt.get("phase") == "temper"
            and ckpt.get("temper_elapsed", 1e9) < BUDGET_TEMPER - 10.0
            and ckpt.get("res_cur") == res_live)

if resuming:
    temper_elapsed = float(ckpt["temper_elapsed"])
    T0 = float(ckpt.get("T0") or 1.0e6)
    logline(f"[resume] continuing interrupted temper: elapsed {temper_elapsed:.0f}s, T0 {T0:.0f}, seed {seed}")
else:
    # basin memory: exact switch-backs of live to best before the fresh kick
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
    # ---- KICK: ONE pair (two forced switches, delta ignored), excess-capped ----
    for attempt in range(6):
        i1, i2 = random.sample(range(len(members)), 2)
        trial = []
        for i in (i1, i2):
            q, h, U, V, Wcur = members[i]
            Wnew = far_W(i)
            if Wnew != Wcur:
                apply_switch(h, U, V, Wcur, Wnew)
                members[i][4] = Wnew
                trial.append((i, h, U, V, Wcur, Wnew))
        res_kick = full_res()
        kick_excess = res_kick - best_res
        if kick_excess <= KICK_CAP or attempt == 5:
            break
        for (i, h, U, V, Wcur, Wnew) in reversed(trial):  # revert, resample
            apply_switch(h, U, V, Wnew, Wcur)
            members[i][4] = Wcur
    logline(f"[cycle {cycle_n+1}] KICK 1-pair members {members[i1][0]},{members[i2][0]} "
            f"-> res {res_kick} ({res_kick/L/L*100:.4f}%), excess {kick_excess:+d} "
            f"(tries {attempt+1}), seed {seed}")
    res_cur = res_kick
    walk_min = res_cur
    # ---- reheat: T0 sized to the kick excess ----
    T0 = min(T0_MAX, max(T0_MIN, kick_excess / 5.0 if kick_excess > 0 else T0_MIN))
    temper_elapsed = 0.0
    save_ckpt("temper", 0.0, T0)

# ---------- TEMPER ----------
t_c = time.time()
last_ckpt = time.time()
tried = acc = 0
while True:
    el = temper_elapsed + (time.time() - t_c)
    if el >= BUDGET_TEMPER:
        break
    frac = el / BUDGET_TEMPER
    T = T0 * (T1 / T0) ** frac
    r = random.random()
    if r < P_NEAR or len(members) < 2:
        i = random.randrange(len(members))
        q, h, U, V, Wold = members[i]
        Wnew = near_W(i, Wold)
        if Wnew == Wold:
            continue
        stats["near"] += 1
        tried += 1; stats["tried"] += 1
        d = delta_eval(h, U, V, Wold, Wnew)
        stats["min_delta"] = min(stats["min_delta"], d)
        stats["max_delta"] = max(stats["max_delta"], d)
        if d < 0:
            stats["neg_props"] += 1
        if d <= 0 or (d > 0 and random.random() < math.exp(-d / T)):
            apply_switch(h, U, V, Wold, Wnew)
            members[i][4] = Wnew
            acc += 1; stats["acc"] += 1
            if d == 0: stats["acc_neut"] += 1
            elif d > 0: stats["acc_up"] += 1
            res_cur += d
            walk_min = min(walk_min, res_cur)
            if res_cur < best_res:
                r_true = full_res()
                res_cur = r_true
                if r_true < best_res:
                    improve += 1
                    bank(r_true, "near move")
                    if r_true == 0:
                        break
                elif r_true != res_cur:
                    logline(f"[warn] tracked {res_cur} vs scan {r_true}")
    elif r < P_NEAR + P_FAR:
        i = random.randrange(len(members))
        q, h, U, V, Wold = members[i]
        Wnew = far_W(i)
        if Wnew == Wold:
            continue
        stats["far"] += 1
        tried += 1; stats["tried"] += 1
        d = delta_eval(h, U, V, Wold, Wnew)
        stats["min_delta"] = min(stats["min_delta"], d)
        stats["max_delta"] = max(stats["max_delta"], d)
        if d < 0:
            stats["neg_props"] += 1
        if d <= 0 or (d > 0 and random.random() < math.exp(-d / T)):
            apply_switch(h, U, V, Wold, Wnew)
            members[i][4] = Wnew
            acc += 1; stats["acc"] += 1
            if d == 0: stats["acc_neut"] += 1
            elif d > 0: stats["acc_up"] += 1
            res_cur += d
            walk_min = min(walk_min, res_cur)
            if res_cur < best_res:
                r_true = full_res()
                res_cur = r_true
                if r_true < best_res:
                    improve += 1
                    bank(r_true, "far move")
                    if r_true == 0:
                        break
    else:
        i1, i2 = random.sample(range(len(members)), 2)
        l1, l2 = members[i1], members[i2]
        q1, h1, U1, V1, Wold1 = l1
        q2, h2, U2, V2, Wold2 = l2
        Wnew1 = near_W(i1, Wold1)
        if Wnew1 == Wold1:
            continue
        stats["pair"] += 1
        tried += 1; stats["tried"] += 1
        d1 = delta_eval(h1, U1, V1, Wold1, Wnew1)
        apply_switch(h1, U1, V1, Wold1, Wnew1)
        Wnew2 = near_W(i2, Wold2) if random.random() < 0.7 else far_W(i2)
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
            acc += 1; stats["acc"] += 1
            if d_total == 0: stats["acc_neut"] += 1
            elif d_total > 0: stats["acc_up"] += 1
            res_cur += d_total
            walk_min = min(walk_min, res_cur)
            if res_cur < best_res:
                r_true = full_res()
                res_cur = r_true
                if r_true < best_res:
                    improve += 1
                    bank(r_true, "pair move")
                    if r_true == 0:
                        break
        else:
            apply_switch(h1, U1, V1, Wnew1, Wold1)
    if time.time() - last_ckpt >= CKPT_EVERY:
        r_now = full_res()
        if r_now != res_cur:
            logline(f"[ckpt] DRIFT tracked {res_cur} vs scan {r_now}; adopting scan")
            res_cur = r_now
        logline(f"[ckpt c{cycle_n+1}] t={temper_elapsed + (time.time()-t_c):.0f}s "
                f"res {res_cur} ({res_cur/L/L*100:.4f}%) T={T0*(T1/T0)**min((temper_elapsed+(time.time()-t_c))/BUDGET_TEMPER,1.0):.0f} "
                f"acc {stats['acc']}/{stats['tried']}")
        save_ckpt("temper", temper_elapsed + (time.time() - t_c), T0)
        last_ckpt = time.time()

# ---------- cycle end ----------
r_end = full_res()
temper_elapsed += time.time() - t_c
logline(f"[cycle {cycle_n+1}] temper end ({temper_elapsed:.0f}s): res {r_end} "
        f"({r_end/L/L*100:.4f}%), walk-min {walk_min}, tried {stats['tried']}, "
        f"acc {stats['acc']} (neut {stats['acc_neut']}, up {stats['acc_up']}), "
        f"props near/far/pair {stats['near']}/{stats['far']}/{stats['pair']}, "
        f"neg {stats['neg_props']}, delta range [{stats['min_delta']}, {stats['max_delta']}]")

if r_end == 0:
    atomic_json({"L": L, "layers": [list(x) for x in live]},
                W + "covering_closed_27720v5.json")
    atomic_json(live, W + "state27720live.json")
    logline("=== KILL: COVERING CLOSED (cycle end) ===")
    sys.exit(0)

if r_end > best_res:
    n_back = 0
    for i in range(len(live)):
        if live[i][4] != best_layers[i][4]:
            q, h, U, V, Wcur = live[i]
            apply_switch(h, U, V, Wcur, best_layers[i][4])
            live[i][4] = best_layers[i][4]
            n_back += 1
    r_chk = full_res()
    if r_chk != best_res:
        logline(f"[cycle {cycle_n+1}] WARN reset drift {r_chk} vs best {best_res}")
    logline(f"[cycle {cycle_n+1}] basin failed -> {n_back} switch-backs to best {best_res}")
elif r_end == best_res:
    logline(f"[cycle {cycle_n+1}] ended AT best (plateau)")

atomic_json(live, W + "state27720live.json")
atomic_json({
    "cycle": cycle_n + 1, "phase": "done", "temper_elapsed": temper_elapsed,
    "res_cur": best_res if r_end > best_res else r_end, "best": best_res,
    "stats": stats, "walk_min": walk_min,
    "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
}, W + "ckpt_v5.json")
logline(f"== v5 cycle {cycle_n+1} done: best {best_res} ({best_res/L/L*100:.4f}%), "
        f"improvements this session {improve}, wall {(time.time()-t0):.0f}s")
