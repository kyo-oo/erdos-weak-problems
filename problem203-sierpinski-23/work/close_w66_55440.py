#!/usr/bin/env python3
"""
close_w66_55440.py — THE W66 L=55440 COVERING HUNT (sound greedy engine).

W65 post-mortem (why this rewrite):
  * close_cover_55440.py/b OOM'd (full-bool 3.1GB / 4096-chunk int64 1.8GB);
  * close_cover_55440c.py only CLEARED bits (never un-applied a member's old
    coset on a W switch): its bitmap accumulated MULTIPLE cosets per prime
    over rounds, so any "CLOSED" claim from it would be unsound; it also
    never finished a round in the logs (453MB int64 chunk transients).

SOUNDNESS ANALYSIS (the W66 law for this engine):
  * state = ONE coset per family prime (the true hunt object);
  * two packed bitmaps (unc = count==0 cells, once = count==1 cells) are
    EXACT under APPLY (0->1, 1->>=2 are unambiguous) but NOT under UNAPPLY
    (a cell with count >= 2 could be exactly 2 or more; removal ambiguity).
    => THIS ENGINE NEVER UNAPPLIES: it runs apply-only greedy sequences,
       each restart rebuilding the cover from scratch.  The residual
       (popcount of unc) is EXACT at every point.  (Coordinate-descent
       switches need exact counts: at 55440 that is a 3.07GB int8 map —
       documented as the W67 disk-memmap design in STATUS203_W66E.md.)
  * per-member placement pass = one chunked sweep giving the FULL gain
    histogram G[W] for every W (bincount of (U k + V l) mod h over the
    currently-uncovered cells) -> W = argmax (or top-k randomized for
    restart diversity).

Hunt modes (this run):
  0. seed rebuild: the W65 greedy W's (state55440_base.json), applied SOUNDLY
     (one coset per prime) -> the first-ever honest 55440 residual;
  1. greedy-add the 3 NEW W66 palette members (18481, 110881, 332641);
  2. restarts: from-scratch greedy with shuffled member order and
     randomized top-k W picks; every improvement banked atomically to
     bestres55440_w66.txt + state55440_w66.json + close_w66_55440.log.

Family: pal_dlog_w66.json (the W66 complete 55-prime family, budget 1.163041,
full factorization of gcd(2^55440-1, 3^55440-1) — w66_palette.py).

Usage: close_w66_55440.py [wall_budget_s] [n_restarts]
"""
import json, os, time, math, random, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..")
L = 55440
NB = L // 8                      # 6930 bytes per row (L divisible by 8)
CH = 96                          # rows per chunk
LOG = os.path.join(HERE, "close_w66_55440.log")
WALL = float(sys.argv[1]) if len(sys.argv) > 1 else 5400.0
NRST = int(sys.argv[2]) if len(sys.argv) > 2 else 8

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

# ---------------- family ----------------
pal = json.load(open(os.path.join(OUT, "pal_dlog_w66.json")))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal if L % int(r[1]) == 0]
bases = {}
for (q, h, U, V) in pal:                 # dedup by base prime, keep min h
    p = q; d = 2
    while d * d <= q:
        if q % d == 0: p = d; break
        d += 1
    if p not in bases or 1.0 / h > 1.0 / bases[p][1]:
        bases[p] = (q, h, U, V)
fam = sorted(bases.values(), key=lambda r: -1.0 / r[1])

seed_layers_map = {}   # q -> (h, U, V, W) VERBATIM from the W65 state
# (the W labels refer to the W65 (U,V) dlog basis — must not be mixed with
#  the new W66 basis; both are valid coset labelings of the same structure)
try:
    seed_layers = json.load(open(os.path.join(HERE, "state55440_base.json")))
    for r in seed_layers:
        seed_layers_map[int(r[0])] = (int(r[1]), int(r[2]), int(r[3]), int(r[4]))
except Exception as e:
    logline(f"no seed state: {e}")

fam_final = []         # seeded members use the W65 (U,V) basis verbatim
new_members = []       # new W66 palette members
for (q, h, U, V) in fam:
    if q in seed_layers_map:
        h5, U5, V5, W5 = seed_layers_map[q]
        assert h5 == h, f"h mismatch for q={q}: {h5} vs {h}"
        fam_final.append((q, h, U5, V5))
    else:
        fam_final.append((q, h, U, V))
        new_members.append(q)
fam = fam_final
layers = [[q, h, U, V, -1] for (q, h, U, V) in fam]
logline(f"[w66-55440] family: {len(fam)} primes, budget "
        f"{sum(1.0/r[1] for r in fam):.6f}; new palette members: {new_members}")

# ---------------- bitmaps (apply-only engine) ----------------
unc  = np.full((L, NB), 0xFF, dtype=np.uint8)     # every cell uncovered
once = np.zeros((L, NB), dtype=np.uint8)
ks32 = np.arange(L, dtype=np.int32)
_POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.uint32)

def residual():
    return int(_POP[unc].sum())

def clear_all():
    unc[:] = 0xFF; once[:] = 0

def apply_coset(idx, W):
    """mark cells (U k + V l) % h == W as covered (count += 1); layer idx.
    FAST row-mask form: per row k the coset is the residue class
    l = l0(k) mod hg;  hg <= 4096 -> cached full-row packed masks (dense);
    hg > 4096 -> <= L/4096 = 13 sparse bit flips per row."""
    q, h, U, V, Wold = layers[idx]
    g = math.gcd(V, h); hg = h // g
    Vg = (V // g) % hg if hg > 1 else 0
    inv = pow(int(Vg), -1, int(hg)) if hg > 1 else 0
    rhs = (W - U * ks32.astype(np.int64)) % h
    ok = (rhs % g == 0)
    idxok = np.nonzero(ok)[0]
    if not len(idxok): return
    l0arr = ((rhs[idxok] // g) * inv) % hg
    dense = hg <= 4096
    if dense:
        masks = {}
    for t, kk in enumerate(idxok):
        k = int(kk); l0 = int(l0arr[t])
        if dense:
            m = masks.get(l0)
            if m is None:
                pat = np.zeros(L, dtype=bool); pat[l0::hg] = True
                m = np.packbits(pat, bitorder="little")
                masks[l0] = m
            urow = unc[k]
            orow = once[k]
            # once' = (once & ~m) | (unc & m);  unc' = unc & ~m
            once[k] = (orow & ~m) | (urow & m)
            unc[k] = urow & ~m
        else:
            urow = unc[k]
            orow = once[k]
            # sparse: <= L/4096 individual bit flips per row
            for l in range(l0, L, hg):
                byte = l >> 3; bit = 1 << (l & 7)
                if urow[byte] & bit:            # count 0 -> 1
                    orow[byte] |= np.uint8(bit)
                    urow[byte] &= np.uint8(0xFF ^ bit)
                elif orow[byte] & bit:           # count 1 -> >=2 (leaves once)
                    orow[byte] &= np.uint8(0xFF ^ bit)
                # else count >= 2: unchanged

def gain_hist(idx):
    """G[W] = currently-uncovered cells in coset W, for every W (one pass)."""
    q, h, U, V, Wold = layers[idx]
    B32 = ((V * ks32.astype(np.int64)) % h).astype(np.int32)
    G = np.zeros(h, dtype=np.int64)
    for a in range(0, L, CH):
        b = min(a + CH, L)
        A32 = ((U * ks32[a:b].astype(np.int64)) % h).astype(np.int32)
        vals = (A32[:, None] + B32[None, :]) % h
        ub = np.unpackbits(unc[a:b], bitorder="little").reshape(b - a, L).astype(bool)
        G += np.bincount(vals[ub], minlength=h)
        del vals, ub
    return G

# ---------------- banking ----------------
best_res = None
t0 = time.time()
def bank(tag):
    global best_res
    best_res = residual()
    atomic_txt(f"{best_res}\n", os.path.join(HERE, "bestres55440_w66.txt"))
    atomic_json([list(l) for l in layers],
                os.path.join(HERE, "state55440_w66.json"))
    atomic_json({
        "L": L,
        "engine": "close_w66_55440.py (sound apply-only greedy + restarts)",
        "residual": best_res, "residual_pct": best_res / L / L * 100.0,
        "budget": sum(1.0 / l[1] for l in layers if l[4] >= 0),
        "family_size": len(layers), "tag": tag,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }, os.path.join(HERE, "best55440_w66.json"))
    logline(f"BANK res {best_res} ({best_res/L/L*100:.4f}%) [{tag}] "
            f"({time.time()-t0:.0f}s)")

# ---------------- mode 0+1: seed rebuild + greedy new members ----------------
for i, l in enumerate(layers):
    q = l[0]
    if q in seed_layers_map and seed_layers_map[q][3] >= 0:
        l[4] = seed_layers_map[q][3]
        apply_coset(i, l[4])
logline(f"seed rebuild: {sum(1 for l in layers if l[4]>=0)} members applied")
res0 = residual()
logline(f"SEED RESIDUAL (sound, first-ever measurement): {res0} "
        f"({res0/L/L*100:.4f}%)")
bank("w65-seed sound rebuild")

for i, l in enumerate(layers):
    if l[4] < 0:
        G = gain_hist(i)
        W = int(np.argmax(G))
        if G[W] > 0:
            apply_coset(i, W)
            l[4] = W
            r = residual()
            logline(f"greedy new member q={l[0]} h={l[1]} W={W} gain "
                    f"{int(G[W])} -> res {r} ({r/L/L*100:.4f}%)")
            if r < best_res: bank("greedy new palette member")
        else:
            logline(f"greedy new member q={l[0]} h={l[1]}: no gain, skipped")
r_seed = residual()
logline(f"seed + new members residual: {r_seed} ({r_seed/L/L*100:.4f}%)")

# ---------------- mode 2: restarts (from-scratch greedy, randomized) --------
random.seed(20261114)
order0 = list(range(len(layers)))
for rst in range(NRST):
    if time.time() - t0 > WALL: break
    clear_all()
    for l in layers: l[4] = -1
    order = order0 if rst == 0 else random.sample(order0, len(order0))
    topk = 1 if rst == 0 else 3
    for i in order:
        if time.time() - t0 > WALL: break
        G = gain_hist(i)
        if topk == 1:
            W = int(np.argmax(G))
        else:
            cand = np.argsort(G)[-topk:]
            wts = np.array([float(G[c]) for c in cand]) + 1e-9
            W = int(random.choices(cand, weights=wts)[0])
        if G[W] > 0:
            apply_coset(i, W)
            layers[i][4] = W
        elif rst == 0:
            pass
        else:
            # keep inactive only if truly no gain
            if G[int(np.argmax(G))] == 0:
                continue
    r = residual()
    logline(f"[restart {rst}] res {r} ({r/L/L*100:.4f}%) "
            f"(order {'canonical' if rst==0 else 'shuffled'}, topk={topk})")
    if best_res is None or r < best_res:
        bank(f"restart {rst}")

r = residual()
logline(f"== close_w66_55440 DONE: best {best_res} "
        f"({best_res/L/L*100:.4f}%), wall {time.time()-t0:.0f}s")
if r == 0 or best_res == 0:
    logline("=== KILL: COVERING CLOSED at L=55440 ===")
    atomic_json({"L": L, "layers": [list(l) for l in layers]},
                os.path.join(HERE, "covering_closed_55440_w66.json"))
