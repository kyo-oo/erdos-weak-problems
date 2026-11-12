"""L=27720 closure — ALL-MEMBER engine (S054 fix: no base dedup).

The r1 engine deduped the palette by smallest prime factor (41 members,
budget 1.0563) — an unnecessary restriction: the covering condition
allows every palette prime with h | L. This engine uses ALL of them
(hundreds of members), greedy by density, with:
  - incremental state save after EVERY layer (L80: never lose compute),
  - no per-member remaining() scans (only per round),
  - resumable rounds (channel law: one call = one bounded pass).
"""
import json, time, os
import numpy as np

L = 27720
BITS = L * L
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
pal = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/pal_dlog_full.json"))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]
fam_all = [r for r in pal if L % r[1] == 0]
fam_all.sort(key=lambda r: -1.0 / r[1])
print(f"L={L} ALL-member family: {len(fam_all)} primes, budget {sum(1.0/r[1] for r in fam_all):.4f}", flush=True)

if os.path.exists(W + "state27720all.json"):
    layers = json.load(open(W + "state27720all.json"))
    unc = np.load(W + "unc27720all.npy")
    print(f"resumed: {len(layers)} layers, remaining {int(np.unpackbits(unc, bitorder='little')[:BITS].sum())}", flush=True)
else:
    layers = []
    unc = np.ones(BITS // 8 + 1, dtype=np.uint8)
    print("fresh start", flush=True)

placed = {l[0] for l in layers}
ks = np.arange(L, dtype=np.int64)
CH = 512

def count_per_W(h, U, V):
    counts = np.zeros(h, dtype=np.int64)
    lmod = ks % h
    for a in range(0, L, CH):
        b = min(a + CH, L)
        r = ks[a:b] % h
        vals = (U * r[:, None] + V * lmod[None, :]) % h
        seg = unc[a * L // 8:(b * L + 7) // 8]
        bits = np.unpackbits(seg, bitorder='little')[: (b - a) * L].reshape(b - a, L)
        counts += np.bincount(vals.ravel(), weights=bits.ravel(), minlength=h).astype(np.int64)
        del vals, bits
    return counts

def apply_coset(h, U, V, Wv):
    lmod = ks % h
    for a in range(0, L, CH):
        b = min(a + CH, L)
        r = ks[a:b] % h
        vals = (U * r[:, None] + V * lmod[None, :]) % h
        hit = (vals == Wv)
        seg = unc[a * L // 8:(b * L + 7) // 8]
        bits = np.unpackbits(seg, bitorder='little')[: (b - a) * L].reshape(b - a, L)
        bits[hit] = 0
        packed = np.packbits(bits.reshape(-1), bitorder='little')
        unc[a * L // 8:a * L // 8 + len(packed)] = packed
        del vals, hit, bits, packed

def remaining():
    return int(np.unpackbits(unc, bitorder='little')[:BITS].sum())

t0 = time.time()
rnd = 0
try:
    rnd = json.load(open(W + "round27720all.json"))
except Exception:
    pass
rnd += 1
BUDGET_S = 520

for (q, h, U, V) in fam_all:
    if q in placed:
        continue
    if time.time() - t0 > BUDGET_S:
        print("budget reached; state saved; rerun for next round", flush=True)
        break
    counts = count_per_W(h, U, V)
    Wv = int(np.argmax(counts))
    if counts[Wv] == 0:
        layers.append([int(q), int(h), int(U), int(V), -1])
        placed.add(q)
        json.dump(layers, open(W + "state27720all.json", "w"))  # incremental (L80)
        continue
    apply_coset(h, U, V, Wv)
    layers.append([int(q), int(h), int(U), int(V), int(Wv)])
    placed.add(q)
    json.dump(layers, open(W + "state27720all.json", "w"))  # incremental (L80)
    np.save(W + "unc27720all.npy", unc)
    print(f"r{rnd} q={q:6d} h={h:5d} W={Wv:5d} new={counts[Wv]:8d} ({time.time()-t0:.0f}s)", flush=True)

rem = remaining()
np.save(W + "unc27720all.npy", unc)
json.dump(rnd, open(W + "round27720all.json", "w"))
json.dump(layers, open(W + "state27720all.json", "w"))
print(f"== round {rnd} done: remaining {rem} ({rem/L/L*100:.3f}%), layers {len(layers)}/{len(fam_all)} ({time.time()-t0:.0f}s)", flush=True)
if rem == 0:
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [l for l in layers if l[4] >= 0]},
              open(W + "covering_closed_27720all.json", "w"))
    print(f"wrote covering_closed_27720all.json with {sum(1 for l in layers if l[4] >= 0)} layers")
