"""L=27720 closure — ROUND-BASED (channel law: no persistent background procs).

Usage: python3 close_cover_27720d.py            # round 1: sequential greedy sweep
State: state27720.json (layer list) + unc27720.npy (96MB bit-packed bitmap).
Each invocation = ONE greedy pass, state saved to disk, exits.
Budget: 41 primes, 1.0563 >= 1 — feasible.
"""
import json, time
import numpy as np

L = 27720
BITS = L * L
pal = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/pal_dlog_full.json"))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]
pal = [r for r in pal if L % r[1] == 0]
bases = {}
for (q, h, U, V) in pal:
    p = q
    for d in range(2, int(q**0.5) + 1):
        if q % d == 0:
            p = d
            break
    if p not in bases or 1.0 / h > 1.0 / bases[p][1]:
        bases[p] = (q, h, U, V)
fam = sorted(bases.values(), key=lambda r: -1.0 / r[1])
print(f"L={L} family: {len(fam)} primes, budget {sum(1.0/r[1] for r in fam):.4f}", flush=True)

try:
    layers = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/state27720.json"))
    unc = np.load("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/unc27720.npy")
    print(f"resumed: {len(layers)} layers", flush=True)
except Exception:
    layers = []
    unc = np.ones(BITS // 8 + 1, dtype=np.uint8)
    print("fresh start", flush=True)

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

def apply_coset(h, U, V, W):
    lmod = ks % h
    for a in range(0, L, CH):
        b = min(a + CH, L)
        r = ks[a:b] % h
        vals = (U * r[:, None] + V * lmod[None, :]) % h
        hit = (vals == W)
        seg = unc[a * L // 8:(b * L + 7) // 8]
        bits = np.unpackbits(seg, bitorder='little')[: (b - a) * L].reshape(b - a, L)
        bits[hit] = 0
        packed = np.packbits(bits.reshape(-1), bitorder='little')
        unc[a * L // 8:a * L // 8 + len(packed)] = packed
        del vals, hit, bits, packed

def remaining():
    return int(np.unpackbits(unc, bitorder='little')[:BITS].sum())

t0 = time.time()
round_no = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/round27720.json")) if __import__('os').path.exists("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/round27720.json") else 0
round_no += 1

for idx in range(len(fam)):
    q, h, U, V = fam[idx]
    if any(lay[0] == q for lay in layers):
        continue  # member already has a layer (sticky greedy)
    counts = count_per_W(h, U, V)
    W = int(np.argmax(counts))
    if counts[W] == 0:
        layers.append([int(q), int(h), int(U), int(V), -1])  # member useless
        continue
    apply_coset(h, U, V, W)
    layers.append([int(q), int(h), int(U), int(V), int(W)])
    rem = remaining()
    print(f"r{round_no} q={q:6d} h={h:5d} W={W:5d} new={counts[W]:8d} rem={rem:9d} ({rem/L/L*100:.2f}%) ({time.time()-t0:.0f}s)", flush=True)

rem = remaining()
json.dump(layers, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/state27720.json", "w"))
np.save("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/unc27720.npy", unc)
json.dump(round_no, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/round27720.json", "w"))
print(f"== round {round_no} done: remaining {rem} ({rem/L/L*100:.2f}%), layers {len(layers)} ({time.time()-t0:.0f}s)", flush=True)
if rem == 0:
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [l for l in layers if l[4] >= 0]},
              open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/covering_closed_27720.json", "w"))
    print("wrote covering_closed_27720.json")
