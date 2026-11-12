"""L=55440 closure: greedy + iterative sweeps until closed. Standalone."""
import json, time
import numpy as np

L = 55440
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

CH = 320
ks = np.arange(L, dtype=np.int64)

def chunk_iter():
    for a in range(0, L, CH):
        yield a, min(a + CH, L)

unc = [np.ones((b - a, L), dtype=bool) for a, b in chunk_iter()]
print(f"chunks: {len(unc)}", flush=True)

t0 = time.time()
fixed = {}
for rnd in range(6):
    for idx in range(len(fam)):
        q, h, U, V = fam[idx]
        # count per W on uncovered
        counts = np.zeros(h, dtype=np.int64)
        for ci, (a, b) in enumerate(chunk_iter()):
            kc = ks[a:b]
            r = kc % h
            lmod = ks % h
            vals = (U * r[:, None] + V * lmod[None, :]) % h
            v = vals[unc[ci]]
            counts += np.bincount(v, minlength=h)
        W = int(np.argmax(counts))
        if counts[W] == 0:
            continue
        if idx in fixed and fixed[idx] == W:
            continue
        fixed[idx] = W
        for ci, (a, b) in enumerate(chunk_iter()):
            kc = ks[a:b]
            r = kc % h
            lmod = ks % h
            vals = (U * r[:, None] + V * lmod[None, :]) % h
            unc[ci][vals == W] = False
        rem = sum(int(u.sum()) for u in unc)
        print(f"r{rnd} q={q:6d} h={h:5d} W={W:5d} new={counts[W]:9d} rem={rem:10d} ({time.time()-t0:.0f}s)", flush=True)
        if rem == 0:
            break
    rem = sum(int(u.sum()) for u in unc)
    print(f"== round {rnd} done: remaining {rem} ({rem/L/L*100:.2f}%) ({time.time()-t0:.0f}s)", flush=True)
    if rem == 0:
        break

rem = sum(int(u.sum()) for u in unc)
if rem == 0:
    print("COVERING CLOSED")
    layers = []
    for idx, W in fixed.items():
        q, h, U, V = fam[idx]
        layers.append([q, h, U, V, W])
    json.dump({"L": L, "layers": layers}, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/covering_closed_55440.json", "w"))
    print(f"wrote covering_closed_55440.json with {len(layers)} layers")
else:
    print(f"NOT CLOSED: {rem} remaining ({rem/L/L*100:.2f}%)")
