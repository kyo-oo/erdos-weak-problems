"""Close the Sierpinski 2*3 covering over Z_L^2, L=27720, multi-sweep greedy.

Layers: one coset per prime (q, h, U, V, W). Sweeps: repeat passes where
every prime re-picks the W maximizing newly covered mass on the CURRENT
uncovered set (allowing W changes). Chunked over k-columns.
"""
import json, time
import numpy as np

L = 27720
pal = json.load(open("../pal_dlog_full.json"))
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
print(f"family (distinct bases, h|{L}): {len(fam)}, budget {sum(1.0/r[1] for r in fam):.4f}", flush=True)

CH = 640
ks = np.arange(L, dtype=np.int64)
lmod_full = ks % 1  # placeholder

def chunk_iter():
    for a in range(0, L, CH):
        yield a, min(a + CH, L)

# uncovered: list of 2D bool arrays per k-chunk (k-chunk x L)
unc = [np.ones((b - a, L), dtype=bool) for a, b in chunk_iter()]
total = L * L

def sweep(fixed):
    """one pass: for each unused prime (or re-pickable), choose best W"""
    changed = False
    for idx in range(len(fam)):
        q, h, U, V = fam[idx]
        counts = np.zeros(h, dtype=np.int64)
        for ci, (a, b) in enumerate(chunk_iter()):
            kc = ks[a:b]
            r = kc % h
            lmod = ks % h
            vals = (U * r[:, None] + V * lmod[None, :]) % h
            m = unc[ci][vals == 0]  # dummy to force types
            cnts = np.zeros(h, dtype=np.int64)
            # bincount over vals at uncovered positions
            um = unc[ci]
            v = vals[um]
            cnts += np.bincount(v, minlength=h)
            counts += cnts
        W = int(np.argmax(counts))
        if counts[W] == 0:
            continue
        if idx in fixed and fixed[idx] == W:
            continue
        # apply this coset; REMOVE the old coset of this prime if re-picking?
        # (re-picking invalidates previous coverage -> skip re-picks in sw1)
        fixed[idx] = W
        # apply
        for ci, (a, b) in enumerate(chunk_iter()):
            kc = ks[a:b]
            r = kc % h
            lmod = ks % h
            vals = (U * r[:, None] + V * lmod[None, :]) % h
            unc[ci][vals == W] = False
        changed = True
        rem = sum(int(u.sum()) for u in unc)
        print(f"  q={q:6d} h={h:5d} W={W:5d} new={counts[W]:9d} rem={rem:10d} ({time.time()-t0:.0f}s)", flush=True)
        if rem == 0:
            return True
    return sum(int(u.sum()) for u in unc) == 0

t0 = time.time()
fixed = {}
closed = sweep(fixed)
rem = sum(int(u.sum()) for u in unc)
print(f"after sweep1: remaining {rem} ({rem/L/L*100:.2f}%)", flush=True)

if not closed:
    # sweep2: fresh start, primes in different order (smallest h first),
    # guided: process primes by best marginal again on current uncovered
    order = sorted(range(len(fam)), key=lambda i: -1.0 / fam[i][1])
    for idx in order:
        if rem == 0:
            break
        q, h, U, V = fam[idx]
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
        fixed[idx] = W
        for ci, (a, b) in enumerate(chunk_iter()):
            kc = ks[a:b]
            r = kc % h
            lmod = ks % h
            vals = (U * r[:, None] + V * lmod[None, :]) % h
            unc[ci][vals == W] = False
        rem = sum(int(u.sum()) for u in unc)
        print(f"  s2 q={q:6d} h={h:5d} W={W:5d} new={counts[W]:9d} rem={rem:10d}", flush=True)

print(f"FINAL REMAINING: {rem} ({rem/L/L*100:.2f}%)")
if rem == 0:
    print("COVERING CLOSED")
    layers = []
    for idx, W in fixed.items():
        q, h, U, V = fam[idx]
        layers.append([q, h, U, V, W])
    json.dump({"L": L, "layers": layers}, open("covering_closed.json", "w"))
    print(f"wrote covering_closed.json with {len(layers)} layers")
