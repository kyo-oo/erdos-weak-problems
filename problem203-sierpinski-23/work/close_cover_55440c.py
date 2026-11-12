"""L=55440 closure, MEMORY-LEAN: 384MB packbits bitmap + CH=2048 int64 chunks.

The r1/r2 engines died OOM (full-bool 3.1GB / 4096-chunk vals 1.8GB).
This one: unc = bit-packed uint8 (L*L bits = 384MB), chunk transients
<= 908MB, freed per chunk. Greedy + iterative sweeps until closed.
"""
import json, time
import numpy as np

L = 55440
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

unc = np.full(BITS // 8 + 1, 0xFF, dtype=np.uint8)   # 384MB bit-packed
total = BITS
ks = np.arange(L, dtype=np.int64)
CH = 1024
print(f"bitmap allocated: {BITS//8+1} bytes; CH={CH}", flush=True)

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
fixed = {}
for rnd in range(12):
    for idx in range(len(fam)):
        q, h, U, V = fam[idx]
        if idx in fixed:
            # re-check: does the fixed coset still need to move?
            counts = count_per_W(h, U, V)
            W = int(np.argmax(counts))
            if counts[W] == 0:
                continue
            if fixed[idx] == W:
                continue
            fixed[idx] = W
            apply_coset(h, U, V, W)
        else:
            counts = count_per_W(h, U, V)
            W = int(np.argmax(counts))
            if counts[W] == 0:
                continue
            fixed[idx] = W
            apply_coset(h, U, V, W)
            rem = remaining()
            print(f"r{rnd} q={q:6d} h={h:5d} W={W:5d} new={counts[W]:9d} rem={rem:10d} ({rem/L/L*100:.2f}%) ({time.time()-t0:.0f}s)", flush=True)
    rem = remaining()
    print(f"== round {rnd}: remaining {rem} ({rem/L/L*100:.2f}%) ({time.time()-t0:.0f}s)", flush=True)
    if rem == 0:
        break

rem = remaining()
if rem == 0:
    print("COVERING CLOSED")
    layers = [[q, h, U, V, fixed[i]] for i, (q, h, U, V) in enumerate(fam) if i in fixed]
    json.dump({"L": L, "layers": layers}, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/covering_closed_55440.json", "w"))
    print(f"wrote covering_closed_55440.json with {len(layers)} layers")
else:
    print(f"NOT CLOSED: {rem} ({rem/L/L*100:.2f}%)")
