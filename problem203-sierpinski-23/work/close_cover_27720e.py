"""L=27720 closure — REPAIR ENGINE (W-moves with exact rebuilds).

Channel law: no persistent procs; one call = a few repair moves.
Per move: rebuild bitmap minus member i (exact), argmax-repick W_i, apply.
A move is kept only if the new W covers more than the old W.
State on disk: state27720.json + unc27720.npy.
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
layers = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/state27720.json"))
print(f"L={L} family: {len(fam)}, layers {len(layers)}", flush=True)

ks = np.arange(L, dtype=np.int64)
CH = 512

unc = np.ones(BITS // 8 + 1, dtype=np.uint8)

def apply_coset(u, h, U, V, W):
    lmod = ks % h
    for a in range(0, L, CH):
        b = min(a + CH, L)
        r = ks[a:b] % h
        vals = (U * r[:, None] + V * lmod[None, :]) % h
        hit = (vals == W)
        seg = u[a * L // 8:(b * L + 7) // 8]
        bits = np.unpackbits(seg, bitorder='little')[: (b - a) * L].reshape(b - a, L)
        bits[hit] = 0
        packed = np.packbits(bits.reshape(-1), bitorder='little')
        u[a * L // 8:a * L // 8 + len(packed)] = packed
        del vals, hit, bits, packed

def count_per_W(u, h, U, V):
    counts = np.zeros(h, dtype=np.int64)
    lmod = ks % h
    for a in range(0, L, CH):
        b = min(a + CH, L)
        r = ks[a:b] % h
        vals = (U * r[:, None] + V * lmod[None, :]) % h
        seg = u[a * L // 8:(b * L + 7) // 8]
        bits = np.unpackbits(seg, bitorder='little')[: (b - a) * L].reshape(b - a, L)
        counts += np.bincount(vals.ravel(), weights=bits.ravel(), minlength=h).astype(np.int64)
        del vals, bits
    return counts

def remaining(u):
    return int(np.unpackbits(u, bitorder='little')[:BITS].sum())

t0 = time.time()
moves = 0
BUDGET_S = 500

# order members by potential: try members whose current W has small coverage first
try:
    order = json.load(open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/repair_order.json"))
except Exception:
    order = list(range(len(fam)))

for idx in order:
    if time.time() - t0 > BUDGET_S:
        break
    q, h, U, V = fam[idx]
    lay = next((l for l in layers if l[0] == q), None)
    if lay is None or lay[4] < 0:
        continue
    # exact rebuild: all-ones, apply all layers EXCEPT member q
    unc[:] = 1
    for l2 in layers:
        if l2[0] != q and l2[4] >= 0:
            apply_coset(unc, l2[1], l2[2], l2[3], l2[4])
    counts = count_per_W(unc, h, U, V)
    Wnew = int(np.argmax(counts))
    Wold = int(lay[4])
    if counts[Wnew] > counts[Wold]:
        apply_coset(unc, h, U, V, Wnew)
        lay[4] = Wnew
        rem = remaining(unc)
        print(f"MOVE q={q:6d} h={h:5d} W {Wold}->{Wnew} cover {counts[Wold]}->{counts[Wnew]} rem={rem} ({rem/L/L*100:.2f}%) ({time.time()-t0:.0f}s)", flush=True)
        moves += 1
        json.dump(layers, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/state27720.json", "w"))
        np.save("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/unc27720.npy", unc)
        if rem == 0:
            print("COVERING CLOSED")
            json.dump({"L": L, "layers": [l for l in layers if l[4] >= 0]},
                      open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/covering_closed_27720.json", "w"))
            break

rem = remaining(unc)
json.dump(layers, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/state27720.json", "w"))
np.save("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/unc27720.npy", unc)
print(f"== repair pass done: moves={moves} remaining {rem} ({rem/L/L*100:.2f}%) ({time.time()-t0:.0f}s)", flush=True)
if rem == 0 and not __import__('os').path.exists("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/covering_closed_27720.json"):
    print("COVERING CLOSED")
    json.dump({"L": L, "layers": [l for l in layers if l[4] >= 0]},
              open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/covering_closed_27720.json", "w"))
