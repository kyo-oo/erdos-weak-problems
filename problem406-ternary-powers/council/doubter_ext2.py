import json, time, sys

def v2(x):
    if x == 0: return 1 << 30
    return (x & -x).bit_length() - 1

def v2star(M, tmax=None):
    h1 = (M + 1) // 2
    A = [0]
    for i in range(h1): A = A + [a + 3**i for a in A]
    B = [0]
    for i in range(h1, M + 1): B = B + [b + 3**i for b in B]
    best = 0
    for a in A:
        if a != 0:
            t = (a & -a).bit_length() - 1
            if t > best: best = t
    for b in B:
        if b != 0:
            t = (b & -b).bit_length() - 1
            if t > best: best = t
    if tmax is None: tmax = M + 14
    Bnz = [b for b in B if b != 0]
    Bneg = None
    for t in range(1, tmax + 1):
        mod = 1 << t
        if Bneg is None:
            Bneg = [(-b) % mod for b in Bnz]
        else:
            Bneg = [x % mod for x in Bneg]
        Amod = set(a % (1 << (t-1)) for a in A) if False else None
        Amod = set()
        for a in A: Amod.add(a % mod)
        ok = False
        for x in Bneg:
            if x in Amod: ok = True; break
        if not ok: break
        if t > best: best = t
    return best

results = json.load(open('S094_v2star_recomputed.json'))
t0 = time.time()
for M in [42, 43, 44]:
    v = v2star(M)
    results[str(M)] = v
    print(f"M={M} v2*={v} excess={v-M} rider_margin={v - 1.5849625*M:+.1f}", flush=True)
    json.dump(results, open('S094_v2star_recomputed.json','w'), indent=0)
print("WALL", time.time() - t0, flush=True)
