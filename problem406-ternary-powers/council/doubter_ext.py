import json, time

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
        if a != 0 and v2(a) > best: best = v2(a)
    for b in B:
        if b != 0 and v2(b) > best: best = v2(b)
    if tmax is None: tmax = M + 12
    Bnz = [b for b in B if b != 0]
    for t in range(1, tmax + 1):
        mod = 1 << t
        Amod = set(a % mod for a in A)
        if not any((-b) % mod in Amod for b in Bnz):
            break
        if t > best: best = t
    return best

results = json.load(open('S094_v2star_recomputed.json'))
t0 = time.time()
for M in range(37, 42):
    v = v2star(M)
    results[str(M)] = v
    print(f"M={M} v2*={v} excess={v-M}", flush=True)
json.dump(results, open('S094_v2star_recomputed.json','w'), indent=0)
print("WALL", time.time() - t0, flush=True)
