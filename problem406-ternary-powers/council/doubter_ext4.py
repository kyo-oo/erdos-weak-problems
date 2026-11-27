import json, time
def v2star(M, tmax=None):
    h1 = (M + 1) // 2
    A = [0]
    for i in range(h1): A = A + [a + 3**i for a in A]
    B = [0]
    for i in range(h1, M + 1): B = B + [b + 3**i for b in B]
    best = 0
    for lst in (A, B):
        for a in lst:
            if a != 0:
                x = (a & -a).bit_length() - 1
                if x > best: best = x
    if tmax is None: tmax = M + 14
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
v = v2star(44)
results['44'] = v
print(f"M=44 v2*={v} excess={v-44} rider_margin={v - 1.5849625*44:+.1f}", flush=True)
json.dump(results, open('S094_v2star_recomputed.json','w'), indent=0)
print("WALL", time.time()-t0)
