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
# drop the untrusted ext2 entries
for k in ['42','43','44']:
    results.pop(k, None)
t0 = time.time()
for M in [42, 43]:
    v = v2star(M)
    results[str(M)] = v
    print(f"M={M} v2*={v} excess={v-M} rider_margin={v - 1.5849625*M:+.1f}", flush=True)
    json.dump(results, open('S094_v2star_recomputed.json','w'), indent=0)
print("WALL", time.time()-t0)
