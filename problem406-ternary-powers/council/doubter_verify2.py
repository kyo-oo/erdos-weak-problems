import json, time

def v2(x):
    return (x & -x).bit_length() - 1

def witness(M, t):
    h1 = (M + 1) // 2
    A = [(0, 0)]
    for i in range(h1): A = A + [(a + 3**i, m | (1 << i)) for a, m in A]
    B = [(0, 0)]
    for i in range(h1, M+1): B = B + [(b + 3**i, m | (1 << i)) for b, m in B]
    mod = 1 << t
    from collections import defaultdict
    Amap = defaultdict(list)
    for a, m in A: Amap[a % mod].append((a, m))
    for b, mb in B:
        r = (-b) % mod
        if r in Amap:
            for a, ma in Amap[r]:
                if a != 0 or b != 0:
                    return ma | mb, a + b
    return None, None

for (M, t) in [(42, 56), (44, 58)]:
    S, n = witness(M, t)
    if S is None:
        print(f"M={M} t={t}: NO WITNESS — flag!"); continue
    pos = [i for i in range(M+1) if (S >> i) & 1]
    val = sum(3**i for i in pos)
    print(f"M={M} t={t}: {len(pos)} digits | direct v2 = {v2(val)} | sum=={val==n} | odd part {val >> t}")
    nxt = witness(M, t+1)
    print(f"  t+1={t+1} witness exists: {nxt[0] is not None}")

# fast points 45, 46
def v2star(M, tmax=None):
    h1 = (M + 1) // 2
    A = [0]
    for i in range(h1): A = A + [a + 3**i for a in A]
    B = [0]
    for i in range(h1, M + 1): B = B + [b + 3**i for b in B]
    best = 0
    for a in A:
        if a != 0:
            x = (a & -a).bit_length() - 1
            if x > best: best = x
    for b in B:
        if b != 0:
            x = (b & -b).bit_length() - 1
            if x > best: best = x
    if tmax is None: tmax = M + 16
    Bnz = [b for b in B if b != 0]
    for t in range(1, tmax + 1):
        mod = 1 << t
        Amod = set(a % mod for a in A)
        ok = any((-b) % mod in Amod for b in Bnz)
        if not ok: break
        if t > best: best = t
    return best

results = json.load(open('S094_v2star_recomputed.json'))
t0 = time.time()
for M in [45, 46]:
    v = v2star(M)
    results[str(M)] = v
    print(f"M={M} v2*={v} excess={v-M} rider_margin={v - 1.5849625*M:+.1f}", flush=True)
json.dump(results, open('S094_v2star_recomputed.json','w'), indent=0)
print("WALL", time.time()-t0)
