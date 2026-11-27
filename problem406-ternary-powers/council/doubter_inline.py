import json, sys

def v2(x):
    if x == 0: return 1 << 30
    return (x & -x).bit_length() - 1

def v2star(M, tmax=None):
    # uniform exact-integer MITM: A = subset sums of low half, B of high half
    h1 = (M + 1) // 2
    low = [3**i for i in range(h1)]
    high = [3**i for i in range(h1, M + 1)]
    A = [0]
    for p in low: A = A + [a + p for a in A]
    B = [0]
    for p in high: B = B + [b + p for b in B]
    # nonempty witnesses inside one half:
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

results = {}
t0 = __import__('time').time()
for M in range(0, 37):
    v = v2star(M)
    results[M] = v
    print(f"M={M} v2*={v} excess={v-M}", flush=True)

json.dump(results, open('S094_v2star_recomputed.json','w'), indent=0)
print("WALL", __import__('time').time() - t0, flush=True)

# compare with the campaign table
camp = json.load(open('../caplaw/v2star_table.json'))
if isinstance(camp, dict):
    mism = []
    items = camp.get('v2star', camp)
    for k, val in items.items():
        try:
            m = int(k)
            if m in results and int(val) != results[m]:
                mism.append((m, val, results[m]))
        except Exception: pass
    print("CAMPAIGN-TABLE MISMATCHES:", mism if mism else "NONE — third-method agreement")
