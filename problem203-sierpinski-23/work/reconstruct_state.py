"""Reconstruct state27720.json from the round-1 log output (L80 salvage).

Round 1 completed the greedy (41 layers, 1.58% remaining) but died before
its final save. The W choices are recorded in the log; fam (q,h,U,V) is
deterministically recomputed from pal_dlog_full.json.
"""
import json

L = 27720
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

# (q, W) pairs from the round-1 log (order = fam order)
W_FROM_LOG = [
    (5, 0), (7, 0), (11, 1), (23, 0), (13, 2), (19, 1), (29, 1), (31, 2),
    (71, 4), (37, 1), (73, 4), (41, 18), (43, 31), (61, 2), (67, 1),
    (89, 40), (241, 25), (127, 28), (337, 8), (181, 10), (199, 12),
    (211, 41), (281, 20), (331, 259), (397, 106), (421, 158), (463, 80),
    (1009, 250), (617, 532), (631, 356), (661, 58), (1321, 130),
    (991, 808), (2971, 125), (2521, 779), (3697, 62), (7393, 238),
    (2311, 1040), (9241, 2239),
]

wmap = dict(W_FROM_LOG)
layers = []
for (q, h, U, V) in fam:
    W = wmap.get(q)
    if W is None:
        layers.append([int(q), int(h), int(U), int(V), -1])
    else:
        layers.append([int(q), int(h), int(U), int(V), int(W)])

assert len(layers) == len(fam), f"layer count {len(layers)} vs fam {len(fam)}"
missing = [l[0] for l in layers if l[4] < 0]
print(f"reconstructed {len(layers)} layers; missing: {missing}")
json.dump(layers, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/state27720.json", "w"))
json.dump(1, open("/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/round27720.json", "w"))
print("state27720.json + round27720.json written")
