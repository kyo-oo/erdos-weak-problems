"""eng203_v7tree.py — THE PRODUCT-REGION COVER TREE for Erdos #203 (W66-K).

Exact DISJOINT cover of Z^2 by product regions R = {k=a mod nu} x {l=b mod nup}
absorbed by palette primes. Absorb law (verified):
  R(a,nu,b,nup) <= C(q,W)  iff  (U*nu)%h==0 and (V*nup)%h==0 and W=(U*a+V*b)%h
i.e. o2(q)|nu, o3(q)|nup, value match. One W per prime globally; re-absorption
at the same W is free.

Splits refine nu or nup by CRT prime factors of L (p children each).
The tree IS the disjointness certificate (leaf densities sum to 1).

Usage: eng203_v7tree.py <palette> <L> <seed> [node_limit]
"""
import json, math, os, random, sys, time
import heapq

PALF = sys.argv[1]
L = int(sys.argv[2]) if len(sys.argv) > 2 else 55440
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 1
NODE_LIMIT = int(sys.argv[4]) if len(sys.argv) > 4 else 400000
W_DIR = os.path.dirname(os.path.abspath(__file__))

pal = json.load(open(PALF))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]
fam = [r for r in pal if L % r[1] == 0]
fam.sort(key=lambda r: -1.0 / r[1])

DATA = []
for (q, h, U, V) in fam:
    o2 = h // math.gcd(h, U)
    o3 = h // math.gcd(h, V)
    DATA.append({"q": q, "h": h, "U": U, "V": V, "o2": o2, "o3": o3})

n = L; FAC = {}
d = 2
while d * d <= n:
    while n % d == 0:
        FAC[d] = FAC.get(d, 0) + 1; n //= d
    d += 1 if d == 2 else 2
if n > 1:
    FAC[n] = FAC.get(n, 0) + 1
FACP = sorted(FAC.keys())

print(f"L={L}: family {len(fam)} primes, budget {sum(1.0/r[1] for r in fam):.4f}", flush=True)

def absorbs(a, nu, b, nup, d):
    h, U, V = d["h"], d["U"], d["V"]
    if (U * nu) % h != 0 or (V * nup) % h != 0:
        return None
    return (U * a + V * b) % h

def run(seed, verbose=True):
    rng = random.Random(seed)
    fixed = {}                       # prime index -> W
    unused = set(range(len(DATA)))
    frontier = []                    # (-density, tiebreak, region)
    tb = 0
    heapq.heappush(frontier, (-1.0, tb, (0, 1, 0, 1))); tb += 1
    leaves = []
    nodes = 0
    stuck = []
    t0 = time.time()
    while frontier and nodes < NODE_LIMIT:
        nodes += 1
        negd, _, region = heapq.heappop(frontier)
        a, nu, b, nup = region
        # 1) free re-absorption by fixed primes
        hit = None
        for qi, W in fixed.items():
            W2 = absorbs(a, nu, b, nup, DATA[qi])
            if W2 is not None and W2 == W:
                hit = (qi, W, True)
                break
        if hit is None:
            # 2) new primes: absorbable?
            cands = [qi for qi in unused
                     if absorbs(a, nu, b, nup, DATA[qi]) is not None]
            if cands:
                # prefer the prime with the LARGEST o2*o3 among absorbable
                # (the specialized ones are wasted elsewhere; versatile
                # small-(o2,o3) primes stay for the many shapes ahead)
                cands.sort(key=lambda qi: (-DATA[qi]["o2"] * DATA[qi]["o3"],
                                           DATA[qi]["q"]))
                qi = cands[0]
                W = absorbs(a, nu, b, nup, DATA[qi])
                hit = (qi, W, False)
        if hit is not None:
            qi, W, isfree = hit
            leaves.append((region, qi, W))
            if not isfree:
                fixed[qi] = W
                unused.discard(qi)
            continue
        # 3) split: pick axis+factor by unused-prime progress
        # progress = the split supplies a MISSING factor of some unused prime's
        # o2 (k-axis) / o3 (l-axis): refined nu becomes a multiple of o2.
        opts = []
        for p in FACP:
            if nu * p <= L:
                prog_k = sum(1 for qi in unused
                             if (nu * p) % DATA[qi]["o2"] == 0 and nu % DATA[qi]["o2"] != 0)
                opts.append((prog_k + 0.5 * rng.random(), "k", p))
            if nup * p <= L:
                prog_l = sum(1 for qi in unused
                             if (nup * p) % DATA[qi]["o3"] == 0 and nup % DATA[qi]["o3"] != 0)
                opts.append((prog_l + 0.5 * rng.random(), "l", p))
        if not opts:
            stuck.append(region)
            continue
        opts.sort(reverse=True)
        _, ax, p = opts[0]
        if ax == "k":
            for j in range(p):
                r = ((a + j * nu) % (nu * p), nu * p, b, nup)
                heapq.heappush(frontier, (-1.0 / (r[1] * r[3]), tb, r)); tb += 1
        else:
            for j in range(p):
                r = (a, nu, (b + j * nup) % (nup * p), nup * p)
                heapq.heappush(frontier, (-1.0 / (r[1] * r[3]), tb, r)); tb += 1
        if nodes % 50000 == 0 and verbose:
            dens = sum(-negd for (negd, _, _) in frontier)
            print(f"  n={nodes} fr={len(frontier)} dens={dens:.5f} "
                  f"fixed={len(fixed)} stuck={len(stuck)} ({time.time()-t0:.0f}s)", flush=True)
    dens = sum(-negd for (negd, _, _) in frontier)
    ok = (not frontier) and (not stuck)
    if verbose:
        print(f"[seed {seed}] nodes={nodes} leaves={len(leaves)} fixed={len(fixed)} "
              f"frontier={len(frontier)} dens={dens:.6f} stuck={len(stuck)} "
              f"{'*** CLOSED ***' if ok else 'open'} ({time.time()-t0:.0f}s)", flush=True)
    return ok, leaves, fixed, stuck

if __name__ == "__main__":
    ok, leaves, fixed, stuck = run(SEED)
    if ok:
        out = {"L": L,
               "leaves": [[list(map(int, r)), DATA[qi]["q"], int(w)] for (r, qi, w) in leaves],
               "fixed": {str(DATA[qi]["q"]): int(w) for qi, w in fixed.items()}}
        json.dump(out, open(W_DIR + f"/tree_closed_L{L}_s{SEED}.json", "w"))
        print(f"*** TREE COVER CLOSED: {len(leaves)} leaves, {len(fixed)} primes ***", flush=True)
    else:
        # bank the stuck analysis
        json.dump({"L": L, "seed": SEED, "stuck": [list(map(int, r)) for r in stuck[:2000]],
                   "n_stuck": len(stuck), "n_fixed": len(fixed)},
                  open(W_DIR + f"/tree_open_L{L}_s{SEED}.json", "w"))
        print(f"open: {len(stuck)} stuck regions banked", flush=True)
