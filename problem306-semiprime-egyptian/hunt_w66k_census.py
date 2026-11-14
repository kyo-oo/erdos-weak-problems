#!/usr/bin/env python3
"""W66-P306-K census re-derivation v2: the 181-box + the represented set.

Census box: all a/b, 0 < a < b, gcd(a,b)=1, b squarefree <= 30.
Engine: pair-window subset-sum (complement-flip for >1/2 targets) with
  - descending include-first DFS + suffix-sum prune + dead-end prune
  - node caps + per-window timeouts (bounded work per target)
  - randomized restarts for the stubborn ones (bounded rounds)
Chunked: processes at most CHUNK targets per invocation, checkpoints to
EVIDENCE_306_W66K.json after every target (resume-safe).
"""
import sys, os, time, json, random
sys.setrecursionlimit(100000)
from fractions import Fraction
from math import gcd
from sympy import primerange

T0 = time.time()
CHUNK = int(os.environ.get("CHUNK", "40"))

BOX = []
for b in [2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30]:
    for a in range(1, b):
        if gcd(a, b) == 1:
            BOX.append(Fraction(a, b))
BOX.sort()
assert len(BOX) == 181

REPS = {}
CKPT = "EVIDENCE_306_W66K.json"
if os.path.exists(CKPT):
    with open(CKPT) as f:
        old = json.load(f)
    for k, v in old["reps"].items():
        t = Fraction(k)
        if t in BOX:
            REPS[t] = v

with open("../EVIDENCE_306.txt") as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith("#") or "represented" in line:
            continue
        lhs, rhs = line.split("=")
        t = Fraction(lhs.strip())
        dens = [int(x.strip()[2:]) for x in rhs.split("+")]
        assert sum(Fraction(1, n) for n in dens) == t
        if t in BOX:
            REPS.setdefault(t, dens)

# kernel r1 certified reps (Erdos306.lean §4)
KERNEL_R1 = {
    Fraction(1, 2): [6,10,15,21,26,35,39,65,91],
    Fraction(2, 3): [6,10,14,21,22,26,33,35,38,51,57,77,91,95,119,133,143,187,209,247,323],
    Fraction(3, 5): [6,10,14,15,22,26,34,35,51,77,119,143,187],
    Fraction(4, 5): [6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,69,77,85,115,143,299,323,391],
    Fraction(5, 6): [6,10,14,15,21,22,33,34,35,38,39,46,51,55,57,65,69,77,85,91,95,115,119,133,143,221,299,391],
    Fraction(3, 10): [10,21,22,26,33,55,77,143],
    Fraction(2, 5): [6,15,21,26,35,39,65,91],
    Fraction(3, 7): [6,10,14,26,39,65,91],
    Fraction(4, 7): [6,10,14,15,21,26,35,39,65,91],
    Fraction(1, 3): [6,10,15],
    Fraction(1, 5): [10,14,35],
    Fraction(1, 7): [15,21,35],
    Fraction(2, 7): [6,14,21],
    Fraction(3, 13): [6,26,39],
    Fraction(3, 11): [6,21,22,77],
    Fraction(8, 21): [6,10,15,21],
    Fraction(3, 14): [6,21],
    Fraction(2, 21): [15,35],
    Fraction(1, 6): [6],
}
for t, dens in KERNEL_R1.items():
    assert sum(Fraction(1, n) for n in dens) == t, t
    if t in BOX:
        REPS.setdefault(t, dens)

PRIMES = list(primerange(2, 100))
CACHE = {}

def window(w):
    if w not in CACHE:
        P = [p for p in PRIMES if p <= w]
        L = 1
        for p in P:
            L *= p
        pairs = []
        n = len(P)
        for i in range(n):
            for j in range(i + 1, n):
                d = P[i] * P[j]
                pairs.append((d, L // d))
        CACHE[w] = (L, pairs)
    return CACHE[w]

def subset_sum(pairs, T, tmo=3.0, node_cap=300_000, order="desc", seed=0):
    total = sum(v for _, v in pairs)
    if T > total or T < 0:
        return None
    flip = (2 * T > total)
    if flip:
        T = total - T
    if order == "desc":
        ps = sorted(pairs, key=lambda t: -t[1])
    else:
        ps = sorted(pairs, key=lambda t: t[1])
    if seed:
        rnd = random.Random(seed)
        # jitter within bands of equal-ish magnitude: shuffle in blocks of 8
        for i in range(0, len(ps), 8):
            blk = ps[i:i+8]
            rnd.shuffle(blk)
            ps[i:i+8] = blk
        if order == "desc":
            ps.sort(key=lambda t: -t[1] // 10**6)  # coarse band sort keeps blocks
    vals = [v for _, v in ps]
    dens = [d for d, _ in ps]
    m = len(vals)
    suf = [0] * (m + 1)
    mnv = [0] * (m + 1)  # min suffix value
    for k in range(m - 1, -1, -1):
        suf[k] = suf[k + 1] + vals[k]
        mnv[k] = vals[k] if mnv[k + 1] == 0 else min(vals[k], mnv[k + 1])
    res = [None]
    nodes = [0]
    t0 = time.time()
    def dfs(k, rem, acc):
        if res[0] is not None or nodes[0] > node_cap:
            return
        nodes[0] += 1
        if (nodes[0] & 8191) == 0 and time.time() - t0 > tmo:
            return
        if rem == 0:
            res[0] = acc[:]
            return
        if k >= m or rem > suf[k]:
            return
        if rem < mnv[k]:
            return
        v = vals[k]
        if v <= rem:
            acc.append(dens[k])
            dfs(k + 1, rem - v, acc)
            if res[0] is not None:
                return
            acc.pop()
        # skip branch only if the remainder is still coverable
        if rem <= suf[k + 1]:
            dfs(k + 1, rem, acc)
    dfs(0, T, [])
    if res[0] is None:
        return None
    if flip:
        chosen = set(res[0])
        return [d for d, _ in pairs if d not in chosen]
    return res[0]

def verify(dens, t):
    s = sum(Fraction(1, n) for n in dens)
    assert s == t, (str(t), s, dens[:6])
    assert len(set(dens)) == len(dens)
    import sympy
    for n in dens:
        f = sympy.factorint(n)
        assert len(f) == 2 and all(e == 1 for e in f.values()), (n, f)

WINDOWS = [13, 17, 19, 23, 29, 31, 37, 41, 47]

todo = [t for t in BOX if t not in REPS]
print(f"state: {len(REPS)}/181 represented; hunting {min(CHUNK, len(todo))} of {len(todo)}", flush=True)
done_ct = 0
still = []
for t in todo:
    if done_ct >= CHUNK and time.time() - T0 < 420:
        break
    if time.time() - T0 > 480:
        break
    a, b = t.numerator, t.denominator
    got = None
    attempts = [("desc", 0), ("asc", 0), ("desc", 7), ("asc", 13), ("desc", 21), ("asc", 29)]
    for w in WINDOWS:
        L, pairs = window(w)
        if L % b != 0:
            continue
        T = a * (L // b)
        total = sum(v for _, v in pairs)
        if T > total:
            continue
        for order, seed in attempts:
            r = subset_sum(pairs, T, tmo=3.0, node_cap=250_000, order=order, seed=seed)
            if r is not None:
                dens = sorted(r)
                ok = True
                try:
                    verify(dens, t)
                except AssertionError:
                    ok = False
                if ok:
                    got = dens
                    break
        if got is not None:
            break
    if got is not None:
        REPS[t] = got
        print(f"  HIT {t}: {len(got)} terms, max den {got[-1]}", flush=True)
    else:
        still.append(t)
        print(f"  MISS {t}", flush=True)
    done_ct += 1
    with open(CKPT, "w") as f:
        json.dump({"box_size": len(BOX), "represented": len(REPS),
                   "reps": {str(t): REPS[t] for t in sorted(REPS)},
                   "remaining": [str(x) for x in BOX if x not in REPS]},
                  f, indent=1)

print(f"\n=== CENSUS STATE: {len(REPS)}/{len(BOX)} represented; "
      f"REMAINING ({len([x for x in BOX if x not in REPS])}): "
      f"{[str(x) for x in BOX if x not in REPS]} [{time.time()-T0:.0f}s]", flush=True)
