"""sweep203.py — THE COMPLETE FAMILY SWEEP for Erdos #203 (W66-P203-K).

Structural law: prime q (q>=5, q not 2,3) is usable on torus L iff
ord_q(2) | L and ord_q(3) | L, i.e. 2^L == 1 mod q and 3^L == 1 mod q.
The palette pal_dlog_full.json (1004 entries, h <= 4998) is INCOMPLETE:
the r3 hunt factored 2^d-1/3^e-1 only for d,e | 27720 <= 720 (plus partial
extensions). This sweep enumerates ALL eligible primes q <= QMAX directly,
computes (o2, o3, h, U, V) exactly, and writes the complete palette.

Output: pal_sweep.json rows [q, h, U, V, o2, o3] sorted by h.
Multi-L eligibility tracked for L in {55440, 720720, 12252240}
(720720 = 55440*13, 12252240 = 720720*17) via chained pows.
"""
import json, math, os, sys, time
from sympy import primerange, factorint

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10**8
OUT = "/home/z/waves/w66-p203-k/problem203-sierpinski-23/work/v6/pal_sweep.json"
CKPT = OUT + ".ckpt"

L1 = 55440           # 2^4 * 3^2 * 5 * 7 * 11
L2 = L1 * 13         # 720720
L3 = L2 * 17         # 12252240

def mult_order(a, q, fac):
    n = q - 1
    o = n
    for p in fac:
        while o % p == 0 and pow(a, o // p, q) == 1:
            o //= p
    return o

def bsgs_dlog(g, target, h, q):
    """i with g^i == target mod q, 0 <= i < h (target in <g>)."""
    if target % q == 1:
        return 0
    m = int(math.isqrt(h)) + 1
    table = {}
    e = 1
    for j in range(m):
        if e not in table:
            table[e] = j
        e = e * g % q
    factor = pow(g, -m, q)
    y = target % q
    for i in range(m + 1):
        if y in table:
            return i * m + table[y]
        y = y * factor % q
    return None

def full_entry(q):
    """(q, h, U, V, o2, o3) or None."""
    fac = factorint(q - 1)
    o2 = mult_order(2, q, fac)
    o3 = mult_order(3, q, fac)
    h = o2 * o3 // math.gcd(o2, o3)
    if h < 4:
        return None
    # generator of the order-h subgroup of F_q^*
    e = (q - 1) // h
    fh = factorint(h)
    g = None
    for base in (5, 6, 7, 10, 11, 12, 13, 17, 19, 23, 2, 3):
        if base % q == 0:
            continue
        cand = pow(base, e, q)
        o = h
        for p in fh:
            while o % p == 0 and pow(cand, o // p, q) == 1:
                o //= p
        if o == h and cand != 1:
            g = cand
            break
    if g is None:
        return None
    U = bsgs_dlog(g, 2 % q, h, q)
    V = bsgs_dlog(g, 3 % q, h, q)
    if U is None or V is None:
        return None
    # sanity: dlogs correct + the surjectivity law gcd(U,V,h)=1
    assert pow(g, U, q) == 2 % q and pow(g, V, q) == 3 % q, (q, U, V)
    assert math.gcd(math.gcd(U, V), h) == 1, (q, U, V, h)
    return [int(q), int(h), int(U), int(V), int(o2), int(o3)]

t0 = time.time()
rows = []
stats = {"tested": 0, "eL1": 0, "eL2": 0, "eL3": 0}
try:
    if os.path.exists(CKPT):
        st = json.load(open(CKPT))
        rows = st["rows"]; stats = st["stats"]
        print(f"resumed: {len(rows)} rows, tested {stats['tested']}", flush=True)
except Exception:
    pass

BUF = 200000
buf = []
last_q = rows[-1][0] if rows else 4
for q in primerange(max(5, last_q + 1), QMAX + 1):
    if q in (2, 3):
        continue
    stats["tested"] += 1
    t2 = pow(2, L1, q)
    t3 = pow(3, L1, q)
    if t2 == 1 and t3 == 1:
        stats["eL1"] += 1
    u2 = pow(t2, 13, q)
    u3 = pow(t3, 13, q)
    if u2 == 1 and u3 == 1:
        stats["eL2"] += 1
    w2 = pow(u2, 17, q)
    w3 = pow(u3, 17, q)
    if w2 == 1 and w3 == 1:
        stats["eL3"] += 1
        ent = full_entry(q)
        if ent is not None:
            rows.append(ent)
            buf.append(ent)
    if stats["tested"] % 5_000_000 == 0:
        json.dump({"rows": rows, "stats": stats}, open(CKPT, "w"))
        print(f"tested {stats['tested']}: eL1={stats['eL1']} eL2={stats['eL2']} "
              f"eL3={stats['eL3']} rows={len(rows)} ({time.time()-t0:.0f}s)", flush=True)

# dedupe + sort by h
seen = {}
for r in rows:
    seen[r[0]] = r
rows = sorted(seen.values(), key=lambda r: (r[1], r[0]))
json.dump(rows, open(OUT, "w"))
# budgets
for L, key in ((L1, "eL1"), (L2, "eL2"), (L3, "eL3")):
    fam = [r for r in rows if L % r[1] == 0]
    print(f"L={L}: {len(fam)} primes, budget {sum(1.0/r[1] for r in fam):.4f}", flush=True)
print(f"DONE: {len(rows)} rows total ({time.time()-t0:.0f}s)", flush=True)
