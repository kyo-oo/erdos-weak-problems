#!/usr/bin/env python3
"""E10 MASTER: for all n<=10, all m in full period, all ANTICHAINS S:
 (a) margin = |N(S)| - |S|   (Hall margin; must be >= 0)
 (b) private-multiple property: does SOME key in S have a private multiple in window?
 (c) strengthened: |N(S)| >= max(|S|, floor(W/k_min))?
Report all violations, and census of tight ANTICHAINS (margin==0, |S|>=2)."""
import sys
from math import gcd
from functools import reduce
def lcm(a,b): return a*b//gcd(a,b)

def run(n, per):
    W = 2*n-2
    viol_b = []; viol_c = []; tight = {}
    minmargin = 10**9; min_at = None
    for m in range(1, per+1):
        Ms = {k: frozenset(x for x in range(m+1, m+W+1) if x % k == 0) for k in range(1, n+1)}
        for S in range(1, 1<<n):
            ks = [i+1 for i in range(n) if S>>i & 1]
            if len(ks) < 2: continue
            ok = True
            for a in range(len(ks)):
                for b in range(a+1, len(ks)):
                    if ks[b] % ks[a] == 0: ok=False; break
                if not ok: break
            if not ok: continue
            u = frozenset().union(*[Ms[k] for k in ks])
            margin = len(u) - len(ks)
            if margin < minmargin: minmargin = margin; min_at = (m, tuple(ks))
            if margin == 0: tight[tuple(ks)] = tight.get(tuple(ks), 0) + 1
            if margin < 0: print("HALL VIOLATION!", n, m, ks); sys.exit(1)
            # (b) private multiple for some key
            haspriv = False
            for k in ks:
                for x in Ms[k]:
                    if all(x not in Ms[j] for j in ks if j != k): haspriv = True; break
                if haspriv: break
            if not haspriv: viol_b.append((m, tuple(ks)))
            # (c) strengthened
            if len(u) < max(len(ks), W // ks[0]): viol_c.append((m, tuple(ks), len(u)))
    return minmargin, min_at, viol_b, viol_c, tight

for n in range(2, 11):
    L = reduce(lcm, range(1, n+1), 1); per = min(L, 2520)
    mm, ma, vb, vc, tight = run(n, per)
    print(f"n={n}: min margin {mm} at {ma}; no-private-key violations: {len(vb)} ex {vb[:3]}; strengthened-max viol: {len(vc)} ex {vc[:3]}")
    bigs = sorted(((len(t), t, c) for t, c in tight.items()), key=lambda z: -z[0])[:8]
    for sz, t, c in bigs: print(f"   tight ANTICHAIN {t} (|S|={sz}) x{c}")
