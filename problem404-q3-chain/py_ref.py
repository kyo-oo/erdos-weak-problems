#!/usr/bin/env python3
"""REFERENCE DRIVER for cross-validating the C engine (class_dp.c).

This is an EXACT copy of class_dp2.py's class_dp() semantics (sound
scheduled-precision class-DP), with per-class logging added so the C port can
be diffed class-by-class (coins, state counts, maxevent) and end-to-end
(g, first_unreach, maxevent).  No semantic changes whatsoever.
"""
import sys
from collections import defaultdict

def vp_fact(n, p):
    v, q = 0, p
    while q <= n:
        v += n // q; q *= p
    return v

def class_dp(a, p, L, slack=8, log_every=1):
    CP = L + slack
    imax = a + 1
    while vp_fact(imax + 1, p) - vp_fact(a, p) < L:
        imax += 1
    classes = defaultdict(list)
    if p == 2:
        MODP = 1 << (CP + 64)
        q = 1
        for i in range(a + 1, imax + 1):
            q = (q * i) % MODP
            V = vp_fact(i, 2) - vp_fact(a, 2)
            if 0 <= V < L:
                classes[V].append((i, (q >> V) & ((1 << (CP - V)) - 1)))
    else:
        raise NotImplementedError("py_ref: p != 2 not needed for the C port")
    states = {(0, 1 % (p ** (CP)) if p != 2 else 1): None}
    parents = [dict(states)]
    maxevent = 0
    for V in range(0, L):
        coins = classes.get(V, [])
        precV = CP - V
        units = [u for (i, u) in coins]
        sigmas = {0}
        for u in units:
            sigmas |= {s + u for s in sigmas}
        sigmas = {s % (1 << precV) if p == 2 else s % (p ** precV) for s in sigmas}
        sigmas.discard(0)
        newstates = {}
        def add(st, par):
            if st not in newstates:
                newstates[st] = par
        for (t, u) in states:
            if t < V:
                continue
            add((t, u), ((t, u), 0, V))
            for sig in sigmas:
                if p == 2:
                    if t >= V:
                        sh = t - V
                        if sh >= precV:
                            s = sig % (1 << precV)
                        else:
                            s = ((u << sh) + sig) % (1 << precV)
                        if s == 0:
                            add((CP, 1), ((t, u), sig, V))
                            if CP > maxevent: maxevent = CP
                        else:
                            delta = (s & -s).bit_length() - 1
                            t2 = V + delta
                            u2 = s >> delta
                            if t2 > maxevent: maxevent = t2
                            add((t2, u2), ((t, u), sig, V))
        states = newstates
        parents.append(dict(states))
        if V % log_every == 0 or V == L - 1:
            print(f"V={V:4d}: coins={len(coins):2d} states={len(states):6d} maxevent={maxevent}", flush=True)
    reach = defaultdict(int)
    for V in range(0, L + 1):
        for (t, u) in parents[V]:
            for l in range(V, t + 1):
                if t > reach[l]: reach[l] = t
    g = max([l for l in range(0, L + 1) if reach.get(l, 0) >= l], default=0)
    first_unreach = None
    for l in range(1, L + 1):
        ok = False
        for V in range(0, min(l, L) + 1):
            for (t, u) in parents[V]:
                if t >= l and V <= l and t < CP:
                    ok = True; break
            if ok: break
        if not ok:
            first_unreach = l; break
    return g, first_unreach, maxevent

if __name__ == '__main__':
    a = int(sys.argv[1]); p = int(sys.argv[2]); L = int(sys.argv[3])
    slack = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    g, fu, maxev = class_dp(a, p, L, slack)
    print(f"g({a},{p}) [py_ref] = {g}")
    print(f"first UNREACHABLE level = {fu if fu else f'> {L} (all 1..{L} reachable)'}")
    print(f"max event valuation = {maxev}")
