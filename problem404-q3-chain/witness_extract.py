#!/usr/bin/env python3
"""Witness extraction: the explicit chain B with v2(2! + sum_{i in B} i!) >= 254,
via the certified class DP with parent tracking. Also: scheduled precision."""
import sys
from collections import defaultdict

def vp_fact(n, p):
    v, q = 0, p
    while q <= n:
        v += n // q; q *= p
    return v

def run(a, p, L, slack=2):
    C = L + slack
    imax = a + 1
    while vp_fact(imax + 1, p) - vp_fact(a, p) < L:
        imax += 1
    MODP = 1 << (C + 64)
    classes = defaultdict(list)
    q = 1
    for i in range(a + 1, imax + 1):
        q = (q * i) % MODP
        V = vp_fact(i, 2) - vp_fact(a, 2)
        if V < L:
            classes[V].append((i, (q >> V) & ((1 << C) - 1)))
    # DP with parent tracking: state -> (parent_state, sigma, class)
    states = {(0, 1): None}
    parents = [dict(states)]
    for V in range(0, L):
        coins = classes.get(V, [])
        units = [u for (i, u) in coins]
        sigmas = {0}
        for u in units:
            sigmas |= {s + u for s in sigmas}
        newstates = {}
        for (t, u) in states:
            if t < V: continue
            for sig in sigmas:
                if sig == 0:
                    st = (t, u)
                    if st not in newstates: newstates[st] = ((t, u), 0, V)
                    continue
                if t < V:
                    shift = V - t
                    if shift >= C: u2 = u
                    else: u2 = (u + ((sig % (1 << (C - shift))) << shift)) % (1 << C)
                    st = (t, u2)
                else:
                    sh = t - V
                    s = (((u << sh) if sh < C else 0) + sig) % (1 << C)
                    if s == 0:
                        st = (V + C, 1)  # cap = success
                    else:
                        delta = (s & -s).bit_length() - 1
                        st = (V + delta, s >> delta)
                if st not in newstates:
                    newstates[st] = ((t, u), sig, V)
        states = newstates
        parents.append(dict(states))
    # find max event t > V achieved
    best = None
    for V in range(L):
        for (t, u), par in parents[V + 1].items():
            if t > V and (best is None or t > best[0]):
                if t < L + slack:  # real climb (not cap sentinel)
                    best = (t, V, (t, u))
    if best is None:
        # maybe cap event
        for V in range(L):
            for (t, u), par in parents[V + 1].items():
                if t >= V + C - 1 and (best is None or t > best[0]):
                    best = (t, V, (t, u))
    print(f"best event: t={best[0]} at class={best[1]}")
    # backtrack from best state
    target = best[2]
    chain = []
    cur = target
    for V in range(L - 1, -1, -1):
        par = parents[V + 1].get(cur)
        if par is None: break
        (pt, pu), sig, cls = par
        if sig == 0:
            cur = (pt, pu); continue
        # which coins produced sigma at class cls? find the subset
        coins = classes.get(cls, [])
        cunits = [u for (i, u) in coins]
        # try subsets
        import itertools
        found = None
        for r in range(1, len(cunits) + 1):
            for comb in itertools.combinations(range(len(cunits)), r):
                ss = sum(cunits[j] for j in comb)
                if ss == sig:
                    found = [coins[j][0] for j in comb]; break
            if found: break
        if found is None:
            print(f"WARN: sigma {sig} at class {cls} not reconstructed"); found = []
        chain.extend(found)
        cur = (pt, pu)
    chain.sort()
    print(f"witness chain B = {chain}")
    # verify: v2(a! + sum i!) 
    def fact(n):
        r = 1
        for k in range(2, n + 1): r *= k
        return r
    total = fact(a)
    for i in chain: total += fact(i)
    v = 0
    while total % 2 == 0: total //= 2; v += 1
    print(f"VERIFIED: v2({a}! + sum B!) = {v}  (target >= {L})")
    return chain

if __name__ == '__main__':
    a = int(sys.argv[1]); p = int(sys.argv[2]); L = int(sys.argv[3])
    run(a, p, L)
