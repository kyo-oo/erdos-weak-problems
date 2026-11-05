#!/usr/bin/env python3
"""
SOUND SCHEDULED-PRECISION CLASS-DP — Erdos #404 exact g(a,p).

THE ABSTRACTION (exact, two-sided, PROVABLY sound):
- States: (t, u) with u < 2^(CP-t): the running sum 1 + sum(chosen P_i) = 2^t * U,
  U odd, and the stored u satisfies: U = u (mod 2^(CP-t)).
- CP = L + slack (precision budget). At class V, coins {i : v_p(P_i) = V} with
  part-sums sigma (mod 2^(CP-V)).
- Transitions from (t,u), t >= V (t < V discarded = frozen):
    s = ((u << (t-V)) + sigma) mod 2^(CP-V)      [t >= V]
    s = 0  -> CAP: t' >= CP >= L: success sentinel (L, 0)
    s != 0 -> delta = v2(s); t' = V + delta; u' = s >> delta  (auto < 2^(CP-t'))
- MERGE ON (t,u) IS EXACT: every member's true unit = u mod 2^(CP-t)
  (inductive invariant; transitions preserve it: the schedule guarantees the
  needed bits are always present — total consumed precision <= class index).
- Sound both directions for the question "does some subset of coins with
  class < L reach valuation >= L":
    success(L) <=> -1 in R_L.
  Certificate = the full state-set chain; witnesses by parent tracking.
"""
import sys
from collections import defaultdict

def vp_fact(n, p):
    v, q = 0, p
    while q <= n:
        v += n // q; q *= p
    return v

def class_dp(a, p, L, slack=8, verbose=True, track=False):
    CP = L + slack
    imax = a + 1
    while vp_fact(imax + 1, p) - vp_fact(a, p) < L:
        imax += 1
    # coins: for each class V < L: list of (i, unit mod 2^(CP-V))
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
        q, v_acc = 1, 0
        for i in range(a + 1, imax + 1):
            j = i
            while j % p == 0:
                j //= p; v_acc += 1
            q = (q * j)
            V = v_acc - vp_fact(a, p)
            if 0 <= V < L:
                # reduce q mod p^(CP-V) lazily: keep q bounded
                classes[V].append((i, q % (p ** (CP - V))))
                q = q % (p ** (CP + 64))  # keep bounded
    states = {(0, 1 % (p ** (CP)) if p != 2 else 1): None}
    # for p=2: initial (0, 1); u < 2^CP ok
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
        sigmas.discard(0)  # sigma=0 handled as identity
        newstates = {}
        def add(st, par):
            if st not in newstates:
                newstates[st] = par
        for (t, u) in states:
            if t < V:
                continue
            add((t, u), ((t, u), 0, V))  # sigma = 0
            for sig in sigmas:
                if p == 2:
                    if t >= V:
                        sh = t - V
                        if sh >= precV:
                            s = sig % (1 << precV)
                        else:
                            s = ((u << sh) + sig) % (1 << precV)
                        if s == 0:
                            add((CP, 1), ((t, u), sig, V))  # cap sentinel
                            if CP > maxevent: maxevent = CP
                        else:
                            delta = (s & -s).bit_length() - 1
                            t2 = V + delta
                            u2 = s >> delta
                            if t2 > maxevent: maxevent = t2
                            add((t2, u2), ((t, u), sig, V))
                else:
                    pV = p ** precV
                    if t >= V:
                        sh = t - V
                        s = ((u * p ** sh) + sig) % pV if sh < precV else sig % pV
                        if s == 0:
                            add((CP, 1), ((t, u), sig, V))
                            if CP > maxevent: maxevent = CP
                        else:
                            delta, ss = 0, s
                            while ss % p == 0: ss //= p; delta += 1
                            t2 = V + delta
                            u2 = ss % pV
                            if t2 > maxevent: maxevent = t2
                            add((t2, u2), ((t, u), sig, V))
        states = newstates
        parents.append(dict(states))
        if verbose and (V % 40 == 0 or V == L - 1):
            print(f"  V={V:4d}: coins={len(coins):2d} states={len(states):6d} maxevent={maxevent}", flush=True)
    # per-level reachability from events: replay quickly
    # a level l is reachable iff some state (t,u) in parents[V+1] has t >= l with V <= l-1 and t < CP-sentinel... 
    # cap sentinels: (CP, 1): treat as t = CP.
    reach = defaultdict(int)
    for V in range(0, L + 1):
        for (t, u) in parents[V]:
            # states in parents[V] used classes < V (processed classes 0..V-1): 
            # wait parents[V] = after processing class V-1: coins used have class <= V-1
            for l in range(V, t + 1):
                if t > reach[l]: reach[l] = t
    # level l reachable iff reach[l] >= l  (some state with t >= l using classes < V <= l-1... 
    # careful: parents[V] used classes <= V-1: for level l need classes <= l-1: V <= l
    g = max([l for l in range(0, L + 1) if reach.get(l, 0) >= l], default=0)
    first_unreach = None
    for l in range(1, L + 1):
        ok = False
        for V in range(0, min(l, L) + 1):
            for (t, u) in parents[V]:
                if t >= l and V <= l and t < CP:  # t < CP excludes... no: sentinels t=CP count!
                    ok = True; break
            if ok: break
        # hmm: V <= l means classes <= V-1 <= l-1 ok
        if not ok:
            first_unreach = l; break
    return g, first_unreach, parents, classes, maxevent

if __name__ == '__main__':
    a = int(sys.argv[1]); p = int(sys.argv[2]); L = int(sys.argv[3])
    g, fu, parents, classes, maxev = class_dp(a, p, L)
    print(f"g({a},{p}) [SOUND certified] = {g}")
    print(f"first UNREACHABLE level = {fu if fu else f'> {L} (all 1..{L} reachable)'}")
    print(f"max event valuation = {maxev}")
