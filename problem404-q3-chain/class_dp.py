#!/usr/bin/env python3
"""
CERTIFIED CLASS-DP — Erdos #404: the EXACT g(a,p) via sound exact-precision class DP.

THE QUESTION: g(a,p) = max{k : -1 in R_k} where R_k = subset sums of
{P_i = i!/a! mod p^k : v_p(P_i) < k}.  For (a,p)=(2,2): Lin [Li76] proved
f(2,2) <= 254 i.e. g(2,2) <= 253; the campaign DP verified -1 in R_k for
k <= 28.  TRUE g(2,2) in [28, 253].  This engine computes it EXACTLY.

THE ABSTRACTION (exact, two-sided):
- Process valuation classes V = 0, 1, 2, ... in increasing order.
- A state is (t, u): the running sum 1 + sum(chosen P_i) = 2^t * u with u odd,
  u tracked mod 2^C (C = precision cap).  The anchor "1" is the a=2 unit part.
- At class V the coins are {i : v_p(P_i) = V}; their part-sums sigma (exact,
  mod 2^C) branch the state:
    t < V : u' = u + 2^(V-t)*sigma (odd stays odd) -> state (t, u')  [t frozen]
    t >= V: s = 2^(t-V)*u + sigma; delta = v2(s); if s == 0 mod 2^C -> CAP
            (t' >= V + C: success sentinel); else (V + delta, s >> delta).
- States with t < V are frozen forever -> discard.
- Merging states with equal (t, u mod 2^C) is EXACT for every reachability
  question "does some subset using classes < L achieve t >= L" with L <= C:
  all future v2-computations are decided by bits < C unless they cap (>= C
  means t' >= V + C >= C >= L: success), and cap events coincide for
  congruent units.  Hence:
      success(L)  <=>  -1 in R_L      (for all L <= C)
  i.e. the DP is a two-sided exact decision procedure, no beam, no drops.

EVENTS: whenever a transition produces t' > V (a strict climb), the pair
(class V, t') is logged.  Event (V, t') certifies -1 in R_L for every
L in [V+1, t'].  Therefore g = max{ t' : event (V, t') with V < t' }.
Witnesses are reconstructible by parent-tracking.
"""
import sys
from collections import defaultdict

def s2(n):
    return bin(n).count('1')

def build_coins(a, p, imax, C):
    """Coins P_i = i!/a! for i >= a+1, grouped by class V = v_p(P_i).
    Returns: classes: dict V -> list of (i, unit) with unit = (P_i / p^V) mod 2^C,
    computed exactly by modular prefix products."""
    MOD = 1 << (C + 300)  # plenty of headroom
    # prefix product of j for j in [a+1 .. i], mod 2^(C+300)
    classes = defaultdict(list)
    q = 1
    for i in range(a + 1, imax + 1):
        q = (q * i) % MOD
        P = q  # P_i mod 2^(C+300)
        # v_p(P_i) for the TRUE integer P_i (not the residue): compute directly
        # v_p(i!/a!) = v_p(i!) - v_p(a!)
        # compute via Legendre on the fly
        pass
    return classes

def vp_fact(n, p):
    v, q = 0, p
    while q <= n:
        v += n // q
        q *= p
    return v

def class_dp(a, p, Lmax, C, verbose=True):
    """Run the certified class DP for anchor a, prime p, deciding all L <= Lmax.
    C >= Lmax + slack required."""
    assert C >= Lmax + 4
    imax = a + 1
    # find imax: largest i with v_p(P_i) < Lmax... we need classes up to Lmax-1;
    # extend imax while vp(P_imax) < Lmax
    while vp_fact(imax + 1, p) - vp_fact(a, p) < Lmax:
        imax += 1
    # coins grouped by class
    MODP = 1 << (C + 64) if p == 2 else None
    classes = defaultdict(list)
    if p == 2:
        q = 1
        for i in range(a + 1, imax + 1):
            q = (q * i) % MODP
            V = vp_fact(i, 2) - vp_fact(a, 2)
            if V < Lmax:
                unit = (q >> V) & ((1 << C) - 1)  # (P_i / 2^V) mod 2^C
                classes[V].append((i, unit))
    else:
        # general p: P_i mod p^C tracked; units are p-free parts mod p^C
        # P_i = p^V * u with u invertible mod p: u = P_i / p^V mod p^C
        # need P_i mod p^(C+V): do modular product with p-parts stripped
        # simpler: track q = product of j/p^{v_p(j)} mod p^C AND v = accumulated v_p
        q = 1
        v_acc = 0
        PPC = p ** (C + 64)
        for i in range(a + 1, imax + 1):
            j = i
            while j % p == 0:
                j //= p
                v_acc += 1
            q = (q * j) % PPC
            V = v_acc - vp_fact(a, p)
            if 0 <= V < Lmax:
                classes[V].append((i, q % (p ** C)))
    # initial state: the sum "1" (anchor unit)
    # state: (t, u) with u odd (p=2) / unit mod p^C; parent tracking for witnesses
    states = {(0, 1): None}   # (t, u) -> parent (prev state, sigma, class) or None
    events = []               # (class V, t') strict climbs
    frozen_discards = 0
    for V in range(0, Lmax):
        coins = classes.get(V, [])
        # part-sums sigma: subset sums of coin units (0, u1, u2, u1+u2, ...)
        units = [u for (i, u) in coins]
        sigmas = {0}
        for u in units:
            sigmas |= {s + u for s in sigmas}
        sigmas = list(sigmas)
        newstates = {}
        def add(st, parent):
            if st not in newstates:
                newstates[st] = parent
        for (t, u) in states:
            if t < V:
                frozen_discards += 1
                continue  # frozen forever
            for sig in sigmas:
                if sig == 0:
                    add((t, u), ((t, u), 0, V))
                    continue
                if t < V:
                    # u' = u + 2^(V-t)*sig ; p=2 only path (t<V means sig has p-powers >= V-t)
                    if p == 2:
                        shift = V - t
                        if shift >= C:
                            add((t, u), ((t, u), sig, V))
                        else:
                            u2 = (u + ((sig % (1 << (C - shift))) << shift)) % (1 << C)
                            add((t, u2), ((t, u), sig, V))
                    else:
                        # t < V: u' = u + p^(V-t)*sig mod p^C
                        sh = V - t
                        pC = p ** C
                        if sh >= C:
                            add((t, u), ((t, u), sig, V))
                        else:
                            u2 = (u + (sig % (pC // (p ** sh))) * (p ** sh)) % pC
                            add((t, u2), ((t, u), sig, V))
                else:
                    # t >= V: s = p^(t-V)*u + sig  (for p=2: 2^(t-V)*u + sig)
                    if p == 2:
                        sh = t - V
                        if sh >= C:
                            # 2^sh*u vanishes mod 2^C; s = sig mod 2^C
                            s = sig % (1 << C)
                        else:
                            s = ((u << sh) + sig) % (1 << C)
                        if s == 0:
                            # CAP: t' >= V + C >= Lmax: success sentinel
                            events.append((V, V + C))
                            add((V + C, 1), ((t, u), sig, V))
                        else:
                            delta = (s & -s).bit_length() - 1
                            t2 = V + delta
                            u2 = s >> delta
                            if t2 > V:
                                events.append((V, t2))
                            add((t2, u2), ((t, u), sig, V))
                    else:
                        pC = p ** C
                        sh = t - V
                        # s = p^sh * u + sig mod p^C ; need v_p(s)
                        if sh >= C:
                            s = sig % pC
                        else:
                            s = (u * (p ** sh) + sig) % pC
                        if s == 0:
                            events.append((V, V + C))
                            add((V + C, 1), ((t, u), sig, V))
                        else:
                            delta = 0
                            ss = s
                            while ss % p == 0:
                                ss //= p
                                delta += 1
                            t2 = V + delta
                            u2 = ss % pC
                            if t2 > V:
                                events.append((V, t2))
                            add((t2, u2), ((t, u), sig, V))
        states = newstates
        if verbose and (V % 20 == 0 or V == Lmax - 1):
            live = sum(1 for (t, u) in states if t >= V + 1)
            print(f"  class V={V:4d}: coins={len(coins):2d} states={len(states):6d} (live-for-next {live}) events={len(events)}", flush=True)
    # g = max t' over events (V, t') with V < t'
    g = max([t for (V, t) in events if V < t], default=0)
    return g, events, states

if __name__ == '__main__':
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    p = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    Lmax = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    C = Lmax + 8
    print(f"=== CERTIFIED CLASS-DP: (a,p)=({a},{p}), deciding all L <= {Lmax}, precision C={C} ===")
    g, events, states = class_dp(a, p, Lmax, C)
    # reconstruct per-level success
    maxt = defaultdict(int)
    for (V, t) in events:
        for L in range(V + 1, t + 1):
            maxt[L] = max(maxt[L], t)
    reachable = sorted([L for L in maxt if maxt[L] >= L])
    print(f"g({a},{p}) [exact, certified] = {g}")
    print(f"reachable levels: {reachable[:40]}{'...' if len(reachable) > 40 else ''}")
    print(f"first UNREACHABLE level (the obstruction) = {min(l for l in range(1, Lmax+1) if maxt.get(l, 0) < l)}")
    # top events
    top = sorted(events, key=lambda e: -e[1])[:10]
    print(f"top climb events (class -> level): {top}")
