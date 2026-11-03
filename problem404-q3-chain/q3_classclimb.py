#!/usr/bin/env python3
"""
Q3 CLASS-CLIMB ENGINE — Erdos #404 sub-Q3 (UNANCHORED infinite chain).

QUESTION (verbatim): Is there a prime p and an infinite sequence a1 < a2 < ...
such that, with p^{m_k} the highest power of p dividing sum_{i<=k} a_i!, m_k -> infinity?

EQUIVALENT (compactness, Kill #7 Theorem A machinery): does the subsum set of
{i! : i >= 1} contain 0 in Z_p for some prime p?

STRUCTURE (this engine):
- Elements group into p-adic valuation classes k = v_p(i!).
- Non-gap classes carry a window of ~p consecutive i; wall-gaps (j-1 empty
  classes) occur only at i = p^j.
- Between walls the climb V -> V+1 uses class-V gadgets (subsets of the window).
- At wall j (bottom W_j = v_p((p^j - 1)!)), a class-W_j gadget whose unit-sum
  cancels the running unit mod p^j jumps the whole gap (+j).

ENGINE: reservoir DP over (valuation V, unit u) states with EXACT units
(tracked mod p^S; precision decay handled honestly per state).
Receipts printed for the Lean kernel.
"""
import sys
from itertools import combinations

def vp_fact(i, p):
    v, q = 0, p
    while q <= i:
        v += i // q
        q *= p
    return v

def sum_p_check(p, verbose=True):
    facts = [1] * p
    for r in range(1, p):
        facts[r] = (facts[r-1] * r) % p
    sums = {0}
    for f in facts:
        sums |= {(s + f) % p for s in sums}
    ok = len(sums) == p
    if verbose:
        print(f"[SUM({p})] r! mod {p}: {facts} -> cover {len(sums)}/{p}: {'PASS' if ok else 'FAIL'}")
    return ok

def run_climb(p, Vmax, S=6, gmax=3, verbose=True):
    """
    States: (V, u mod p^s) — u = sigma / p^V mod p^s with sigma an exact
    subsum of element UNITS (i! with p-parts removed), v_p(sigma) = V exact.
    Precision s decays by delta on each lift; states with s < 2 dropped.
    Honest: all arithmetic on residues mod p^S; delta capped at s-1.
    """
    PS = p ** S
    # element units: unit(i) = unit((i-1)!)*unit(i) — unit of i! = prod of p-free parts
    cap = p * (Vmax + 3) + p
    units = [0] * (cap + 1)   # unit(i!) exact
    u = 1
    for i in range(1, cap + 1):
        x = i
        while x % p == 0:
            x //= p
        u *= x
        units[i] = u
    # classes
    cls = {}
    for i in range(1, cap + 1):
        k = vp_fact(i, p)
        if k > Vmax + 2:
            break
        cls.setdefault(k, []).append(i)
    gaps = sorted(k for k in range(0, Vmax + 1) if k not in cls)
    if verbose:
        print(f"[p={p}] classes <= Vmax present: {len(cls)}, gaps: {gaps}")
    # gadget unit sums per class (subsets of window, size 1..gmax), mod PS
    gsets = {}
    for k, ws in cls.items():
        if k > Vmax:
            continue
        us = [units[i] % PS for i in ws]
        gs = set()
        for r in range(1, min(gmax, len(us)) + 1):
            for c in combinations(us, r):
                gs.add(sum(c) % PS)
        gsets[k] = sorted(gs)

    # initial: nonempty subsets of class-0 elements, unit sums with v_p = 0
    us0 = [units[i] % PS for i in cls.get(0, [])]
    init = set()
    for r in range(1, min(4, len(us0)) + 1):
        for c in combinations(us0, r):
            s = sum(c)
            if s % p:
                init.add((s % PS, S))
    # states[V] = set of (unit mod p^s, s)
    states = {0: init}
    wall_events = []
    for V in range(0, Vmax):
        cur = states.get(V)
        if not cur:
            continue
        if V not in gsets:
            continue  # gap: states here are stuck (arrived exactly at V)
        gs = gsets[V]
        for (u_res, s) in list(cur):
            for w in gs:
                t = u_res + w
                if t % p:
                    continue
                d = 0
                tt = t
                while tt % p == 0 and d < s - 1:
                    tt //= p
                    d += 1
                if tt % p == 0:
                    continue  # too deep for our precision; skip (conservative)
                nv = V + d
                ns = s - d
                if ns < 2:
                    continue
                states.setdefault(nv, set()).add((tt % (p ** ns), ns))
                if nv > V + 1:
                    wall_events.append((V, nv))
        # cap reservoir: stratified stride
        for k in list(states):
            if len(states[k]) > 8000:
                lst = sorted(states[k])
                step = len(lst) / 8000
                states[k] = set(lst[int(i * step)] for i in range(8000))

    live = sorted(V for V, s in states.items() if s)
    return states, live, wall_events, gaps

def main():
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    Vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    S = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    print(f"=== Q3 CLASS-CLIMB: p={p} Vmax={Vmax} S={S} ===")
    sum_p_check(p)
    states, live, walls, gaps = run_climb(p, Vmax, S)
    top = max(live) if live else -1
    print(f"live top valuation: V={top} (target {Vmax})")
    crossed = [g for g in gaps if g < top]
    print(f"gaps in range: {gaps}")
    print(f"gaps crossed : {crossed}")
    jumps = {}
    for (V, nv) in walls:
        jumps.setdefault((V, nv), 0)
        jumps[(V, nv)] += 1
    print("jump events (V -> V', #states):")
    for kk in sorted(jumps):
        print(f"  {kk[0]} -> {kk[1]} : {jumps[kk]} states")
    for V in sorted(live):
        if len(states[V]) and (V in gaps or V - 1 in gaps or V % 10 == 0):
            print(f"  V={V}: {len(states[V])} states")
    if top >= Vmax - 2:
        print(f"VERDICT p={p}: chain ALIVE through V={top}; all gaps in range crossed = {crossed == gaps}")
    else:
        print(f"VERDICT p={p}: chain stalled at V={top}")

if __name__ == "__main__":
    main()
