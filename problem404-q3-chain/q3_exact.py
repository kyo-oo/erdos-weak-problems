#!/usr/bin/env python3
"""
Q3 CLASS-CLIMB ENGINE v2 — EXACT UNITS + STRATIFIED BEAM.

Target: Erdos #404 sub-Q3. Does the subsum set of {i!} contain 0 in Z_p?
Method: exact-integer DP over states (V, u) where u = sigma/p^V is the EXACT
unit of a subsum sigma with v_p(sigma) = V. Class-V gadgets = subsets of the
class-V window {i : v_p(i!) = V} (size <= 3). Beam with stratified sampling
(bucket by u mod p^3) to preserve diversity for future deep jumps.

Outputs: survival profile, gap crossings, fullness profile F(V) = max s such
that states at V cover ALL unit residues mod p^s (the key invariant).
"""
import sys
from itertools import combinations
from collections import defaultdict

def vp(x, p):
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def run(p, Vmax, beam_per_bucket=14, gmax=3, verbose=True):
    # exact units of i! (unit = i! with all p factors removed)
    cap = p * (Vmax + 4) + p
    units = [0] * (cap + 1)
    u = 1
    for i in range(1, cap + 1):
        x = i
        while x % p == 0:
            x //= p
        u *= x
        units[i] = u
    # class windows
    cls = defaultdict(list)
    vp_cache = {}
    for i in range(1, cap + 1):
        k = 0
        q = p
        while q <= i:
            k += i // q
            q *= p
        if k > Vmax + 2:
            break
        cls[k].append(i)
    gaps = [k for k in range(Vmax + 1) if k not in cls]
    if verbose:
        print(f"[p={p}] windows: {len(cls)} classes, gaps: {gaps[:15]}{'...' if len(gaps)>15 else ''}")
    # gadget subsets per class: (exact unit sum) list
    gsets = {}
    for k, ws in cls.items():
        if k > Vmax or k == 0:
            continue
        us = [units[i] for i in ws]
        gs = set()
        for r in range(1, min(gmax, len(us)) + 1):
            for c in combinations(us, r):
                gs.add(sum(c))
        gsets[k] = list(gs)
    # INIT: all nonempty subsets of class-0 elements (i in cls[0]); their
    # natural valuations and exact units. class-0 is fully consumed here.
    us0 = [units[i] for i in cls.get(0, [])]
    init_states = defaultdict(set)  # V -> set of exact units
    n0 = len(us0)
    for r in range(1, n0 + 1):
        for c in combinations(us0, r):
            s = sum(c)
            d = vp(s, p)
            if d > Vmax + 2:
                continue
            init_states[d].add(s // p**d)
    if verbose:
        for V in sorted(init_states):
            print(f"  init V={V}: {len(init_states[V])} exact units")

    states = dict(init_states)
    fullness = {}
    P3 = p**3
    def coverage(sv):
        best = 0
        for s in range(min(8, 12), 0, -1):
            m = p**s
            have = set(x % m for x in sv)
            ok = all(r in have for r in range(1, m) if r % p)
            if ok:
                best = s
                break
        return best

    for V in range(0, Vmax):
        cur = states.get(V)
        if not cur:
            continue
        fullness[V] = (len(cur), coverage(cur))
        gs = gsets.get(V)
        if gs is None:
            continue  # gap: states stuck (must have jumped past)
        for u_ex in list(cur):
            for w in gs:
                t = u_ex + w
                if t % p:
                    continue
                d = vp(t, p)
                nv = V + d
                if nv > Vmax + 2:
                    continue
                nu = t // p**d
                if nv not in states:
                    states[nv] = set()
                states[nv].add(nu)
        # beam: stratify by u mod p^3, cap per bucket
        for k in list(states.keys()):
            if k <= V:
                continue
            sv = states[k]
            if len(sv) <= beam_per_bucket * P3:
                continue
            buckets = defaultdict(list)
            for x in sv:
                buckets[x % P3].append(x)
            new = set()
            for b, lst in buckets.items():
                lst.sort()
                if len(lst) <= beam_per_bucket:
                    new.update(lst)
                else:
                    step = len(lst) / beam_per_bucket
                    for i in range(beam_per_bucket):
                        new.add(lst[int(i * step)])
            states[k] = new
    return states, fullness, gaps, gsets, cls

def main():
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    Vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    beam = int(sys.argv[3]) if len(sys.argv) > 3 else 14
    print(f"=== Q3 EXACT-CLIMB p={p} Vmax={Vmax} beam={beam} ===")
    states, fullness, gaps, gsets, cls = run(p, Vmax, beam)
    live = sorted(V for V, s in states.items() if s)
    top = max(live) if live else -1
    print(f"\nlive top: V={top} / {Vmax}")
    print(f"gaps: {gaps}")
    crossed = [g for g in gaps if g < top]
    print(f"crossed: {crossed}  ({'ALL' if crossed == gaps else 'PARTIAL'})")
    print("\nfullness profile (V: #states, F(V)=unit-coverage precision):")
    for V in sorted(fullness):
        n, f = fullness[V]
        mark = ' <-- GAP-CROSS' if (V - 1) in gaps or V in gaps else ''
        print(f"  V={V:3d}: {n:6d} states, F={f}{mark}")
    if top >= Vmax - 1:
        print(f"\nVERDICT p={p}: ALIVE at V={top}, crossed all {len(crossed)} gaps — Q3-consistent, pattern data collected")
    else:
        stalled = [g for g in gaps if g >= top][:5]
        print(f"\nVERDICT p={p}: stalled at/before V={top}; blocking gaps near: {stalled}")

if __name__ == "__main__":
    main()
