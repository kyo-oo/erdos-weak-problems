#!/usr/bin/env python3
"""#306 round 1: semiprime Egyptian representation evidence engine.
For a/b with b squarefree, find n_1 < ... < n_k DISTINCT semiprimes
(p*q, p<q primes) with a/b = sum 1/n_i. Greedy + backtracking search."""
import sympy
from fractions import Fraction

# semiprime table
SEMIS = []
p_list = list(sympy.primerange(2, 200000))
for i, p in enumerate(p_list):
    for q in p_list[i:]:
        if p == q: continue  # DISTINCT primes
        n = p * q
        if n > 4_000_000: break
        SEMIS.append(n)
SEMIS = sorted(set(SEMIS))
print(f"semiprime table: {len(SEMIS)} entries, max {SEMIS[-1]}", flush=True)

import bisect

def search(target, max_terms=60, max_den=4_000_000, deadline_nodes=300000):
    """greedy with limited backtracking: returns list of semiprimes or None."""
    nodes = [0]
    best = [None]
    def rec(rem, start_idx, chosen):
        nodes[0] += 1
        if nodes[0] > deadline_nodes: return False
        if rem == 0:
            if best[0] is None or len(chosen) < len(best[0]):
                best[0] = list(chosen)
            return True
        if len(chosen) >= max_terms: return False
        # smallest semiprime n with 1/n <= rem: n >= ceil(1/rem) = ceil(den/num)
        n_min = -(-rem.denominator // rem.numerator)
        idx = bisect.bisect_left(SEMIS, max(n_min, start_val(chosen)), lo=start_idx)
        # try up to 3 candidate semiprimes at each step (greedy + slack)
        tried = 0
        for j in range(idx, len(SEMIS)):
            n = SEMIS[j]
            if n > max_den: break
            if rem < Fraction(1, n): continue
            new_rem = rem - Fraction(1, n)
            if new_rem < 0: continue
            chosen.append(n)
            ok = rec(new_rem, j + 1, chosen)
            chosen.pop()
            if ok: return True
            tried += 1
            if tried >= 4: break
        return False
    def start_val(chosen):
        return chosen[-1] + 1 if chosen else 2
    ok = rec(target, 0, [])
    return best[0] if ok else None

targets = []
for b in [2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30]:
    for a in range(1, b):
        from math import gcd
        if gcd(a, b) == 1:
            targets.append(Fraction(a, b))
targets.sort()

results = {}
fail = []
for t in targets:
    r = search(t)
    if r is None:
        fail.append(t)
    else:
        results[t] = r
        # verify
        assert sum(Fraction(1, n) for n in r) == t
        assert all(sympy.factorint(n) and len(sympy.factorint(n)) == 2 and max(sympy.factorint(n).values()) == 1 for n in r), r
        assert len(set(r)) == len(r)

print(f"\n=== #306 ROUND 1 EVIDENCE: {len(results)}/{len(targets)} rationals represented ===")
for t in sorted(results):
    r = results[t]
    print(f"  {t}: {len(r)} terms, max den {r[-1]}")
if fail:
    print(f"FAILED: {fail}")

with open("EVIDENCE_306.txt", "w") as f:
    f.write(f"#306 semiprime Egyptian representations — round 1 evidence\n")
    f.write(f"{len(results)}/{len(targets)} rationals a/b (b squarefree, b<=30) represented\n\n")
    for t in sorted(results):
        f.write(f"{t} = " + " + ".join(f"1/{n}" for n in results[t]) + "\n")
print("EVIDENCE_306.txt written")
