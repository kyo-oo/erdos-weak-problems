#!/usr/bin/env python3
"""Nested witness extraction for (a,p): build B_1 ⊆ B_2 ⊆ ... witnesses, print the limit structure."""
import sys
from math import isqrt

def vp_fact(n, p):
    s = 0; q = p
    while q <= n:
        s += n // q; q *= p
    return s

def window(a, p, k):
    va = vp_fact(a, p); out = []; i = a + 1
    while vp_fact(i, p) - va < k:
        out.append(i); i += 1
    return out

def P_mod(a, i, p, k):
    m = p ** k; r = 1
    for j in range(a + 1, i + 1):
        r = (r * (j % m)) % m
    return r

def nested_witness(a, p, kmax, try_extend=True):
    """Return list of nested witnesses B_1..B_kmax (B_k satisfies sum P_i = -1 mod p^k)."""
    B = []
    witnesses = []
    for k in range(1, kmax + 1):
        m = p ** k
        idx = window(a, p, k)
        terms = {i: P_mod(a, i, p, k) for i in idx}
        # try to extend current B
        found = None
        if try_extend:
            cur = sum(terms[i] for i in B if i in terms) % m
            # free terms: idx minus B
            free = [i for i in idx if i not in B]
            # DP over free terms to reach (m-1-cur)
            target = (m - 1 - cur) % m
            reach = {0: []}
            for i in free:
                t = terms[i]
                if t == 0: continue
                nxt = dict(reach)
                for r, sub in reach.items():
                    r2 = (r + t) % m
                    if r2 not in nxt:
                        nxt[r2] = sub + [i]
                reach = nxt
                if target in reach:
                    found = B + reach[target]; break
                if len(reach) > 2_000_000: break
        if found is None:
            # full research at this level (allow changing B)
            reach = {0: []}
            for i in idx:
                t = terms[i]
                if t == 0: continue
                nxt = dict(reach)
                for r, sub in reach.items():
                    r2 = (r + t) % m
                    if r2 not in nxt:
                        nxt[r2] = sub + [i]
                reach = nxt
                if (m - 1) in reach:
                    found = reach[m - 1]; break
                if len(reach) > 2_000_000: break
            if found is None:
                return witnesses, k  # failed at level k
        B = sorted(set(found))
        witnesses.append(list(B))
    return witnesses, None

if __name__ == "__main__":
    a, p, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    ws, failed = nested_witness(a, p, kmax)
    if failed:
        print(f"NESTED EXTRACTION FAILED at level {failed} (g = {failed-1})")
    for k, B in enumerate(ws, 1):
        if k >= len(ws) - 25:
            print(f"level {k:>3}: B = {B}")
    # structure: differences between consecutive
    print("\n=== membership evolution (last levels) ===")
    if len(ws) >= 2:
        prev = set()
        for k, B in enumerate(ws, 1):
            if k < len(ws) - 12: continue
            s = set(B)
            print(f"level {k:>3}: +{sorted(s - prev)} -{sorted(prev - s)}")
            prev = s
