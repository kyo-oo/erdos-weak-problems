#!/usr/bin/env python3
"""Block-valuation coverage check for #404 (2,2): every target bit t achieved by a small block/single?"""
from math import comb

def v2(n):
    if n == 0: return 10**9
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

def s2(n):
    return bin(n).count('1')

def v2fact(n): return n - s2(n)

def fact(n):
    r = 1
    for i in range(2, n+1): r *= i
    return r

def block_val(w, j):
    """v_2 of sum_{i in [w, j]} i!  (exact big-int)."""
    r = 0
    f = fact(w)
    for i in range(w, j+1):
        if i > w: f *= i
        r += f
    return v2(r)

def main():
    # achievable valuations from singles, pairs, triples, 4-blocks, 5-blocks in windows
    print("target coverage: for each t in [1..120], find a block [w, j] with j - w <= 4 and v_2(sum) == t, w fresh (>= 2)")
    covered = {}
    used_until = 1
    for t in range(1, 121):
        found = None
        w0 = used_until + 1
        for w in range(w0, w0 + 400):
            for L in range(0, 5):  # block length 1..5
                v = block_val(w, w + L)
                if v == t:
                    found = (w, w + L)
                    break
            if found: break
        if found:
            covered[t] = found
            used_until = found[1]
        else:
            print(f"t={t}: NOT COVERED by blocks of length<=5 within 400 of {w0}")
    print(f"covered {len(covered)}/120 consecutive-bit targets with disjoint blocks")
    print("sample:", {t: covered[t] for t in list(covered)[:15]})
    # verify the two identities
    print("\nidentity check: [u,u+1] sum == u!*(u+2):", all(fact(u)*(u+2) == fact(u)+fact(u+1) for u in range(1, 30)))
    print("identity check: [u,u+2] sum == u!*(u+2)**2:", all(fact(u)*(u+2)**2 == fact(u)+fact(u+1)+fact(u+2) for u in range(1, 30)))
    # the explicit Z chain construction (greedy: lift valuation step by step)
    print("\n=== GREEDY Z-CHAIN (2,2) ===")
    Z = [2, 3]
    S = fact(2) + fact(3)
    print(f"Z={Z}  v_2(S) = {v2(S)}  S = {S}")
    cur = max(Z)
    for step in range(30):
        # try to raise valuation: find block [w, j] beyond cur with v2(S + block) > v2(S)
        v_now = v2(S)
        best = None
        for w in range(cur + 1, cur + 600):
            f = fact(w)
            for L in range(0, 6):
                if w + L > cur + 600: break
                if L > 0:
                    for i in range(w, w + L + 1):
                        if i == w: continue
                        f2 = fact(i)
                        # incremental
                # compute block sum exactly
                b = 0
                g = 1
                for i in range(w, w + L + 1):
                    if i == w: g = fact(w)
                    else: g *= i
                    b += g
                if v2(S + b) > v_now:
                    best = (w, w + L, b)
                    break
            if best: break
        if not best:
            print("STUCK at v =", v_now); break
        w, j, b = best
        Z.extend(range(w, j + 1))
        S += b
        cur = j
        print(f"add [{w},{j}]  ->  v_2(S) = {v2(S)}   (S = 2^{v2(S)} * {S >> v2(S)})")
        if v2(S) > 60: print("... (stopping, deep enough)"); break

if __name__ == "__main__":
    main()
