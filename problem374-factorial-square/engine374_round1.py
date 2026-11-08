#!/usr/bin/env python3
"""#374 round 1 — the F(m)/D_k engine (K17+K19 transfer).
Statement (verbatim, erdosproblems.com/374):
  For any m in N, let F(m) be the minimal k >= 2 (if it exists) such that
  there are a_1 < ... < a_k = m with a_1!*...*a_k! a square. Let
  D_k = {m : F(m) = k}. What is the order of growth of |D_k ∩ [1,n]| for
  3 <= k <= 6? For example, is it true that |D_6 ∩ [1,n]| >> n?

Machinery (the #1108 arsenal): a_1!*...*a_k! is a square iff the XOR
(sum mod 2) of the Legendre parity vectors kappa(a_i) = (v_p(a_i!) mod 2)_p
is zero. kappa(a) = XOR_{2<=j<=a} sqf(j) where sqf(j) = squarefree kernel
indicator vector of j. So F(m) = 1 + min{|S| : S subset of [2, m-1],
XOR of kappa(a), a in S, equals kappa(m)}.

Engine v2 (S039): incremental kappa table + meet-in-the-middle over prior
kappas (sizes 1, 2, then triples via pair table) to resolve F(m) <= 4
exactly. This run also certifies the D2 = squares law and produces the
witness lists for the kernel census bounds."""
from sympy import factorint

def solve(N):
    K = {1: frozenset()}
    cur = set()
    for a in range(2, N + 1):
        for p, e in factorint(a).items():
            if e % 2 == 1:
                cur.symmetric_difference_update({p})
        K[a] = frozenset(cur)
    singles = {}   # xor value -> earliest a (>=2) with that kappa
    pairs = {}     # xor of two kappas (a<b) -> the later element b of the earliest attaining pair
    F = {}
    D = {}
    witnesses = {}
    for m in range(2, N + 1):
        km = K[m]
        f = None
        wit = None
        if km in singles and singles[km] != m:
            f = 2
            wit = (singles[km],)
        elif km in pairs and pairs[km] < m:
            f = 3
            wit = None  # filled below by explicit triple witness search
        else:
            # F = 4 iff exists a < m with (km ^ K[a]) in pairs, pair usable < m
            for a in range(2, m):
                t = km ^ K[a]
                if t in pairs and pairs[t] < m:
                    f = 4
                    wit = None
                    break
        if f == 3:
            # explicit triple witness (a, b, m): kappa(a)^kappa(b) == kappa(m)
            found = None
            for a in range(2, m - 1):
                for b in range(a + 1, m):
                    if K[a] ^ K[b] == km:
                        found = (a, b)
                        break
                if found:
                    break
            wit = found
        if f == 4:
            # explicit quadruple witness (a, b, c, m)
            found = None
            for c in range(3, m):
                rest = km ^ K[c]
                for a in range(2, c - 1):
                    for b in range(a + 1, c):
                        if K[a] ^ K[b] == rest:
                            found = (a, b, c)
                            break
                    if found:
                        break
                if found:
                    break
            wit = found
        F[m] = f
        if f:
            D[f] = D.get(f, 0) + 1
            witnesses[m] = wit
        if km not in singles:
            singles[km] = m
        for a in range(2, m):
            x = K[a] ^ km
            if x not in pairs:
                pairs[x] = m  # the later element of the earliest attaining pair
    return F, D, witnesses, K

def is_square(n):
    import math
    r = math.isqrt(n)
    return r * r == n

if __name__ == "__main__":
    import sys
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    F, D, witnesses, K = solve(N)
    print(f"=== #374 round 1 (S039 re-run): F(m) for m <= {N} ===")
    print("D_k counts:", dict(sorted(D.items())))
    undef = [m for m in range(2, N + 1) if F[m] is None]
    print(f"F(m) unresolved beyond k=4: {len(undef)} values; first 20: {undef[:20]}")
    for k in (2, 3, 4):
        dk = [m for m in range(2, N + 1) if F[m] == k]
        print(f"D_{k} ({len(dk)} members, first 30):", dk[:30])
        if dk:
            half = N // 2
            h = len([m for m in dk if m <= half]) / half
            print(f"   density in [1,{half}] = {h:.4f}; in [1,{N}] = {len(dk)/N:.4f}")
    # THE D2 = SQUARES LAW certification
    d2 = [m for m in range(2, N + 1) if F[m] == 2]
    sqs = [m for m in range(4, N + 1) if is_square(m)]
    print(f"=== D2 == squares>=4 law: {'EXACT' if d2 == sqs else 'VIOLATED'} (D2={d2}, squares={sqs}) ===")
    # Witness verification: every witness actually gives a square product
    import math
    from math import factorial
    bad = 0
    for m, w in witnesses.items():
        if w is None:
            print(f"  MISSING WITNESS at m={m}, F={F[m]}")
            bad += 1
            continue
        prod = 1
        for a in w:
            prod *= factorial(a)
        prod *= factorial(m)
        if not is_square(prod):
            print(f"  BAD WITNESS at m={m}: {w}")
            bad += 1
    print(f"=== witness square-verification: {len(witnesses) - bad}/{len(witnesses)} exact squares ===")
    # The family identity check: (t^2-1)! * (t^2)! = (t*(t^2-1)!)^2
    fam_ok = all(factorial(t*t - 1) * factorial(t*t) == (t * factorial(t*t - 1))**2 for t in range(2, 20))
    print(f"=== family identity (t^2-1)!*(t^2)! = (t*(t^2-1)!)^2 for t in [2,20): {fam_ok} ===")
    # D2 witness structure: squares use a = t^2 - 1
    struct = [(m, witnesses[m]) for m in d2[:12]]
    print("D2 witnesses (m, (a,)):", struct)
    # D3 witness table for the kernel
    d3w = [(m, witnesses[m]) for m in range(2, N + 1) if F[m] == 3]
    print(f"D3 witnesses (m, (a,b)) first 40:", d3w[:40])
    d4w = [(m, witnesses[m]) for m in range(2, N + 1) if F[m] == 4]
    print(f"D4 witnesses (m, (a,b,c)) first 40:", d4w[:40])
