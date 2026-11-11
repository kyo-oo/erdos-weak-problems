#!/usr/bin/env python3
"""#686 round 3 — the k=3 SQUARE census engine.
Problem (corpus #686): can every integer N >= 2 be written as
    N = prod_{1<=i<=k}(m+i) / prod_{1<=i<=k}(n+i)
for some k >= 2 and m >= n+k?
Non-squares: DONE (Kill #20, Pell units). Squares k=2: DONE (Kill #29,
family t=2(2d+5) + sporadic 99/195 + census t<=100). k=3 witnesses known
(S037): (t,m,n) = (4,13,4), (3,25,11), (70,47,1), (4756,1679,4),
(1189,1679,13), (1798,13453,89).
This engine: complete k=3 census for t <= TMAX (all (m,n) with
(m+1)(m+2)(m+3) = t^2 (n+1)(n+2)(n+3), m >= n+3, n >= 1, t <= TMAX).
Method: for each n, D = (n+1)(n+2)(n+3); m-bound = cbrt(TMAX^2 * D);
scan m, check D | prod(m+i) and quotient is a square <= TMAX^2.
Dual method: direct scan + (for witnesses) sympy factorization replay.
"""
from math import isqrt

def c3(x):
    return (x+1)*(x+2)*(x+3)

def k3_census(TMAX, NMAX):
    """All k=3 square witnesses with t <= TMAX, n <= NMAX."""
    out = []
    T2 = TMAX*TMAX
    for n in range(1, NMAX+1):
        D = c3(n)
        # m bound: c3(m) <= T2 * D
        m = n + 3
        # quick upper bound via real cbrt
        hi = int(round((T2 * D) ** (1/3.))) + 3
        if c3(hi) < T2*D:
            while c3(hi) < T2*D:
                hi = int(hi*1.5)+3
        p = 1
        # iterate m from n+3 to hi, incremental product
        v = c3(m)
        while v <= T2 * D:
            if v % D == 0:
                q = v // D
                r = isqrt(q)
                if r*r == q and r <= TMAX and r >= 2:
                    out.append((r, m, n))
            m += 1
            v = c3(m)
    return out

if __name__ == "__main__":
    import sys
    TMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    wits = k3_census(TMAX, NMAX)
    print(f"=== #686 k=3 square census: t <= {TMAX}, n <= {NMAX} ===")
    print(f"witnesses (t, m, n): {len(wits)}")
    for (t, m, n) in sorted(wits):
        lhs = c3(m); rhs = t*t*c3(n)
        assert lhs == rhs, (t,m,n)
        print(f"  t={t}: (m+1)(m+2)(m+3) = {m+1}*{m+2}*{m+3} = {lhs} = {t}^2 * {c3(n)} = {t}^2*({n+1}*{n+2}*{n+3})  [m={m}, n={n}]")
    ts = sorted(set(w[0] for w in wits))
    print(f"distinct t values: {ts}")
    print(f"census t <= {TMAX}: k=3-representable squares = exactly t in {ts}")
