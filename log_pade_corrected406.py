#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
THE LOG-PADE MEASUREMENT, CORRECTED (S096c).

FORMER BUG: the [n/n] Pade of log(1+x) at x=3 approximates log(4) — the
linear form is  Q_n(3)*log(4) - P_n(3).  The first experiment wrongly used
lambda = log(4)/3 inside the form.  Corrected here, plus:

* primitive reduction: divide (q_n, p_n) by gcd (content) — sizes drop,
  precision invariant when the content is a 3-unit (measured both ways);
* the race: precision slope vs log_3 size slope — WIN iff slope margin > 0;
* two-method lambda (tower + series), both proven equal.

If  v_3(q_n log4 - p_n) - log_3(max|q_n|,|p_n|) -> +inf  along a
subsequence, then log(4) is 3-adically irrational — THE FULL KILL:
lambda = log4/3 irrational ⟹ NO rider at ANY head ⟹ MahlerSharp
⟹ (S093/S094/S095 green chain) ⟹ tailF ⟹ Erdos #406 unconditional.
"""
from fractions import Fraction
import math
import sys

def v3(x: int) -> int:
    if x == 0:
        raise ValueError("v3(0)")
    x = abs(x)
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v

def s3(n: int) -> int:
    s = 0
    while n:
        s += n % 3
        n //= 3
        if s > 10**6:
            break
    return s

def lambda_via_tower(K: int) -> int:
    M = 3 ** (2 * K + 1)
    t = pow(3, K)
    num = (pow(4, t, M) - 1) % M
    c = num // (3 ** (K + 1))
    return c % (3 ** K)

def log4_mod(K: int) -> int:
    """log(4) mod 3^K via lambda*3: log4 = 3*lambda, v_3 = 1 exactly,
    so log4 mod 3^K needs lambda mod 3^(K-1)."""
    lam = lambda_via_tower(K + 2)
    return (3 * lam) % (3 ** K)

def pade_nn_log(n: int):
    a = [Fraction(0)] + [Fraction((-1) ** (i + 1), i) for i in range(1, 2 * n + 2)]
    F = Fraction
    A = []
    for j in range(n + 1, 2 * n + 1):
        row = [a[j - k] if j - k >= 1 else F(0) for k in range(1, n + 1)]
        rhs = -a[j]
        A.append((row, rhs))
    nv = n
    M = [list(r) + [rhs] for (r, rhs) in A]
    for col in range(nv):
        piv = None
        for r in range(col, len(M)):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("singular")
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(len(M)):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    q = [F(1)] + [M[i][nv] for i in range(nv)]
    p = []
    for j in range(0, n + 1):
        val = F(0)
        for k in range(0, min(j, n) + 1):
            if j - k >= 1:
                val += q[k] * a[j - k]
        p.append(val)
    den = 1
    for c in q + p:
        den = den * c.denominator // math.gcd(den, c.denominator)
    Qi = [int(c * den) for c in q]
    Pi = [int(c * den) for c in p]
    # primitive reduction
    g = 0
    for c in Qi + Pi:
        g = math.gcd(g, abs(c))
    if g > 1:
        Qi = [c // g for c in Qi]
        Pi = [c // g for c in Pi]
    return Qi, Pi, g

def eval_poly(cs, x: int) -> int:
    v = 0
    for c in reversed(cs):
        v = v * x + c
    return v

def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    print("== log(4) = 3*lambda two-method cross-check ==")
    # method B for log4: direct series log(4) = sum (-1)^(j+1) 3^j / j
    def log4_series(K):
        MK = 3 ** K
        total = 0
        NBOUND = K + 2 * K.bit_length() + 30
        for n in range(1, NBOUND + 1):
            m = n
            aa = n - v3(n)  # valuation of 3^n/n
            if aa >= K:
                continue
            Mod = 3 ** (K - aa)
            inv = pow(m // (3 ** v3(m)) % Mod, -1, Mod)
            term = inv % Mod
            if n % 2 == 0:
                term = (-term) % Mod
            total = (total + term * (3 ** aa)) % MK
        return total
    for K in (20, 50):
        A = log4_mod(K)
        B = log4_series(K)
        print(f"K={K}: tower==series: {A == B}")
        assert A == B
    print()
    print("== the CORRECTED [n/n] log-Pade forms: q_n*log4 - p_n ==")
    print(f"{'n':>3} {'v3':>6} {'log3|q|':>9} {'log3|p|':>9} {'margin':>8} {'content':>10} {'v3cont':>6} {'verdict':>8}")
    for n in range(1, NMAX + 1):
        Q, P, g = pade_nn_log(n)
        qn = eval_poly(Q, 3)
        pn = eval_poly(P, 3)
        K = 2 * n + 60
        l4 = log4_mod(K)
        MK = 3 ** K
        form = (qn % MK) * l4 - (pn % MK)
        form %= MK
        if form == 0:
            v = K
        else:
            v = v3(form)
            K2 = K + 25
            l42 = log4_mod(K2)
            form2 = (qn % (3 ** K2)) * l42 - (pn % (3 ** K2))
            form2 %= 3 ** K2
            if form2 == 0:
                v = K2
            else:
                assert v3(form2) == v, f"instability n={n}"
        lq = math.log(abs(qn), 3) if qn else 0.0
        lp = math.log(abs(pn), 3) if pn else 0.0
        margin = v - max(lq, lp)
        verdict = "WIN" if margin > 0 else "LOSS"
        print(f"{n:>3} {v:>6} {lq:>9.2f} {lp:>9.2f} {margin:>8.2f} "
              f"{str(g)[:10]:>10} {v3(g) if g else 0:>6} {verdict:>8}")

if __name__ == "__main__":
    main()
