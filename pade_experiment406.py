#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
THE PADE EXPERIMENT (S096) — the socket's decisive numerical reconnaissance.

TARGET: lambda = log(4)/3 in Z_3 (the frozen diagonal limit L = lim c_s,
c_s = (4^(3^s)-1)/3^(s+1)).  The S095 kernel reduced the HFTAIL socket to:
the six rider streams uhat(m) = m/(2*lambda), m in {1,5,7} (+ antipodes),
are NOT natural numbers.  A sufficient kill: lambda is 3-adically IRRATIONAL.

CRITERION (the p-adic irrationality machine): if integers (p_n, q_n) satisfy
  (i)  q_n*lambda - p_n != 0,
  (ii) v_3(q_n*lambda - p_n) >= (mu+eps)*n,
  (iii) max(|p_n|,|q_n|) <= 3^(mu*n),
with eps > 0 fixed, then lambda is irrational: a rational P/Q would force
the nonzero integer q_n*P - p_n*Q to be divisible by 3^((mu+eps)n) while
bounded by (|P|+Q)*3^(mu*n) — false for large n.

WEAPON: the [n/n] Pade approximants of log(1+x), evaluated at x = 3.
  Q_n(x)*log(1+x) - P_n(x) = O(x^(2n+1))  =>  v_3 >= 2n+1 + (losses).
Sizes: |Q_n(3)| ~ C*rho^n (Legendre growth).  The experiment MEASURES
both slopes and reads the verdict.  Two independent methods for lambda
(the tower + the log series) — the two-method receipt law.

OUTPUT: per n — v_3 of the linear form, log_3 of the sizes, the margin.
"""
from fractions import Fraction
import sys

# ---------------------------------------------------------------- helpers

def v3(x: int) -> int:
    """3-adic valuation of a nonzero integer (negative allowed via sign)."""
    if x == 0:
        raise ValueError("v3(0)")
    x = abs(x)
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v

def lambda_via_tower(K: int) -> int:
    """lambda mod 3^K, METHOD A: the tower  c_s = (4^(3^s)-1)/3^(s+1),
    lambda = lim c_s, v_3(lambda - c_s) = s+1 exactly.  Take s = K."""
    # need c_K mod 3^K:  4^(3^K) mod 3^(2K+1)
    M = 3 ** (2 * K + 1)
    t = pow(3, K)                      # 3^K
    num = (pow(4, t, M) - 1) % M       # 4^(3^K) - 1, divisible by 3^(K+1)
    c = num // (3 ** (K + 1))          # exact integer division
    return c % (3 ** K)

def lambda_via_series(K: int) -> int:
    """lambda mod 3^K, METHOD B:  lambda = sum_{n>=1} (-1)^(n+1) 3^(n-1)/n.
    Term n has v_3 = n-1-v_3(n); only n with n-1-v_3(n) < K contribute."""
    MK = 3 ** K
    total = 0
    # term n has valuation n-1-v_3(n), NOT monotone (n=8 -> 7, n=9 -> 6);
    # safe bound: include every n with n-1-v_3(n) < K; since v_3(n) <=
    # log_3(n), all n <= K + log_3(K) + 2 have valuation < K + margin and
    # every n >= K + 2 has valuation >= K-... just scan a generous window.
    NBOUND = K + 2 * K.bit_length() + 30
    for n in range(1, NBOUND + 1):
        m = n
        a = n - 1
        while m % 3 == 0:
            m //= 3
            a -= 1
        if a >= K:
            continue
        # term_n = (-1)^(n+1) * 3^a * m^{-1},  a = n-1-v3(n), m = n/3^v3(n)
        Mod = 3 ** (K - a)
        inv = pow(m % Mod, -1, Mod)
        term = inv % Mod
        if n % 2 == 0:
            term = (-term) % Mod
        total = (total + term * (3 ** a)) % MK
        n += 1
    return total % MK

# ---------------------------------------------------------------- Pade

def pade_nn_log(n: int):
    """[n/n] Pade of log(1+x): integer coefficient polys (Qn, Pn) with
    Qn*log(1+x) - Pn = O(x^(2n+1)), Qn normalized to integer coefficients
    (cleared denominators, positive leading scale).  Returns (Q, P) as
    coefficient lists (index = power)."""
    # log(1+x) coefficients: a_0 = 0, a_i = (-1)^(i+1)/i
    a = [Fraction(0)] + [Fraction((-1) ** (i + 1), i) for i in range(1, 2 * n + 2)]
    # unknowns: q_0..q_n (set q_0 = 1), p_0..p_n
    # equations j = 0..2n:  sum_{k=0}^{min(j,n)} q_k a_{j-k}  -  p_j = 0
    #                    (p_j taken as 0 when j > n)
    # solve sequentially: j = 0: q_0*a_0 - p_0 = 0 => p_0 = 0.
    # For j <= n:  q_j*a_0 + sum_{k<j} q_k a_{j-k} - p_j = 0
    #            => p_j = sum_{k=1}^{j} q_k a_{j-k}   (a_0 = 0, k=0 drops)
    # For j > n:   sum_{k=0}^{n} q_k a_{j-k} - 0 = 0  — determines q_j? no:
    #            q's are n+1 unknowns; equations j = n+1..2n are n equations.
    # Together with q_0 = 1: n+1 conditions. Solve bottom-up:
    #   j from 1..n: choose q_j freely? NO — standard: use j = n+1..2n to
    #   determine q_1..q_n (triangular via a_{j-k} with k = n: a_{j-n}).
    # Build the linear system with Fractions.
    from fractions import Fraction as F
    # variables: q_1..q_n (q_0 = 1 fixed); equations j = n+1..2n
    A = []  # rows: list of F coefficients for q_1..q_n, plus rhs
    for j in range(n + 1, 2 * n + 1):
        row = []
        rhs = F(0)
        # sum_{k=0}^{n} q_k a_{j-k} = 0  =>  sum_{k=1}^{n} q_k a_{j-k} = -a_j
        for k in range(1, n + 1):
            row.append(a[j - k] if j - k >= 1 else F(0))
        rhs = -a[j]
        A.append((row, rhs))
    # Gaussian elimination with Fractions
    nv = n
    M = [list(r) + [rhs] for (r, rhs) in A]
    for col in range(nv):
        # find pivot
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
    # p_j for j = 0..n: p_j = sum_{k=1}^{j} q_k a_{j-k}  (+ q_0 a_j = 0)
    p = []
    for j in range(0, n + 1):
        val = F(0)
        for k in range(0, min(j, n) + 1):
            if j - k >= 1:
                val += q[k] * a[j - k]
        p.append(val)
    # clear denominators
    from math import lcm
    den = 1
    for c in q + p:
        den = lcm(den, c.denominator)
    Qi = [int(c * den) for c in q]
    Pi = [int(c * den) for c in p]
    return Qi, Pi

def eval_poly(cs, x: int) -> int:
    v = 0
    for c in reversed(cs):
        v = v * x + c
    return v

# ---------------------------------------------------------------- main

def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    print("== lambda two-method cross-check ==")
    for K in (20, 60, 120):
        A = lambda_via_tower(K)
        B = lambda_via_series(K)
        print(f"K={K}: tower==series: {A == B}")
        assert A == B, "TWO-METHOD DISAGREEMENT"
    print()
    print("== the [n/n] Pade linear forms at x=3 ==")
    print(f"{'n':>3} {'v3(L_n)':>8} {'log3|q|':>9} {'log3|p|':>9} "
          f"{'log3max':>8} {'margin':>8} {'verdict':>8}")
    lam_digits = {}
    for n in range(1, NMAX + 1):
        Q, P = pade_nn_log(n)
        qn = eval_poly(Q, 3)
        pn = eval_poly(P, 3)
        # v3 of qn*lambda - pn:  need lambda to precision K
        import math
        K = 4 * n + 30
        lam = lambda_via_tower(K)
        MK = 3 ** K
        form = (qn % MK) * lam - (pn % MK)
        form %= MK
        if form == 0:
            v = K  # at least K
        else:
            v = v3(form)
            # cert: recompute with higher precision to confirm
            K2 = K + 20
            lam2 = lambda_via_tower(K2)
            form2 = (qn % (3 ** K2)) * lam2 - (pn % (3 ** K2))
            form2 %= 3 ** K2
            if form2 == 0:
                v = K2
            else:
                assert v3(form2) == v, f"precision instability at n={n}"
        lq = math.log(abs(qn), 3) if qn else 0.0
        lp = math.log(abs(pn), 3) if pn else 0.0
        lmax = max(lq, lp)
        margin = v - lmax
        verdict = "WIN" if margin > 0 else "LOSS"
        print(f"{n:>3} {v:>8} {lq:>9.2f} {lp:>9.2f} {lmax:>8.2f} "
              f"{margin:>8.2f} {verdict:>8}")
    print()
    print("Reading: margin = v3(form) - log3(max size).  Slope-wise win")
    print("(margin growing with n) => lambda irrational by the criterion.")

if __name__ == "__main__":
    main()
