#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
THE ASYMMETRIC LOG-PADE FAMILIES (S096d) — the classical optimizer hunt.

Diagonal [n/n] loses by 0.88 slope (precision 1.95n vs size 2.83n).
The [p/q] family with p = rho*q: precision = p+q+1 (the x^{p+q+1} gain),
sizes ~ |Q(3)| (Jacobi-type growth in q) with |P(3)| ~ log4*|Q(3)|.
The optimizer over rho is the classical irrationality-measure machine
(the Rukhadze/Baker structure for log).

Measure [rho*n / n] for rho in {1, 1.5, 2, 2.5, 3, 4} — find any family
with margin slope > 0.
"""
from fractions import Fraction
import math
import sys

def v3(x: int) -> int:
    if x == 0:
        raise ValueError
    x = abs(x)
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v

def lambda_via_tower(K: int) -> int:
    M = 3 ** (2 * K + 1)
    num = (pow(4, pow(3, K), M) - 1) % M
    return (num // (3 ** (K + 1))) % (3 ** K)

def log4_mod(K: int) -> int:
    return (3 * lambda_via_tower(K + 2)) % (3 ** K)

def pade_pq_log(p: int, q: int):
    """[p/q] Pade of log(1+x): Q deg q, P deg p,
    Q*log(1+x) - P = O(x^{p+q+1}).  Q(0)=1 normalization, cleared,
    primitive."""
    N = p + q + 1
    a = [Fraction(0)] + [Fraction((-1) ** (i + 1), i) for i in range(1, N + 1)]
    F = Fraction
    # unknowns q_1..q_q (q_0 = 1); equations j = q+1 .. p+q (that's p
    # equations for q unknowns — OVERDETERMINED unless p <= q.
    # For p > q we instead fix P's high coefficients to zero: the system
    # is: for j = 0..p+q: sum_k q_k a_{j-k} - p_j = 0, p_j = 0 for j > p.
    # Unknowns: q_1..q_q and p_j (j<=p) are DETERMINED once q is fixed.
    # Equations with j > p: sum_{k=0}^{q} q_k a_{j-k} = 0 — that's
    # (p+q) - p = q equations for q unknowns q_1..q_q.  Square system.
    A = []
    for j in range(p + 1, p + q + 1):
        row = []
        for k in range(1, q + 1):
            row.append(a[j - k] if j - k >= 1 else F(0))
        A.append((row, -a[j]))
    nv = q
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
    qq = [F(1)] + [M[i][nv] for i in range(nv)]
    pp = []
    for j in range(0, p + 1):
        val = F(0)
        for k in range(0, min(j, q) + 1):
            if j - k >= 1:
                val += qq[k] * a[j - k]
        pp.append(val)
    den = 1
    for c in qq + pp:
        den = den * c.denominator // math.gcd(den, c.denominator)
    Qi = [int(c * den) for c in qq]
    Pi = [int(c * den) for c in pp]
    g = 0
    for c in Qi + Pi:
        g = math.gcd(g, abs(c))
    if g > 1:
        Qi = [c // g for c in Qi]
        Pi = [c // g for c in Pi]
    return Qi, Pi

def eval_poly(cs, x: int) -> int:
    v = 0
    for c in reversed(cs):
        v = v * x + c
    return v

def measure(q: int, p: int, tag: str):
    Q, P = pade_pq_log(p, q)
    qn = eval_poly(Q, 3)
    pn = eval_poly(P, 3)
    K = p + q + 60
    l4 = log4_mod(K)
    MK = 3 ** K
    form = (qn % MK) * l4 - (pn % MK)
    form %= MK
    if form == 0:
        v = K
    else:
        v = v3(form)
        K2 = K + 25
        form2 = (qn % (3 ** K2)) * (log4_mod(K2)) - (pn % (3 ** K2))
        form2 %= 3 ** K2
        if form2 == 0:
            v = K2
        else:
            assert v3(form2) == v
    lq = math.log(abs(qn), 3) if qn else 0.0
    lp = math.log(abs(pn), 3) if pn else 0.0
    margin = v - max(lq, lp)
    print(f"  {tag:>10} p={p:>3} q={q:>3}  v3={v:>5}  log3|q|={lq:>7.2f} "
          f"log3|p|={lp:>7.2f}  margin={margin:>8.2f}")
    return v, max(lq, lp)

def main():
    print("== asymmetric log-Pade families at x=3 ==")
    for rho_num, rho_den in ((3, 2), (2, 1), (5, 2), (3, 1), (4, 1), (1, 1), (1, 2)):
        print(f"-- family p/q = {rho_num}/{rho_den} --")
        base = 6
        for q in range(base, base + 9):
            p = (rho_num * q) // rho_den
            if p < 1:
                continue
            try:
                measure(q, p, f"[{p}/{q}]")
            except Exception as e:
                print(f"  [{p}/{q}] FAILED: {e}")
                break
        print()

if __name__ == "__main__":
    main()
