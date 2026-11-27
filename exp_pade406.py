#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
THE EXP-PADE MEASUREMENT (S096b) — the rider's door.

THE RIDER EQUATION (S095 socket): a rider (a, u) forces
    4^(2u) = exp(3k),  k = 2a-9 in {+-1, +-5, +-7}.
So the socket dies if  exp(3m) is irrational for m in {1, 5, 7}
(negatives come free: exp(-x) = 1/exp(x)).

WEAPON: [n/n] Pade of e^z, evaluated at z = 3m.  Hermite's engine:
    Q_n(z) e^z - P_n(z) = z^(2n+1) * S_n(z),  S_n with factorial
    denominators — the p-adic precision can WIN here because the
    numerator gain z^(2n+1) (v_3 = 2n+1 for z = 3m) races against
    v_3((2n+1+j)!) ~ (2n+1+j)/2, and each term of the remainder
    series has INCREASING valuation (j+s_3(j))/2-ish.

CRITERION: slope(v_3(L_n)) > slope(log_3 max(|p_n|,|q_n|)) along an
infinite n-subsequence  =>  exp(3m) irrational.

Two methods for exp(3m) mod 3^K: (A) direct series, (B) the functional
equation exp(3m) = exp(3)^m (tower-independent cross-check).
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

def exp_padic(z: int, K: int) -> int:
    """exp(z) mod 3^K for v_3(z) >= 1:  sum z^j / j!.
    Term j has v_3 = j*v_3(z) - v_3(j!) = j - (j - s_3(j))/2 (for v_3(z)=1),
    which is (j + s_3(j))/2 — increasing.  Include all j with val < K."""
    MK = 3 ** K
    # find j bound: (j + s_3(j))/2 >= K  =>  j >= 2K - s_3(j) <= 2K
    def s3(n):
        s = 0
        while n:
            s += n % 3
            n //= 3
        return s
    total = 0
    j = 0
    # term values as exact ints: t_j = z^j / j! — track as Fraction? too slow.
    # Better: term_j = z^j/j! — v_3(t_j) = j*v3(z) - v3(j!).
    # Compute incrementally with modular inverse of the 3-free part.
    vz = v3(z)
    zfree = z // (3 ** vz)
    jbound = 2 * K + 10
    for j in range(0, jbound + 1):
        # v_3(j!)
        vj = 0
        p3 = 3
        while p3 <= j:
            vj += j // p3
            p3 *= 3
        a = j * vz - vj
        if a >= K:
            if j > 0 and j * vz - vj >= K:
                # all later terms also >= K? valuation increases in j
                # (j+1)*vz - v_{j+1}! vs j*vz - v_j!: +vz - v_3(j+1) >= 1-... 
                # not strictly increasing when v_3(j+1) = 2? vz=1, v3(j+1)=2:
                # change = 1-2 = -1. NOT monotone. keep scanning.
                continue
            continue
        # t_j = z^j / j! = 3^a * (zfree^j * 3^{j*vz - a}) / (j!/3^vj)
        #      = 3^a * zfree^j * 3^{j*vz - a - ???} ... careful:
        # z^j = 3^{j*vz} zfree^j;  j! = 3^{vj} * m, m = j!/3^vj (3-free)
        # t_j = 3^{j*vz - vj} * zfree^j / m  = 3^a * zfree^j * m^{-1}
        # with a = j*vz - vj  (may be negative for tiny j? j=0: 0; fine)
        m = math.factorial(j)
        assert v3(m) == vj
        mfree = m // (3 ** vj)
        Mod = 3 ** (K - a)
        num = pow(zfree % Mod, j, Mod)
        inv = pow(mfree % Mod, -1, Mod)
        term = (num * inv) % Mod
        total = (total + term * (3 ** a)) % MK
    return total % MK

def pade_nn_exp(n: int):
    """[n/n] Pade of e^z: integer polys (Q, P) with
    Q*e^z - P = O(z^{2n+1}).  Q normalized with integer coeffs
    (the Hermite normalization: Q_n(z) = sum_k binom(n,k)(2n-k)!/(n-k)!k! (-z)^k
    times n! — we just solve exactly and clear denominators)."""
    a = [Fraction(1, math.factorial(j)) for j in range(2 * n + 2)]
    # unknowns q_0..q_n, p_0..p_n; want sum_k q_k a_{j-k} = p_j (j<=n),
    # sum_k q_k a_{j-k} = 0 (n < j <= 2n).  Fix q_0 = 1? — standard [n/n]
    # normalization Q(0)=1.  Use equations j = n+1..2n for q_1..q_n.
    F = Fraction
    A = []
    for j in range(n + 1, 2 * n + 1):
        row = [a[j - k] if j - k >= 0 else F(0) for k in range(1, n + 1)]
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
            val += q[k] * a[j - k]
        p.append(val)
    den = 1
    for c in q + p:
        den = den * c.denominator // math.gcd(den, c.denominator)
    Qi = [int(c * den) for c in q]
    Pi = [int(c * den) for c in p]
    return Qi, Pi

def eval_poly(cs, x: int) -> int:
    v = 0
    for c in reversed(cs):
        v = v * x + c
    return v

def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    print("== exp two-method cross-check (series vs functional eq) ==")
    for z in (3, 15, 21):
        for K in (30, 60):
            A = exp_padic(z, K)
            # method B: exp(3m) = exp(3)^m
            m = z // 3
            e3 = exp_padic(3, K + 20)
            B = pow(e3, m, 3 ** K)
            print(f"z={z} K={K}: series==func-eq: {A == B}")
            assert A == B, f"DISAGREEMENT z={z} K={K}"
    print()
    for z in (3, 15, 21):
        print(f"== the [n/n] exp-Pade linear forms at z={z} ==")
        print(f"{'n':>3} {'v3(L_n)':>8} {'log3|q|':>9} {'log3|p|':>9} "
              f"{'margin':>8} {'verdict':>8}")
        prev_margin = None
        for n in range(2, NMAX + 1):
            Q, P = pade_nn_exp(n)
            qn = eval_poly(Q, z)
            pn = eval_poly(P, z)
            K = 3 * n + 40
            e = exp_padic(z, K)
            MK = 3 ** K
            form = (qn % MK) * e - (pn % MK)
            form %= MK
            if form == 0:
                v = K
            else:
                v = v3(form)
                K2 = K + 25
                e2 = exp_padic(z, K2)
                form2 = (qn % (3 ** K2)) * e2 - (pn % (3 ** K2))
                form2 %= 3 ** K2
                if form2 == 0:
                    v = K2
                else:
                    assert v3(form2) == v, f"instability z={z} n={n}"
            lq = math.log(abs(qn), 3) if qn else 0.0
            lp = math.log(abs(pn), 3) if pn else 0.0
            margin = v - max(lq, lp)
            verdict = "WIN" if margin > 0 else "LOSS"
            print(f"{n:>3} {v:>8} {lq:>9.2f} {lp:>9.2f} {margin:>8.2f} {verdict:>8}")
        print()

if __name__ == "__main__":
    main()
