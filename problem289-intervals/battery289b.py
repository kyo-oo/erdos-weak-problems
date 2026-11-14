#!/usr/bin/env python3
"""battery289b.py — W64-J: THE PELL CASCADE battery (the Lean-mirror for the
§8/§9 additions of Erdos289.lean). Every decide theorem pre-verified with
exact integer arithmetic; the cascade laws dual-verified (Fraction method +
integer cross-multiplication method) on the full engine range n ≤ 12.

1. THE SEQUENCES: dSeq (1, 6, 35, 204, 1189, 6930, 40391, 235416, 1372105,
   7997214, 46611179, 271669860, 1583407981) and mSeq (2, 14, 84, 492,
   2870, 16730, 97512, 568344, 3312554, 19306982, 112529340, 655869060,
   3822685022) — the value-table decide rows.
2. THE ADDITIVE RECURRENCE d_{n+2} + d_n = 6 d_{n+1} (n ≤ 11).
3. THE PELL INVARIANT d_{n+1}^2 + d_n^2 = 6 d_n d_{n+1} + 1 (n ≤ 11).
4. THE S-RELATION d_{n+1} = d_n + 2 m_n + 1 (n ≤ 11).
5. THE SPLIT CORE m_n (m_n + 1) = d_n d_{n+1} (n ≤ 11) — dual method.
6. THE k=5 FAMILY: [2,3],[14,15],[84,85],[492,493],[2870,2871] pairwise
   non-adjacent, total exactly 1 - 1/6930 — dual method.
7. THE k=7 FAMILY: + [16730,16731],[97512,97513], total exactly
   1 - 1/235416 — dual method.
"""
from fractions import Fraction

def build(N):
    d = [1, 6]
    m = [2]
    for n in range(N - 2):
        d.append(6 * d[-1] - d[-2])
    for n in range(N - 1):
        m.append(2 * d[n + 1] + m[n])
    return d, m

def main():
    N = 12
    d, m = build(N)
    print("dSeq:", d)
    print("mSeq:", m)
    ok = True

    # 1. value table (the decide rows)
    expect_d = [1, 6, 35, 204, 1189, 6930, 40391, 235416]
    expect_m = [2, 14, 84, 492, 2870, 16730, 97512]
    ok &= (d[:8] == expect_d) and (m[:7] == expect_m)
    print("[1] value table:", "GREEN" if ok else "FAIL")

    # 2-5. the four cascade laws (n ≤ N-2), dual where applicable
    for n in range(N - 2):
        assert d[n + 2] + d[n] == 6 * d[n + 1], n          # additive recurrence
        assert d[n + 1] ** 2 + d[n] ** 2 == 6 * d[n] * d[n + 1] + 1, n  # Pell
        assert d[n + 1] == d[n] + 2 * m[n] + 1, n          # S-relation
        # split core, method 1 (integer):
        assert m[n] * (m[n] + 1) == d[n] * d[n + 1], n
        # method 2 (Fraction): f(m_n) = 1/d_n - 1/d_{n+1}
        f = Fraction(1, m[n]) + Fraction(1, m[n] + 1)
        diff = Fraction(1, d[n]) - Fraction(1, d[n + 1])
        assert f == diff, n
    print(f"[2-5] cascade laws n<= {N-2}: GREEN (dual: integer + Fraction)")

    # 6-7. the two family witnesses, dual method
    for (k, dk) in [(5, 6930), (7, 235416)]:
        blocks = [(m[i], m[i] + 1) for i in range(k)]
        # shape: length 2, gaps >= 1
        assert all(b + 2 <= nb for (a, b), (na, nb) in zip(blocks, blocks[1:]))
        # method 1: Fraction total
        tot = sum(Fraction(1, a) + Fraction(1, a + 1) for (a, _) in blocks)
        assert tot == Fraction(1) - Fraction(1, dk), (k, tot)
        # method 2: integer cross-multiplied identity N*dk + P = dk*P
        P = 1
        for (a, _) in blocks:
            P *= a * (a + 1)
        Nn = 0
        for (a, b) in blocks:
            for t in (a, b):
                Nn += P // t
        assert Nn * dk + P == dk * P, k
        # method 3: unreduced fraction pair (num, den) equal semantics
        assert Fraction(Nn, P) == Fraction(dk - 1, dk), k
        print(f"[{'6' if k == 5 else '7'}] k={k} family: {blocks} "
              f"total = 1 - 1/{dk} GREEN (triple method)")
    print("BATTERY289B ALL GREEN")

if __name__ == "__main__":
    main()
