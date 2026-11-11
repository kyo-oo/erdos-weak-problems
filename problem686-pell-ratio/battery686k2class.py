#!/usr/bin/env python3
"""battery686k2class.py — Erdős #686 Kernel 42 battery (the k=2 classification).
Triple-method, the campaign standard:
  M1 (chain replay): every chain value t ≤ 3000 — verify (m+1)(m+2) = t²(n+1)(n+2).
  M2 (Pell reconstruction): X² − t²Y² = 1 − t² with X,Y recovered from m,n.
  M3 (the classification seal): the divisor-pair scan (K26 divNoRepSmall logic)
      agrees with the chain set EXACTLY on t ≤ 2000 (zero symmetric difference).
Also: the six new-layer witness edges + the de-sporadicized 99/195 + the no-go list.
"""
import sys

def chev(y, n):
    a, b = 1, y
    if n == 0: return 1
    for _ in range(n - 1):
        a, b = b, y * b - a
    return b

def chain_values(limit):
    """All (y, j, t) chain values with y ≡ 2 mod 4, y ≥ 10, t ≤ limit."""
    out = []
    y = 10
    while y <= limit:
        j = 1
        while True:
            t = chev(y, j)
            if t > limit: break
            out.append((y, j, t))
            j += 1
        y += 4
    return out

def div_no_rep_small(t, d1):
    """The K26 divisor-pair validity check (verbatim port)."""
    M = t * t - 1
    if d1 == 0 or M % d1 != 0: return False
    d2 = M // d1
    if d1 >= d2: return False
    X, Y = (d2 - d1) // 2, (d2 + d1) // (2 * t)
    return (d2 - d1) % 2 == 0 and X % 2 == 1 and X >= 9 and \
           (d2 + d1) % (2 * t) == 0 and Y % 2 == 1 and Y >= 5 and X >= Y + 2

def scan_rep2(t):
    return any(div_no_rep_small(t, d1) for d1 in range(1, t))

def main():
    fails = 0
    # M1 + M2: chain replay
    cv = chain_values(3000)
    for (y, j, t) in cv:
        X = (chev(y, j + 1) - chev(y, j - 1)) // 2
        Y = y // 2
        m, n = (X - 3) // 2, (Y - 3) // 2
        ok1 = (m + 1) * (m + 2) == t * t * (n + 1) * (n + 2)
        ok2 = X * X - t * t * Y * Y == 1 - t * t
        ok3 = 2 * m + 3 == X and 2 * n + 3 == Y and X % 2 == 1 and Y % 2 == 1
        ok4 = n >= 1 and m >= n + 2
        if not (ok1 and ok2 and ok3 and ok4):
            fails += 1
            print(f"FAIL M1/M2 at (y={y}, j={j}, t={t})")
    # M3: the classification seal (scan vs chain set, t ≤ 2000)
    chain_set = {t for (_, _, t) in chain_values(2000)}
    scan_set = {t for t in range(2, 2001) if scan_rep2(t)}
    if chain_set != scan_set:
        fails += 1
        print("FAIL M3: scan/chain mismatch",
              "chain-only:", sorted(chain_set - scan_set)[:10],
              "scan-only:", sorted(scan_set - chain_set)[:10])
    # the witness edges (kernel-decided receipts)
    for (t, m, n) in [(980, 2399, 1), (2716, 9407, 2), (9701, 23761, 1),
                      (323, 1443, 3), (10604, 58079, 4), (17524, 113567, 5),
                      (99, 241, 1), (195, 674, 2)]:
        if (m + 1) * (m + 2) != t * t * (n + 1) * (n + 2):
            fails += 1
            print(f"FAIL edge t={t}")
    # the de-sporadicization: 99 = chev(10,2), 195 = chev(14,2)
    if chev(10, 2) != 99 or chev(14, 2) != 195:
        fails += 1; print("FAIL de-sporadicization")
    # the no-go list
    for t in [2, 5, 6, 7, 8, 9, 11, 12, 13, 15, 16]:
        if t in chain_set or scan_rep2(t):
            fails += 1; print(f"FAIL no-go t={t}")
    if fails == 0:
        n_cv = len(cv)
        print(f"BATTERY686K2CLASS_GREEN=1 chain-replays={n_cv} "
              f"seal(2000)={len(scan_set)} exact both directions")
    else:
        print(f"BATTERY686K2CLASS_FAIL failures={fails}")
        sys.exit(1)

if __name__ == "__main__":
    main()
