#!/usr/bin/env python3
"""Independent verification battery for the bulldoze double kill.

KILL #3 — Erdos #271 (Stanley S(0,2)):
  1. greedy == digit-predicate up to 3^7
  2. census |A(2) ∩ [0,3^k)| = 2^k for k ≤ 7
  3. AP-freeness of D, exhaustive in [0, 3^5)
  4. maximality: every m ∉ D with 3 ≤ m < 3^5 has a blocking D-pair below

KILL #4 — Erdos #404 (left-factorial kernel law):
  5. v2(sum_{a=u}^{N} a!) == v2(u!) + v2(u+2) for 0 ≤ u ≤ 60, u+3 ≤ N ≤ u+15
  6. closed form K(u,3) = (u+2)(1 + (u+1)(u+4)) with odd cofactor, u ≤ 300
"""
import math


def no_two(n):
    while n:
        if n % 3 == 2:
            return False
        n //= 3
    return True


def in_d(m):
    return m % 3 in (0, 2) and no_two(m // 3)


def greedy_stanley(limit):
    """Greedy 3-AP-free set seeded with {0, 2}."""
    S = []
    for m in range(limit):
        if m in (0, 2):
            S.append(m)
            continue
        if m < 3:
            continue
        blocked = False
        for i in range(len(S)):
            for j in range(i + 1, len(S)):
                a, b = S[i], S[j]
                if b < m and a + m == 2 * b:
                    blocked = True
                    break
            if blocked:
                break
        if not blocked:
            S.append(m)
    return S


def v2(n):
    if n == 0:
        return 0
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def fact(n):
    return math.factorial(n)


def main():
    failures = 0

    # --- 1+2: greedy == D; census 2^k ---
    LIM = 3 ** 7
    G = greedy_stanley(LIM)
    D = [m for m in range(LIM) if in_d(m)]
    if G != D:
        print("FAIL 1: greedy != digit predicate up to 3^7")
        failures += 1
    else:
        print("PASS 1: greedy == digit predicate up to 3^7 "
              f"({len(D)} members)")
    for k in range(8):
        cnt = sum(1 for m in range(3 ** k) if in_d(m))
        if cnt != 2 ** k:
            print(f"FAIL 2: census at k={k}: {cnt} != {2 ** k}")
            failures += 1
        else:
            print(f"PASS 2: |A(2) ∩ [0,3^{k})| = {cnt} = 2^{k}")

    # --- 3: AP-freeness of D in [0, 3^5) ---
    W = [m for m in range(3 ** 5) if in_d(m)]
    ap_free = True
    for i in range(len(W)):
        for j in range(i + 1, len(W)):
            for l in range(j + 1, len(W)):
                if W[i] + W[l] == 2 * W[j]:
                    ap_free = False
    if ap_free:
        print("PASS 3: D is 3-AP-free in [0, 3^5) "
              f"({len(W)} points, no AP)")
    else:
        print("FAIL 3: found an AP in D")
        failures += 1

    # --- 4: maximality — every m ∉ D (3 ≤ m < 3^5) blocked from below ---
    missing = 0
    for m in range(3, 3 ** 5):
        if in_d(m):
            continue
        blocked = any(a + m == 2 * b
                      for a in D if a < m for b in D if a < b < m)
        if not blocked:
            missing += 1
    if missing == 0:
        print("PASS 4: every non-member in [3, 3^5) blocked by a D-pair")
    else:
        print(f"FAIL 4: {missing} unblocked non-members")
        failures += 1

    # --- 5: kernel law ---
    checked = 0
    for u in range(61):
        s = 0
        for a in range(u, u + 16):
            s += fact(a)
            if a >= u + 3:
                checked += 1
                if v2(s) != v2(fact(u)) + v2(u + 2):
                    print(f"FAIL 5: u={u}, N={a}: "
                          f"{v2(s)} != {v2(fact(u)) + v2(u + 2)}")
                    failures += 1
    print(f"PASS 5: kernel law v2(sum) = v2(u!) + v2(u+2) "
          f"verified on {checked} (u, N) pairs")

    # --- 6: closed form of the 3-kernel ---
    for u in range(301):
        K3 = 1 + (u + 1) + (u + 1) * (u + 2) + (u + 1) * (u + 2) * (u + 3)
        rhs = (u + 2) * (1 + (u + 1) * (u + 4))
        if K3 != rhs:
            print(f"FAIL 6: K({u},3) closed form mismatch")
            failures += 1
            break
        if (1 + (u + 1) * (u + 4)) % 2 != 1:
            print(f"FAIL 6: cofactor even at u={u}")
            failures += 1
            break
    else:
        print("PASS 6: K(u,3) = (u+2)(1+(u+1)(u+4)), odd cofactor, u ≤ 300")

    print()
    if failures:
        print(f"VERIFICATION FAILED: {failures} failures")
        raise SystemExit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
