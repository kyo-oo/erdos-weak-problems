#!/usr/bin/env python3
"""
ASSAULT406 — PASS 2 (S078): the corrected shadow dust + the new laws.

  F1. SHADOW DUST (FIXED): cores mod 3^(k+1) dodging all windows at sheets
      1..k-1 AND diagonal trits 3..k <= 1.  Nested conditions, true counts.
      Convergence to the pi-points?
  F2. WINDOW INCREMENT LAW: trit_{s+1}(w_{s+1}) = (trit_{s+1}(w_s) + 1) % 3
      for all cores, all sheets s >= 1.  (The escalate-branch engine.)
  F3. EXACT FAMILY CARDINALITIES of tree A:
      |dust j ∩ (r%9=1)| = 2^(j-2), |dust j ∩ (r%9=4)| = 2^(j-2),
      |dust j ∩ (r%9=7)| = 0, |dust j ∩ (3|r)| = 2^(j-1)  (j >= 2)
  F4. TOWER SUBTREE SELF-SIMILARITY: dust j ∩ 3Z = 3 * tau(j-1) where
      tau = the survivor tree of 64^c — is tau(j) = dust j??  (If yes: the
      tower dust is EXACTLY the scaled row dust — a self-similarity law.)
  F5. PI-POINT RECEIPTS: trits of pi4/pi7/pi1 to level 60, positions of 2s.
"""
import sys

def tri(x, i):
    return (x // (3 ** i)) % 3

def trits(x, k):
    t = []
    for _ in range(k):
        t.append(x % 3)
        x //= 3
    return t

def powmod(a, e, m):
    r = 1
    a %= m
    while e:
        if e & 1:
            r = (r * a) % m
        a = (a * a) % m
        e >>= 1
    return r

def unit_word(K):
    M = 3 ** K
    w = 1
    for s in range(0, K):
        w = (w + (3 ** (s + 1)) * ((w * w) % M + (3 ** s) * ((w * w * w) % M))) % M
    return w

def hensel_inv(a, K):
    x = 0
    ainv = 1 if a % 3 == 1 else 2
    for k in range(1, K + 1):
        cur = (a * x) % (3 ** k)
        num = ((1 - cur) % (3 ** k)) // (3 ** (k - 1))
        x += ((num * ainv) % 3) * (3 ** (k - 1))
    assert (a * x) % (3 ** K) == 1
    return x

def pi_point(T, K):
    W = unit_word(K + 1)
    M = 3 ** K
    return ((T % M) * hensel_inv((2 * W) % M, K)) % M

def cut_chain(core, K):
    """omega_s(core) mod 3^K for s = 0..K-1 (iteratively, all mod 3^K)."""
    M = 3 ** K
    M2 = 3 * M
    w = (((pow(4, core, M2) - 1) % M2) // 3) % M
    out = [w]
    for i in range(1, K):
        w = (w + (3 ** i) * ((w * w) % M + (3 ** (i - 1)) * ((w * w * w) % M))) % M
        out.append(w)
    return out

def tree_A_iterative(J):
    alive = [0]
    levels = {0: [0]}
    for j in range(0, J):
        M = 3 ** (j + 2)
        new = []
        for r in alive:
            base = powmod(4, r, M)
            d = (base // (3 ** (j + 1))) % 3
            for t in range(3):
                if (d + t) % 3 != 2:
                    new.append(r + t * (3 ** j))
        alive = new
        levels[j + 1] = alive
    return levels

def tau_iterative(J):
    """The survivor tree of 64^c (the tower cores' own tree): classes c mod
    3^j with digit_q(64^c) != 2 for all q <= j."""
    alive = [0]
    levels = {0: [0]}
    for j in range(0, J):
        M = 3 ** (j + 2)
        new = []
        for r in alive:
            base = powmod(64, r, M)
            d = (base // (3 ** (j + 1))) % 3
            for t in range(3):
                if (d + t) % 3 != 2:
                    new.append(r + t * (3 ** j))
        alive = new
        levels[j + 1] = alive
    return levels

def main():
    print("ASSAULT406 PASS 2 — exact arithmetic only")
    print("=" * 78)

    # ---------------- F2: window increment law ----------------
    print("\nF2. WINDOW INCREMENT LAW: trit_{s+1}(w_{s+1}) = trit_{s+1}(w_s) + 1 mod 3")
    ok = True
    for core in [1, 2, 4, 5, 7, 8, 10, 13, 17, 22, 28, 43, 100, 970, 10021]:
        K = 14
        chain = cut_chain(core, K)
        for s in range(1, K - 1):
            lhs = tri(chain[s + 1], s + 1)
            rhs = (tri(chain[s], s + 1) + 1) % 3
            if lhs != rhs:
                ok = False
                print(f"  VIOLATION core={core} s={s}: {lhs} != {rhs}")
    print(f"  window-increment law: {'VERIFIED (15 cores x 12 sheets)' if ok else 'REFUTED'}")

    # ---------------- F3: exact family cardinalities ----------------
    print("\nF3. EXACT FAMILY CARDINALITIES OF TREE A (j = 2..13):")
    levels = tree_A_iterative(13)
    all_ok = True
    for j in range(2, 14):
        alive = levels[j]
        c1 = sum(1 for r in alive if r % 9 == 1)
        c4 = sum(1 for r in alive if r % 9 == 4)
        c7 = sum(1 for r in alive if r % 9 == 7)
        ct = sum(1 for r in alive if r % 3 == 0)
        e1, e4, e7, et = 2**(j-2), 2**(j-2), 0, 2**(j-1)
        status = "OK" if (c1, c4, c7, ct) == (e1, e4, e7, et) else "MISMATCH"
        if status != "OK":
            all_ok = False
        print(f"  j={j:2d}: fam1={c1:5d}/{e1:<5d} fam4={c4:5d}/{e4:<5d} "
              f"fam7={c7}/{e7} tower={ct:5d}/{et:<5d}  {status}")
    print(f"  EXACT FAMILY LAWS: {'ALL CONFIRMED through j=13' if all_ok else 'CHECK'}")

    # ---------------- F4: tower subtree self-similarity ----------------
    print("\nF4. TOWER SUBTREE: is dust j ∩ 3Z == 3 * tau(j-1)?")
    taus = tau_iterative(12)
    ok4 = True
    for j in range(2, 13):
        tower_part = sorted(r for r in levels[j] if r % 3 == 0)
        scaled = sorted(3 * c for c in taus[j - 1])
        match = tower_part == scaled
        if not match:
            ok4 = False
            print(f"  j={j}: tower part {tower_part[:8]}... vs 3*tau {scaled[:8]}...  MISMATCH")
    print(f"  SELF-SIMILARITY dust j ∩ 3Z = 3·tau(j-1): {'CONFIRMED j=2..12' if ok4 else 'see above'}")
    # and is tau itself equal to dust? (the deep question: does the tower
    # core tree coincide with the exponent tree?)
    same = all(sorted(taus[j]) == sorted(levels[j]) for j in range(0, 12))
    print(f"  tau == dust (tower tree IS the exponent tree): {same}")
    if not same:
        for j in range(2, 12):
            if sorted(taus[j]) != sorted(levels[j]):
                print(f"    first difference at j={j}: tau={sorted(taus[j])[:12]} dust={sorted(levels[j])[:12]}")
                break

    # ---------------- F1: shadow dust (FIXED) ----------------
    print("\nF1. SHADOW DUST (FIXED: cores mod 3^(k+1), windows sheets 1..k-1, diag 3..k):")
    for k in range(4, 13):
        M = 3 ** (k + 1)
        W = unit_word(k + 1)
        res = {1: [], 4: [], 7: []}
        for c in range(3 ** (k + 1)):
            if c % 3 == 0:
                continue
            fam = c % 9
            if fam not in res:
                continue
            chain = cut_chain(c, k + 1)
            ok = True
            for i in range(1, k):
                if tri(chain[i], i + 1) == 2:
                    ok = False
                    break
            if not ok:
                continue
            D = (W * c) % M
            for i in range(3, k + 1):
                if tri(D, i) == 2:
                    ok = False
                    break
            if ok:
                res[fam].append(c)
        p4 = pi_point(-7, k + 1)
        p7 = pi_point(-1, k + 1)
        p1 = pi_point(5, k + 1)
        print(f"  level {k:2d}: fam4={len(res[4]):2d} {res[4][:4]} (pi4={p4}, in: {p4 in res[4]})"
              f" fam7={len(res[7]):2d} {res[7][:4]} (pi7={p7}, in: {p7 in res[7]})"
              f" fam1={len(res[1]):2d} {res[1][:4]} (pi1={p1}, in: {p1 in res[1]})")

    # ---------------- F5: pi receipts ----------------
    print("\nF5. PI-POINT TRITS (60 levels):")
    K = 60
    for name, T in (("pi4", -7), ("pi7", -1), ("pi1", 5)):
        pi = pi_point(T, K)
        pt = trits(pi, K)
        twos = [i for i, x in enumerate(pt) if x == 2]
        ones = [i for i, x in enumerate(pt) if x == 1]
        print(f"  {name}: trits = {''.join(map(str, pt))}")
        print(f"        #2s={len(twos)} first-2-positions={twos[:10]} #1s={len(ones)} #0s={60-len(twos)-len(ones)}")

    print("\nPASS 2 COMPLETE — the engine never stops; it never lies.")

if __name__ == "__main__":
    main()
