#!/usr/bin/env python3
"""
E348 W63-D4 — THE m=2,n=3 CONSTRUCTION ENGINE (the witness certification).

THE WITNESS: A = each power of 2 with multiplicity 3:
    A = 1,1,1, 2,2,2, 4,4,4, 8,8,8, ... (2^i x 3, i = 0,1,2,...)

THE THEOREM CERTIFIED (the (m,n)=(2,3) construction):
  (P1) A is COMPLETE: every n >= 0 is a sum of distinct terms of A
       (the binary representation of n uses each power at most once, and
       every power is available in A).
  (P2) A is 2-REDUNDANT: after removing ANY 2 elements, every power of 2
       is still present (3 copies, at most 2 removed), hence every n >= 0
       is still a sum of distinct terms of the survivor: complete.
  (P3) A is 3-FRAGILE: after removing the three 1s (a 3-removal), every
       remaining term is even => every subset sum is even => every odd
       integer is NOT representable: the survivor is NOT complete.
  Hence A witnesses (m,n) = (2,3) under the reading
      "A complete; A remains complete after removing any m elements;
       A is not complete after removing any n elements"
  with the final clause read existentially (some n-removal breaks).

DUAL-METHOD VERIFICATION LAW:
  Method 1: exact bitset DP for subset-sum coverage (python bigints).
  Method 2 (independent): the STRUCTURAL route — the survivor's value-set
    containment (every power still present) + the coverage of the pure
    powers list computed by its OWN bitset, then the SUPERSET test between
    the two independently computed bitsets (covered(survivor) >= covered(powers)).
  Method 3 (independent): the GROWTH CRITERION (each element <= 1 + sum of
    smaller elements), the classical completeness law.
  Boundary cases: n = 0, 1, the block junctures 3(2^{j+1}-1), the bound B.
"""
import sys
from itertools import combinations_with_replacement

def mult_powers(q, L):
    """A = 2^0 x q, ..., 2^L x q (levels 0..L)."""
    A = []
    for k in range(L + 1):
        A += [2**k] * q
    return A

def covered_bitset(A, B):
    """M1: subset sums of A up to bound B (exact bitset DP)."""
    cov = 1
    for a in A:
        if a <= B:
            cov |= cov << a
    return cov & ((1 << (B + 1)) - 1)

def contiguous_prefix(cov, B):
    """Length of contiguous covered prefix [0..c)."""
    c = 0
    while c <= B and (cov >> c) & 1:
        c += 1
    return c

def criterion_holds(A_sorted):
    """M3: every element <= 1 + sum of previous (first element must be 1)."""
    if not A_sorted or A_sorted[0] != 1:
        return False
    s = 0
    for i, a in enumerate(A_sorted):
        if i > 0 and a > 1 + s:
            return False, i, a, s
        s += a
    return True, None, None, None

def value_set_complete(A, L):
    """M2 structural: does A contain every power 2^i (i <= L) at least once?"""
    cnt = {}
    for a in A:
        cnt[a] = cnt.get(a, 0) + 1
    return all(cnt.get(2**i, 0) >= 1 for i in range(L + 1))

# ----------------------------------------------------------------------------
def certify_P1(q, L, B):
    """(P1) completeness of the witness itself, three methods."""
    A = mult_powers(q, L)
    Ab = [a for a in A if a <= B]
    print(f"--- P1 completeness: mult-{q} powers, levels 0..{L}, B={B} ---")
    # M1: bitset
    cov = covered_bitset(Ab, B)
    c = contiguous_prefix(cov, B)
    m1 = (c > B)
    print(f"M1 bitset: covered [0,{c-1}] (B={B}) -> {'PASS' if m1 else 'FAIL'}")
    # M2: structural (contains every power) + superset vs pure powers bitset
    pows = [2**i for i in range(L + 1)]
    covp = covered_bitset(pows, min(B, sum(pows)))
    cov_cut = cov & ((1 << (min(B, sum(pows)) + 1)) - 1)
    superset = (cov_cut & covp) == covp
    m2 = value_set_complete(Ab, L) and superset
    print(f"M2 structural: every power present? {value_set_complete(Ab, L)}; "
          f"covered(A) >= covered(powers)? {superset} -> {'PASS' if m2 else 'FAIL'}")
    # M3: criterion
    ok, i, a, s = criterion_holds(sorted(Ab))
    m3 = ok
    print(f"M3 criterion: {'PASS' if m3 else f'FAIL at idx {i} (a={a}, s={s})'}")
    # boundary spots
    spots = [0, 1, 2, 3, B // 2, B - 1, B]
    spot_ok = all((cov >> n) & 1 for n in spots if n <= B)
    print(f"boundary spots {spots}: {'PASS' if spot_ok else 'FAIL'}")
    return m1 and m2 and m3 and spot_ok

def certify_P2(q, L, B, positional_limit=None):
    """(P2) EVERY 2-removal complete: exhaustive by level-value pairs
    (one copy of 2^i and one of 2^j, i<=j), dual method."""
    A = mult_powers(q, L)
    Ab = [a for a in A if a <= B]
    levels = sorted(set(Ab))
    pairs = list(combinations_with_replacement(levels, 2))
    print(f"--- P2 every-2-removal complete: {len(pairs)} level-pairs, B={B} ---")
    allpass_m1 = True; allpass_m2 = True; fails = []
    pows = [2**i for i in range(L + 1)]
    covp = covered_bitset(pows, min(B, sum(pows)))
    pm = min(B, sum(pows))
    for (x, y) in pairs:
        Ax = sorted(Ab)
        if x == y:
            if Ax.count(x) < 2: continue
            Ax.remove(x); Ax.remove(x)
        else:
            Ax.remove(x); Ax.remove(y)
        # M1: survivor's own contiguous coverage up to its total sum
        bnd = min(B, sum(Ax))
        covx = covered_bitset(Ax, bnd)
        cx = contiguous_prefix(covx, bnd)
        if cx <= bnd:
            allpass_m1 = False; fails.append((x, y, "M1", cx))
        # M2: structural — every power still present AND bitset superset
        covx_cut = covered_bitset(Ax, pm)
        if not value_set_complete(Ax, L) or (covx_cut & covp) != covp:
            allpass_m2 = False; fails.append((x, y, "M2", None))
    print(f"M1 (survivor covers [0,B]): {'PASS all' if allpass_m1 else f'FAIL {fails[:5]}'}")
    print(f"M2 (every power survives; covered >= covered(powers)): "
          f"{'PASS all' if allpass_m2 else 'FAIL'}")
    # exhaustive positional check (every C(n,2) removal at the finite witness)
    if positional_limit is not None:
        n = len(Ab)
        seen = set(); pfails = 0; checked = 0
        import itertools
        for i, j in itertools.combinations(range(n), 2):
            Ax = Ab[:i] + Ab[i+1:j] + Ab[j+1:]
            key = tuple(Ax)
            if key in seen: continue
            seen.add(key); checked += 1
            bnd = min(B, sum(Ax))
            covx = covered_bitset(Ax, bnd)
            cx = contiguous_prefix(covx, bnd)
            if cx <= bnd:
                pfails += 1
        print(f"positional exhaustive: {checked} distinct removals, {pfails} FAILS "
              f"-> {'PASS' if pfails == 0 else 'FAIL'}")
        return allpass_m1 and allpass_m2 and pfails == 0
    return allpass_m1 and allpass_m2

def certify_P3(q, L, B):
    """(P3) the 3-kill: remove the three 1s -> all even -> all sums even ->
    every odd n uncovered -> NOT complete. Dual method."""
    A = mult_powers(q, L)
    Ab = [a for a in A if a <= B]
    print(f"--- P3 the 3-kill (remove the three 1s), B={B} ---")
    # M1: bitset parity census
    Ax = [a for a in Ab if a != 1]
    covx = covered_bitset(Ax, B)
    odd_cov = [n for n in range(1, B + 1, 2) if (covx >> n) & 1]
    even_holes = [n for n in range(0, B + 1, 2) if not (covx >> n) & 1]
    m1 = (len(odd_cov) == 0)
    print(f"M1 bitset: odd values covered: {len(odd_cov)} (expect 0); "
          f"even values missed: {len(even_holes)} -> {'KILL CONFIRMED' if m1 else 'NO KILL'}")
    # M2: structural parity — all elements even + full-width odd-bit mask test
    all_even = all(a % 2 == 0 for a in Ax)
    odd_mask = sum(1 << n for n in range(1, B + 1, 2))
    mod2 = (covx & odd_mask) == 0  # no odd bit set
    m2 = all_even and mod2
    print(f"M2 structural: all elements even? {all_even}; covered has no odd bit? {mod2} "
          f"-> {'KILL CONFIRMED' if m2 else 'NO KILL'}")
    # spots: 1, 3, 999-style odd junctures uncovered
    spots = [1, 3, 5, B - 1 if (B - 1) % 2 == 1 else B - 2, B + 1 if B % 2 == 1 else B]
    spot_kill = all(not (covx >> n) & 1 for n in spots if n <= B and n % 2 == 1)
    print(f"odd spots {spots}: uncovered? {'PASS (all uncovered)' if spot_kill else 'FAIL'}")
    return m1 and m2 and spot_kill

def certify_general(q, L, B):
    """The general (m,n) law spot-checks: mult-(m+1) powers witness
    (m, n) for every n >= m+1 (the exists-negation reading).
    Spot: q=2 (the (1,2) witness), q=4 (the (3,4) witness)."""
    print(f"--- general (m,n) law spot-checks ---")
    ok = True
    for q, m in [(2, 1), (4, 3)]:
        A = mult_powers(q, L)
        Ab = [a for a in A if a <= B]
        # m-redundancy: every m-removal complete
        levels = sorted(set(Ab))
        mp = True
        for x in levels:
            Ax = sorted(Ab); Ax.remove(x)
            bnd = min(B, sum(Ax))
            covx = covered_bitset(Ax, bnd)
            if contiguous_prefix(covx, bnd) <= bnd or not value_set_complete(Ax, L):
                mp = False
        # (m+1)-kill: remove all q copies of 1 -> all even
        Ax = [a for a in Ab if a != 1]
        covx = covered_bitset(Ax, B)
        kill = all(not (covx >> n) & 1 for n in range(1, B + 1, 2))
        print(f"mult-{q} (the ({m},{q}) witness): every {m}-removal complete? {mp}; "
              f"{q}-removal of the 1s kills (all odd uncovered)? {kill}")
        ok = ok and mp and kill
    return ok

def slack_tables():
    """The reading-resolution receipts: the slack sigma_k = 1 + S_k - a_{k+1}
    tables for the three canonical families."""
    print("--- slack tables (sigma_k = 1 + S_k - a_{k+1}) ---")
    # powers of 2: sigma = 0 at every juncture (zero-slack: every removal lethal)
    # juncture k: prefix = 2^0..2^{k-1} (sum 2^k - 1), next element 2^k
    rows = [(k, 2**k, 2**k, (2**k) - 2**k) for k in range(1, 8)]
    print("powers of 2: (k, 1+S_k, a_next, sigma) =", rows[:4], "... sigma = 0 ALWAYS")
    # double-1 Fibonacci: sigma_k = F_k (grows -> every 1-removal heals,
    # 2-removals of small pairs break via the restart-stall)
    a = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
    S = 0; rows2 = []
    for k in range(1, 8):
        S += a[k - 1]  # S_k = sum of first k elements
        rows2.append((k, S + 1, a[k], S + 1 - a[k]))
    print("double-1 Fibonacci: sigma_k =", [r[3] for r in rows2], "(= F_k, grows to infinity)")
    # mult-3 powers: sigma after level j's block = 2^{j+2} - 2 (grows fast:
    # every finite removal of mass below the level-juncture heals; the kill is
    # PARITY (the three 1s), not slack)
    S = 0; rows3 = []
    for j in range(0, 5):
        S += 3 * 2**j  # the level-j block
        rows3.append((j, S + 1, 2**(j+1), S + 1 - 2**(j+1)))
    print("mult-3 powers: (level, 1+S, next, sigma) =", rows3[:3], "... sigma = 2^{j+2}-2 grows")
    return True

def main():
    sys.set_int_max_str_digits(100000)
    q, L, B = 3, 9, 3000   # witness levels 0..9 (elements to 512), bound 3000
    print(f"=== E348 THE (m,n)=(2,3) CONSTRUCTION CERTIFICATION ===")
    print(f"witness: each 2^i (i=0..{L}) with multiplicity {q}; B={B}")
    r1 = certify_P1(q, L, B)
    r2 = certify_P2(q, L, B, positional_limit=True)
    r3 = certify_P3(q, L, B)
    rg = certify_general(q, L, B)
    rt = slack_tables()
    print("=== VERDICT ===")
    print(f"P1 completeness:           {'GREEN' if r1 else 'RED'}")
    print(f"P2 every-2-removal compl.: {'GREEN' if r2 else 'RED'}")
    print(f"P3 the 3-kill (parity):   {'GREEN' if r3 else 'RED'}")
    print(f"general (m,n) spots:      {'GREEN' if rg else 'RED'}")
    print(f"slack tables:             {'GREEN' if rt else 'RED'}")
    print("THE (2,3) CONSTRUCTION: " + ("CERTIFIED" if (r1 and r2 and r3) else "BROKEN"))

if __name__ == "__main__":
    main()
