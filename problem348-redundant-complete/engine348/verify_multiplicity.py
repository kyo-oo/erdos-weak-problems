#!/usr/bin/env python3
"""
E348 W63-D4 — the multiplicity witness battery.
Candidate: A = each power of 2 with multiplicity q.
Claims to test (finite, exhaustive where possible):
  C1: A is complete (covered set contiguous [0, S_k] at every level k).
  C2: every 2-removal (remove 2 terms) leaves a sequence whose covered set is
      contiguous [0, ...] at every level -> complete.
  C3: the 3-removal of the three 1s leaves all-even -> NOT complete (parity kill).
Dual method: (i) direct subset-sum bitset computation up to a bound;
             (ii) the criterion check (element <= 1 + sum of all smaller elements),
                  proven equivalent to contiguity-from-0 for sorted positive multisets
                  with first element 1.
"""
import sys
from itertools import combinations_with_replacement

def mult_powers(q, L):
    """A = 2^0 x q, 2^1 x q, ..., 2^L x q  (levels 0..L)."""
    A = []
    for k in range(L + 1):
        A += [2**k] * q
    return A

def covered_bitset(A, B):
    """Subset sums of multiset A up to bound B (bitset DP; distinct positions)."""
    cov = 1  # bitset, bit n set if n covered
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
    """Every element <= 1 + sum of previous elements (first must be 1 handled separately)."""
    s = 0
    ok_first = (A_sorted[0] == 1)
    for i, a in enumerate(A_sorted):
        if i > 0 and a > 1 + s:
            return False, i, a, s
        s += a
    return ok_first, None, None, None

def main():
    q = 3
    L = 12
    B = 4000  # coverage bound: elements > B irrelevant for coverage up to B
    A = mult_powers(q, L)
    # restrict to elements <= B for bitset checks
    Ab = [a for a in A if a <= B]
    print(f"Multiplicity-{q} powers, levels 0..{L}; {len(Ab)} elements <= B={B}")

    # C1: A complete?
    ok, i, a, s = criterion_holds(sorted(Ab))
    print(f"C1 criterion(A): first=1? {ok}, violation at index {i}")
    cov = covered_bitset(Ab, B)
    c = contiguous_prefix(cov, B)
    print(f"C1 contiguity: covered [0, {c-1}] (B={B}) -> {'PASS' if c > B else 'FAIL'}")

    # C2: every 2-removal (by level pair, multiplicity-aware)
    levels = sorted(set(Ab))
    pairs = list(combinations_with_replacement(levels, 2))
    allpass = True
    worst = None
    for (x, y) in pairs:
        # remove one copy of x and one copy of y (x<=y; if x==y need 2 copies)
        Ax = sorted(Ab)
        if x == y:
            if Ab.count(x) < 2:
                continue
            Ax.remove(x); Ax.remove(x)
        else:
            Ax.remove(x); Ax.remove(y)
        ok, i, a, s = criterion_holds(Ax)
        covx = covered_bitset(Ax, B)
        cx = contiguous_prefix(covx, B)
        if not ok or cx <= B:
            allpass = False
            worst = (x, y, ok, i, a, s, cx)
            print(f"C2 FAIL pair ({x},{y}): criterion_ok={ok} viol(i={i},a={a},s={s}) prefix={cx}")
    print(f"C2 every-2-removal complete up to B: {'PASS' if allpass else 'FAIL'} ({len(pairs)} level-pairs checked)")
    if allpass:
        # margin report: minimal prefix over all pairs
        mins = []
        for (x, y) in pairs:
            Ax = sorted(Ab)
            if x == y:
                if Ab.count(x) < 2: continue
                Ax.remove(x); Ax.remove(x)
            else:
                Ax.remove(x); Ax.remove(y)
            covx = covered_bitset(Ax, B)
            mins.append((contiguous_prefix(covx, B), x, y))
        mins.sort()
        print("C2 worst three (prefix,x,y):", mins[:3])

    # C2-exhaustive: by POSITIONS (not levels) — all C(n,2) removals, dedup via sorted multiset identity
    # For q=3, L=12 bounded: 3*(L+1) = 39 elements <= 4096... B=4000 caps at level 11 (2048).
    import itertools
    n = len(Ab)
    seen = set()
    fails = 0
    checked = 0
    for i, j in itertools.combinations(range(n), 2):
        Ax = Ab[:i] + Ab[i+1:j] + Ab[j+1:]
        key = tuple(sorted(Ax))
        if key in seen:
            continue
        seen.add(key)
        checked += 1
        ok, ii, a, s = criterion_holds(Ax)
        covx = covered_bitset(Ax, B)
        cx = contiguous_prefix(covx, B)
        if not ok or cx <= B:
            fails += 1
            if fails < 10:
                print(f"C2pos FAIL remove ({Ab[i]},{Ab[j]}): ok={ok} prefix={cx}")
    print(f"C2-exhaustive by position: {checked} distinct removals, {fails} FAILS")

    # C3: kill witness — remove the three 1s -> all even
    Ax = [a for a in Ab if a != 1]
    covx = covered_bitset(Ax, B)
    odd_missing = [n for n in range(1, B + 1, 2) if not (covx >> n) & 1]
    print(f"C3 kill {{1,1,1}}: {len(odd_missing)} odd holes up to B (expect ~B/2): {'KILL CONFIRMED' if len(odd_missing) > B//4 else 'NO KILL'}")

if __name__ == "__main__":
    sys.set_int_max_str_digits(100000)
    main()
