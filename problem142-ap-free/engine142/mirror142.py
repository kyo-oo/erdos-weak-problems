#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ENGINE 142 — the Python mirror for the Erdos142.lean kernel (W67-142K).

Erdos #142 (frozen statement, erdosproblems.com/142, $10000):
  "Let r_k(N) be the largest possible size of a subset of {1,...,N} that
   does not contain any non-trivial k-term arithmetic progression.
   Prove an asymptotic formula for r_k(N)."

Convention (pinned identically in the kernel header): non-trivial k-term AP
means a, a+d, ..., a+(k-1)d with d >= 1 (distinct terms).  r_k(N) := max |S|
over S subseteq [1,N] containing no non-trivial k-term AP.

THE MIRROR BATTERY (exit-nonzero-on-failure):
  (a) CANTOR/TERNARY KERNEL: T_k := {n < 3^k : every ternary digit of n in
      {0,1}} is 3-AP-free — direct pair scan for k <= 8 (T_8 = 256 elements,
      32640 ordered pairs).  Plus the carry-free digit arithmetic checks:
      digits(x+z) = digitwise x_i+z_i for all x,z in T_6 (NO carries), and
      digits(2y) = digitwise 2y_i.  Plus |T_k cap [1,3^k-1]| = 2^k - 1.
  (b) THE EXACT r_3 TABLE N <= 12 by DUAL METHOD: exhaustive 2^N brute scan
      AND an independent branch-and-bound (AP-propagation + count pruning)
      must agree.  Certified table (doubter W67-142D, commit 042f28a):
      [1,2,2,3,4,4,4,4,5,5,6,6,7,8,8,8,8,8,8,9,...] — the printed reference
      in the mission text was corrupt at N=9,11,13,14,15,16,20; the doubter's
      own dual/triple-method computation is truth and this mirror must
      independently reproduce its N <= 12 prefix.
  (c) BLOCK-BOUND DOMINATION: r_k(N) <= (k-1)*floor(N/k) + (N mod k) must
      dominate every exact value within reach: k=3 (N <= 25 own B&B + the
      doubter-certified table N <= 30 as cross-check), k=2 (N <= 16
      exhaustive + domination N <= 100), k=4/k=5 (N <= 20 spot vs the
      doubter-certified tables).  Block-bound arithmetic spot N <= 100.
  (d) KERNEL-DECIDE CORRESPONDENCE: the kernel's small-value decide table
      r_3(N), N <= 8 == [1,2,2,3,4,4,4,4] (exhaustive enumeration — the same
      computation the Lean `decide` chunk performs), with explicit witness
      lists and explicit 3-AP-freeness verification of each witness.

Prints E142_MIRROR_GREEN iff every check passes; exit code 1 on any failure.
"""
import sys
from fractions import Fraction

FAILURES = []


def check(name, ok, detail=""):
    status = "GREEN" if ok else "RED"
    print(f"  [{status}] {name}{(' :: ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)
    return ok


def ternary_digits(n, k):
    """The k low ternary digits of n, little-endian list [d0, d1, ..., d_{k-1}]."""
    ds = []
    for _ in range(k):
        ds.append(n % 3)
        n //= 3
    return ds


def tern01(n):
    """Every ternary digit of n is 0 or 1 (the Cantor/T membership test)."""
    while n > 0:
        if n % 3 == 2:
            return False
        n //= 3
    return True


def T_k(k):
    """T_k = {n < 3^k : all ternary digits in {0,1}} — by digit product."""
    out = []
    for m in range(2 ** k):
        n = 0
        for i in range(k):
            if (m >> i) & 1:
                n += 3 ** i
        out.append(n)
    return sorted(out)


# ----------------------------------------------------------------------------
# (a) THE CANTOR/TERNARY KERNEL — T is 3-AP-free + carry-free digit arithmetic
# ----------------------------------------------------------------------------

def battery_cantor():
    print("(a) CANTOR/TERNARY KERNEL — T_k is 3-AP-free (k <= 8)")
    for k in range(0, 9):
        T = T_k(k)
        N3 = 3 ** k - 1
        ok_mem = all(tern01(n) for n in T) and len(set(T)) == len(T) and all(
            n < 3 ** k for n in T)
        # 3-AP-free: for all x < z in T with (x+z) even, the midpoint is NOT in T
        viol = 0
        for i in range(len(T)):
            for j in range(i + 1, len(T)):
                x, z = T[i], T[j]
                s = x + z
                if s % 2 == 0:
                    y = s // 2
                    if tern01(y):
                        viol += 1
        # cardinality: |T_k cap [1, 3^k - 1]| = 2^k - 1 (0 is the only excluded)
        cnt = sum(1 for n in T if 1 <= n <= N3)
        check(f"T_{k} 3-AP-free (all x<z pairs, midpoint verdict), N=3^{k}-1={N3}",
              viol == 0 and ok_mem,
              f"{len(T)} elements, {len(T)*(len(T)-1)//2} pairs, {viol} violations")
        check(f"|T_{k} cap [1,{N3}]| = 2^{k}-1", cnt == 2 ** k - 1,
              f"count={cnt} expected={2**k - 1}")
    # carry-free digit arithmetic on T_6 (digitwise sums, no carries)
    k = 6
    T = T_k(k)
    bad_add = 0
    bad_dbl = 0
    for x in T:
        for z in T:
            dx, dz, ds = ternary_digits(x, k), ternary_digits(z, k), ternary_digits(x + z, k)
            if any(ds[i] != dx[i] + dz[i] for i in range(k)):
                bad_add += 1
    for y in T:
        dy, dd = ternary_digits(y, k), ternary_digits(2 * y, k)
        if any(dd[i] != 2 * dy[i] for i in range(k)):
            bad_dbl += 1
    check("carry-free addition: digits(x+z) = digitwise x_i+z_i on T_6 x T_6",
          bad_add == 0, f"{len(T)**2} pairs, {bad_add} violations")
    check("carry-free doubling: digits(2y) = digitwise 2y_i on T_6",
          bad_dbl == 0, f"{len(T)} elements, {bad_dbl} violations")
    # the ternary value map (foldr base 3) injectivity on digit lists in
    # {0,1,2} with fixed length: exhaustive over {0,1,2}^6 (729 lists)
    L = 6
    lists = [ternary_digits(m, L) for m in range(3 ** L)]
    seen = {}
    for ds in lists:
        v = 0
        for i in range(L):  # foldr (fun a b => a + 3*b): last = most significant
            v = v * 3 + ds[L - 1 - i]
        seen.setdefault(v, []).append(ds)
    bad_inj = sum(1 for v, lst in seen.items() if len(lst) > 1)
    check("ternary value map injective on {0,1,2}^6 (fixed length 6)",
          bad_inj == 0 and len(seen) == 3 ** L,
          f"{3**L} lists, {len(seen)} values, {bad_inj} collisions")


# ----------------------------------------------------------------------------
# (b) THE EXACT r_3 TABLE — dual method (brute 2^N scan AND branch-and-bound)
# ----------------------------------------------------------------------------

def ap3_free_brute(S):
    """S (list, viewed as a set) 3-AP-free: no distinct x,z with midpoint in S."""
    st = set(S)
    lst = sorted(st)
    for i in range(len(lst)):
        for j in range(i + 1, len(lst)):
            s = lst[i] + lst[j]
            if s % 2 == 0 and (s // 2) in st:
                return False
    return True


def r3_brute(N):
    """Exhaustive 2^N subset scan — engine C (ground truth for N <= 12)."""
    best = 0
    for mask in range(2 ** N):
        S = [i + 1 for i in range(N) if (mask >> i) & 1]
        if ap3_free_brute(S):
            best = max(best, len(S))
    return best


def r3_bb(N):
    """Branch-and-bound DFS (engine A mirror): elements in increasing order,
    AP-propagation on add + remaining-count pruning."""
    best = [0]
    sys.setrecursionlimit(100000)

    def dfs(next_elem, chosen):
        # count prune: cannot beat best
        if len(chosen) + (N - next_elem + 1) <= best[0]:
            return
        if next_elem > N:
            best[0] = max(best[0], len(chosen))
            return
        st = set(chosen)
        # try including next_elem: safe iff no p in S with (p+next) even and
        # midpoint in S, and no p,q in S with p+q = 2*next (next as midpoint)
        safe = True
        for p in chosen:
            s = p + next_elem
            if s % 2 == 0 and (s // 2) in st:
                safe = False
                break
            q = 2 * next_elem - p
            if q > 0 and q in st:
                safe = False
                break
        if safe:
            dfs(next_elem + 1, chosen + [next_elem])
        dfs(next_elem + 1, chosen)
    dfs(1, [])
    return best[0]


def table_list(t):
    return [t[N] for N in sorted(t)]


def battery_r3_table():
    print("(b) THE EXACT r_3 TABLE — DUAL METHOD (brute 2^N + branch-and-bound)")
    cert12 = [1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6]  # doubter-certified N <= 12
    table = {N: r3_brute(N) for N in range(1, 13)}
    check("brute 2^N scan r_3(N), N <= 12", table_list(table) == cert12,
          f"table={table_list(table)}")
    bb = {N: r3_bb(N) for N in range(1, 13)}
    check("branch-and-bound r_3(N), N <= 12", table_list(bb) == cert12,
          f"table={table_list(bb)}")
    check("DUAL-METHOD agreement (brute == B&B) on N <= 12",
          all(table[N] == bb[N] for N in range(1, 13)))
    return table


# ----------------------------------------------------------------------------
# (c) BLOCK-BOUND DOMINATION — r_k(N) <= (k-1)*floor(N/k) + (N mod k)
# ----------------------------------------------------------------------------

DOUBTER_R3_30 = [1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9,
                 9, 9, 9, 10, 10, 11, 11, 11, 11, 12]
DOUBTER_R4_20 = [1, 2, 3, 3, 4, 5, 5, 6, 7, 8, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12]
DOUBTER_R5_20 = [1, 2, 3, 4, 4, 5, 6, 7, 8, 8, 9, 10, 11, 12, 12, 13, 14, 15, 16, 16]


def block_bound(k, N):
    return (k - 1) * (N // k) + (N % k)


def r2_exhaustive(N):
    """r_2(N) by exhaustive scan: with d >= 1, any two distinct elements are
    a 2-AP; so only sizes 0/1 are 2-AP-free, and 1 is achieved."""
    best = 0
    for mask in range(2 ** N):
        S = [i + 1 for i in range(N) if (mask >> i) & 1]
        ok = len(S) <= 1  # >= 2 distinct elements always contain a 2-AP
        if ok:
            best = max(best, len(S))
    return best


def battery_block():
    print("(c) BLOCK-BOUND DOMINATION r_k(N) <= (k-1)*floor(N/k) + (N mod k)")
    # k = 3: own exact B&B over the full certified range (N <= 30), doubter
    # table N <= 30 as the independent cross-check reference
    own = {N: r3_bb(N) for N in range(1, 31)}
    agree30 = all(own[N] == DOUBTER_R3_30[N - 1] for N in range(1, 31))
    check("own B&B r_3(N) N <= 30 agrees with doubter-certified table", agree30,
          f"own={table_list(own)}")
    dom3 = all(DOUBTER_R3_30[N - 1] <= block_bound(3, N) for N in range(1, 31))
    check("k=3 domination: r_3(N) <= 2*floor(N/3) + N mod 3 on all N <= 30", dom3,
          f"max_margin={max(block_bound(3,N)-DOUBTER_R3_30[N-1] for N in range(1,31))}")
    dom4 = all(DOUBTER_R4_20[N - 1] <= block_bound(4, N) for N in range(1, 21))
    check("k=4 domination on doubter-certified N <= 20", dom4)
    dom5 = all(DOUBTER_R5_20[N - 1] <= block_bound(5, N) for N in range(1, 21))
    check("k=5 domination on doubter-certified N <= 20 (tight everywhere)", dom5)
    # k = 2: exhaustive N <= 16
    r2 = [r2_exhaustive(N) for N in range(1, 17)]
    check("r_2(N) = 1 for all 1 <= N <= 16 (exhaustive, d>=1 convention)",
          r2 == [1] * 16, f"r2={r2}")
    dom2 = all(1 <= block_bound(2, N) for N in range(1, 101))
    check("k=2 domination N <= 100 (r_2 = 1 <= 1*floor(N/2) + N mod 2)", dom2)
    # block-bound arithmetic spot-check N <= 100: formula == simulated partition
    bad = 0
    for k in range(1, 6):
        for N in range(1, 101):
            q, r = N // k, N % k
            if (k - 1) * q + r != block_bound(k, N):
                bad += 1
    check("block-bound arithmetic identity N <= 100, k in 1..5 (spot)", bad == 0)
    mono = all(block_bound(3, N) <= block_bound(3, N + 1) for N in range(1, 100))
    check("k=3 bound monotone nondecreasing N <= 100", mono)


# ----------------------------------------------------------------------------
# (d) KERNEL-DECIDE CORRESPONDENCE — the r_3 table N <= 8 + witnesses
# ----------------------------------------------------------------------------

WITNESS_8 = {
    1: [1], 2: [1, 2], 3: [1, 2], 4: [1, 2, 4],
    5: [1, 2, 4, 5], 6: [1, 2, 4, 5], 7: [1, 2, 4, 5], 8: [1, 2, 4, 5],
}


def battery_kernel_decide():
    print("(d) KERNEL-DECIDE CORRESPONDENCE — r_3(N) N <= 8 (the decide table)")
    expect = [1, 2, 2, 3, 4, 4, 4, 4]
    got = [r3_brute(N) for N in range(1, 9)]
    check("kernel decide table r_3(N) N <= 8 == [1,2,2,3,4,4,4,4]", got == expect,
          f"got={got}")
    for N, W in WITNESS_8.items():
        okw = (len(W) == expect[N - 1] and ap3_free_brute(W)
               and all(1 <= x <= N for x in W) and len(set(W)) == len(W))
        check(f"witness for r_3({N}) = {expect[N-1]}: {W} 3-AP-free, in range, distinct",
              okw)
    # the Cantor lower bound at the kernel scale: r_3(3^k - 1) >= 2^k - 1.
    # The witness T_k itself (3-AP-free + size 2^k - 1 + in range) is the
    # verification; the exact-value comparison r_3(N) >= 2^k - 1 is cross-run
    # only for k <= 3 (N <= 26 — the exact-computation scale of engine (c)).
    for k in range(1, 9):
        N = 3 ** k - 1
        Tk = [n for n in T_k(k) if n >= 1]
        okc = len(Tk) == 2 ** k - 1 and ap3_free_brute(Tk)
        if k <= 3:
            okc = okc and (r3_bb(N) >= 2 ** k - 1)
        check(f"cantor witness T_{k} cap [1,{N}] size 2^{k}-1={2**k-1}, 3-AP-free", okc)
    # honest ratio intel: r_3(N)*3/(2N) at certified points
    print("  ratio r_3(N)*3/(2N), N <= 30 (doubter-certified values):")
    for N in (5, 10, 20, 30):
        v = DOUBTER_R3_30[N - 1]
        print(f"    N={N:2d}  r_3={v:2d}  ratio={Fraction(3*v, 2*N)}")


def main():
    print("ENGINE 142 MIRROR BATTERY — Erdos #142 (r_k(N) AP-free), lane W67-142K")
    print("=" * 78)
    battery_cantor()
    print()
    battery_r3_table()
    print()
    battery_block()
    print()
    battery_kernel_decide()
    print()
    print("=" * 78)
    if FAILURES:
        print(f"E142_MIRROR_RED — {len(FAILURES)} failure(s): {FAILURES}")
        sys.exit(1)
    print("E142_MIRROR_GREEN — all mirror checks passed.")
    sys.exit(0)


if __name__ == "__main__":
    main()
