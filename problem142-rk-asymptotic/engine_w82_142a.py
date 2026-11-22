#!/usr/bin/env python3
# engine_w82_142a.py — W82-142A numerical validation receipts.
# Pure python3. Brute-force r_k(N) tables (independent re-derivation, no z3)
# + validation of every target statement + every witness stone.
import itertools, json, sys

def k_ap_free(S, k):
    S = sorted(S)
    n = len(S)
    # a k-AP: k equally spaced elements. Check via first-two-terms pair scan:
    for i in range(n):
        for j in range(i+1, n):
            d = S[j] - S[i]
            if d == 0: continue
            if all((S[i] + t*d) in S for t in range(k)):
                return False
    return True

def r_brute(k, N):
    # exact max |A| over A ⊆ [1,N] k-AP-free (exhaustive for small N)
    best = 0
    for mask in range(1 << N):
        A = [i+1 for i in range(N) if (mask >> i) & 1]
        if len(A) > best and k_ap_free(A, k):
            best = len(A)
    return best

WIT = {
 (3,61,19): [1, 6, 7, 9, 14, 18, 20, 23, 24, 36, 38, 43, 44, 46, 51, 55, 57, 60, 61],
 (3,48,16): [1, 4, 6, 10, 12, 13, 15, 21, 31, 33, 34, 39, 40, 42, 43, 48],
 (4,42,22): [1, 2, 3, 5, 6, 8, 9, 10, 16, 18, 19, 21, 22, 24, 30, 31, 33, 34, 35, 38, 39, 40],
 (5,55,36): [1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 51, 52, 53, 54],
 (6,43,31): [1, 2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 23, 24, 25, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41],
 (7,45,36): [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 30, 31, 33, 34, 37, 39, 40, 41, 42, 43, 45],
}

def main():
    ok = True
    print("=== PART 1: witness stones (source: tables_rk_v3.json certified cells + UPPER_STACK k=7) ===")
    for (k, N, m), w in sorted(WIT.items()):
        c1 = (len(w) == m)
        c2 = all(1 <= x <= N for x in w)
        c3 = k_ap_free(w, k)
        c4 = len(set(w)) == len(w)
        print(f"  r_{k}({N}) >= {m}: |w|={len(w)} in[1,{N}]={c2} {k}-AP-free={c3} distinct={c4} -> {'GREEN' if (c1 and c2 and c3 and c4) else 'RED'}")
        ok &= (c1 and c2 and c3 and c4)
    print("=== PART 2: brute-force r_k(N) tables (N <= 11, exhaustive 2^N) ===")
    tab = {}
    for k in range(2, 6):
        row = [r_brute(k, N) for N in range(0, 12)]
        tab[k] = row
        print(f"  r_{k}(N), N=0..11: {row}")
    print("=== PART 3: LAW M-1 (r_k(N) <= r_(k+1)(N)) on the brute-force tables ===")
    for k in range(2, 5):
        viol = [N for N in range(12) if tab[k][N] > tab[k+1][N]]
        print(f"  k={k}: violations = {viol if viol else 'NONE'} (GREEN)")
        ok &= not viol
    print("  k=1 counterexample check: r_1(N)=N (trivial: every set is 1-AP-free),")
    print("    r_2(N)=min(N,1): r_1(2)=2 > 1=r_2(2) -> the unrestricted M-1 is FALSE at k=1 (documented).")
    print("=== PART 4: LAW U-GEN-0 (r_k(N) <= N - N//k) on the tables ===")
    for k in range(2, 6):
        viol = [N for N in range(12) if tab[k][N] > N - N//k]
        print(f"  k={k}: violations = {viol if viol else 'NONE'} (GREEN)")
        ok &= not viol
    print("=== PART 5: certified-table cross-check (W77-142E values, N<=38, r_3) ===")
    banked3 = [1,2,2,3,4,4,4,4,5,5,6,6,7,8,8,8,8,8,8,9,9,9,9,10,10,11,11,11,11,12,12,13,13,13,13,14,14,14]
    mine = [r_brute(3, N) for N in range(1, 12)]
    agree = all(banked3[N-1] == mine[N-1] for N in range(1, 12))
    print(f"  r_3 N=1..11 brute {mine} vs banked prefix {banked3[:11]}: {'AGREE' if agree else 'DISAGREE'}")
    ok &= agree
    print("=== PART 6: the brief's literal '61 <= r 3 19' is FALSE over the official defs ===")
    print(f"  r_3(19) = {banked3[18]} (banked dual-certified; also r_3(N) <= N = 19 for any N),")
    print("  so 61 <= r_3(19) is IMPOSSIBLE. The true banked stone is the transpose 19 <= r_3(61)")
    print("  (UPPER_STACK.md:116 'k = 3: L = 61, r = 19'; NEW_LAWS_142.md:458 'Best stones: 61@19').")
    print("=== PART 7: U-GEN-0 block mechanism (the disjoint k-blocks, not the d-progressions) ===")
    # verify: [1,N] partitioned into q=N//k blocks [jk+1, jk+k] (j<q) + tail; each block is a k-AP
    for (k, N) in [(3,19),(4,42),(5,55),(6,43),(7,45),(3,61)]:
        q = N//k
        blocks = [list(range(j*k+1, (j+1)*k+1)) for j in range(q)]
        tail = list(range(q*k+1, N+1))
        disjoint = sum(len(b) for b in blocks) + len(tail) == N
        blocks_are_aps = all(len(b) == k for b in blocks)
        bound = q*(k-1) + len(tail)
        print(f"  k={k},N={N}: q={q}, blocks+tail partition OK={disjoint}, full blocks={blocks_are_aps}, q(k-1)+(N mod k)={bound}=N-q={N-q}: {'GREEN' if disjoint and blocks_are_aps and bound == N-q else 'RED'}")
        ok &= disjoint and blocks_are_aps and bound == N-q
    print()
    print("W82_142A_ENGINE_GREEN" if ok else "W82_142A_ENGINE_RED")
    sys.exit(0 if ok else 1)

main()
