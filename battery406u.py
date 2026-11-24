#!/usr/bin/env python3
# THE CARRY MACHINE VALIDATION — the quiet-2 dynamics of the x4 chart.
# Machine: state c_p = directCarry4 (4^K) p = (4*(4^K mod 3^p))/3^p  in {0,1,2,3}
# Reading digit t_p = digit3 (4^K) p:
#   c_{p+1} = (c_p + 4*t_p) // 3
#   digit of 4^(K+1) at row p: (t_p + c_p) % 3
# FIRE beyond K's trit length (trit_p = 0): treeBad K p  <=>  t_{p+1} = 2 and c_{p+1} in {0,3}
# COUNTEREXAMPLE dodge: never (t_q = 2 and c_q in {0,3}) for q >= L+1.
import sys

POW3 = [1]
for _ in range(200):
    POW3.append(POW3[-1]*3)

def digit_of_pow4(m, q):
    M = POW3[q+1]
    return pow(4, m, M) // POW3[q]

def treeBad(K, p):
    P = POW3[p]
    m = K % P
    d1 = digit_of_pow4(m, p+1)
    d2 = digit_of_pow4(m+1, p+1)
    trit = (K // P) % 3
    return (d1 == d2) and (trit == 2 - d1)

# --- validate the machine against treeBad for p beyond K's trit length ---
def trit_len(K):
    l = 0
    while POW3[l] <= K: l += 1
    return l  # number of trits

def carry_seq(K, maxq):
    # c_p for p = 0..maxq, via the recursion, with t_p = digit of 4^K at row p
    c = 0
    seq = []
    for p in range(0, maxq+1):
        t = digit_of_pow4(K, p)  # digit of 4^K at row p (K itself as exponent — m = K)
        seq.append((p, t, c))
        c = (c + 4*t) // 3
    return seq

print("=== CARRY MACHINE vs treeBad (deep levels, trit = 0) ===")
bad = 0
for K in [1501, 26849, 1502, 9999, 27181, 12345]:
    L = trit_len(K)
    seq = carry_seq(K, 70)
    for p in range(max(2, L), 66):
        t_next = seq[p+1][1] if p+1 < len(seq) else digit_of_pow4(K, p+1)
        # recompute properly
        t_next = digit_of_pow4(K, p+1)
        c_next = None
        # c_{p+1} from the recursion
        c = 0
        for q in range(0, p+2):
            t = digit_of_pow4(K, q)
            if q == p+1: c_next = c  # c at row p+1 before consuming t_{p+1}? careful
            c = (c + 4*t) // 3
        # c_{p+1} is the carry AT row p+1, i.e., after consuming digits 0..p
        c_at = None
        c = 0
        for q in range(0, p+2):
            t = digit_of_pow4(K, q)
            c = (c + 4*t) // 3
        c_at = c  # carry after consuming t_0..t_{p+1}? No — after consuming t_0..t_p it's c_p... recompute below
        # clean recompute: c_p = (4 * (4^K mod 3^p)) // 3^p
        c_clean = (4 * (pow(4, K, POW3[p+2]))) // POW3[p+1]  # directCarry4 (4^K) (p+1)
        pred_fire = (t_next == 2) and (c_clean in (0, 3))
        actual = treeBad(K, p)
        if pred_fire != actual:
            bad += 1
            if bad < 8:
                print(f"  MISMATCH K={K} p={p}: machine says {pred_fire}, treeBad says {actual}")
print("mismatches (should be 0 for p >= trit_len):", bad)

print()
print("=== THE DEEPEST DODGERS: carry/digit structure at the fire row ===")
# For the K's with the LARGEST fire rows, show what the dodge looks like
def fire_row(K, maxp=140):
    for p in range(2, maxp):
        if treeBad(K, p):
            return p
    return None

for K in [26849, 27181, 24310, 21952, 16510]:
    r = fire_row(K)
    L = trit_len(K)
    # at the fire row r: t_{r+1} = 2, c_{r+1} in {0,3}
    t = digit_of_pow4(K, r+1)
    c = (4 * pow(4, K, POW3[r+3])) // POW3[r+2]
    print(f"K={K} (trit_len {L}): fires at row {r}; t_(r+1)={t}, c_(r+1)={c}")

print()
print("=== THE SURVIVOR-PATH DENSITY PARADOX: natural survivors above 30000? ===")
# check [30000, 60000) quickly
cnt = 0
mx = 0; amx = 0
import collections
dist = collections.Counter()
for K in range(30000, 60000):
    r = fire_row(K, 140)
    if r is None:
        cnt += 1
        print("  NO FIRE:", K)
    else:
        dist[r] += 1
        if r > mx: mx = r; amx = K
print("K in [30000,60000): no-fire:", cnt, "| max row:", mx, "at", amx)
tail = {r: dist[r] for r in sorted(dist) if r >= 50}
print("rows >= 50:", tail)
