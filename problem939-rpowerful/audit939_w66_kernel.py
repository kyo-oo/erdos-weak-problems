#!/usr/bin/env python3
# audit939_w66_kernel.py — W66-P939-D Task 3: INDEPENDENT verification of every
# numeric claim embedded in Erdos939.lean / Erdos939R4.lean (Kernel 60 / 60b).
# Pure python + sympy only. Receipt file: audit939_w66_kernel_output.txt.
from math import gcd
from sympy import factorint, isprime

OUT = []
def P(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s); print(s, flush=True)

# ---------- the KERNEL-faithful rpow mirror (Lean def transcribed literally) ----------
# rpow r n = decide (1 <= n and divAll r n n) where divAll checks, for every
# e in [1, n]: e | n -> (e not prime or e^r | n).
def lean_prime(n):
    return 2 <= n and all(n % e != 0 for e in range(2, n))  # trial division

def rpow(r, n):
    # exact mirror of the Lean fold for the audit (slow but literal); used on small n
    if n < 1:
        return False
    for e in range(1, n + 1):
        if n % e == 0 and lean_prime(e) and n % (e ** r) != 0:
            return False
    return True

# math definition (independent): every prime divisor p has p^r | n
def rpow_math(r, n):
    if n < 1:
        return False
    return all(e >= r for e in factorint(n).values())

# ---------- 1. edge cases of the rpow def ----------
P("== EDGE CASES of rpow (Lean-literal fold vs math def) ==")
for (r, n) in [(4, 0), (4, 1), (4, 2), (4, 15), (4, 16), (4, 32), (4, 81),
               (2, 1), (2, 8), (3, 1), (3, 8), (3, 16), (4, 10000), (4, 2592), (4, 3888)]:
    P(f"  rpow {r} {n}: Lean-literal={rpow(r, n)}  math={rpow_math(r, n)}  AGREE={rpow(r, n) == rpow_math(r, n)}")
P("  NOTE: kernel rpow 4 1 = true (1 is 4-powerful, vacuous); hunt engines gen4")
P("       EXCLUDE 1 from their lists — audit of that mismatch handled in the box scan.")

# ---------- 2. the census rows (membership AND completeness, brute force) ----------
P("== CENSUS ROWS (membership + completeness, brute force) ==")
C2 = [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100]
C3 = [1, 8, 16, 27, 32, 64, 81, 125, 128, 216, 243, 256, 343, 432, 512, 625, 648, 729, 864, 1000]
C4 = [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592,
      3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000]
for r, N, L in ((2, 100, C2), (3, 1000, C3), (4, 10000, C4)):
    brute = [n for n in range(1, N + 1) if rpow_math(r, n)]
    P(f"  r={r} N={N}: kernel row has {len(L)} values; brute force finds {len(brute)}; "
      f"MEMBERSHIP+COMPLETENESS={'PASS' if brute == L else 'FAIL ' + str(set(brute) ^ set(L))}")
P(f"  r=4 census row length = {len(C4)} (brief says 25) -> {len(C4) == 25}")

# ---------- 3. the two witness identities + their coprimality structure ----------
P("== WITNESS IDENTITIES (r=3, Nitaj lane) ==")
w1a, w1b, w1c = 271 ** 3, 2 ** 3 * 3 ** 5 * 73 ** 3, 919 ** 3
P(f"  19902511 + 756249048 = 776151559 : {w1a + w1b == w1c == 776151559}")
P(f"    271^3 = {w1a}; 2^3*3^5*73^3 = {w1b}; 919^3 = {w1c}")
P(f"    3-powerful all three: {rpow_math(3, w1a)}, {rpow_math(3, w1b)}, {rpow_math(3, w1c)}")
P(f"    pairwise gcds: gcd(a,b)={gcd(w1a, w1b)}, gcd(a,c)={gcd(w1a, w1c)}, "
  f"gcd(b,c)={gcd(w1b, w1c)} -> PAIRWISE COPRIME: "
  f"{gcd(w1a, w1b) == 1 and gcd(w1a, w1c) == 1 and gcd(w1b, w1c) == 1}")
P("    -> AUDIT VERDICT on the brief's 'the known 19902511-type witnesses share gcd 11':")
P("       FALSE as stated — these two witnesses are pairwise COPRIME (they are r=3")
P("       witnesses, the Nitaj class). No gcd-11 structure exists in them.")
w2a, w2b, w2c = 3 ** 4 * 29 ** 3 * 89 ** 3, 7 ** 3 * 11 ** 3 * 167 ** 3, 2 ** 7 * 5 ** 4 * 353 ** 3
P(f"  1392672604221 + 2126285555779 = 3518958160000 : {w2a + w2b == w2c == 3518958160000}")
P(f"    3^4*29^3*89^3 = {w2a}; 7^3*11^3*167^3 = {w2b}; 2^7*5^4*353^3 = {w2c}")
P(f"    3-powerful all three: {rpow_math(3, w2a)}, {rpow_math(3, w2b)}, {rpow_math(3, w2c)}")
P(f"    pairwise gcds: {gcd(w2a, w2b)}, {gcd(w2a, w2c)}, {gcd(w2b, w2c)} -> "
  f"PAIRWISE COPRIME: {gcd(w2a, w2b) == 1 and gcd(w2a, w2c) == 1 and gcd(w2b, w2c) == 1}")

# ---------- 4. the bracket ----------
P("== THE BRACKET (kernel rows: 999706081460641 < 1000000000000000 < 1000417426149376) ==")
lo, mid, hi = 999706081460641, 1000000000000000, 1000417426149376
P(f"  lo < mid < hi : {lo < mid < hi}")
P(f"  5623^4 = {5623 ** 4} == lo : {5623 ** 4 == lo}")
P(f"  5624^4 = {5624 ** 4} == hi : {5624 ** 4 == hi}")
P(f"  mid = 10^15 : {mid == 10 ** 15}")
P("  -> VERDICT: the bracket is the 10^15 fourth-power bracket (5623^4 < 1e15 < 5624^4),")
P("     the hunt939b scale receipt. The W66 brief calls it 'the 1e13 bracket' — MISLABELED")
P("     in the brief; the kernel numbers themselves are TRUE.")

# ---------- 5. no_small_solution_r4 (List.range 16) ----------
P("== no_small_solution_r4 (pairs a, b < 16) ==")
small = [n for n in range(16) if rpow_math(4, n)]
bad = [(a, b) for a in range(16) for b in range(16)
       if rpow_math(4, a) and rpow_math(4, b) and rpow_math(4, a + b)]
P(f"  4-powerful < 16: {small}; violating pairs: {bad} -> THEOREM HOLDS: {not bad}")

# ---------- 6. mod16_obstruction sanity + the 81+243 kill ----------
P("== mod16_obstruction sanity ==")
P(f"  81 + 243 = {81 + 243} = 324; 324 % 16 = {324 % 16}; 324 factorization = {factorint(324)}")
P(f"  324 is 4-powerful: {rpow_math(4, 324)} (must be False — 2^2 exponent)")
# machine-check the obstruction on every odd pair <= 10^4 with 4-powerful sum
odd4 = [n for n in C4 if n % 2 == 1]
viol = [(x, y) for x in odd4 for y in odd4 if rpow_math(4, x + y) and (x + y) % 16 != 0]
P(f"  exhaustive odd-pair check <= 10^4 (sums that are 4-powerful): "
  f"{[(x, y, x + y) for x in odd4 for y in odd4 if rpow_math(4, x + y)]}")
P(f"  obstruction violations: {viol} (must be empty)")

# ---------- 7. kills_r4 / kills_r2_r3 numeric rows ----------
P("== kills_r4 / kills_r2_r3 rows ==")
P("  kills_r4:", 3 ** 4 * 5 ** 4 > 10 ** 4, 3 ** 4 * 7 ** 4 > 10 ** 4, 5 ** 4 * 7 ** 4 > 10 ** 4,
  2 ** 7 * 3 ** 4 > 10 ** 4, 2 ** 4 * 3 ** 6 > 10 ** 4, 2 ** 5 * 5 ** 4 > 10 ** 4,
  2 ** 4 * 7 ** 4 > 10 ** 4, 2 ** 4 * 3 ** 4 * 5 ** 4 > 10 ** 4,
  11 ** 2 > 100, 11 ** 3 > 1000, 11 ** 4 > 10 ** 4)
P("  kills_r2_r3:", 3 ** 2 * 5 ** 2 > 100, 3 ** 2 * 7 ** 2 > 100, 5 ** 2 * 7 ** 2 > 100,
  2 ** 4 * 3 ** 2 > 100, 2 ** 2 * 3 ** 3 > 100, 2 ** 3 * 5 ** 2 > 100, 2 ** 2 * 7 ** 2 > 100,
  3 ** 3 * 5 ** 3 > 1000, 3 ** 3 * 7 ** 3 > 1000, 5 ** 3 * 7 ** 3 > 1000,
  2 ** 6 * 3 ** 3 > 1000, 2 ** 3 * 3 ** 5 > 1000, 2 ** 4 * 5 ** 3 > 1000,
  2 ** 3 * 7 ** 3 > 1000)

# ---------- 8. beyond_flt_32 + prime roster ----------
P("== beyond_flt_32 + primes ==")
P(f"  rpow 4 32 = {rpow_math(4, 32)}; no m^4 = 32 for m < 4: {all(m ** 4 != 32 for m in range(4))}")
P("  primes:", [(p, isprime(p)) for p in (2, 3, 5, 7, 11, 29, 73, 89, 167, 271, 353, 919)])

# ---------- 9. odd_pairs_no_r4_sum + ODD9/E16 rows ----------
P("== odd_pairs_no_r4_sum (ODD9 pairs never land in the r4 census) ==")
ODD9 = [1, 81, 243, 625, 729, 2187, 2401, 3125, 6561]
bad_odd = [(a, b) for a in ODD9 for b in ODD9 if (a + b) in C4]
P(f"  violating pairs: {bad_odd} (must be empty)")

with open("audit939_w66_kernel_output.txt", "w") as f:
    f.write("\n".join(OUT) + "\n")
print("AUDIT939_W66_KERNEL_DONE", len(OUT), "lines")
