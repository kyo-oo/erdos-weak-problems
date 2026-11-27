#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""battery406i.py — THE S093 DIAGONAL-TRAJECTORY BATTERY (dual-method, ALL GREEN).

The computational certificates behind the S093 round module
MonolithGate/MahlerDiagonal406.lean:

  T1  THE CUT-WORD UNIFICATION: for every K in [0, 500], CantorianPower K
      (4^K owns no ternary digit two at any position >= 1) is EQUIVALENT
      to the cut word C(K) = (4^K - 1) / 3^(v3(K)+1) being digit-two-free.
      Dual method: exact big-integer ternary digit scan vs the modular
      cut-word read.  Cantorian K < 300 == {0, 1, 4} exactly.

  T2  THE CLASS-64 KILL (the corrected frontier): every K = 64 mod 81
      fires its ternary digit two at position 4 (the green cascade level
      two law) — the stale cell of the sharp frontier's row accounting.
      Dual method: modular digit read at position 4 vs exact conversion.

  T3  THE CORRECTED ROW RESIDUAL: the 3-free survivor tree through row 9
      has exactly 256 classes mod 19683 whose mod-81 projection is
      EXACTLY {1, 4, 10, 13, 28, 31, 37, 40} — stable from row 4 on
      (the projection does not change at any deeper level through 9);
      after the CommonTwo covered classes the row frontier is the FOUR
      cells {1, 10, 28, 37}.  Consistency: survivors mod 59049 = 768
      (3x256, the period law), through row 10 = 512 (exact doubling).

  T4  THE TRAJECTORY LAW: v3(c(s+1) - c(s)) = s+1 EXACTLY for s in 1..29
      with the unit part e(s) = (c(s+1)-c(s))/3^(s+1) = 1 mod 3; the
      frozen diagonal digits c(s) -> L with L = 7 mod 9, 16 mod 27,
      16 mod 81, 178 mod 243.  Dual method: modular tower arithmetic vs
      exact big-integer computation for s <= 8.

  T5  THE WITNESS DICHOTOMY: for every 3-free u <= 400 and head
      a in {1,2,4,5,7,8}, the valuation t_s = v3(2u*c(s) - 2a + 9)
      never rides the exact diagonal (t_s >= s+1) beyond depth 6, and
      every tail is eventually constant — the fracture case of the
      dichotomy, at every tested pair.

  T6  THE FAMILY NON-MEMBERSHIP: for every 3-free u <= 3000 and
      m in {+-1, +-5, +-7}, the congruence 2u*c(k-1) = m (mod 3^k)
      breaks by depth 8 (max lock depth over the whole family) — the
      numerical shadow of the Mahler sharpness input, now read through
      the diagonal-chain equivalence.

NO-OOM compliant: everything modular (no tower big-ints beyond s = 8).
"""
import sys

def v3(n):
    v = 0
    while n and n % 3 == 0:
        v += 1
        n //= 3
    return v

KMAX = 45

def c_mod(s, k):
    """c(s) = (4^(3^s)-1)/3^(s+1) mod 3^k, exact for k <= KMAX."""
    m = 3 ** (s + 1 + k)
    N = (pow(4, 3 ** s, m) - 1) % m
    return (N // 3 ** (s + 1)) % (3 ** k)

def c_exact(s):
    assert s <= 8
    return (4 ** (3 ** s) - 1) // 3 ** (s + 1)

def digits3(n):
    ds = []
    while n:
        ds.append(n % 3)
        n //= 3
    return ds

def digit_pow(K, p):
    """Position p of 4^K, modular (position p needs 4^K mod 3^(p+2))."""
    m = 3 ** (p + 2)
    return (pow(4, K, m) // 3 ** p) % 3

PASS, FAIL = [], []

def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("PASS" if ok else "FAIL"), name, detail)

# ============ T0: c_mod dual-method agreement ============
ok = True
for s in range(0, 9):
    for k in (5, 12, 20):
        if c_mod(s, k) != c_exact(s) % 3 ** k:
            ok = False
check("T0 c_mod dual-method agreement (s<=8, exact big-int vs modular)", ok)

# ============ T1: CUT-WORD UNIFICATION ============
def cutword(K):
    return (4 ** K - 1) // 3 ** (v3(K) + 1)

ok = True
for K in range(0, 501):
    cw_clean = all(d in (0, 1) for d in digits3(cutword(K)))
    pow_clean = all(d != 2 for d in digits3(4 ** K)[1:])
    if cw_clean != pow_clean:
        ok = False
        print("  MISMATCH K =", K)
check("T1 cut-word unification: CantorianPower K <=> cut word clean, K in [0,500]", ok)
cant = [K for K in range(300) if all(d != 2 for d in digits3(4 ** K)[1:])]
check("T1b Cantorian K < 300 == {0,1,4}", cant == [0, 1, 4], f"got {cant}")

# ============ T2: CLASS-64 KILL ============
ok = True
for K in range(0, 4000):
    if K % 81 == 64 and digit_pow(K, 4) != 2:
        ok = False
        print("  MISS K =", K)
check("T2 class 64 mod 81 fires position 4 (K in [0,4000), modular vs K<200 exact)",
      ok and all((4 ** K // 81) % 3 == 2 for K in range(64, 200, 81)))

# ============ T3: CORRECTED ROW RESIDUAL ============
M = 3 ** 9
surv = [K for K in range(M)
        if K % 3 != 0 and all(digit_pow(K, p) != 2 for p in range(1, 10))]
check("T3 row-9 survivor count mod 19683 == 256", len(surv) == 256,
      f"got {len(surv)}")
proj = sorted(set(K % 81 for K in surv))
check("T3b mod-81 projection == {1,4,10,13,28,31,37,40}",
      proj == [1, 4, 10, 13, 28, 31, 37, 40], f"got {proj}")
# stability from row 4
stable = True
for r in range(4, 10):
    Mr = 3 ** r
    sr = [K for K in range(Mr)
          if K % 3 != 0 and all(digit_pow(K, p) != 2 for p in range(1, r + 1))]
    if sorted(set(K % 81 for K in sr)) != proj:
        stable = False
check("T3c projection stable from row 4 through row 9", stable)
# consistency: mod 59049 = 768 (3x), row 10 = 512
M2 = 3 ** 10
s10 = [K for K in range(M2)
       if K % 3 != 0 and all(digit_pow(K, p) != 2 for p in range(1, 10))]
s10b = [K for K in range(M2)
        if K % 3 != 0 and all(digit_pow(K, p) != 2 for p in range(1, 11))]
check("T3d survivors mod 59049 == 768 (3x256 period law)", len(s10) == 768,
      f"got {len(s10)}")
check("T3e survivors through row 10 == 512 (exact doubling)", len(s10b) == 512,
      f"got {len(s10b)}")
# the honest frontier accounting: the true 3-free uncovered classes (32),
# the green cascade's cut (10 killed -> 22 remain), and the survivor target (8)
def decomp(K):
    k = K; a = 0
    while k % 3 == 0: k //= 3; a += 1
    return a, k
def covered(K):
    if K % 9 in (5, 6): return True
    if K % 27 in (14, 18, 19, 25): return True
    return K % 81 in (8, 20, 41, 42, 51, 52, 53, 54, 55, 56, 57, 58, 66, 76)
def omega(K):
    a, core = decomp(K)
    return a >= 1 and (core % 3 == 2 or core % 9 in (1, 5, 6))
def window(K):
    a, core = decomp(K)
    return (a >= 2 and core % 27 in (13, 25)) or (a >= 3 and core % 81 in (4, 34, 49, 70))
true_frontier = sorted(set(K % 81 for K in range(501, 20000)
                           if K % 3 != 0 and not covered(K) and not omega(K) and not window(K)))
check("T3f TRUE 3-free frontier == 32 classes mod 81 (the docstring's five missed 27)",
      len(true_frontier) == 32, f"got {len(true_frontier)}")
cascade_killed = [r for r in true_frontier
                  if r % 9 == 7 or r % 27 in (19, 22, 25)
                  or r % 81 in (55, 58, 64, 67, 73, 76)]
check("T3g the green cascade kills exactly 10 of the 32 (22 remain; class 64 dead at row 4)",
      len(cascade_killed) == 10 and 64 in cascade_killed,
      f"killed {len(cascade_killed)}: {cascade_killed}")
remain = [r for r in true_frontier if r not in cascade_killed]
in_proj = [r for r in remain if r in proj]
out_proj = [r for r in remain if r not in proj]
die_by_9 = all(any(digit_pow(K, p) == 2 for p in range(1, 10))
               for K in range(501, 20000) if K % 81 in out_proj)
check("T3h of the 22 cascade-cut classes exactly 8 lie in the survivor projection; the other 14 all die by row 9 (the deeper cascade domain)",
      len(in_proj) == 8 and die_by_9,
      f"in={in_proj} out(die by row 9)={out_proj}")

# ============ T4: TRAJECTORY LAW ============
ok = True
det = []
for s in range(1, 30):
    k = s + 12
    diff = (c_mod(s + 1, k) - c_mod(s, k)) % 3 ** k
    if v3(diff) != s + 1:
        ok = False
        det.append(f"s={s}:v3={v3(diff)}")
    if (diff // 3 ** (s + 1)) % 3 != 1:
        ok = False
        det.append(f"s={s}:e%3={(diff // 3 ** (s + 1)) % 3}")
check("T4 v3(c(s+1)-c(s)) = s+1 exact, e(s)%3=1 (s=1..29)", ok,
      ";".join(det[:4]))
c30 = c_mod(30, 6)
check("T4b frozen diagonal L mod 9 == 7", c30 % 9 == 7)
check("T4c L mod 27 == 16", c30 % 27 == 16)
check("T4d L mod 81 == 16", c30 % 81 == 16)
check("T4e L mod 243 == 178", c30 % 243 == 178, f"got {c30 % 243}")

# ============ T5: WITNESS DICHOTOMY ============
maxdiag = 0
holder = None
bad = []
for u in range(1, 401):
    if u % 3 == 0:
        continue
    for a in (1, 2, 4, 5, 7, 8):
        ts = []
        for s in range(1, 31):
            D = (2 * u * c_mod(s, 40) - 2 * a + 9) % 3 ** 40
            ts.append(v3(D) if D != 0 else 99)
        run = 0
        for idx in range(len(ts)):
            if ts[idx] >= idx + 2:
                run = idx + 1
        if run > maxdiag:
            maxdiag, holder = run, (a, u)
        if len(set(ts[11:])) > 1:
            bad.append((a, u, ts[11:15]))
check("T5 max diagonal run <= 6 over u <= 400 (no pair rides the diagonal)",
      maxdiag <= 6, f"maxdiag={maxdiag} at (a,u)={holder}")
check("T5b every witness tail eventually constant (s>=12)", not bad,
      f"{len(bad)} non-constant")

# ============ T6: FAMILY NON-MEMBERSHIP ============
maxk = 0
hold = None
for u in range(1, 3001):
    if u % 3 == 0:
        continue
    for m in (1, -1, 5, -5, 7, -7):
        k = 2
        while k < 28:
            if (2 * u * c_mod(k - 1, k + 2) - m) % 3 ** k == 0:
                k += 1
            else:
                break
        if k - 1 > maxk:
            maxk, hold = k - 1, (u, m)
check("T6 family lock depth <= 8 for u <= 3000 (MahlerSharp's shadow)",
      maxk <= 8, f"maxk={maxk} at (u,m)={hold}")

print()
print(f"BATTERY406I VERDICT: {len(PASS)} PASS / {len(FAIL)} FAIL")
for n in FAIL:
    print("FAILED:", n)
if not FAIL:
    print("BATTERY406I_GREEN=1")
sys.exit(1 if FAIL else 0)
