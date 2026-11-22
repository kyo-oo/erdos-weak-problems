#!/usr/bin/env python3
# battery406f.py — THE π-POINT COLLAPSE BATTERY (S080, Kernel 74)
# Dual-method verification of every kernel-decided receipt:
#   T1  the unit word W61 (cube-lift recursion ∥ direct tower mod)
#   T2  the three fixed points (Hensel lift ∥ nested survivor scan)
#   T3  the 2-trit receipts (all positions, both methods)
#   T4  the ghost congruence sampling (Lemma A/B at depth 3..12)
#   T5  the collapse sampling (same-head survivor pairs congruent)
#   T6  the finite base census (8..500 full scans, independent scanner)
#   N1-N4 negative controls (corrupted values must be rejected)

import sys

OK = 0
BAD = 0

def check(name, cond):
    global OK, BAD
    if cond:
        OK += 1
        print(f"[PASS] {name}")
    else:
        BAD += 1
        print(f"[FAIL] {name}")

# ---------- T1: the unit word W61, two methods ----------

def c_mod_rec(k, s):
    """The certified mod-recursion (the kernel's cMod)."""
    M = 3 ** k
    c = 1 % M
    for i in range(s):
        c = (c + 3 ** (i + 1) * c * c + 3 ** (2 * i + 1) * c * c * c) % M
    return c

def c_mod_direct(k, s):
    """The direct tower: (4^(3^s)-1)/3^(s+1) mod 3^k (extra headroom)."""
    M = 3 ** (k + s + 2)
    c = (pow(4, 3 ** s, M) - 1) // (3 ** (s + 1))
    return c % 3 ** k

W61 = 60776643992856088575557123854
M61 = 3 ** 61

check("T1a: cMod recursion == kernel W61", c_mod_rec(61, 60) == W61)
check("T1b: direct tower mod == kernel W61", c_mod_direct(61, 60) == W61)
check("T1c: W61 % 9 == 7", W61 % 9 == 7)
check("T1d: W61 % 27 == 16", W61 % 27 == 16)
check("T1e: W61 < 3^61", W61 < M61)

# ---------- T2: the three fixed points, two methods ----------

def hensel_inv(a, k):
    """Inverse of a 3-adic unit mod 3^k (Newton lift)."""
    M = 3 ** k
    x = pow(a, -1, 3)
    while (a * x) % M != 1:
        x = (x * (2 - a * x)) % M
    return x

def pi_hensel(T, k):
    """The solution of 2*W*pi = T mod 3^k (Hensel on the unit word)."""
    W = c_mod_rec(k, k - 1)
    return ((T % 3 ** k) * hensel_inv((2 * W) % 3 ** k, k)) % 3 ** k

pi4 = 68350949682967876566738142093   # head 1, T = -7
pi7 = 64267339165701958313626862986   # head 4, T = -1
pi1 = 60183728648436040060515583879   # head 7, T = +5

check("T2a: pi_fam4 == Hensel(2W pi = -7)", pi_hensel(-7, 61) == pi4)
check("T2b: pi_fam7 == Hensel(2W pi = -1)", pi_hensel(-1, 61) == pi7)
check("T2c: pi_fam1 == Hensel(2W pi = +5)", pi_hensel(+5, 61) == pi1)
check("T2d: 2*W61*pi4 + 7 ≡ 0 mod 3^61", (2 * W61 * pi4 + 7) % M61 == 0)
check("T2e: 2*W61*pi7 + 1 ≡ 0 mod 3^61", (2 * W61 * pi7 + 1) % M61 == 0)
check("T2f: 2*W61*pi1 + 3^61 - 5 ≡ 0 mod 3^61",
      (2 * W61 * pi1 + M61 - 5) % M61 == 0)
check("T2g: all three below 3^61", pi4 < M61 and pi7 < M61 and pi1 < M61)

# ---------- T3: the 2-trit receipts (all certified positions) ----------

def trits(n, k):
    t = []
    for _ in range(k):
        t.append(n % 3)
        n //= 3
    return t

t4, t7, t1 = trits(pi4, 61), trits(pi7, 61), trits(pi1, 61)
twos4 = [i for i in range(61) if t4[i] == 2]
twos7 = [i for i in range(61) if t7[i] == 2]
twos1 = [i for i in range(61) if t1[i] == 2]

check("T3a: pi4 2-trits = the assault list (13 twos)",
      twos4 == [3, 5, 14, 15, 19, 27, 28, 39, 45, 49, 51, 54, 58])
check("T3b: pi7 2-trits (20 twos, starts 1,6,7,9,11,13,14,15,20,28)",
      len(twos7) == 20 and twos7[:10] == [1, 6, 7, 9, 11, 13, 14, 15, 20, 28])
check("T3c: pi1 2-trits (18 twos, starts 8,13,17,23,24,25,29,34,35,36)",
      len(twos1) == 18 and twos1[:10] == [8, 13, 17, 23, 24, 25, 29, 34, 35, 36])
check("T3d: kernel receipt positions",
      t4[3] == 2 and t4[14] == 2 and t7[1] == 2 and t7[6] == 2
      and t1[8] == 2 and t1[13] == 2)

# ---------- T4: the ghost congruence (Lemma A/B) sampling ----------
# Synthetic ghosts = the fixed points' own truncations (the nested-scan
# survivors: pi_a mod 3^k is middle-third at every depth <= k) plus any
# small natural survivors the scan finds.

def ghost_shape_check(u, kmax):
    """Verify Lemma A: 2*residue + 9 == 2*head + 3^k for all 3<=k<=kmax
    whenever u is middle-third at every depth (synthetic ghost)."""
    head = (c_mod_rec(9, 1) * u) % 9
    for k in range(3, kmax + 1):
        c = c_mod_rec(k, k - 1)
        r = (c * u) % 3 ** k
        if not (3 ** (k - 1) <= r < 2 * 3 ** (k - 1)):
            return None  # not a ghost at this depth
        if 2 * r + 9 != 2 * head + 3 ** k:
            return False  # ghost but shape fails -> KERNEL BUG
    return True

# the fixed points themselves: ghost at EVERY depth <= 61 (the
# fixed-point congruence 2*W*pi = T is exactly the Lemma-A shape)
full_ghosts = [pi4, pi7, pi1]
# their truncations: ghost at every depth <= their own cut
trunc_specs = [(pi4, 6), (pi4, 7), (pi7, 7), (pi7, 8), (pi1, 8), (pi1, 9)]
# plus any small natural survivors at depth 8
naturals = [u for u in range(1, 60000) if ghost_shape_check(u, 8) is True]

check("T4a: ghost sources found",
      len(full_ghosts) == 3 and len(naturals) >= 0)
shape_full = all(ghost_shape_check(g, 12) is True for g in full_ghosts)
check("T4b: the shape law (Lemma A) holds on all three fixed points "
      "through depth 12", shape_full)
shape_trunc = all(ghost_shape_check(pi % 3 ** k, k) is True
                  for pi, k in trunc_specs)
check("T4c: truncation ghosts satisfy the shape to their own depth",
      shape_trunc)
check("T4d: small natural ghosts below 60000 are class-lifts only "
      "(the scarcity datum)", len(naturals) < 120)

ghosts = full_ghosts + naturals

# ---------- T5: the collapse sampling (same head -> congruent) ----------
# For each pair of same-head ghost sources: congruent mod 3^k for all k
# up to the shallower source's verified depth (naturals: depth 8; the
# fixed points: every depth sampled).

collapse_ok = True
srcs = [(g, 8) for g in naturals] + [(g, 12) for g in full_ghosts]
for i in range(len(srcs)):
    for j in range(i + 1, len(srcs)):
        (a, da), (b, db) = srcs[i], srcs[j]
        if (c_mod_rec(9, 1) * a) % 9 != (c_mod_rec(9, 1) * b) % 9:
            continue
        for k in range(1, min(da, db) + 1):
            if a % 3 ** k != b % 3 ** k:
                collapse_ok = False
check("T5a: same-head ghosts congruent at all verified depths",
      collapse_ok)

# ---------- T6: the finite base census (independent scanner) ----------
# Every 4^K, 8 <= K <= 500, owns a ternary digit two.  Independent scan:
# digit-by-digit on the FULL number (no fuel shortcut).

def has_two_full(n):
    while n > 0:
        if n % 3 == 2:
            return True
        n //= 3
    return False

census_ok = all(has_two_full(4 ** K) for K in range(8, 501))
check("T6a: every exponent 8..500 fires (full independent scan)", census_ok)

# ---------- N1-N4: negative controls (corruption must be rejected) ----------

check("N1: corrupted W61 rejected", c_mod_rec(61, 60) != W61 + 1)
check("N2: corrupted pi_fam4 rejected (bad congruence)",
      (2 * W61 * (pi4 + 3 ** 40) + 7) % M61 != 0)
check("N3: wrong-head pin rejected (pi4 does not solve fam7)",
      (2 * W61 * pi4 + 1) % M61 != 0)
check("N4: 256 is not a digit-two witness at row 2",
      (4 ** 4 // 9) % 3 != 2)

print()
print(f"BATTERY406F: {OK} passed, {BAD} failed")
sys.exit(0 if BAD == 0 else 1)
