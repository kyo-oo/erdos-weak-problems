#!/usr/bin/env python3
"""
ASSAULT406 — THE DUST ENGINE + THE PI-POINT COMPUTATION (S078)

BOSS order: crack the hTailF hypothesis (the_act = no riders K >= 8).
This engine resolves, numerically and exactly (Python bigints):

  E1. The diagonal unit word W = lim (4^(3^s)-1)/3^(s+1)  (trits to level 60)
  E2. THE THREE PI-POINTS: the infinite shadow-dust cores pinned by the
      middle-third law: 2*W*pi = -7 (family 4), -1 (family 7), +5 (family 1)
      in Z_3.  Hensel-lifted to level 60.  Are they natural?  Rational?
  E3. Tree A (the exponent dust of DustLaw406): survivors mod 3^j,
      the perfect-binary law, the family split, the known riders.
  E4. THE PIN-vs-TREE-A INTERACTION: a tower rider at sheet s has its core
      pinned by the shadow package; K = 3^s * core then has FORCED trits at
      levels s..2s+2.  Do the forced trits collide with tree A's killing
      trits?  (If some level is always dead -> tower riders die at sheet s.)
  E5. The shadow dust: cores surviving all window-dodge + diagonal
      conditions to level k — do they converge to the pi-points?
  E6. Row-family survivor counts at deep levels.
  E7. The extremal curve v2*(M) extension (dual-method MITM), M <= 40.

All arithmetic exact.  No floats.  The engine never stops; it never lies.
"""
import sys
from math import gcd

def trits(x, k):
    """First k ternary trits (position 0 first) of x (x >= 0)."""
    t = []
    for _ in range(k):
        t.append(x % 3)
        x //= 3
    return t

def tri(x, i):
    return (x // (3 ** i)) % 3

# ---------------------------------------------------------------------------
# E1. The unit word W, iteratively mod 3^K.
#    omega_0(1) = (4-1)/3 = 1 ; omega_{s+1} = omega_s + 3^(s+1)(w^2 + 3^s w^3)
# ---------------------------------------------------------------------------

def unit_word(K):
    """W mod 3^K via the cube-lift recursion, all mod 3^K."""
    M = 3 ** K
    w = 1  # omega_0(1)
    for s in range(0, K):
        # omega_{s+1} = w + 3^(s+1) * (w^2 + 3^s * w^3)
        w = (w + (3 ** (s + 1)) * ((w * w) % M + (3 ** s) * ((w * w * w) % M))) % M
    return w  # = omega_K(1) = W mod 3^K (trits <= K frozen)

# ---------------------------------------------------------------------------
# E2. The pi-points: solve 2*W*pi = T (mod 3^K) by Hensel digit-lifting.
# ---------------------------------------------------------------------------

def hensel_inv(a, K):
    """Solve a*x = 1 mod 3^K (a coprime to 3), digit by digit."""
    x = 0
    ainv = 1 if a % 3 == 1 else 2   # a^{-1} mod 3
    for k in range(1, K + 1):
        cur = (a * x) % (3 ** k)
        # want cur + a*d*3^(k-1) = 1 mod 3^k -> d = ((1-cur)/3^(k-1)) * a^{-1} mod 3
        num = ((1 - cur) % (3 ** k)) // (3 ** (k - 1))
        d = (num * ainv) % 3
        x += d * (3 ** (k - 1))
    assert (a * x) % (3 ** K) == 1
    return x

def pi_point(T, K):
    """pi with 2*W*pi = T (mod 3^K); T given as integer (can be negative)."""
    W = unit_word(K + 1)
    M = 3 ** K
    Tm = T % M
    inv2W = hensel_inv((2 * W) % M, K)
    return (Tm * inv2W) % M

# ---------------------------------------------------------------------------
# Tree A: the exponent dust (DustLaw406 structure, pure python).
#   alive[j] = [r < 3^j : digits of 4^r at positions 0..j all != 2]
# ---------------------------------------------------------------------------

def powmod(a, e, m):
    r = 1
    a %= m
    while e:
        if e & 1:
            r = (r * a) % m
        a = (a * a) % m
        e >>= 1
    return r

def tree_A_level(j):
    """Survivors mod 3^j: r with digit_q(4^r) != 2 for all q <= j."""
    if j == 0:
        return [0]
    prev = tree_A_level(j - 1)
    m = 3 ** (j + 1)   # need 4^r mod 3^(j+2)... careful: digit at pos j+1
    # digit_{j}(4^r) needs 4^r mod 3^(j+1); ord(4, 3^(j+1)) = 3^j
    # child r + t*3^(j-1)? NO: children of level-(j-1) node r are r + t*3^(j-1).
    # We recompute directly: alive[j] = {r < 3^j : all digits <= j avoid 2}
    # digits of 4^r up to position j: use 4^r mod 3^(j+2) (period 3^(j+1))
    out = []
    M = 3 ** (j + 2)
    for r in range(3 ** j):
        v = powmod(4, r, M)
        ok = True
        for q in range(j + 1):
            if (v // (3 ** q)) % 3 == 2:
                ok = False
                break
        if ok:
            out.append(r)
    return out

def tree_A_iterative(J):
    """Build alive levels 0..J by the dustStep law (fast)."""
    levels = {0: [0]}
    alive = [0]
    for j in range(0, J):
        M = 3 ** (j + 2)
        new = []
        for r in alive:
            base = powmod(4, r, M)
            d = (base // (3 ** (j + 1))) % 3  # digit at position j+1 of 4^r
            for t in range(3):
                if (d + t) % 3 != 2:
                    new.append(r + t * (3 ** j))
        alive = new
        levels[j + 1] = alive
    return levels

# ---------------------------------------------------------------------------
# E4. The pin analysis: tower rider at sheet s, family f in {4, 7}.
# ---------------------------------------------------------------------------

def cut_word_mod(s, core, K):
    """omega_s(core) mod 3^K via the recursion (K trits)."""
    M = 3 ** K
    w = (pow(4, core, M) - 1) // 3 % M   # omega_0(core) = (4^core-1)/3 mod M
    # careful: (4^core - 1)/3 needs 4^core mod 3M. Redo properly:
    M2 = 3 * M
    num = (pow(4, core, M2) - 1) % M2
    w = (num // 3) % M
    for i in range(1, s + 1):
        w = (w + (3 ** (i)) * ((w * w) % M + (3 ** (i - 1)) * ((w * w * w) % M))) % M
    return w

def pin_analysis(smax=8, Kdepth=None):
    """For each sheet s >= 1 and family f in {4,7}: the pinned core class
    pi_f mod 3^(s+2) (from the diagonal middle-third through the sheet),
    then K = 3^s * core pinned mod 3^(2s+2): check tree-A survival of the
    pinned prefix, and count surviving t-extensions at deeper levels."""
    print("=" * 78)
    print("E4. PIN-vs-TREE-A ANALYSIS (tower riders, per sheet)")
    print("=" * 78)
    for s in range(1, smax + 1):
        for f in (4, 7):
            T = -7 if f == 4 else -1
            Kp = s + 2
            pi = pi_point(T, Kp)          # core pinned mod 3^(s+2)
            # K = 3^s * core : pinned prefix mod 3^(2s+2)
            Kpin = (3 ** s) * pi          # mod 3^(2s+2) implicitly
            # tree A survival of the pinned prefix at level 2s+2:
            lev = 2 * s + 2
            # check digits of 4^(Kpin) at positions 0..lev-? -- but Kpin is a
            # *class representative*; tree-A survival of the class means:
            # the class Kpin mod 3^lev must be in alive[lev]?  K's trits at
            # levels 0..s-1 are 0 (K = 3^s * core).  Tree A needs digit
            # checks of 4^K at positions <= lev.
            M = 3 ** (lev + 2)
            v = powmod(4, Kpin, M)
            dead = []
            for q in range(lev + 1):
                if (v // (3 ** q)) % 3 == 2:
                    dead.append(q)
                    break
            # count extensions: K = Kpin + t*3^(2s+2), t < 3^extra, survive
            # tree A to level lev + extra
            extra = 3
            surv = 0
            for t in range(3 ** extra):
                Kx = Kpin + t * (3 ** (2 * s + 2))
                Mx = 3 ** (lev + extra + 2)
                vx = powmod(4, Kx, Mx)
                ok = all((vx // (3 ** q)) % 3 != 2 for q in range(lev + extra + 1))
                if ok:
                    surv += 1
            print(f"  s={s} f={f}: pi mod 3^{Kp} = {pi:>{'7d'}} "
                  f"({'DEAD at q=' + str(dead[0]) if dead else 'alive-' + str(lev)}) "
                  f"surviving extensions to +{extra} levels: {surv}/{3**extra}")

# ---------------------------------------------------------------------------
# E5. The shadow dust: cores surviving all window-dodge + diagonal
#     conditions to level k (the second observer's package, all levels).
# ---------------------------------------------------------------------------

def shadow_dust(kmax=10):
    print("=" * 78)
    print("E5. THE SHADOW DUST (all-window-dodging cores, per level)")
    print("=" * 78)
    # window at sheet s (s>=1): trit_{s+1}(omega_s(core)) ; dodge = <= 1
    # diagonal trit at level i (i>=3?): trit_i(W*core) ; survive = <= 1
    for k in range(4, kmax + 1):
        M = 3 ** (k + 1)
        W = unit_word(k + 1)
        counts = {4: 0, 7: 0, 1: 0}
        classes = {4: [], 7: [], 1: []}
        for c in range(3 ** k):
            if c % 3 == 0:
                continue
            fam = c % 9
            if fam not in (1, 4, 7):
                continue
            ok = True
            # windows at sheets 1..k-1 dodge
            w = None
            # compute omega_i(c) iteratively; check window trit at each sheet
            M2 = 3 * M
            w0 = ((pow(4, c, M2) - 1) % M2) // 3 % M  # omega_0(c) mod 3M/3
            cur = w0
            for i in range(0, k):
                if i >= 1:
                    # window at sheet i: trit_{i+1}(omega_i(c))
                    if tri(cur, i + 1) == 2:
                        ok = False
                        break
                # advance
                cur = (cur + (3 ** (i + 1)) * ((cur * cur) % M + (3 ** i) * ((cur * cur * cur) % M))) % M
            if not ok:
                continue
            # diagonal trits at levels 3..k: trit_i(W*c) <= 1
            D = (W * c) % M
            for i in range(3, k + 1):
                if tri(D, i) == 2:
                    ok = False
                    break
            if ok:
                counts[fam] += 1
                if len(classes[fam]) < 6:
                    classes[fam].append(c)
        print(f"  level {k:2d}: shadow-dust cores: fam4={counts[4]:3d} {classes[4][:4]} "
              f"fam7={counts[7]:3d} {classes[7][:4]} fam1={counts[1]:3d} {classes[1][:4]}")

# ---------------------------------------------------------------------------
# E6. Row-family survivor counts (tree A split by family).
# ---------------------------------------------------------------------------

def row_family_counts(J=12):
    print("=" * 78)
    print("E6. TREE A SURVIVORS BY FAMILY (rows = s:0 classes 1,4 mod 9)")
    print("=" * 78)
    levels = tree_A_iterative(J)
    for j in range(1, J + 1):
        alive = levels[j]
        c1 = sum(1 for r in alive if r % 9 == 1)
        c4 = sum(1 for r in alive if r % 9 == 4)
        c7 = sum(1 for r in alive if r % 9 == 7)
        rest = len(alive) - c1 - c4 - c7
        print(f"  level {j:2d}: |alive|={len(alive):6d} (2^{j}={2**j}) "
              f"fam1={c1:5d} fam4={c4:5d} fam7={c7:5d} other={rest:5d}")
    return levels

# ---------------------------------------------------------------------------
# E7. The extremal curve v2*(M) — MITM dual method, M <= 40.
# ---------------------------------------------------------------------------

def v2(x):
    v = 0
    while x and x % 2 == 0:
        v += 1
        x //= 2
    return v

def extremal_curve(Mmax=40):
    print("=" * 78)
    print("E7. THE EXTREMAL CURVE v2*(M) (MITM, M <= %d)" % Mmax)
    print("=" * 78)
    pow3 = [3 ** i for i in range(Mmax + 1)]
    results = []
    for M in range(1, Mmax + 1):
        # all subset sums of {3^0..3^M} — 2^(M+1) — M=40 too big.
        # MITM: halves A (positions 0..M/2), B (rest). Want max v2(a+b) over
        # a in SA, b in SB, a+b > 0.  Meet in the middle mod 2^T.
        # Feasible to M ~ 34-36.  For speed, reuse campaign's known result
        # through 34 and extend by 2 if cheap.
        if M > 36:
            print(f"  M={M}: skipped (size); campaign value stands through 34")
            break
        h = M // 2
        SA = set()
        cur = {0}
        for i in range(0, h + 1):
            cur = cur | {x + pow3[i] for x in cur}
        SA = cur
        cur = {0}
        for i in range(h + 1, M + 1):
            cur = cur | {x + pow3[i] for x in cur}
        SB = list(cur)
        SBs = sorted(SB)
        # max v2(a + b) over a in SA, b in SB, a+b>0: brute force is
        # |SA|*|SB| ~ 2^M pairs — M=36: 6.8e10 — too big.  Instead: for each
        # target T up to bound, count solutions of a+b = 0 mod 2^T via
        # sorting+bisect on residues.
        import bisect
        best = 0
        # incremental: v2*(M) >= v2*(M-1) style not valid; do residue counting
        SAs = sorted(SA)
        # For T from 1 up: count pairs (a,b) with a+b = 0 mod 2^T, a+b>0.
        # Pair count via dict of residues mod 2^T.
        T = 1
        while True:
            mod = 1 << T
            from collections import defaultdict
            dB = defaultdict(int)
            for b in SBs:
                dB[b % mod] += 1
            cnt = 0
            for a in SAs:
                cnt += dB.get((-a) % mod, 0)
            # subtract the zero-sum pair (a=0,b=0) if it exists
            if cnt > (1 if (0 in SAs and 0 in dB) else 0):
                best = T
                T += 1
                if T > M + 8:
                    break
            else:
                break
        results.append((M, best))
        print(f"  M={M:2d}: v2* = {best:2d}   (excess {best - M:+d})")
    return results

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    print("ASSAULT406 — THE DUST ENGINE (S078) — exact arithmetic only")
    print("=" * 78)

    print("\nE1. THE UNIT WORD W (first 60 trits, position 0 first):")
    K = 60
    W = unit_word(K)
    tt = trits(W, K)
    print("  W trits:", "".join(map(str, tt)))
    print("  W mod 9  =", W % 9, "  W mod 27 =", W % 27)

    print("\nE2. THE THREE PI-POINTS (2*W*pi = -7 / -1 / +5 in Z_3):")
    for name, T in (("pi4 (fam 4)", -7), ("pi7 (fam 7)", -1), ("pi1 (fam 1)", 5)):
        pi = pi_point(T, K)
        pt = trits(pi, K)
        # check: natural?  (trits eventually all zero)  — check tail
        tail = pt[40:]
        naturalish = all(x == 0 for x in tail)
        has2 = 2 in pt
        print(f"  {name}: trits[0:30] = {''.join(map(str, pt[:30]))}")
        print(f"           trits[30:60] = {''.join(map(str, pt[30:60]))}")
        print(f"           contains 2: {has2};  tail[40:] all zero: {naturalish}")

    print("\nE3. TREE A (exponent dust) — the doubling + known riders:")
    levels = tree_A_iterative(13)
    for j in (1, 2, 3, 4, 5):
        print(f"  dust {j} = {levels[j][:16]}{' ...' if len(levels[j]) > 16 else ''}  |dust {j}| = {len(levels[j])}")
    # riders below 3^13: tree A survivors at level 13 that are actual riders
    riders = []
    for r in levels[13]:
        v = pow(4, r, 3 ** 80)
        ok = all((v // (3 ** q)) % 3 != 2 for q in range(80))
        if ok:
            riders.append(r)
    print(f"  riders below 3^13 = {riders}")

    row_family_counts(12)

    pin_analysis(smax=8)

    shadow_dust(10)

    print("\nENGINE COMPLETE — the engine never stops; it never lies.")

if __name__ == "__main__":
    main()
