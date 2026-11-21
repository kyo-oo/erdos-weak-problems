#!/usr/bin/env python3
"""
BATTERY406D — the S078 assault battery (Kernel 71 + Kernel 72 certification)

Verifies, exactly and independently of Lean:
  T1  THE EVEN CENSUS (dual method): for every even k <= 500, 2^k is
      0/1-ternary iff k in {0, 2, 8}  (divmod method + array-doubling
      method, no shared code).
  T2  THE RIDER-EDGE ANTI-CLUSTERING (digit form, the Kernel-71 law):
      for every level j in [0, 40] and every r <= 250 with 4^r < 3^(j+1):
      if all ternary digits of 4^r at positions <= j avoid 2, then
      r in {0, 1, 4}.  (The first infinite-family anti-clustering law.)
  T3  THE FIVE EXACT FAMILY LAWS (the Kernel-72 laws): tree A levels
      2..16: fam1 = 2^(j-2), fam4 = 2^(j-2), fam7 = 0, tower = 2^(j-1),
      mod3two = 0.
  T4  THE SHADOW DUST STRUCTURE: at every level 4..12, exactly 2
      window-dodging + diagonal-clean cores per family, and the
      middle-third pi-point of each family is among them.
  T5  THE WINDOW INCREMENT LAW: trit_{s+1}(w_{s+1}) = trit_{s+1}(w_s) + 1
      (mod 3) for 15 cores x 12 sheets (the engine behind the escalate
      branch of the three-window dichotomy).

The engine never stops; it never lies.
"""
import sys

def powmod(a, e, m):
    r = 1
    a %= m
    while e:
        if e & 1:
            r = (r * a) % m
        a = (a * a) % m
        e >>= 1
    return r

def tri(x, i):
    return (x // (3 ** i)) % 3

def trits_of(n):
    t = []
    while n:
        t.append(n % 3)
        n //= 3
    return t

# ---------------- T1: the even census, dual method ----------------

def t1_divmod():
    good = []
    for k in range(0, 501, 2):
        n = 1 << k
        ok = True
        while n:
            if n % 3 == 2:
                ok = False
                break
            n //= 3
        if ok:
            good.append(k)
    return good

def t1_array():
    # base-3 array doubling: digits of 2^k by repeated doubling with
    # carries, no divmod anywhere.
    good = []
    d = [1]  # digits of 2^0 = 1, little-endian
    for k in range(0, 501, 2):
        # current d = digits of 2^k
        ok = all(x <= 1 for x in d)
        if ok:
            good.append(k)
        # advance two exponents (keep even k's only): double twice
        for _ in range(2):
            d = d + [0]
            carry = 0
            for i in range(len(d)):
                v = 2 * d[i] + carry
                d[i] = v % 3
                carry = v // 3
            while len(d) > 1 and d[-1] == 0:
                d.pop()
    return good

# ---------------- T2: the rider-edge anti-clustering ----------------

def t2_anticluster():
    # precompute: for each r <= 250, the first death position of 4^r
    # (first ternary digit 2), and the ternary length of 4^r.
    info = {}
    for r in range(0, 251):
        n = 4 ** r
        t = trits_of(n)
        death = next((i for i, x in enumerate(t) if x == 2), None)
        info[r] = (death, len(t))  # death None = all digits <= 1
    bad = []
    for j in range(0, 41):
        window = 3 ** (j + 1)
        for r in range(0, 251):
            death, length = info[r]
            if 4 ** r >= window:
                continue  # not in the edge window at this level
            # digits at positions <= j all avoid 2?
            if death is None or death > j:
                # survives the level-j test inside the window -> must be
                # a known rider
                if r not in (0, 1, 4):
                    bad.append((j, r))
    return bad

# ---------------- T3: the five family laws ----------------

def tree_A_levels(J):
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

def t3_family_laws():
    levels = tree_A_levels(16)
    bad = []
    for j in range(1, 17):
        alive = levels[j]
        c1 = sum(1 for r in alive if r % 9 == 1)
        c4 = sum(1 for r in alive if r % 9 == 4)
        c7 = sum(1 for r in alive if r % 9 == 7)
        ct = sum(1 for r in alive if r % 3 == 0)
        cm = sum(1 for r in alive if r % 3 == 2)
        e = (2 ** (j - 2) if j >= 2 else None, 2 ** (j - 2) if j >= 2 else None, 0, 2 ** (j - 1), 0)
        if j >= 2 and (c1, c4, c7, ct, cm) != e:
            bad.append((j, (c1, c4, c7, ct, cm), e))
        if j == 1 and (c7, ct, cm) != (0, 1, 0):
            bad.append((j, (c1, c4, c7, ct, cm), "level-1 special"))
        if len(alive) != 2 ** j:
            bad.append((j, "count", len(alive), 2 ** j))
    return bad, levels

# ---------------- T4: the shadow dust structure ----------------

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
    M = 3 ** K
    M2 = 3 * M
    w = (((pow(4, core, M2) - 1) % M2) // 3) % M
    out = [w]
    for i in range(1, K):
        w = (w + (3 ** i) * ((w * w) % M + (3 ** (i - 1)) * ((w * w * w) % M))) % M
        out.append(w)
    return out

def t4_shadow_dust():
    bad = []
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
            ok = all(tri(chain[i], i + 1) != 2 for i in range(1, k))
            if not ok:
                continue
            D = (W * c) % M
            if all(tri(D, i) != 2 for i in range(3, k + 1)):
                res[fam].append(c)
        pis = {4: pi_point(-7, k + 1), 7: pi_point(-1, k + 1), 1: pi_point(5, k + 1)}
        for fam in (1, 4, 7):
            if len(res[fam]) != 2:
                bad.append((k, fam, "count", len(res[fam])))
            if pis[fam] not in res[fam]:
                bad.append((k, fam, "pi-missing", res[fam][:4]))
    return bad

# ---------------- T5: the window increment law ----------------

def t5_increment():
    bad = []
    for core in [1, 2, 4, 5, 7, 8, 10, 13, 17, 22, 28, 43, 100, 970, 10021]:
        K = 14
        chain = cut_chain(core, K)
        for s in range(1, K - 1):
            if tri(chain[s + 1], s + 1) != (tri(chain[s], s + 1) + 1) % 3:
                bad.append((core, s))
    return bad

# ---------------- main ----------------

def main():
    print("BATTERY406D — the S078 assault battery (Kernel 71 + 72)")
    ok = True

    g1 = t1_divmod()
    g2 = t1_array()
    print(f"T1 even census (divmod):    good exponents = {g1}  "
          f"{'OK' if g1 == [0, 2, 8] else 'FAIL'}")
    print(f"T1 even census (array):     good exponents = {g2}  "
          f"{'OK' if g2 == [0, 2, 8] and g1 == g2 else 'FAIL'}")
    ok &= (g1 == [0, 2, 8] == g2)

    bad2 = t2_anticluster()
    print(f"T2 rider-edge anti-clustering (j in [0,40], r <= 250): "
          f"{'OK — violations: none' if not bad2 else 'FAIL ' + str(bad2[:6])}")
    ok &= (not bad2)

    bad3, _ = t3_family_laws()
    print(f"T3 five exact family laws (tree A levels 1..16): "
          f"{'OK — all levels exact' if not bad3 else 'FAIL ' + str(bad3[:4])}")
    ok &= (not bad3)

    bad4 = t4_shadow_dust()
    print(f"T4 shadow dust 2-per-family + pi-points (levels 4..12): "
          f"{'OK — structure exact' if not bad4 else 'FAIL ' + str(bad4[:4])}")
    ok &= (not bad4)

    bad5 = t5_increment()
    print(f"T5 window increment law (15 cores x 12 sheets): "
          f"{'OK — law holds' if not bad5 else 'FAIL ' + str(bad5[:4])}")
    ok &= (not bad5)

    if ok:
        print("BATTERY406D_GREEN=1")
        print("The engine never stops; it never lies.")
        return 0
    print("BATTERY406D FAILED")
    return 1

if __name__ == "__main__":
    sys.exit(main())
