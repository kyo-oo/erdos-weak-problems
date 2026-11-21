#!/usr/bin/env python3
"""
ASSAULT406 PASS 3 (S078): THE DEEP SHADOW DUST — the nested scan.

The shadow-dust conditions are NESTED (level k+1 survivors are children of
level-k survivors), so the deep scan costs O(1) per level: carry the ~6
surviving classes forward, split each into 3 children, keep the clean ones.

Questions answered:
  P1. Does the 2-per-family structure persist to level 30?
  P2. Do the transients die?  (Which classes die, at which level?)
  P3. Is pi always among the survivors?  (pi computed independently by
      Hensel lifting — two methods must agree.)
  P4. The deep trits of pi (to level 40): the non-naturality evidence.
"""
import sys

def tri(x, i):
    return (x // (3 ** i)) % 3

def trits(x, k):
    t = []
    for _ in range(k):
        t.append(x % 3)
        x //= 3
    return t

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
    """omega_i(core) mod 3^K for i = 0..K-1."""
    M = 3 ** K
    M2 = 3 * M
    w = (((pow(4, core, M2) - 1) % M2) // 3) % M
    out = [w]
    for i in range(1, K):
        w = (w + (3 ** i) * ((w * w) % M + (3 ** (i - 1)) * ((w * w * w) % M))) % M
        out.append(w)
    return out

def survives(core, k):
    """Shadow-dust conditions at level k: windows sheets 1..k-1 dodge,
    diagonal trits 3..k avoid 2.  core is a class mod 3^(k+1)."""
    M = 3 ** (k + 1)
    chain = cut_chain(core, k + 1)
    for i in range(1, k):
        if tri(chain[i], i + 1) == 2:
            return False
    W = unit_word(k + 1)
    D = (W * core) % M
    for i in range(3, k + 1):
        if tri(D, i) == 2:
            return False
    return True

def main():
    print("ASSAULT406 PASS 3 — THE DEEP SHADOW DUST (nested scan)")
    print("=" * 74)
    KMAX = 30
    # level 4 seed: full scan (done before: 2 per family)
    survivors = {1: [], 4: [], 7: []}
    k0 = 4
    for c in range(3 ** (k0 + 1)):
        if c % 3 == 0:
            continue
        fam = c % 9
        if fam not in survivors:
            continue
        if survives(c, k0):
            survivors[fam].append(c)
    print(f"level {k0} seed: " + "  ".join(f"fam{f}: {survivors[f]}" for f in (1, 4, 7)))

    # nested scan: each survivor class c (mod 3^(k+1)) has children
    # c + t*3^(k+1) mod 3^(k+2) — check level k+1.
    history = []
    for k in range(k0, KMAX):
        nxt = {1: [], 4: [], 7: []}
        for fam in (1, 4, 7):
            for c in survivors[fam]:
                for t in range(3):
                    child = c + t * (3 ** (k + 1))
                    if survives(child, k + 1):
                        nxt[fam].append(child)
        survivors = nxt
        pis = {4: pi_point(-7, k + 2), 7: pi_point(-1, k + 2), 1: pi_point(5, k + 2)}
        counts = {f: len(survivors[f]) for f in (1, 4, 7)}
        has_pi = {f: any(c == pis[f] for c in survivors[f]) for f in (1, 4, 7)}
        history.append((k + 1, counts, has_pi))
        status = "  ".join(
            f"fam{f}: n={counts[f]}{' +PI' if has_pi[f] else ' NO-PI!'}"
            for f in (1, 4, 7))
        print(f"level {k+1:2d}: {status}   classes: "
              + "  ".join(f"{survivors[f]}" for f in (1, 4, 7)))
        if any(counts[f] == 0 for f in (1, 4, 7)):
            print(f"  ** family emptied at level {k+1} **")

    ok2 = all(h[1][f] == 2 for h in history for f in (1, 4, 7))
    okpi = all(h[2][f] for h in history for f in (1, 4, 7))
    print()
    print(f"P1  2-per-family at every level {k0+1}..{KMAX}: "
          f"{'CONFIRMED' if ok2 else 'VIOLATED (see above)'}")
    print(f"P3  pi always present: {'CONFIRMED' if okpi else 'VIOLATED'}")

    # P4: pi trits to 40, the non-naturality evidence
    print("\nP4  pi trits (40 levels):")
    for name, T in (("pi4", -7), ("pi7", -1), ("pi1", 5)):
        pi = pi_point(T, 40)
        tt = trits(pi, 40)
        twos = [i for i, x in enumerate(tt) if x == 2]
        print(f"  {name}: {''.join(map(str, tt))}")
        print(f"        #2s={len(twos)} at {twos[:14]}")

    print("\nPASS 3 COMPLETE — the engine never stops; it never lies.")

if __name__ == "__main__":
    main()
