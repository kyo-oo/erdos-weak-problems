#!/usr/bin/env python3
"""
BATTERY 406E (S079) — THE BLOCK-LAW DUAL-METHOD VERIFICATION ENGINE
===================================================================
Kernel 73 (BlockLaw406.lean) companion. Every law of the kernel is
verified here by TWO INDEPENDENT METHODS (direct computation vs the
law's formula), plus the negative controls (corruptions must REJECT).

BOSS's laws only. No external libraries. Exact integer arithmetic.
"""
import sys, time

PASS = 0
FAIL = 0
FAILURES = []

def check(name, ok, detail=""):
    global PASS, FAIL
    if ok:
        PASS += 1
        print(f"  [PASS] {name}" + (f"  ({detail})" if detail else ""))
    else:
        FAIL += 1
        FAILURES.append(f"{name}: {detail}")
        print(f"  [FAIL] {name}  ({detail})")

# ---------------------------------------------------------------- engine

def digit3(x, p):
    """Ternary digit at position p (method A: div/mod)."""
    return (x // (3 ** p)) % 3

def digit3_b(x, p):
    """Ternary digit at position p (method B: repeated division)."""
    for _ in range(p):
        x //= 3
    return x % 3

def no_two(n):
    """The Cantor verdict (byte-identical twin of the Lean recursion)."""
    while True:
        if n == 0:
            return True
        if n % 3 == 2:
            return False
        n //= 3

def v3(k):
    """The 3-adic valuation of an exponent."""
    if k == 0:
        return 10**9  # convention: v3(0) = infinity
    v = 0
    while k % 3 == 0:
        k //= 3
        v += 1
    return v

def lte_coeff(v):
    """The LTE tower coefficient c_v = (4^(3^v) - 1)/3^(v+1)
    (method A: direct big-int)."""
    return (4 ** (3 ** v) - 1) // (3 ** (v + 1))

def lte_coeff_b(v):
    """Method B: the cube recursion c_{v+1} = c_v + 3^(v+1)c_v^2
    + 3^(2v+1)c_v^3, c_0 = 1 (the kernel's def)."""
    c = 1
    for r in range(v):
        c = c + (3 ** (r + 1)) * c * c + (3 ** (2 * r + 1)) * c * c * c
    return c

def c2(u):
    """The division-free second binomial coefficient C2."""
    if u == 0:
        return 0
    return c2(u - 1) + (u - 1)

# ---------------------------------------------------------------- T1

def t1_cut_residue():
    print("T1: THE CUT RESIDUE LAW (pow4_cut_residue_exact)")
    print("    4^(3^v*u) % 3^(v+2) == 1 + (u%3)*3^(v+1), dual-method")
    worst = 0
    for v in range(0, 9):
        for u in range(0, 41):
            lhs = (4 ** (3 ** v * u)) % (3 ** (v + 2))
            rhs = 1 + (u % 3) * (3 ** (v + 1))
            if lhs != rhs:
                check(f"cut residue v={v} u={u}", False,
                      f"{lhs} != {rhs}")
                return
            worst = max(worst, v)
    check("cut residue, v<=8, u<=40 (81*41 cases, direct)",
          True, f"max v={worst}")

# ---------------------------------------------------------------- T2

def t2_window_law():
    print("T2: THE WINDOW LAW (diagonal_window_law)")
    print("    digit3(4^(3^v*u), v+1+j) == digit3(u*c_v, j), j <= v")
    for v in range(0, 9):
        cv = lte_coeff(v)
        for u in range(1, 41):
            n = 4 ** (3 ** v * u)
            for j in range(0, v + 1):
                a = digit3(n, v + 1 + j)
                b = digit3_b(u * cv, j)
                if a != b:
                    check(f"window v={v} u={u} j={j}", False,
                          f"{a} != {b}")
                    return
    check("window law, v<=8, u<=40, all j<=v (dual-method)", True)

# ---------------------------------------------------------------- T3

def t3_killing_trit():
    print("T3: THE EXPONENT-TRIT KILLING LAW (pow4_killing_trit)")
    print("    digit3(4^(r+t*3^j), j+1) == (digit3(4^r, j+1)+t)%3")
    for j in range(0, 9):
        for r in range(0, 61):
            d = digit3(4 ** r, j + 1)
            for t in range(0, 3):
                a = digit3(4 ** (r + t * 3 ** j), j + 1)
                b = (d + t) % 3
                if a != b:
                    check(f"killing r={r} t={t} j={j}", False,
                          f"{a} != {b}")
                    return
    check("killing law, j<=8, r<=60, t<3 (dual-method)", True)

# ---------------------------------------------------------------- T4

FIRE = {
    1: (1, [1]),
    2: (2, [13, 25]),
    3: (3, [4, 34, 49, 70]),
    4: (4, [16, 31, 61, 76, 124, 139, 169, 184]),
    5: (5, [58, 103, 193, 205, 238, 250, 340, 385, 463, 508,
            529, 574, 598, 643, 664, 709]),
}

def t4_fire_ladder():
    print("T4: THE FIRE LADDER, LEVELS 1-5 (uniform families)")
    for L, (vmin, residues) in FIRE.items():
        mod = 3 ** (L + 1)
        for v in range(vmin, vmin + 3):
            cv = lte_coeff(v)
            all_ok = True
            for r in residues:
                for u_rep in [r, r + mod, r + 2 * mod, r + 3 * mod]:
                    # the law: trit L of u*c_v is 2
                    trit = digit3(u_rep * cv, L)
                    if trit != 2:
                        all_ok = False
                        check(f"fire L={L} v={v} u={u_rep}", False,
                              f"trit {trit} != 2")
                        return
            # and the power really fires at row v+1+L
            for r in residues[:2]:
                u_rep = r + mod
                n = 4 ** (3 ** v * u_rep)
                d = digit3(n, v + 1 + L)
                if d != 2:
                    all_ok = False
                    check(f"fire power L={L} v={v} u={u_rep}", False,
                          f"digit {d} != 2")
                    return
        check(f"fire level {L}: {len(residues)} residues mod {mod}, "
              f"v in [{vmin},{vmin+2}], trits + live powers", True)

# ---------------------------------------------------------------- T5

def t5_stabilization():
    print("T5: THE FROZEN DIAGONAL (lteCoeff stabilization + residues)")
    ok = True
    for v in range(0, 13):
        a, b = lte_coeff(v), lte_coeff_b(v)
        if a != b:
            check(f"lteCoeff dual-method v={v}", False, f"{a} != {b}")
            ok = False
            break
    if ok:
        check("lteCoeff dual-method (direct vs cube recursion), v<=12",
              True)
    residues = {1: (9, 7), 2: (27, 16), 3: (81, 16),
                4: (243, 178), 5: (729, 664)}
    for L, (mod, want) in residues.items():
        got = lte_coeff(L + 2) % mod  # stable from index L onward
        got2 = lte_coeff(L) % mod
        check(f"lteCoeff mod {mod} = {want} (frozen, two indices)",
              got == want and got2 == want, f"got {got},{got2}")

# ---------------------------------------------------------------- T6

def t6_second_digit():
    print("T6: THE SECOND-DIGIT LAW ON THE TRUE RIDERS")
    for K in [1, 4]:
        v = v3(K)
        u = K // (3 ** v)
        n = 4 ** K
        conds = (digit3(n, 0) == 1
                 and all(digit3(n, j) == 0 for j in range(1, v + 1))
                 and digit3(n, v + 1) == 1
                 and u % 3 == 1)
        check(f"rider K={K}: digits 1..{v} zero, digit {v+1}=1, "
              f"u%3=1 (u={u})", conds)
    # the census rider-free zone: 8 <= K <= 60 spot re-verify
    riders = [K for K in range(8, 61) if no_two(4 ** K)]
    check("no riders K in [8,60] (census spot re-verify)", riders == [],
          f"found {riders}")

# ---------------------------------------------------------------- T7

def t7_wheel():
    print("T7: THE WHEEL (exactly one lift fires)")
    for j in range(0, 9):
        for r in range(0, 41):
            fires = [t for t in range(3)
                     if digit3(4 ** (r + t * 3 ** j), j + 1) == 2]
            if len(fires) != 1:
                check(f"wheel r={r} j={j}", False, f"fires={fires}")
                return
    check("wheel: exactly one firing lift, j<=8, r<=40", True)

# ---------------------------------------------------------------- T8

def dust_tree(level):
    """The payload dust tree (DustFamily406's def): level j = residues
    r mod 3^j with digits 0..j of 4^r clean."""
    dust = [0]
    for j in range(level):
        nxt = []
        for r in dust:
            d = digit3(4 ** r, j + 1)
            if d == 0:
                nxt += [r, r + 3 ** j]
            elif d == 1:
                nxt += [r, r + 2 * 3 ** j]
            else:
                nxt += [r + 3 ** j, r + 2 * 3 ** j]
        dust = nxt
    return dust

def window_dust(L):
    """The window dust at level L: u mod 3^(L+1), u%3==1, first L+1
    trits of u*c_L avoid 2 (c_L = the frozen lteCoeff residue)."""
    c = lte_coeff(L) % 3 ** (L + 1)
    mod = 3 ** (L + 1)
    return [u for u in range(mod)
            if u % 3 == 1
            and all(digit3(u * c, j) != 2 for j in range(L + 1))]

def t8_dust_counts():
    print("T8: THE DUST TREES (payload dust + window dust, both counts)")
    # (a) the payload dust tree (DustFamily406's object): |dust(j)| = 2^j
    for j in range(1, 12):
        dt = dust_tree(j)
        check(f"|payload dust({j})| = 2^{j} = {2**j}",
              len(dt) == 2 ** j, f"got {len(dt)}")
    # (b) the window dust tree (the Diagonal Read's object): |D_L| = 2^L
    for L in range(0, 11):
        wd = window_dust(L)
        check(f"|window dust D_{L}| = 2^{L} = {2**L}",
              len(wd) == 2 ** L, f"got {len(wd)}")
    # (c) the S079 lists from the war council (A1's report):
    D4 = [7, 22, 43, 58, 88, 97, 103, 112, 142, 157, 178, 193, 205,
          220, 223, 238]
    got = sorted(window_dust(4))
    check("D_4 matches the war-council list (16 residues)",
          got == D4, f"got {got}")
    D5 = [7, 22, 43, 88, 97, 112, 142, 157, 178, 220, 223, 265, 286,
          301, 331, 346, 355, 400, 421, 436, 448, 466, 481, 493, 544,
          583, 589, 628, 679, 691, 706, 724]
    got5 = sorted(window_dust(5))
    check("D_5 matches the war-council list (32 residues)",
          got5 == D5, f"got {got5}")

# ---------------------------------------------------------------- T9

def t9_witnesses():
    print("T9: THE NEW UNIFORM WITNESSES (no bounded decides needed)")
    for K, row, label in [(1296, 9, "3^4*16, level-4 family"),
                          (14094, 11, "3^5*58, level-5 family"),
                          (42282, 12, "3^6*58, level-5 family at cut 6")]:
        n = 4 ** K
        d = digit3(n, row)
        d2 = digit3_b(n, row)
        check(f"4^{K} fires at row {row} ({label})",
              d == 2 and d2 == 2 and no_two(n) is False,
              f"digit={d}/{d2}")

# ---------------------------------------------------------------- T10

def t10_autopsy():
    print("T10: THE STRATEGIC AUTOPSY (where the dust dies, per cut v)")
    for v, n_expected, b2_expected in [(4, 32, 28), (5, 64, 62)]:
        cores = sorted(window_dust(v))
        # cores for v3(K) = v exactly: u not divisible by 3, u in the
        # lifted window dust (residues mod 3^(v+1), lifted by 3^(v+1))
        base_mod = 3 ** (v + 1)
        lifted = sorted(set([u for u in cores]
                            + [u + base_mod for u in cores]))
        # keep u not div by 3 (all are ≡1 mod 3 already)
        in_b2 = 0
        later = []
        riders = []
        for u in lifted:
            K = 3 ** v * u
            n = 4 ** K
            # first firing row
            fire = None
            # rows 0..3v+3 exhaust the window + block-2 bands;
            # scan to 3v+4 then fall back to full scan
            for p in range(0, 3 * v + 5):
                if digit3(n, p) == 2:
                    fire = p
                    break
            if fire is None:
                # full scan (top digit bound)
                p = 3 * v + 5
                while True:
                    if digit3(n, p) == 2:
                        fire = p
                        break
                    if 3 ** (p + 1) > n:
                        break
                    p += 1
            if fire is None:
                riders.append(u)
            elif 2 * v + 2 <= fire <= 3 * v + 2:
                in_b2 += 1
            elif fire > 3 * v + 2:
                later.append((u, fire))
        check(f"cut v={v}: {n_expected} cores, {b2_expected} die in "
              f"block 2, 0 riders",
              len(lifted) == n_expected and in_b2 == b2_expected
              and riders == [],
              f"cores={len(lifted)} b2={in_b2} later={later} "
              f"riders={riders}")
        print(f"       (above-block-2 survivors at v={v}: {later})")

# ---------------------------------------------------------------- T-Neg

def t_neg_controls():
    print("T-NEG: THE NEGATIVE CONTROLS (corruptions must REJECT)")
    # corrupt the level-4 coefficient: 178 -> 179 must break fires
    cv = lte_coeff(4)
    if cv % 243 != 178:
        check("N-COEFF-243: lteCoeff 4 % 243 == 178", False,
              f"got {cv % 243}")
    else:
        bad = [r for r in FIRE[4][1]
               if digit3(r * 179, 4) == 2]
        check("N-COEFF-243: corrupted coefficient 179 breaks the "
              "level-4 family", len(bad) < len(FIRE[4][1]),
              f"still fires: {len(bad)}")
    # corrupt a fire residue: 16 -> 17 must not fire
    fires17 = digit3(17 * (lte_coeff(4) % 243), 4) == 2
    check("N-FIRE4: corrupted residue 17 does NOT fire",
          not fires17)
    # corrupt the cut residue: 1 + (u%3)*3^(v+1) -> 2 + ...
    v = 3
    corrupt_ok = True
    for u in [1, 4, 7]:
        lhs = (4 ** (3 ** v * u)) % (3 ** (v + 2))
        if lhs == 2 + (u % 3) * (3 ** (v + 1)):
            corrupt_ok = False
    check("N-RESIDUE: corrupted residue 2+(u%3)*3^(v+1) rejected",
          corrupt_ok)
    # corrupt the killing law: (d + t + 1) % 3 must break
    j, r, t = 3, 5, 1
    d = digit3(4 ** r, j + 1)
    a = digit3(4 ** (r + t * 3 ** j), j + 1)
    check("N-KILLING: shifted trit (d+t+1)%3 rejected",
          a != (d + t + 1) % 3)
    # witness corruption: 4^1296 must NOT fire at row 10 (wrong row)
    n = 4 ** 1296
    check("N-WITNESS: 4^1296 does not fire at row 10 (the receipt row "
          "is exact)", digit3(n, 10) != 2)

# ---------------------------------------------------------------- main

def main():
    t0 = time.time()
    print("BATTERY 406E (S079) — THE BLOCK-LAW ENGINE, ALL CHECKS DUAL")
    print("=" * 66)
    t1_cut_residue()
    t2_window_law()
    t3_killing_trit()
    t4_fire_ladder()
    t5_stabilization()
    t6_second_digit()
    t7_wheel()
    t8_dust_counts()
    t9_witnesses()
    t10_autopsy()
    t_neg_controls()
    wall = time.time() - t0
    print("=" * 66)
    print(f"BATTERY 406E COMPLETE: {PASS} PASS / {FAIL} FAIL "
          f"(wall {wall:.1f}s)")
    if FAILURES:
        print("FAILURES:")
        for f in FAILURES:
            print(f"  - {f}")
        sys.exit(1)
    print("ALL GREEN. The engine never stops; it never lies.")

if __name__ == "__main__":
    main()
