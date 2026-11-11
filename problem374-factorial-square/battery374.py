#!/usr/bin/env python3
"""Battery374 — dual-method verification of the #374 kernel claims.

Kernel claims under test (Erdos374.lean, Kernel 33):
 1. THE D2 SQUARE FAMILY: (t^2-1)!*(t^2)! = (t*(t^2-1)!)^2 for all t >= 1.
 2. THE D2 = SQUARES LAW at 250: for 2 <= m <= 250, m in D2 iff m is a
    nontrivial square. Dual method: (a) direct isqrt on a!*m! products;
    (b) Legendre parity vectors (the kernel's engine, independent impl).
 3. THE D3 WITNESS TABLE: all 38 (m, a, b) witnesses give exact squares
    (isqrt reconstruction + parity method agree).
 4. THE D4 WITNESS TABLE: all 96 (m, a, b, c) witnesses, same dual method.
 5. THE F-CLASSIFICATION (engine-side): F(m) resolved {2,3,4} with D2
    exclusions cross-checked against the census; D4 pair-exclusions
    verified by the O(m^2) scan (battery-only, as scoped in the kernel).
 6. vff calibration: the fuel-9 Legendre floor sum == v_p(n!) == the
    direct big-int valuation, sampled.
"""
import math
from math import factorial, isqrt

# --- the prime base (all primes <= 251, 54 of them) ---
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
          59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
          127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
          191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

def legendre(p, n):
    """v_p(n!) = sum floor(n/p^i)."""
    s, q = 0, p
    while q <= n:
        s += n // q
        q *= p
    return s

def vff9(p, n):
    """The kernel's fuel-9 engine (exact for n <= 250 < 2^9)."""
    s = 0
    f = 9
    while f > 0:
        n = n // p
        s += n
        f -= 1
    return s

def vp_bigint(p, n):
    """Direct valuation of the big integer n."""
    if n == 0:
        return 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def parvec(n):
    """Legendre parity vector of n! over the prime base."""
    return tuple(legendre(p, n) % 2 for p in PRIMES)

def is_square(n):
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n

def main():
    ok = True
    def check(name, cond):
        nonlocal ok
        print(("PASS " if cond else "FAIL ") + name)
        if not cond:
            ok = False

    # --- 1. THE FAMILY IDENTITY (t <= 30) ---
    fam = all(factorial(t*t - 1) * factorial(t*t) == (t * factorial(t*t - 1))**2
              for t in range(1, 31))
    check("family identity (t^2-1)!*(t^2)! = (t*(t^2-1)!)^2, t in [1,30]", fam)

    # --- 2. THE D2 = SQUARES CENSUS (dual method) ---
    d2_direct, d2_parity = set(), set()
    for m in range(2, 251):
        for a in range(1, m):
            if is_square(factorial(a) * factorial(m)):
                d2_direct.add(m)
                break
    for m in range(2, 251):
        pm = parvec(m)
        for a in range(1, m):
            if parvec(a) == pm:
                d2_parity.add(m)
                break
    squares = {t*t for t in range(2, 16) if t*t <= 250}
    check("D2 census direct-isqrt == squares in [4,250]",
          d2_direct == squares)
    check("D2 census parity-method == squares in [4,250]",
          d2_parity == squares)
    check("D2 census dual-method agreement (direct == parity)",
          d2_direct == d2_parity)

    # --- 3. THE D3 WITNESS TABLE (the kernel's 38 triples, dual method) ---
    d3tab = [6, 3, 5, 8, 2, 7, 10, 6, 7, 18, 2, 17, 20, 6, 19, 24, 3, 23,
             28, 10, 27, 30, 5, 29, 32, 2, 31, 35, 7, 34, 45, 6, 44, 50,
             2, 48, 54, 3, 53, 63, 10, 62, 70, 8, 69, 72, 2, 71, 77, 11,
             76, 80, 6, 79, 96, 3, 95, 98, 2, 97, 112, 10, 111, 120, 5,
             119, 125, 6, 124, 126, 8, 124, 128, 2, 127, 140, 7, 139, 150,
             3, 149, 162, 2, 161, 175, 10, 174, 176, 11, 174, 180, 6, 179,
             200, 2, 199, 216, 3, 215, 221, 18, 219, 231, 12, 230, 242, 2,
             241, 243, 3, 241, 245, 6, 244]
    check("d3tab length == 114 (38 triples)", len(d3tab) == 114)
    d3_ok_isqrt, d3_ok_parity, d3_order = True, True, True
    d3_ms_set = set()
    for i in range(38):
        m, a, b = d3tab[3*i], d3tab[3*i+1], d3tab[3*i+2]
        d3_ms_set.add(m)
        if not (1 <= a < b < m <= 250):
            d3_order = False
        P = factorial(a) * factorial(b) * factorial(m)
        if not is_square(P):
            d3_ok_isqrt = False
        # parity method: XOR of the three parity vectors is zero
        pa, pb, pm = parvec(a), parvec(b), parvec(m)
        if any((x + y + z) % 2 for x, y, z in zip(pa, pb, pm)):
            d3_ok_parity = False
    check("D3 witness table: ordering 1<=a<b<m<=250 all 38", d3_order)
    check("D3 witness table: all 38 products exact squares (isqrt)", d3_ok_isqrt)
    check("D3 witness table: all 38 parity-XOR zero (Legendre)", d3_ok_parity)
    d3ms = [6, 8, 10, 18, 20, 24, 28, 30, 32, 35, 45, 50, 54, 63, 70, 72,
            77, 80, 96, 98, 112, 120, 125, 126, 128, 140, 150, 162, 175,
            176, 180, 200, 216, 221, 231, 242, 243, 245]
    check("d3ms list == the table's m-column (consistency)", set(d3ms) == d3_ms_set
          and len(d3ms) == len(d3_ms_set))
    check("all D3 members are non-squares (F=3 exactness side)",
          all(not is_square(m) for m in d3ms))

    # --- 4. THE D4 WITNESS TABLE (the kernel's 96 quadruples) ---
    d4tab = [12, 2, 3, 11, 14, 2, 10, 13, 15, 3, 7, 13, 21, 3, 8, 19, 22,
             5, 11, 19, 26, 11, 13, 23, 27, 12, 13, 23, 33, 10, 12, 32,
             34, 15, 18, 33, 38, 17, 19, 37, 39, 11, 13, 38, 40, 2, 6, 39,
             42, 3, 10, 41, 44, 10, 11, 43, 48, 2, 3, 47, 51, 15, 18, 47,
             52, 12, 13, 51, 55, 8, 12, 53, 56, 6, 12, 53, 57, 18, 22, 54,
             60, 2, 5, 59, 62, 30, 32, 61, 66, 7, 14, 62, 68, 15, 17, 67,
             75, 2, 3, 74, 76, 56, 57, 74, 78, 2, 13, 76, 82, 39, 41, 79,
             84, 5, 8, 83, 85, 13, 18, 83, 88, 21, 22, 87, 90, 2, 6, 89,
             91, 11, 15, 89, 92, 22, 28, 90, 95, 18, 20, 94, 99, 21, 22,
             97, 102, 48, 51, 101, 104, 24, 26, 103, 105, 12, 15, 103,
             108, 2, 3, 107, 110, 8, 11, 109, 116, 28, 29, 115, 117, 12,
             13, 116, 122, 59, 61, 119, 124, 30, 31, 123, 132, 10, 12,
             131, 133, 74, 77, 131, 135, 2, 5, 134, 136, 14, 18, 134, 138,
             22, 24, 137, 141, 46, 48, 140, 142, 70, 72, 141, 143, 3, 14,
             142, 146, 71, 73, 145, 147, 2, 3, 146, 148, 72, 75, 145, 152,
             17, 19, 151, 153, 15, 19, 151, 154, 14, 22, 151, 155, 123,
             125, 154, 156, 11, 13, 155, 160, 2, 6, 159, 164, 40, 41, 163,
             165, 7, 12, 164, 168, 3, 10, 167, 170, 13, 18, 167, 171, 13,
             19, 167, 172, 42, 43, 171, 182, 12, 14, 181, 184, 45, 46,
             183, 188, 46, 47, 187, 189, 5, 8, 188, 190, 17, 21, 188, 192,
             2, 3, 191, 194, 96, 98, 193, 198, 21, 22, 197, 203, 27, 29,
             202, 204, 50, 51, 203, 207, 22, 23, 206, 208, 22, 27, 206,
             210, 18, 27, 206, 212, 52, 53, 211, 220, 7, 11, 219, 222, 73,
             75, 221, 224, 2, 10, 223, 226, 111, 113, 223, 228, 56, 57,
             227, 230, 44, 46, 229, 232, 173, 176, 230, 234, 24, 26, 233,
             236, 58, 59, 235, 240, 2, 5, 239, 244, 182, 183, 242, 246,
             119, 123, 241, 248, 30, 32, 247, 250, 2, 6, 249]
    check("d4tab length == 384 (96 quadruples)", len(d4tab) == 384)
    d4_ok_isqrt, d4_ok_parity, d4_order = True, True, True
    for i in range(96):
        m, a, b, c = d4tab[4*i], d4tab[4*i+1], d4tab[4*i+2], d4tab[4*i+3]
        if not (1 <= a < b < c < m <= 250):
            d4_order = False
        P = factorial(a) * factorial(b) * factorial(c) * factorial(m)
        if not is_square(P):
            d4_ok_isqrt = False
        pa, pb, pc, pm = parvec(a), parvec(b), parvec(c), parvec(m)
        if any((w + x + y + z) % 2 for w, x, y, z in zip(pa, pb, pc, pm)):
            d4_ok_parity = False
    check("D4 witness table: ordering 1<=a<b<c<m<=250 all 96", d4_order)
    check("D4 witness table: all 96 products exact squares (isqrt)", d4_ok_isqrt)
    check("D4 witness table: all 96 parity-XOR zero (Legendre)", d4_ok_parity)

    # --- 5. THE F-CLASSIFICATION (engine-side; the D4 pair-exclusion) ---
    # Independent method: INT BITMASKS (the engine used frozensets; the
    # kernel uses vff rows — this is the third, fastest representation).
    # mask(n) = sum over primes of bit_i * (v_{p_i}(n!) mod 2). Then
    # a_1!*...*a_k! is a square iff XOR of masks is 0.
    def mask(n):
        v = 0
        for i, p in enumerate(PRIMES):
            if legendre(p, n) & 1:
                v |= (1 << i)
        return v
    masks = {n: mask(n) for n in range(0, 251)}
    F = {}
    pair_seen = {}   # xor-value -> earliest attaining pair (a, b), b the later
    for m in range(2, 251):
        km = masks[m]
        cls = None
        # k = 2: some earlier a with the same mask
        for a in range(1, m):
            if masks[a] == km:
                cls = 2
                break
        if cls is None:
            # k = 3: some earlier pair (a, b), b < m, with a^b == m
            for b in range(2, m):
                t = masks[b] ^ km
                # need a < b with masks[a] == t
                for a in range(1, b):
                    if masks[a] == t:
                        cls = 3
                        break
                if cls:
                    break
        if cls is None:
            # k = 4: some earlier triple — via pair dict: exists a < b < m
            # with masks[a]^masks[b] == masks[c]^km for some c < b
            for c in range(3, m):
                rest = masks[c] ^ km
                if rest in pair_seen and pair_seen[rest] < c:
                    cls = 4
                    break
        F[m] = cls
        # update pair dict with pairs ending at m
        for a in range(1, m):
            x = masks[a] ^ km
            if x not in pair_seen:
                pair_seen[x] = m
    d3_engine = {m for m in range(2, 251) if F[m] == 3}
    d4_engine = {m for m in range(2, 251) if F[m] == 4}
    check("brute-force D3 set == the kernel's 38-member list",
          d3_engine == d3_ms_set)
    d4ms = [12, 14, 15, 21, 22, 26, 27, 33, 34, 38, 39, 40, 42, 44, 48,
            51, 52, 55, 56, 57, 60, 62, 66, 68, 75, 76, 78, 82, 84, 85,
            88, 90, 91, 92, 95, 99, 102, 104, 105, 108, 110, 116, 117,
            122, 124, 132, 133, 135, 136, 138, 141, 142, 143, 146, 147,
            148, 152, 153, 154, 155, 156, 160, 164, 165, 168, 170, 171,
            172, 182, 184, 188, 189, 190, 192, 194, 198, 203, 204, 207,
            208, 210, 212, 220, 222, 224, 226, 228, 230, 232, 234, 236,
            240, 244, 246, 248, 250]
    check("brute-force D4 set == the kernel's 96-member list",
          d4_engine == set(d4ms))
    check("all D4 members are non-squares",
          all(not is_square(m) for m in d4ms))
    unresolved = [m for m in range(2, 251) if F[m] is None]
    print(f"     (info: F unresolved beyond k=4 at 250: {len(unresolved)} "
          f"values, first 10: {unresolved[:10]})")

    # --- 6. THE vff CALIBRATION (fuel-9 == Legendre == direct bigint) ---
    cal_ok = True
    for p in PRIMES:
        for n in (0, 1, 2, 7, 50, 128, 249, 250):
            if not (vff9(p, n) == legendre(p, n) == vp_bigint(p, factorial(n))):
                cal_ok = False
                print(f"     vff MISMATCH: p={p} n={n}")
    check("vff fuel-9 == Legendre == direct v_p(n!) on samples", cal_ok)

    print()
    print("BATTERY374: " + ("GREEN" if ok else "RED"))
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
