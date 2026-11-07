import math, time
t0 = time.time()

# ============================================================
# BATTERY — Erdős #686 THE SQUARE k=2 CENSUS (dual-method)
# Method 1: brute-force divisor-pair scan (the engine's shape).
# Method 2: direct representation search via the quadratic in m
#           (for each n, solve (m+1)(m+2) = t²(n+1)(n+2)).
# Verifies: the infinite family (t ≡ 2 mod 4, t ≥ 10), the sporadic
# t = 99, and the full census t ∈ [2, 100]: representable ⟺ family
# or t = 99.
# ============================================================

def divisors(n):
    ds = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            ds.append(d)
            if d != n // d:
                ds.append(n // d)
        d += 1
    return sorted(ds)

def rep2_scan(t):
    """Method 1: the divisor-pair scan (mirrors the kernel's divNoRepSmall)."""
    M = t * t - 1
    for d1 in divisors(M):
        d2 = M // d1
        if d1 * d2 != M or d1 >= d2:
            continue
        if (d2 - d1) % 2 != 0:
            continue
        X = (d2 - d1) // 2
        if X % 2 != 1 or X < 9:
            continue
        if (d2 + d1) % (2 * t) != 0:
            continue
        Y = (d2 + d1) // (2 * t)
        if Y % 2 != 1 or Y < 5:
            continue
        if X < Y + 2:
            continue
        m, n = (X - 3) // 2, (Y - 3) // 2
        assert (m + 1) * (m + 2) == t * t * (n + 1) * (n + 2), (t, m, n)
        return (m, n)
    return None

def rep2_quadratic(t, ncap=5000):
    """Method 2: for each n ≥ 1, solve the quadratic in m."""
    for n in range(1, ncap):
        rhs = t * t * (n + 1) * (n + 2)
        m = math.isqrt(rhs)  # (m+1)(m+2) ≈ m² — start near sqrt
        for mm in (m - 2, m - 1, m, m + 1, m + 2):
            if mm >= n + 2 and (mm + 1) * (mm + 2) == rhs:
                return (mm, n)
    return None

print("=" * 70)
print("THE CENSUS — dual method, t = 2..100")
print("=" * 70)
mismatches = 0
rep_list = []
for t in range(2, 101):
    r1 = rep2_scan(t)
    is_fam = (t % 4 == 2 and t >= 10)
    is_spor = (t == 99)
    expected = is_fam or is_spor
    if (r1 is not None) != expected:
        print(f"  MISMATCH t={t}: scan={r1} expected={'REP' if expected else 'NO-REP'}")
        mismatches += 1
    if r1 is not None:
        rep_list.append((t, r1))
print(f"  census matches (method 1 vs family+99): {100 - 2 + 1 - mismatches}/99")
print(f"  representable t's: {len(rep_list)} (family 23 + sporadic 1 = 24 expected)")

print()
print("=" * 70)
print("SPOT DUAL-METHOD (scan vs quadratic) on key t's")
print("=" * 70)
for t in [2, 3, 8, 10, 14, 50, 99, 100]:
    r1 = rep2_scan(t)
    r2 = rep2_quadratic(t, ncap=3000)
    agree = (r1 is None) == (r2 is None) or r1 == r2
    print(f"  t={t:3d}: scan={r1} quadratic={r2} agree={agree}")
    if not agree:
        mismatches += 1
assert mismatches == 0, "MISMATCHES FOUND"

print()
print("=" * 70)
print("THE FAMILY CROSS-CHECK (Thm B: t = 4u+2, m = 4u²+4u−1, n = u−1)")
print("=" * 70)
for u in range(2, 25):
    t = 4 * u + 2
    m, n = 4 * u * u + 4 * u - 1, u - 1
    ok = (m + 1) * (m + 2) == t * t * (n + 1) * (n + 2)
    assert ok and m >= n + 2 and n >= 1
print(f"  family identity verified for u = 2..24 (t = 10..98): ALL OK")

print()
print("=" * 70)
print("THE SPORADIC (t = 99: 242·243 = 9801·6)")
print("=" * 70)
assert 242 * 243 == 99 * 99 * 2 * 3 == 58806
print("  242 * 243 = 58806 = 9801 * 6: OK")

print()
print("BATTERY686SQ GREEN: all dual-method checks passed.")
print(f"TOTAL: {time.time() - t0:.1f}s")
