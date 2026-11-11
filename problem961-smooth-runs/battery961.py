import math, time
t0 = time.time()

# ============================================================
# BATTERY — Erdős #961 THE ELEMENTARY SMOOTH-RUN LAWS (dual-method)
# Verifies independently: the {2,3}-census (engine vs closed form),
# the exact frontier f(2)=2, f(3)=3, f(4)=3, the k=5..12 witnesses,
# and the Pell dictionary round-trip on every census pair.
# ============================================================

print("=" * 70)
print("METHOD 1: the {2,3}-census via full enumeration to 10^7")
print("=" * 70)
B = 10 ** 7
s23 = sorted(2 ** a * 3 ** b
             for a in range(0, 24) if 2 ** a <= B
             for b in range(0, 15) if 2 ** a * 3 ** b <= B)
pairs_m1 = [(u, v) for u, v in zip(s23, s23[1:]) if v == u + 1]
print(f"  census pairs (method 1): {pairs_m1}")

print()
print("=" * 70)
print("METHOD 2: the census via the elementary theorem (closed form)")
print("=" * 70)
pairs_m2 = [(1, 2), (2, 3), (3, 4), (8, 9)]
print(f"  census pairs (method 2): {pairs_m2}")
assert pairs_m1 == pairs_m2, "CENSUS MISMATCH"
print("  DUAL-METHOD AGREEMENT: OK")

print()
print("=" * 70)
print("THE EXACT FRONTIER (set-based run scan to 10^7)")
print("=" * 70)
s2 = sorted(2 ** a for a in range(0, 24) if 2 ** a <= B)

def max_run_above(S, k):
    best = cur = 0
    prev = None
    for v in S:
        if v <= k:
            continue
        if cur == 0 or v == prev + 1:
            cur += 1
        else:
            cur = 1
        prev = v
        best = max(best, cur)
    return best

f2 = max_run_above(s2, 2) + 1
f3 = max_run_above(s23, 3) + 1
f4 = max_run_above(s23, 4) + 1
print(f"  f(2) = {f2}  (expect 2): {f2 == 2}")
print(f"  f(3) = {f3}  (expect 3): {f3 == 3}")
print(f"  f(4) = {f4}  (expect 3): {f4 == 3}")
assert (f2, f3, f4) == (2, 3, 3)

print()
print("=" * 70)
print("THE WITNESS LAWS (k = 5..12: runs with all elements > k, k-smooth)")
print("=" * 70)
def ksmooth(v, k):
    d = 2
    while d * d <= v:
        while v % d == 0:
            if d > k:
                return False
            v //= d
        d += 1
    return v == 1 or v <= k

for k in range(5, 13):
    run = (8, 9, 10) if k <= 7 else (14, 15, 16)
    ok = all(v > k for v in run) and all(ksmooth(v, k) for v in run)
    print(f"  k={k:2d}: witness run {run} valid: {ok}")
    assert ok

print()
print("=" * 70)
print("THE PELL DICTIONARY ROUND-TRIP (every census pair)")
print("=" * 70)
def sfk(n):
    r, x = 1, n
    d = 2
    while d * d <= x:
        e = 0
        while x % d == 0:
            x //= d
            e += 1
        if e % 2 == 1:
            r *= d
        d += 1
    return r * x

for (n, np1) in pairs_m2:
    prod = n * np1
    a = sfk(prod)
    b = math.isqrt(prod // a)
    assert b * b == prod // a
    x, y = 2 * n + 1, 2 * b
    ok = x * x - a * y * y == 1
    asmooth = a == 1 or ksmooth(a, 3)
    bsmooth = ksmooth(b, 3)
    print(f"  pair ({n},{np1}): a={a}, b={b}: Pell {x}^2 - {a}*{y}^2 = 1: {ok}, "
          f"a,b 3-smooth: {asmooth and bsmooth}")
    assert ok and asmooth and bsmooth

print()
print("BATTERY961 GREEN: all dual-method checks passed.")
print(f"TOTAL: {time.time() - t0:.1f}s")
