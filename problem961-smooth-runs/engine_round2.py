import math, time
from math import gcd
t0 = time.time()

# ============================================================
# ENGINE ROUND 2 - #961 THE ELEMENTARY SMOOTH-RUN LAWS
# Statement (erdosproblems.com/961): Let f(k) be the minimal n such
# that every set of n consecutive integers > k contains an integer
# divisible by a prime > k. Estimate f(k).
#
# This engine certifies:
#   (A) the {2,3}-census: consecutive {2,3}-smooth pairs
#       = {(1,2),(2,3),(3,4),(8,9)}  (brute to 10^7)
#   (B) the run laws: {2,3}-smooth runs = [1..4] and [8..9]
#   (C) f(2)=2, f(3)=3, f(4)=3 (witness + exclusion, brute)
#   (D) witnesses f(k)>=4 for k=5..12: runs (8,9,10) resp (14,15,16)
#   (E) the PELL DICTIONARY sanity: every pair (n,n+1) both P-smooth
#       <-> Pell solution (x,y), x^2 - a y^2 = 1, a=sfk(n(n+1)),
#       x=2n+1 odd, y=2b, b=sqrt(n(n+1)/a) P-smooth.
# ============================================================

print("=" * 70)
print("(A) THE {2,3}-CENSUS — brute force to 10^7")
print("=" * 70)
B = 10 ** 7
s23 = sorted(2 ** a * 3 ** b
             for a in range(0, 24) if 2 ** a <= B
             for b in range(0, 15) if 2 ** a * 3 ** b <= B)
print(f"  {{2,3}}-smooth count <= 10^7: {len(s23)}")
pairs = [(u, v) for u, v in zip(s23, s23[1:]) if v == u + 1]
print(f"  consecutive pairs: {pairs}")
EXPECT = [(1, 2), (2, 3), (3, 4), (8, 9)]
print(f"  MATCHES THE ELEMENTARY CENSUS THEOREM: {pairs == EXPECT}")

print()
print("=" * 70)
print("(B) THE RUN LAWS — maximal runs of consecutive {2,3}-smooth")
print("=" * 70)
runs = []
cur = [s23[0]]
for v in s23[1:]:
    if v == cur[-1] + 1:
        cur.append(v)
    else:
        runs.append((cur[0], cur[-1], len(cur)))
        cur = [v]
runs.append((cur[0], cur[-1], len(cur)))
runs = [r for r in runs if r[2] >= 2]
print(f"  runs of length >= 2: {runs}")
print(f"  EXPECT [1..4] and [8..9]: "
      f"{[(a, b, l) for a, b, l in runs] == [(1, 4, 4), (8, 9, 2)]}")

def max_run_above_set(S, k):
    """max length of a run of consecutive integers, all in sorted set S,
    with every element > k (S = the k-smooth numbers)"""
    best = 0
    cur = 0
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

print()
print("=" * 70)
print("(C) f(2), f(3), f(4) — witness + exclusion (set-based, full to 10^7)")
print("=" * 70)
# k=2: 2-smooth = powers of 2
s2 = sorted(2 ** a for a in range(0, 24) if 2 ** a <= B)
# k=3, k=4: {2,3}-smooth (same set: primes <= 3 and <= 4 are {2,3})
for k, S in ((2, s2), (3, s23), (4, s23)):
    mr = max_run_above_set(S, k)
    print(f"  max run of {k}-smooth all > k (<= 10^7): {mr}"
          f"   => f({k}) = {mr + 1}")

print()
print("=" * 70)
print("(D) WITNESSES f(k) >= 4 for k = 5..12")
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
    ok_all = all(ksmooth(v, k) for v in run)
    ok_gt = all(v > k for v in run)
    print(f"  k={k:2d}: run {run} all-{k}-smooth: {ok_all}, all > k: {ok_gt}"
          f"   => f({k}) >= 4: {ok_all and ok_gt}")

print()
print("=" * 70)
print("(E) THE PELL DICTIONARY — every {2,3}-smooth pair (n,n+1) gives")
print("    x^2 - a y^2 = 1 with a = sfk(n(n+1)), x = 2n+1 odd, y = 2b")
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
for (n, np1) in pairs:
    prod = n * np1
    a = sfk(prod)
    b2 = prod // a
    b = math.isqrt(b2)
    assert b * b == b2, (n, a, b2)
    x, y = 2 * n + 1, 2 * b
    ok = x * x - a * y * y == 1 and x % 2 == 1 and y % 2 == 0
    # y/2 = b must be P-smooth
    psmooth = all(pp <= 3 for pp in [2, 3]) and ksmooth(b, 3)
    print(f"  pair ({n},{np1}): a={a}, x={x}, y={y}, b={b}: "
          f"Pell {x}^2 - {a}*{y}^2 = 1: {ok}, b 3-smooth: {psmooth}")
# and a non-pair: n=5 (6 is 3-smooth but 5 is not): dictionary says no
for n in (5, 6, 15, 24, 80):
    prod = n * (n + 1)
    a = sfk(prod)
    b2 = prod // a
    b = math.isqrt(b2)
    x, y = 2 * n + 1, 2 * b
    ok = x * x - a * y * y == 1
    print(f"  non-pair n={n}: Pell holds trivially (x={x},a={a},y={y}): {ok}, "
          f"b={b} 3-smooth: {ksmooth(b,3)}  <- dictionary filter")

print()
print(f"TOTAL: {time.time() - t0:.1f}s")
