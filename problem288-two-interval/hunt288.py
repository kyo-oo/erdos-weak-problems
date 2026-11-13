from fractions import Fraction
from collections import defaultdict
import time

t0 = time.time()

# Mirror the Lean defs EXACTLY:
# wprod a b = product of [a..b] (empty -> 1); hnum a b = numerator of sum 1/i over product denominator
def wprod(a, b):
    r = 1
    for i in range(a, b + 1):
        r *= i
    return r

def hnum(a, b):
    if b < a: return 0
    h, p = 0, 1
    for i in range(a, b + 1):
        h = h * i + p
        p = p * i
    return h

def equalWindow(a, b, c, d):
    return hnum(a, b) * wprod(c, d) == hnum(c, d) * wprod(a, b)

def S(a, b):
    s = Fraction(0)
    for i in range(a, b + 1):
        s += Fraction(1, i)
    return s

# sanity: fraction semantics of hnum/wprod
for (a, b) in [(2, 4), (3, 5), (1, 1), (6, 9)]:
    assert Fraction(hnum(a, b), wprod(a, b)) == S(a, b), (a, b)
print("SANITY hnum/wprod == sum 1/i: OK")

# THE HUNT: all window pairs (disjoint) with equal sums, windows inside [1..N]
for N in (60, 120):
    sums = defaultdict(list)
    for a in range(1, N + 1):
        s = Fraction(0)
        for b in range(a, N + 1):
            s += Fraction(1, b)
            sums[s].append((a, b))
    pairs = []
    for s, ws in sums.items():
        if len(ws) >= 2:
            for i in range(len(ws)):
                for j in range(i + 1, len(ws)):
                    (a1, b1), (a2, b2) = ws[i], ws[j]
                    if b1 < a2 or b2 < a1:
                        pairs.append((ws[i], ws[j], s))
    print(f"N={N}: equal-sum window pairs (disjoint): {len(pairs)}")
    for (w1, w2, s) in pairs[:20]:
        (a, b), (c, d) = w1, w2
        ok = equalWindow(a, b, c, d)
        print(f"  [{a},{b}] vs [{c},{d}]  sum={s}  cross-mult-equalWindow={ok}  hnum1*L2={hnum(a,b)*wprod(c,d)} hnum2*L1={hnum(c,d)*wprod(a,b)}")

# overlap equal pairs (non-disjoint) for reference: they exist trivially (same window)
print("\n--- single-term vs later-window family (n < c <= d), n<=40, d<=80 ---")
cnt = 0
for n in range(1, 41):
    for c in range(n + 1, 81):
        for d in range(c, 81):
            if S(c, d) == Fraction(1, n):
                print(f"  FOUND: 1/{n} = sum_[{c},{d}]")
                cnt += 1
print(f"single-family solutions found: {cnt}")

# also: sum of a window equal to another SINGLE term on the right
print("\n--- window vs single-later ---")
cnt2 = 0
for a in range(1, 20):
    for b in range(a, 30):
        s = S(a, b)
        for c in range(b + 1, 60):
            if s == Fraction(1, c):
                print(f"  FOUND: [{a},{b}] = 1/{c}")
                cnt2 += 1
print(f"window-vs-single solutions: {cnt2}")
print(f"elapsed {time.time()-t0:.1f}s")
