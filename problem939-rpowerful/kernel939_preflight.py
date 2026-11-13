# kernel939_preflight.py — cross-verify EVERY numeric receipt Erdos939.lean will embed.
# (Mirrors battery939 + adds the grid-scan / pair-scan / gap-scan preflight so every
# `by decide` in the kernel is TRUE on first compile.)

from math import gcd

def rpowerful(n, r):
    if n == 1: return True
    if n < 1: return False
    f = {}
    d = 2
    m = n
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return all(e >= r for e in f.values())

# the census lists (hand-transcribed into the kernel)
c2 = [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100]
c3 = [1, 8, 16, 27, 32, 64, 81, 125, 128, 216, 243, 256, 343, 432, 512, 625, 648, 729, 864, 1000]
c4 = [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048, 2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000]

# 1. census lists == brute force
for r, N, L in ((2, 100, c2), (3, 1000, c3), (4, 10000, c4)):
    brute = [n for n in range(1, N + 1) if rpowerful(n, r)]
    assert brute == L, (r, brute)
print("1. census lists OK (14/20/25 values, brute-force-verified)")

# 2. grid scans: every exponent combo in range, constraints, product <= bound -> product in L
def grid_check(r, capA, capB, capC, capD, bound, L):
    for a in range(capA + 1):
        for b in range(capB + 1):
            for c in range(capC + 1):
                for d in range(capD + 1):
                    if (a == 0 or r <= a) and (b == 0 or r <= b) and (c == 0 or r <= c) and (d == 0 or r <= d):
                        prod = 2**a * 3**b * 5**c * 7**d
                        if prod <= bound:
                            assert prod in L, (r, a, b, c, d, prod)
    return True

grid_check(2, 6, 4, 2, 2, 100, c2)
grid_check(3, 9, 6, 4, 3, 1000, c3)
grid_check(4, 13, 8, 5, 4, 10000, c4)
print("2. grid scans OK (r2:315 r3:1400 r4:3780 combos, all products covered)")

# 3. cap facts: bound < p^(cap+1)
for (p, cap, bound) in ((2, 13, 10000), (3, 8, 10000), (5, 5, 10000), (7, 4, 10000),
                        (2, 9, 1000), (3, 6, 1000), (5, 4, 1000), (7, 3, 1000),
                        (2, 6, 100), (3, 4, 100), (5, 2, 100), (7, 2, 100)):
    assert bound < p ** (cap + 1), (p, cap, bound)
print("3. cap facts OK (bound < p^(cap+1)): 2^14=16384 3^9=19683 5^6=15625 7^5=16807 / 2^10=1024 3^7=2187 5^5=3125 7^4=2401 / 2^7=128 3^5=243 5^3=125 7^3=343")

# 4. pair scans: coprime a,b in L with a+b <= bound -> a+b NOT in L
def pair_check(bound, L):
    for a in L:
        for b in L:
            if a + b <= bound and gcd(a, b) == 1:
                assert (a + b) not in L, (a, b, a + b)
    return True

pair_check(1000, c3)
pair_check(10000, c4)
print("4. pair scans OK (r3 c<=10^3 and r4 c<=10^4: zero coprime hits)")

# 5. T-case decomposition lists + kills
odd9 = [n for n in c4 if n % 2 == 1]
e16 = [n for n in c4 if n % 16 == 0]
assert odd9 == [1, 81, 243, 625, 729, 2187, 2401, 3125, 6561], odd9
assert e16 == [16, 32, 64, 128, 256, 512, 1024, 1296, 2048, 2592, 3888, 4096, 5184, 7776, 8192, 10000], e16
assert not [(x, y) for x in odd9 for y in odd9 if x + y in e16]
assert not [(a, b) for a in e16 for b in odd9 if a + b in odd9]
assert not [(a, b) for b in e16 for a in odd9 if b + a in odd9]
print("5. T-case lists + kills OK (ODD9 = 9 values, E16 = 16 values, all three kill-lists empty)")

# 6. gap laws: all ordered pairs in c4 differ by >= 13; unique minimum pair (243, 256)
for x in c4:
    for y in c4:
        if x < y:
            assert y - x >= 13, (x, y)
assert 243 + 13 == 256 and 243 in c4 and 256 in c4
gaps = [(c4[i], c4[i+1], c4[i+1]-c4[i]) for i in range(len(c4)-1)]
assert min(g[2] for g in gaps) == 13 and [g for g in gaps if g[2] == 13] == [(243, 256, 13)]
print("6. gap laws OK (min gap 13, unique at 243->256)")

# 7. no consecutive 4-powerful <= 10^4
for n in range(1, 10000):
    assert not (rpowerful(n, 4) and rpowerful(n + 1, 4))
print("7. no consecutive 4-powerful pairs below 10^4 OK")

# 8. witnesses
assert 271**3 + 2**3 * 3**5 * 73**3 == 919**3 == 776151559
assert gcd(271**3, 2**3 * 3**5 * 73**3) == 1
assert 3**4 * 29**3 * 89**3 + 7**3 * 11**3 * 167**3 == 2**7 * 5**4 * 353**3 == 3518958160000
assert gcd(3**4 * 29**3 * 89**3, 7**3 * 11**3 * 167**3) == 1
assert rpowerful(1 + 8, 2) and gcd(1, 8) == 1  # the r=2 positive witness
print("8. witnesses OK (r2: 1+8=9; r3 nitaj-lane x2 with gcd=1)")

# 9. beyond-FLT + hunt bound + perfect-4th count
assert rpowerful(32, 4) and all(m ** 4 != 32 for m in range(4))
assert 5623**4 <= 10**15 < 5624**4
assert sum(1 for m in range(2, 5624) if m ** 4 <= 10**15) == 5622
print("9. beyond-FLT (32=2^5) + hunt bound (5623^4<=10^15<5624^4) + count 5622 OK")

# 10. rpowerful membership soundness of every census row (via prime-power rows)
for r, L in ((2, c2), (3, c3), (4, c4)):
    for n in L:
        assert rpowerful(n, r)
print("10. every census member is r-powerful OK (soundness rows)")

# 11. mod facts for the mod-class theorems
assert 2**4 == 16 and 2**3 == 8 and 2**2 == 4
print("11. mod facts OK (2^4=16, 2^3=8, 2^2=4)")

# 12. the r2/r3/r4 dichotomy spot checks on the census
for r, L in ((2, c2), (3, c3), (4, c4)):
    for n in L:
        assert n % 2 == 1 or (2 ** r) % n == 0 or n % (2 ** r) == 0
print("12. mod-class dichotomy spot checks OK")

print("PREFLIGHT939_ALL_OK")
