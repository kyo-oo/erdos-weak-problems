# battery939.py — Kernel 61's ground-truth battery (no numpy needed; pure python).
# Verifies every numeric the E939 kernel embeds: censuses, witnesses, bounds,
# the coprime-sum zero scan (the kernelized mini-hunt at c <= 10^4), primality.
# House law: state to disk (battery939_output.txt), single Bash call < 10 min.

from sympy import isprime

out = []
def P(*a):
    s = " ".join(str(x) for x in a)
    out.append(s)
    print(s, flush=True)

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def rpowerful(n, r):
    if n == 1:
        return True
    if n < 1:
        return False
    return all(e >= r for e in factor(n).values())

# ---- §1 the censuses (double-derived: brute force + smooth enumeration) ----
for r in (2, 3, 4):
    N = 10 ** r
    brute = [n for n in range(1, N + 1) if rpowerful(n, r)]
    # enumeration over primes <= 10 (p^r <= N => p <= 10) with exponents >= r
    primes = [2, 3, 5, 7]
    enum = []
    def gen(idx, val):
        if val > N:
            return
        if val > 1:
            enum.append(val)
        for i in range(idx, len(primes)):
            p = primes[i]
            v = val * (p ** r)
            while v <= N:
                gen(i + 1, v)
                v *= p
    gen(0, 1)
    enum.append(1)
    enum = sorted(set(enum))
    assert brute == enum, (r, brute, enum)
    P(f"CENSUS r={r} N={N}: {len(brute)} values")
    P("  " + repr(brute))

# ---- §2 the two certified r=3 witnesses (Nitaj-lane instances) ----
w1 = 271 ** 3 + 2 ** 3 * 3 ** 5 * 73 ** 3
w1r = 919 ** 3
P("WITNESS1:", w1 == w1r, w1, w1r)
w2 = 3 ** 4 * 29 ** 3 * 89 ** 3 + 7 ** 3 * 11 ** 3 * 167 ** 3
w2r = 2 ** 7 * 5 ** 4 * 353 ** 3
P("WITNESS2:", w2 == w2r, w2, w2r)
for v in (271 ** 3, 2 ** 3 * 3 ** 5 * 73 ** 3, 919 ** 3,
          3 ** 4 * 29 ** 3 * 89 ** 3, 7 ** 3 * 11 ** 3 * 167 ** 3,
          2 ** 7 * 5 ** 4 * 353 ** 3):
    P("  r3pow", v, factor(v))

# ---- §3 the hunt939b scale receipt: 5623^4 <= 10^15 < 5624^4 ----
P("HUNT_BOUND:", 5623 ** 4 <= 10 ** 15 < 5624 ** 4, 5623 ** 4, 5624 ** 4)
# the forensic: the old hunt's census count == perfect 4th powers 2..5623
cnt = sum(1 for m in range(2, 5624) if m ** 4 <= 10 ** 15)
P("PERFECT4_COUNT(2..5623):", cnt)  # must be 5622 == hunt939b's claim

# ---- §4 the mini-hunt: zero coprime 4-powerful sums c <= 10^4 ----
c4 = [n for n in range(1, 10001) if rpowerful(n, 4)]
s4 = set(c4)
from math import gcd
hits = []
for i in range(len(c4)):
    for j in range(i, len(c4)):
        a, b = c4[i], c4[j]
        if a + b > 10000:
            break
        if gcd(a, b) != 1:
            continue
        if a + b in s4:
            hits.append((a, b, a + b))
P("MINIHUNT r=4 c<=10^4: coprime pairs summed, hits =", len(hits), hits)

# the T-case decomposition lists
odd = [n for n in c4 if n % 2 == 1]
sixteen = [n for n in c4 if n % 16 == 0]
P("ODD9:", odd)
P("E16:", sixteen)
# case 16|c: no odd+odd sum lands in E16
bad1 = [(x, y) for x in odd for y in odd if x + y in sixteen]
# case 16|a: no (E16, odd, odd) triple with a+b=c
bad2 = [(a, b) for a in sixteen for b in odd if (a + b) in odd]
# case 16|b: mirror
bad3 = [(b, a) for b in sixteen for a in odd if (b + a) in odd]
P("TCASE_KILLS:", bad1, bad2, bad3)

# r=3 coprime-sum scan c <= 10^3 (for context: witnesses live ABOVE 10^3)
c3 = [n for n in range(1, 1001) if rpowerful(n, 3)]
s3 = set(c3)
hits3 = []
for i in range(len(c3)):
    for j in range(i, len(c3)):
        a, b = c3[i], c3[j]
        if a + b > 1000:
            break
        if gcd(a, b) != 1:
            continue
        if a + b in s3:
            hits3.append((a, b))
P("MINIHUNT r=3 c<=10^3: hits =", len(hits3), hits3)

# ---- §5 exclusion-tree bound numerics ----
P("BOUNDS:",
   2 ** 6 <= 100 < 2 ** 7,          # r2: a<=6
   3 ** 4 <= 100 < 3 ** 5,          # r2: b<=4
   5 ** 2 <= 100 < 5 ** 3,          # r2: c<=2
   7 ** 2 <= 100 < 7 ** 3,          # r2: d<=2
   2 ** 9 <= 1000 < 2 ** 10,       # r3: a<=9
   3 ** 6 <= 1000 < 3 ** 7,         # r3: b<=6
   5 ** 4 <= 1000 < 5 ** 5,         # r3: c<=4
   7 ** 3 <= 1000 < 7 ** 4,         # r3: d<=3
   2 ** 13 <= 10000 < 2 ** 14,      # r4: a<=13
   3 ** 8 <= 10000 < 3 ** 9,        # r4: b<=8
   5 ** 5 <= 10000 < 5 ** 6,        # r4: c<=5
   7 ** 4 <= 10000 < 7 ** 5)        # r4: d<=4
P("PRIME_BOUND: 11^2=121>100, 11^3=1331>1000, 11^4=14641>10^4:",
   11 ** 2 > 100, 11 ** 3 > 1000, 11 ** 4 > 10000)
P("TWO_ODD_KILLS r4: 3^4*5^4, 3^4*7^4, 5^4*7^4 > 10^4:",
   81 * 625 > 10000, 81 * 2401 > 10000, 625 * 2401 > 10000)
P("TWO_ODD_KILLS r3: 3^3*5^3 etc > 10^3:",
   27 * 125 > 1000, 27 * 343 > 1000, 125 * 343 > 1000)
P("TWO_ODD_KILLS r2: 3^2*5^2 etc > 100:",
   9 * 25 > 100, 9 * 49 > 100, 25 * 49 > 100)
P("PAIR_KILLS r4: 2^7*3^4=10368>10^4, 2^4*3^6=11664>10^4,",
   " 2^5*5^4=20000>10^4, 2^4*7^4=38416>10^4, 2^4*3^4*5^4=810000>10^4:",
   128 * 81 > 10000, 16 * 729 > 10000, 32 * 625 > 10000,
   16 * 2401 > 10000, 16 * 81 * 625 > 10000)
P("PAIR_KILLS r3: 2^6*3^3=1728, 2^3*3^5=1944, 2^4*5^3=2000, 2^3*7^3=2744 >10^3:",
   64 * 27 > 1000, 8 * 243 > 1000, 16 * 125 > 1000, 8 * 343 > 1000)
P("PAIR_KILLS r2: 2^4*3^2=144, 2^2*3^3=108, 2^3*5^2=200, 2^2*7^2=196 > 100:",
   16 * 9 > 100, 4 * 27 > 100, 8 * 25 > 100, 4 * 49 > 100)

# ---- §6 the beyond-FLT witness: 32 is 4-powerful, not a 4th power ----
P("BEYOND_FLT: 32 = 2^5 4-powerful:", rpowerful(32, 4),
   "no m^4=32:", all(m ** 4 != 32 for m in range(4)))
P("GAPS: smallest gap 13 (243->256):",
   min(c4[i+1] - c4[i] for i in range(len(c4)-1)),
   [ (c4[i], c4[i+1]) for i in range(len(c4)-1) if c4[i+1]-c4[i] == 13 ])

# ---- §7 primality of the kernel's primes ----
for p in (2, 3, 5, 7, 11, 29, 73, 89, 167, 271, 353, 919):
    P("PRIME", p, isprime(p))

with open("battery939_output.txt", "w") as f:
    f.write("\n".join(out) + "\n")
print("BATTERY939_DONE", len(out), "lines")
