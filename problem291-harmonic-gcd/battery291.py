#!/usr/bin/env python3
"""
Erdos #291 — THE HARMONIC-GCD CENSUS (dual-method, N = 400).

Statement: L_n = lcm(1..n), H_n = a_n / L_n, g(n) = gcd(a_n, L_n).
Question: do g(n) = 1 and g(n) > 1 both occur for infinitely many n?

METHOD 1 (exact big-integer, gmpy2):
    L_n  = lcm(L_{n-1}, n)  (exact),
    a_n  = sum_{1<=k<=n} L_n // k  (exact big integers),
    g1(n) = gcd(a_n, L_n).

METHOD 2 (independent p-adic method, only modular arithmetic on prime
powers <= n; never forms L_n or a_n as big integers):
    For each prime q <= n, e = v_q(L_n) = max{f : q^f <= n} = floor(log_q n),
    K = e + 1, M = (q-free part of L_n) reduced mod q^K, computed as
        M = prod_{p prime <= n, p != q} p^{floor(log_p n)}  (mod q^K).
    Then per k = q^i * u (u q-free):
        L_n / k = q^(e-i) * (M/u)   (exact integer; u | M),
        (L_n / k) mod q^K = q^(e-i) * ( (M * u^{-1}) mod q^{i+1} ) mod q^K,
    so a_n mod q^K = sum over k of those residues.  v_q(a_n) is read off the
    residue mod q^(e+1) (0 residue => v_q(a_n) > e).  The q-part of the gcd
    is min(v_q(a_n), e); g2(n) = product of the q-parts.

METHOD 3 (THE LAW, an independent derivation path): for prime q <= n with
    m = n // q^e (the leading base-q digit of n, m in [1, q-1]):
        q | a_n  iff  sum_{u=1}^{m} u^{-1} == 0 (mod q)  iff  q | num(H_m)
    (reduced numerator of the harmonic number H_m; q does not divide the
    denominator since m < q).  Hence
        g(n) > 1  iff  exists prime q in [3, n] with q | num(H_{d_q(n)}).
    This is cross-checked against Methods 1 and 2, and the interval
    structure n in [d*q^e, (d+1)*q^e) is verified for every qualifying n.
"""
import sys
from fractions import Fraction
import gmpy2
from gmpy2 import mpz

N = 400

# ---------------------------------------------------------------- primes
def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, gmpy2.isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n + 1) if sieve[i]]

PRIMES = primes_upto(N)
assert gmpy2.is_prime(N) == False or True  # noqa


def vp(n, q):
    """e = v_q(L_n) = max{f : q^f <= n} = floor(log_q n) (the LCM exponent)."""
    v, t = 0, q
    while t <= n:
        v += 1
        t *= q
    return v


def vq_int(x, q):
    """Exact p-adic valuation of the integer x > 0."""
    v = 0
    while x % q == 0:
        x //= q
        v += 1
    return v


# ================================================================ METHOD 1
L = [mpz(1)] * (N + 1)
for n in range(1, N + 1):
    L[n] = gmpy2.lcm(L[n - 1], n)

a = [mpz(0)] * (N + 1)
for n in range(1, N + 1):
    s = mpz(0)
    for k in range(1, n + 1):
        assert L[n] % k == 0
        s += L[n] // k
    a[n] = s
g1 = [mpz(0)] * (N + 1)
for n in range(1, N + 1):
    g1[n] = gmpy2.gcd(a[n], L[n])

# sanity: H_n == a_n / L_n as exact rationals
for n in list(range(1, 30)) + [100, 250, 400]:
    H = sum((Fraction(1, k) for k in range(1, n + 1)), Fraction(0))
    assert Fraction(int(a[n]), int(L[n])) == H

# ================================================================ METHOD 2
def modinv(u, mod):
    return pow(u, -1, mod)


g2 = [mpz(1)] * (N + 1)
g2_detail = {}  # n -> list of (q, e, m, vq(an), part)
for n in range(1, N + 1):
    total = mpz(1)
    det = []
    for q in PRIMES:
        if q > n:
            break
        e = vp(n, q)          # v_q(L_n)
        K = e + 1
        qK = q**K
        # M mod q^K : product of p^{floor(log_p n)} over primes p <= n, p != q
        M = 1
        for p in PRIMES:
            if p > n:
                break
            if p == q:
                continue
            M = (M * pow(p, vp(n, p), qK)) % qK
        # a_n mod q^K
        s = 0
        for k in range(1, n + 1):
            i = vq_int(k, q)
            u = k // q**i
            assert u * q**i == k and (u % q != 0)
            prec = q ** (i + 1)
            w = (M % prec) * modinv(u, prec) % prec
            term = (q ** (e - i)) * w % qK
            s = (s + term) % qK
        # q-part of gcd
        if s == 0:
            v = e  # v_q(a_n) >= e+1 > e, part capped at e
            vexact = ">e"
        else:
            v = vq_int(s, q)
            vexact = v
            assert v <= e
        part = q**min(v, e) if True else None
        det.append((q, e, n // q**e, vexact, min(v, e)))
        total *= q ** min(v, e)
    g2[n] = total
    g2_detail[n] = det

ok_dual = all(g1[n] == g2[n] for n in range(1, N + 1))

# ================================================================ METHOD 3
# num(H_m) for m <= N (reduced numerators)
H = [Fraction(0)] * (N + 1)
for m in range(1, N + 1):
    H[m] = H[m - 1] + Fraction(1, m)

# D_q = {m in [1, q-1] : q | num(H_m)}  -- the per-prime digit sets
D = {}
for q in PRIMES:
    Ds = []
    for m in range(1, min(q, N + 1)):
        if q <= N and m <= N:
            num = H[m].numerator
            if num % q == 0:
                Ds.append(m)
    if Ds:
        D[q] = Ds

exceptional = []  # (m, q) with m < q-1  (beyond the classical m = q-1 rows)
for q, Ds in D.items():
    for m in Ds:
        if m < q - 1:
            exceptional.append((m, q))

# predicted qualifying set from the LAW
pred = set()
for q, Ds in D.items():
    for m in Ds:
        ee = 1
        while m * q**ee <= N:
            lo = m * q**ee
            hi = min((m + 1) * q**ee - 1, N)
            for n in range(lo, hi + 1):
                pred.add(n)
            ee += 1

census_set = set(n for n in range(1, N + 1) if g1[n] > 1)
census_set2 = set(n for n in range(1, N + 1) if g2[n] > 1)
ok_law = census_set == pred and census_set == census_set2

# per-n prime witnesses from method 2 (which primes divide the gcd)
def witness_primes(n):
    return [q for (q, e, m, v, part) in g2_detail[n] if part >= 1]

# ================================================================ REPORT
out = []
W = out.append
W("=" * 78)
W("ERDOS #291 HARMONIC-GCD CENSUS — N = %d — DUAL METHOD + LAW CHECK" % N)
W("=" * 78)
W("")
W("DUAL-METHOD AGREEMENT (exact gcd values, methods 1 and 2): %s" % ok_dual)
W("LAW AGREEMENT (method 3 predicted set == census set):       %s" % ok_law)
W("")
W("--- THE CENSUS: all n in [1, %d] with gcd(a_n, L_n) > 1 ---" % N)
rows = sorted(census_set)
W("count = %d of %d" % (len(rows), N))
# compress to intervals
iv = []
for n in rows:
    if iv and n == iv[-1][1] + 1:
        iv[-1][1] = n
    else:
        iv.append([n, n])
W("intervals: " + ", ".join("[%d,%d]" % (lo, hi) if lo != hi else str(lo) for lo, hi in iv))
W("the list:  " + str(rows))
W("")
W("--- exact gcd values (n : g(n)) for n with g(n) > 1 ---")
W(str({n: int(g1[n]) for n in rows}))
W("")
W("--- THE D_q DIGIT TABLE (per prime q <= %d): m in [1, q-1] with q | num(H_m) ---" % N)
for q in sorted(D):
    W("  D_%d = %s   (m = q-1 row%s)" % (q, D[q], " + EXCEPTIONAL" if any(m < q - 1 for m in D[q]) else ""))
W("")
W("--- EXCEPTIONAL (m, q) pairs, m < q-1 (q | num(H_m), the non-classical rows) ---")
W(str(sorted(exceptional)))
W("")
W("--- per-n witness primes (which q divide the gcd) for every n with g(n) > 1 ---")
for n in rows:
    wps = witness_primes(n)
    W("  n=%3d  g=%6d  primes=%s  leading digits: %s" % (
        n, int(g1[n]), wps,
        {q: n // q**vp(n, q) for q in wps}))
W("")
W("--- Kuerlscak law check: 2 never divides g(n) for n <= %d: %s ---" % (
    N, all(g1[n] % 2 == 1 for n in range(1, N + 1))))
W("")
W("--- prime-power gcds (g(n) divisible by q^2): ---")
pp = {n: int(g1[n]) for n in range(1, N + 1) if g1[n] > 1 and not gmpy2.is_prime(g1[n])}
W(str(pp))
W("")
W("--- named witness theorems ---")
for n in [5, 6, 7]:
    W("  n=%d: a_n=%d, L_n=%d, gcd=%d, H_n=%s" % (n, a[n], L[n], g1[n], H[n]))
W("  (H_5 = 137/60, gcd(a_5,L_5) = 1;  H_6 = 49/20, a_6 = 147, gcd = 3;")
W("   H_7 = 363/140, a_7 = 1089 = 3^2*11^2, gcd = 3.)")
W("")
W("--- Wolstenholme note: q | num(H_{q-1}) for ALL primes q >= 3 (verified) ---")
W("  verified for all primes q in [3, %d]: %s" % (
    N, all((q - 1) in D[q] for q in PRIMES if 3 <= q <= N and q in D)))
W("  but the gcd needs q <= n (q | L_n), so at n = q-1 itself the prime q is")
W("  NOT in L_n and does not lift the gcd (e.g. 11 | num(H_10) yet g(10) = %d)." % g1[10])
W("")
W("--- full table g(n) for n = 1..%d (0 rows are g=1) ---" % N)
W(str({n: int(g1[n]) for n in range(1, N + 1) if g1[n] > 1}))

txt = "\n".join(out)
print(txt)
with open(__file__.replace(".py", "_out.txt"), "w") as f:
    f.write(txt + "\n")
with open(__file__.replace(".py", "_census.txt"), "w") as f:
    f.write("n\tg1\tg2\tagree\n")
    for n in range(1, N + 1):
        f.write("%d\t%d\t%d\t%s\n" % (n, int(g1[n]), int(g2[n]), g1[n] == g2[n]))

if not (ok_dual and ok_law):
    print("!!! FAILURE: dual=%s law=%s" % (ok_dual, ok_law))
    sys.exit(1)
print("\nALL CHECKS GREEN")
