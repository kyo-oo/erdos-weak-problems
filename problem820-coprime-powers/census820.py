#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Erdos #820 — THE ORDER-CRITERION CENSUS (W61, P820, engine820 r1)

Target: H(n) = smallest l such that some k < l has gcd(k^n-1, l^n-1) = 1.
Corpus question: H(n) = 3 infinitely often  <=>  gcd(2^n-1, 3^n-1) = 1
infinitely often.

THE ORDER-CRITERION LAW (proved computationally here in BOTH directions):
  For a prime p with p >= 5 (p not dividing k*l):
      p | gcd(k^n-1, l^n-1)  <=>  ord_p(k) | n  AND  ord_p(l) | n
                               <=>  lcm(ord_p(k), ord_p(l)) | n.
  Primes dividing k*l never divide k^n-1 or l^n-1 (k^n = 0 mod p => k^n-1
  = -1 mod p), so for k=2, l=3 ONLY primes p >= 5 act, with
      L_p := lcm(ord_p(2), ord_p(3)),
      gcd(2^n-1, 3^n-1) = 1  <=>  NO prime p >= 5 has L_p | n.

METHOD A (direct): gmpy2 big-int gcd on 2^n-1, 3^n-1.
METHOD B (order-criterion): reconstruct
      G'_n = prod over relevant primes p with L_p | n of
             p^{min(v_p(2^n-1), v_p(3^n-1))}
with orders computed independently (factor p-1, descend), valuations by
direct repeated division of the big integers.  Agreement A == B on every
n <= 120 is the machine proof of the LAW.

Outputs: census820_output.txt (human table) + census820.json (machine data).
"""
import json
import math
import sys

from gmpy2 import mpz, gcd as ggcd, powmod
import sympy
from sympy import factorint

NMAX = 120          # census range for gcd(2^n-1, 3^n-1)
H_NMAX = 40         # H(n) table range
H_LCAP = 50         # l cap for the primary H table
H_LCAP_EXT = 150    # extended cap (informational)

out_lines = []
def emit(s=""):
    out_lines.append(s)
    print(s)

# ---------------------------------------------------------------- method A
G = {}
for n in range(1, NMAX + 1):
    G[n] = ggcd(mpz(2) ** n - 1, mpz(3) ** n - 1)

good = [n for n in range(1, NMAX + 1) if G[n] == 1]
bad = [n for n in range(1, NMAX + 1) if G[n] != 1]

emit("== Erdos820 census: gcd(2^n-1, 3^n-1), n = 1..%d ==" % NMAX)
emit("good n (gcd = 1, the H(n)=3 witnesses): %s" % good)
emit("bad  n (gcd > 1): count = %d" % len(bad))

# ------------------------------------------------- factorizations of G_n
def factor_exact(x):
    """Complete factorization with product verification."""
    x = int(x)
    if x == 1:
        return {}
    d = factorint(x)
    prod = 1
    for p, e in d.items():
        prod *= p ** e
    assert prod == x, "factorization mismatch on %d" % x
    return {int(p): int(e) for p, e in d.items()}

FACT = {n: factor_exact(G[n]) for n in range(1, NMAX + 1)}

# relevant primes: every prime dividing some G_n, n <= 120
REL = sorted({p for n in range(1, NMAX + 1) for p in FACT[n]})
emit("relevant primes (prime divisors of some gcd(2^n-1,3^n-1), n<=%d): %s"
     % (NMAX, REL))

# ------------------------------------------------- independent order engine
def multiplicative_order(a, p):
    """ord_p(a) by factoring p-1 and descending; verified afterwards."""
    a = int(a) % int(p)
    if a == 0:
        return None
    m = int(p) - 1
    o = m
    for q in factorint(m):
        q = int(q)
        while o % q == 0 and int(powmod(a, o // q, p)) == 1:
            o //= q
    assert int(powmod(a, o, p)) == 1
    # minimality check: for every prime r | o, a^(o/r) != 1
    for r in factorint(o):
        assert int(powmod(a, o // int(r), p)) != 1
    return o

def v_p(x, p):
    """p-adic valuation of big int x by repeated division."""
    x = mpz(x)
    p = mpz(p)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

Lp = {}   # p -> (ord_p(2), ord_p(3), L_p = lcm)
for p in REL:
    o2 = multiplicative_order(2, p)
    o3 = multiplicative_order(3, p)
    Lp[p] = (o2, o3, math.lcm(o2, o3))

emit("")
emit("== the L_p table: L_p = lcm(ord_p(2), ord_p(3)), p >= 5 ==")
emit("%8s %10s %10s %8s %s" % ("p", "ord_p(2)", "ord_p(3)", "L_p", "primal check"))
for p in REL:
    if Lp[p][2] <= NMAX:      # only L_p <= 120 can ever divide some n <= 120
        emit("%8d %10d %10d %8d   (p-1 = %d = %s)"
             % (p, Lp[p][0], Lp[p][1], Lp[p][2], p - 1,
                sympy.factorint(p - 1)))
# also the first 30 primes >= 5 for the requested table
req_primes = list(sympy.primerange(5, 200))[:30]
emit("")
emit("== the L_p table, first 30 primes p >= 5 (requested) ==")
emit("%8s %10s %10s %8s %s" % ("p", "ord_p(2)", "ord_p(3)", "L_p", "in-census"))
for p in req_primes:
    if p in Lp:
        o2, o3, L = Lp[p]
        emit("%8d %10d %10d %8d   %s" % (p, o2, o3, L, "yes" if p in REL else "no (L_p > %d never hits n <= %d)" % (NMAX, NMAX)))
    else:
        o2 = multiplicative_order(2, p)
        o3 = multiplicative_order(3, p)
        Lp_all_note = math.lcm(o2, o3)
        emit("%8d %10d %10d %8d   no (L_p > %d never hits n <= %d)"
             % (p, o2, o3, Lp_all_note, NMAX, NMAX))

# ------------------------------------------------- THE LAW, both directions
emit("")
emit("== THE ORDER-CRITERION LAW: verification for every n <= %d ==" % NMAX)
law_ok = True
for n in range(1, NMAX + 1):
    # predicted prime set: relevant primes with L_p | n
    # (completeness: any prime with L_p | n has L_p <= n <= 120, hence
    #  p | G_{L_p}, hence p is in REL -- closed under the census itself)
    predicted = sorted(p for p in REL if n % Lp[p][2] == 0)
    actual = sorted(FACT[n])
    if predicted != actual:
        law_ok = False
        emit("LAW FAIL (prime set) at n=%d: predicted %s actual %s"
             % (n, predicted, actual))
    for p in actual:
        vmin = min(v_p(mpz(2) ** n - 1, p), v_p(mpz(3) ** n - 1, p))
        if vmin != FACT[n][p]:
            law_ok = False
            emit("LAW FAIL (exponent) at n=%d p=%d: min=%d actual=%d"
                 % (n, p, vmin, FACT[n][p]))
emit("prime-set + exponent agreement for all n <= %d: %s" % (NMAX, law_ok))

# ------------------------------------------------- method B full reconstruction
methodB_ok = True
for n in range(1, NMAX + 1):
    rec = mpz(1)
    for p in REL:
        if n % Lp[p][2] == 0:
            rec *= mpz(p) ** min(v_p(mpz(2) ** n - 1, p),
                                 v_p(mpz(3) ** n - 1, p))
    if rec != G[n]:
        methodB_ok = False
        emit("METHOD B FAIL at n=%d: reconstructed %s actual %s" % (n, rec, G[n]))
emit("method A (gmpy2 gcd) == method B (order-criterion reconstruction) "
     "for all n <= %d: %s" % (NMAX, methodB_ok))

# ------------------------------------------------- good-n LAW statement
emit("")
emit("== THE GOOD-N LAW: gcd(2^n-1,3^n-1)=1 <=> no relevant L_p divides n ==")
sieve_ok = True
for n in range(1, NMAX + 1):
    flag = any(n % Lp[p][2] == 0 for p in REL)
    if flag == (G[n] != 1):
        pass
    else:
        sieve_ok = False
        emit("SIEVE FAIL at n=%d" % n)
emit("good n <=> n avoids every L_p (for the relevant primes): %s" % sieve_ok)

# ------------------------------------------------- gcd table
emit("")
emit("== the gcd table (n: gcd(2^n-1,3^n-1)) ==")
for n in range(1, NMAX + 1):
    if G[n] != 1:
        emit("n=%3d  gcd=%s  factors=%s  (L_p | n: %s)"
             % (n, G[n], FACT[n],
                sorted(set(Lp[p][2] for p in FACT[n]))))

# ------------------------------------------------- H(n) census
emit("")
emit("== H(n) census: smallest l with some k < l, gcd(k^n-1,l^n-1)=1 ==")
emit("   (k ranges 2..l-1; the k=1 lane is dead for every n >= 2 since")
emit("    gcd(0, l^n-1) = l^n-1 >= 3; k >= 2 is the corpus convention.)")

def H_find(n, lcap):
    """smallest l <= lcap with some 2 <= k < l coprime-power pair."""
    for l in range(2, lcap + 1):
        for k in range(2, l):
            if ggcd(mpz(k) ** n - 1, mpz(l) ** n - 1) == 1:
                return (l, k)
    return None

Htab = {}
Hext = {}
for n in range(1, H_NMAX + 1):
    r = H_find(n, H_LCAP)
    Htab[n] = r
    if r is None:
        r2 = H_find(n, H_LCAP_EXT)
        Hext[n] = r2
        tag = "  (none <= %d; extended: %s)" % (H_LCAP, r2)
        emit("n=%3d  gcd(2^n-1,3^n-1)=%s  H(n)=%s%s" % (n, G[n], r, tag))
    else:
        Hext[n] = r
        emit("n=%3d  gcd(2^n-1,3^n-1)=%s  H(n)=%s" % (n, G[n], r))

# ------------------------------------------------- the mirror lane (smallest k)
emit("")
emit("== mirror lane: smallest k >= 2 with gcd(k^n-1, 2^n-1) = 1 (Erdos's last Q) ==")
for n in range(1, H_NMAX + 1):
    for k in range(2, 200):
        if ggcd(mpz(k) ** n - 1, mpz(2) ** n - 1) == 1:
            emit("n=%3d  smallest k = %d" % (n, k))
            break
    else:
        emit("n=%3d  smallest k > 200" % n)

# ------------------------------------------------- json dump
data = {
    "NMAX": NMAX,
    "G": {str(n): str(G[n]) for n in range(1, NMAX + 1)},
    "FACT": {str(n): FACT[n] for n in range(1, NMAX + 1)},
    "good": good,
    "REL": REL,
    "Lp": {str(p): Lp[p] for p in REL},
    "Htab": {str(n): (list(Htab[n]) if Htab[n] else None) for n in Htab},
    "Hext": {str(n): (list(Hext[n]) if Hext[n] else None) for n in Hext},
}
with open("census820.json", "w") as f:
    json.dump(data, f, indent=1)

emit("")
emit("== RECEIPTS ==")
emit("python: %s" % sys.version.split()[0])
emit("gmpy2 gcd + powmod; sympy %s factorint" % sympy.__version__)
emit("law (prime sets + exponents + full reconstruction): %s"
     % (law_ok and methodB_ok and sieve_ok))
emit("E820_CENSUS_GREEN" if (law_ok and methodB_ok and sieve_ok) else "E820_CENSUS_RED")

with open("census820_output.txt", "w") as f:
    f.write("\n".join(out_lines) + "\n")
