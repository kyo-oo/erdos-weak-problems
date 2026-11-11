#!/usr/bin/env python3
"""P677 k=3 convergent-band resolution (PROOF.md §4).

k=3 collision equation reduces EXACTLY to the single Thue equation
    w^3 - w = 2(u^3 - u),   u = n+2 (even), w = m+2 (odd), w >= u+5.
BAND THEOREM (proved in PROOF.md §4.1): every integer solution with w > u >= 4
satisfies 0 < 2^{1/3}u - w <= 0.1596/u, hence w/u is a CONVERGENT of 2^{1/3}
(Legendre: |c - w/u| < 0.5/u^2). This script:
  (1) computes the CF of 2^{1/3} rigorously (interval method, exact rationals),
      convergents p/q with q <= LIMIT (default 10^150);
  (2) for each convergent tests w in {p-2..p+2} EXACTLY in the Thue equation;
  (3) reports all solutions; collision-admissible ones need w>=u+5.
Also handles u in {1,2,3} directly.
"""
from fractions import Fraction
import sys

def iroot3(n):
    if n == 0: return 0
    x = 1 << ((n.bit_length() + 2) // 3 + 1)
    while True:
        y = (2*x + n // (x*x)) // 3
        if y >= x: break
        x = y
    while x**3 > n: x -= 1
    while (x+1)**3 <= n: x += 1
    return x

def cf_cbrt2(ndigits):
    """Rigorous CF of 2^(1/3): common prefix of CFs of lo=A/10^d, hi=(A+1)/10^d."""
    d = ndigits; B = 10**d
    A = iroot3(2 * B**3)
    assert A**3 <= 2*B**3 < (A+1)**3
    lo = Fraction(A, B); hi = Fraction(A+1, B)
    def cf_terms(fr):
        terms = []
        a, b = fr.numerator, fr.denominator
        while b:
            q, r = divmod(a, b)
            terms.append(q); a, b = b, r
        return terms
    # parallel: emulate Euclid on both, stop at first difference
    terms = []
    a1, b1 = lo.numerator, lo.denominator
    a2, b2 = hi.numerator, hi.denominator
    while b1 and b2:
        q1, r1 = divmod(a1, b1)
        q2, r2 = divmod(a2, b2)
        if q1 != q2: break
        terms.append(q1)
        a1, b1 = b1, r1
        a2, b2 = b2, r2
        if len(terms) > 100000: break
    return terms

def convergents(terms, qlimit):
    p0, p1 = 0, 1
    q0, q1 = 1, 0
    out = []
    for a in terms:
        p0, p1 = p1, a*p1 + p0
        q0, q1 = q1, a*q1 + q0
        if q1 > qlimit: break
        out.append((p1, q1))
    return out

def solve_k3(qlimit_digits=150, verbose=True):
    LIMIT = 10**qlimit_digits
    terms = cf_cbrt2(qlimit_digits*3 + 60)
    convs = convergents(terms, LIMIT)
    if verbose:
        print(f"CF of 2^(1/3): {len(terms)} rigorous terms; {len(convs)} convergents with q <= 10^{qlimit_digits}")
        print("first terms:", terms[:20])
    sols = []
    # small u direct
    for u in (1, 2, 3):
        for w in range(u+1, 20):
            if w**3 - w == 2*(u**3 - u): sols.append((u, w, 'small'))
    # convergent band
    for (p, q) in convs:
        if q < 4: continue
        for w in range(p-2, p+3):
            if w > q and w**3 - w == 2*(q**3 - q):
                sols.append((q, w, 'convergent'))
    return sols, len(convs)

if __name__ == "__main__":
    digits = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    sols, nconv = solve_k3(digits)
    print(f"solutions (u,w) of w^3-w = 2(u^3-u) with 1<=u<w<={10}^{digits}: {sols}")
    # collision admissibility: u=n+2 even => u%4==0; w odd; w>=u+5
    adm = [s for s in sols if s[0] % 4 == 0 and s[1] % 2 == 1 and s[1] >= s[0] + 5]
    print(f"collision-admissible (u%4==0, w odd, w>=u+5): {adm}")
    print(f"=> k=3: {'NO COLLISION' if not adm else 'COLLISION FOUND: ' + str(adm)} (u <= 10^{digits})")
