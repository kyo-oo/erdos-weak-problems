#!/usr/bin/env python3
"""
Erdos #456 census engine — the m_n / p_n witness table.

m_n := smallest m >= 1 with n | phi(m).
p_n := smallest prime p with p == 1 (mod n)   [i.e. n | p-1].

DUAL-METHOD (the census law):
  PHI-1: Euler product from an explicit factorization built with
         gmpy2.is_prime certification (every factor verified prime) and
         gmpy2 GMP mpz arithmetic.
  PHI-2: sympy.totient (independent implementation).
  Both must agree on EVERY m they are asked about; any disagreement aborts.

P-1: gmpy2.next_prime scanning with (p-1) % n == 0 test.
P-2: independent sympy.isprime scan over an explicit candidate stream
     (sympy primality = its own implementation); both must agree.

Outputs:
  census456.txt        : full table n = 1..N_MAX (m_n, p_n, sign)
  census456.json       : machine-readable mirror (for the Lean table + DERIVATION)
  witness456_60.txt    : the certified n <= 60 rows (m_n, p_n, sign)
  third_question.txt   : for every prime p <= (max n census)+1, the exact set
                         { n : m_n = p } and whether it equals {p-1}
"""
import json
import sys

import gmpy2
from sympy import totient as sym_totient, isprime as sym_isprime

N_MAX = 200          # the campaign census bound (mandated)
N_EXT = 1300         # extension bound for the third-question certificate

AGREE = {"n_checked": 0}


def factorize_gmpy2(m):
    """Factorization by trial division over gmpy2-certified primes.
    Returns dict prime->exponent; every prime verified with gmpy2.is_prime."""
    fac = {}
    x = int(m)
    p = 2
    while p * p <= x:
        if x % p == 0:
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            assert gmpy2.is_prime(p), f"non-prime factor {p}"
            fac[p] = e
        p = int(gmpy2.next_prime(p))
    if x > 1:
        assert gmpy2.is_prime(x), f"non-prime residual factor {x}"
        fac[x] = fac.get(x, 0) + 1
    return fac


def phi_gmpy2(m):
    """PHI-1: Euler product from the certified factorization."""
    if m == 1:
        return 1
    phi = 1
    for p, a in factorize_gmpy2(m).items():
        phi *= (p ** (a - 1)) * (p - 1)
    return phi


def phi_dual(m):
    """PHI-1 vs PHI-2 agreement gate; returns the certified phi(m)."""
    a = phi_gmpy2(m)
    b = int(sym_totient(int(m)))
    if a != b:
        sys.exit(f"PHI DUAL-METHOD FAILURE at m={m}: gmpy2-route={a} sympy={b}")
    AGREE["n_checked"] += 1
    return a


def p_of(n):
    """P-1: smallest prime p with n | p-1 (gmpy2 next_prime scan).
    P-2 cross-check: sympy isprime scan over the same residue stream."""
    p = 2
    while (p - 1) % n != 0:
        p = int(gmpy2.next_prime(p))
    # independent verification: p is prime by sympy AND no smaller prime works
    assert sym_isprime(p), f"P-2 primality failure at {p}"
    q = 2
    while q < p:
        if sym_isprime(q):
            assert (q - 1) % n != 0, f"P-2 failure: smaller prime {q} == 1 mod {n}"
        q += 1
    return p


def m_of(n, p_n):
    """m_n by direct scan m = 1,2,3,... until n | phi(m) (dual-gated).
    Bounded by p_n since phi(p_n) = p_n - 1 and n | p_n - 1."""
    m = 1
    while phi_dual(m) % n != 0:
        m += 1
        if m > p_n:
            sys.exit(f"m_n search overran p_n bound at n={n}")
    assert m <= p_n, "the m_n <= p_n law must hold"
    return m


def main():
    rows = {}
    print(f"=== Erdos456 census: n = 1..{N_EXT} (dual phi, dual p) ===")
    for n in range(1, N_EXT + 1):
        p_n = p_of(n)
        m_n = m_of(n, p_n)
        rows[n] = (m_n, p_n)
        if n <= N_MAX or n % 50 == 0:
            sign = "<" if m_n < p_n else ("=" if m_n == p_n else ">")
            print(f"n={n:4d}  m_n={m_n:5d}  p_n={p_n:5d}  sign={sign}")
    # the master law: m_n <= p_n for EVERY census row
    assert all(rows[n][0] <= rows[n][1] for n in rows), "LAW m_n <= p_n violated"

    with open("census456.json", "w") as f:
        json.dump({str(k): v for k, v in rows.items()}, f)

    with open("census456.txt", "w") as f:
        f.write("Erdos456 census n=1..%d: m_n (smallest m with n|phi(m)), "
                "p_n (smallest prime = 1 mod n)\n" % N_EXT)
        f.write("n\tm_n\tp_n\tsign\n")
        for n in range(1, N_EXT + 1):
            m_n, p_n = rows[n]
            sign = "<" if m_n < p_n else ("=" if m_n == p_n else ">")
            f.write(f"{n}\t{m_n}\t{p_n}\t{sign}\n")

    # the n <= 200 headline statistics
    n_strict = [n for n in range(1, N_MAX + 1) if rows[n][0] < rows[n][1]]
    n_eq = [n for n in range(1, N_MAX + 1) if rows[n][0] == rows[n][1]]
    n_gt = [n for n in range(1, N_MAX + 1) if rows[n][0] > rows[n][1]]
    assert not n_gt, "m_n > p_n is impossible by the general law"
    print("\n=== HEADLINE (n <= %d) ===" % N_MAX)
    print(f"strict m_n < p_n : {len(n_strict)} of {N_MAX}")
    print(f"equality m_n = p_n: {len(n_eq)} of {N_MAX}")
    print(f"strict n list: {n_strict}")
    print(f"equality n list: {n_eq}")

    # prime-n law check: for prime q, m_q = min(p_q, q^2)?
    plaw_ok = True
    for q in range(2, N_MAX + 1):
        if gmpy2.is_prime(q):
            expect = min(rows[q][1], q * q)
            if rows[q][0] != expect:
                plaw_ok = False
                print(f"PRIME-LAW EXCEPTION: q={q} m={rows[q][0]} "
                      f"expected min(p={rows[q][1]}, q^2)={expect}")
    print(f"prime-n law (m_q = min(p_q, q^2)) holds for all primes q <= {N_MAX}: "
          f"{plaw_ok}")

    # third question: primes p such that {n : m_n = p} == {p-1}
    # m_n = p forces n | phi(p) = p-1, so n <= p-1 <= N_EXT covers ALL of them
    # for every p <= N_EXT + 1.
    with open("third_question.txt", "w") as f:
        f.write("Erdos456 Q3 census (exact for primes p <= %d):\n" % (N_EXT + 1))
        f.write("m_n = p forces n | p-1; all divisors checked against the full "
                "census n <= %d.\n\n" % N_EXT)
        f.write("p\tset{n : m_n = p}\tis_exactly_{p-1}\n")
        q3_yes, q3_no = [], []
        for p in range(2, N_EXT + 2):
            if gmpy2.is_prime(p):
                hitset = [n for n in range(1, N_EXT + 1) if rows[n][0] == p]
                # completeness: any further n with m_n = p must divide p-1
                divs = [d for d in range(1, p) if (p - 1) % d == 0]
                assert set(hitset) <= set(divs), f"Q3 gate failed at p={p}"
                ok = hitset == [p - 1]
                (q3_yes if ok else q3_no).append(p)
                f.write(f"{p}\t{hitset}\t{ok}\n")
        f.write(f"\nYES (p-1 is the ONLY n with m_n = p): {q3_yes}\n")
        f.write(f"count: {len(q3_yes)} of {len(q3_yes)+len(q3_no)} primes <= "
                f"{N_EXT+1}\n")
    print(f"\n=== Q3 (p <= {N_EXT+1}): {len(q3_yes)} primes with "
          f"{{n : m_n=p}} == {{p-1}} ===")
    print(f"YES list: {q3_yes}")

    # the n <= 60 certified witness table (Lean mirror input)
    with open("witness456_60.txt", "w") as f:
        f.write("n\tm_n\tp_n\tsign\n")
        for n in range(1, 61):
            m_n, p_n = rows[n]
            sign = "<" if m_n < p_n else "="
            f.write(f"{n}\t{m_n}\t{p_n}\t{sign}\n")
    print(f"\ndual-gated phi checks performed: {AGREE['n_checked']}")
    print("CENSUS COMPLETE — all dual-method gates green.")


if __name__ == "__main__":
    main()
