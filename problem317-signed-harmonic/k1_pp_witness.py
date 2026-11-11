#!/usr/bin/env python3
"""S27-BETA2 supplement — Theorem A' (prime-power witnesses) at the 37
largest-window-prime-degenerate n's found <= 300k.

Theorem A': if m = q^a (a>=2) lies in (n/2, n] and u := (L_n/m) mod q is not in
{1, q-1}, then m is a WITNESS: no delta in {-1,0,1}^n gives sum = +-1/L_n.
  Proof: v_q(L_n) = a and the only k <= n with v_q(k) = a is k = m (2m > n),
  so M = sum delta_k L_n/k  ==  delta_m * (L_n/m)  (mod q).  QED
Note q = 2 is always degenerate (u odd = 1); q = 3 is ALWAYS degenerate
(u not divisible by 3 => u mod 3 in {1,2} = {+-1}).

Exact computation of u mod q: maintain Mk = L_n mod K where
K = prod over primes q <= sqrt(NMAX) of q^{a_max(q)+1}, using Lemma U
(Mk *= base(n) mod K at prime powers).  Then for m = q^a in (n/2,n]:
  u mod q = ( (Mk mod q^{a+1}) // q^a ) mod q,  since L_n = q^a*u, q ∤ u.
"""
import math

NMAX = 16000
audit_ns = [8, 11, 12, 29, 30, 169, 170, 171, 172, 343, 344, 345, 346] + \
           list(range(787, 797)) + list(range(15773, 15787))

s = bytearray([1]) * (NMAX + 1); s[0:2] = b"\x00\x00"
for i in range(2, math.isqrt(NMAX) + 1):
    if s[i]:
        s[i*i::i] = bytearray(len(s[i*i::i]))
primes = [i for i in range(2, NMAX + 1) if s[i]]

# K = prod q^(a_max+1), q <= sqrt(NMAX), q^amax <= NMAX
SQ = math.isqrt(NMAX)
K = 1
ppow = {}                      # value -> base  (a >= 2)
for q in primes:
    if q > SQ: break
    m = q * q; a = 2
    while m <= NMAX:
        ppow[m] = q; m *= q; a += 1
    K *= q ** a                # q^(a_max+1)
# also primes q <= sqrt with q^2 > NMAX don't exist; fine.

def win_prime_powers(n):
    return [m for m in ppow if n // 2 < m <= n]

Mk = 1
rows = {}
primeset = set(primes)
for n in range(2, NMAX + 1):
    if n in ppow:                    # n = q^a, a >= 2:  L_n = q * L_{n-1}
        Mk = (Mk * ppow[n]) % K
    elif n in primeset:              # n = q^1:          L_n = q * L_{n-1}
        Mk = (Mk * n) % K
    if n in audit_ns:
        ev = []
        for m in win_prime_powers(n):
            q = ppow[m]
            qa = q                        # q^(a+1) mod ...
            t = m
            while t * q <= NMAX * 2 and t * q <= K:  # q^(a+1) as far as tracked
                t *= q
            # q^(a+1) dividing K: since q^(a_max+1) | K and m <= NMAX => a <= a_max
            modp = q
            while modp <= m: modp *= q    # modp = q^(a+1)
            u = ((Mk % modp) // m) % q    # m = q^a
            deg = (u == 1 or u == q - 1)
            ev.append((m, q, u, "DEGEN" if deg else "WITNESS"))
        rows[n] = ev

for n in sorted(rows):
    if rows[n]:
        print(f"n={n}: " + "  ".join(f"{m}={q}^{round(math.log(m,q))}:u={u} {tag}"
                                     for (m, q, u, tag) in rows[n]))
    else:
        print(f"n={n}: (no prime power in window)")
