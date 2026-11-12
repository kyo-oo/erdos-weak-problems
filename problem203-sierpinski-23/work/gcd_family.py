import math, time
t0 = time.time()
for L in (5040, 10080, 2520, 27720):
    N2 = (1 << L) - 1
    N3 = 3**L - 1
    G = math.gcd(N2, N3)
    print(f"L={L}: gcd(2^L-1,3^L-1) has {len(str(G))} digits, log2 ~ {G.bit_length()}")
    # trial divide by small primes to see the small-factor structure quickly
    g = G
    small = []
    d = 2
    import sympy
    # strip all primes below 100000 via sieve
    lim = 100000
    sieve = list(range(lim+1))
    for i in range(2, int(lim**0.5)+1):
        if sieve[i] == i:
            for j in range(i*i, lim+1, i):
                if sieve[j] == j: sieve[j] = i
    for p in range(5, lim+1):
        if sieve[p] == p:
            e = 0
            while g % p == 0:
                g //= p; e += 1
            if e: small.append((p, e))
    print(f"  small primes (<1e5) dividing: {len(small)} primes, stripped sum 1/h of distinct:", 
          sum(1.0/p for p,e in small))
    print("  small factors:", small[:60])
    print(f"  residual cofactor: {g.bit_length()} bits")
    print(f"  time: {time.time()-t0:.1f}s")
