#!/usr/bin/env python3
"""ENGINE 461 ROUND 1 — Erdos-Graham #461: s_t(n) = t-smooth component;
f(n,t) = #distinct s_t(m) for m in [n+1, n+t].  Is f(n,t) >> t uniformly?
(Erdos-Graham: f(n,t) >> t/log t.)  Census: min_n f(n,t) for t = 2..120,
the minimizing windows, the ratio table — the evidence base."""
from collections import Counter

T_MAX = 120
N_MAX = 200000

# primes < T_MAX
def primes_below(n):
    sieve = [True]*n; sieve[0]=sieve[1]=False
    for i in range(2, int(n**0.5)+1):
        if sieve[i]:
            for j in range(i*i, n, i): sieve[j] = False
    return [i for i in range(n) if sieve[i]]

PRIMES = primes_below(T_MAX)

# per-t sieve of s_t over [1, N_MAX + T_MAX]
results = []
for t in range(2, T_MAX + 1):
    ps = [p for p in PRIMES if p < t] or [2]
    # wait: t >= 2 -> primes < t: t=2 -> none!  s_2(m) = product of 2-powers
    if t == 2:
        ps = [2]  # p < t means p < 2 -> NO primes; but s_t with no primes < t is 1 for all m
        # Erdos-Graham def: product of primes p | n with p < t.  t=2: no primes < 2 -> s=1 always -> f=1
        ps = []
    N = N_MAX
    s = [1] * (N + t + 1)
    for p in ps:
        pk = p
        while pk <= N + t:
            for m in range(pk, N + t + 1, pk):
                s[m] *= p
            pk *= p
    # sliding window distinct count over [n+1, n+t], n from 0..N-1
    # initialize window n=0: m in [1, t]
    cnt = Counter(s[1:t+1])
    f = len(cnt)
    best = (f, 0)
    for n in range(1, N):
        # remove s[n], add s[n+t]
        out = s[n]; inx = s[n+t]
        cnt[out] -= 1
        if cnt[out] == 0: del cnt[out]
        cnt[inx] += 1
        f = len(cnt)
        if f < best[0]:
            best = (f, n)
    results.append((t, best[0], best[1]))

print("t   min_n f(n,t)   argmin n   ratio f/t   t/log t   f/(t/log t)")
import math
for t, f, n in results:
    tl = t / math.log(t) if t > 1 else 0
    print(f"{t:>4} {f:>8} {n:>12} {f/t:>9.3f} {tl:>9.2f} {f/tl if tl else 0:>9.3f}")
