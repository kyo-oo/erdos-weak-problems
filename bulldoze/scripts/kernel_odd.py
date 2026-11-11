#!/usr/bin/env python3
"""STRIDE B: odd-p kernel law discovery.
K_p(u) := v_p(sum_{a=u}^{infty} a!) computed with EXACT certificate:
stop when v_p((N+1)!) > v_p(partial): then final valuation = v_p(partial).
k_p(u) := K_p(u) - v_p(u!).  Target: closed form for k_p."""
import math

def vp(n, p):
    if n == 0: return 10**9
    v = 0
    while n % p == 0:
        n //= p; v += 1
    return v

def vfact(n, p):
    v = 0; q = p
    while q <= n:
        v += n // q; q *= p
    return v

def K(u, p, maxN=4000):
    """Certified v_p(sum_{a=u}^{N} a!) for large N with stabilization certificate."""
    s = 0
    for a in range(u, maxN):
        s += math.factorial(a)
        # certificate: next increment is (a+1)!, valuation vfact(a+1,p)
        v = vp(s, p)
        if v < vfact(a + 1, p):
            return v, a  # stable value, certified at N=a
    return None, None

print("k_p(u) = K_p(u) - v_p(u!)  [the kernel: v_p of B(u)]")
print("=" * 78)
for p in [2, 3, 5, 7, 11, 13]:
    print(f"\np = {p}:  k_p(u) for u = 0..{40}:")
    row = []
    for u in range(0, 41):
        Kv, cert = K(u, p)
        kf = vfact(u, p)
        row.append(Kv - kf)
    print("  ", row)
    # residue pattern
    print("   nonzero k at u =", [u for u in range(41) if row[u] > 0])
