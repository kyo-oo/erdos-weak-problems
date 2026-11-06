# carry lemma via Legendre: v_p(C(p^a,k)) = a - v_p(k)
def vp_fact(m, p):
    s = 0
    while m: m //= p; s += m
    return s
def vp_binom(n, k, p):
    return vp_fact(n, p) - vp_fact(k, p) - vp_fact(n-k, p)
def vp_of(k, p):
    c = 0
    while k % p == 0: k //= p; c += 1
    return c
ok = True; tested = 0
for p in [2,3,5,7,11,13]:
    for a in range(2, 8):
        n = p**a
        for k in range(1, min(n, 5000)):
            vp = vp_binom(n, k, p)
            lawv = a - vp_of(k, p)
            tested += 1
            if vp != lawv:
                print(f"FAIL p={p} a={a} k={k}: v_p={vp} law={lawv}"); ok = False; break
        if not ok: break
    if not ok: break
print(f"carry lemma: {tested} instances, {'ALL VERIFIED' if ok else 'FAILURES'}")
# also spot-check vs exact binomials for small n
from math import comb, gcd
import sympy
for p in [2,3,5]:
    for a in range(2,5):
        n = p**a
        for k in [1, 2, 3, p, p**max(0,a-1), n//2, n-1]:
            if not (1 <= k <= n-1): continue
            exact = sympy.factorint(comb(n,k)).get(p,0)
            fast = vp_binom(n,k,p)
            if exact != fast: print("MISMATCH exact-vs-Legendre", p,a,k); ok=False
print("Legendre-vs-exact cross-check:", "OK" if ok else "FAIL")
