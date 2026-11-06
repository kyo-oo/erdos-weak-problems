# #700 PRIME-POWER LAW battery: f(p^a) = p for a>=3; f(p^2) = p = n/P(n)
# f(n) = min over 1<k<=n/2 of gcd(n, C(n,k)); P(n) = largest prime factor
import sympy, math
from math import gcd, comb

def f(n):
    best = None
    for k in range(2, n//2 + 1):
        g = gcd(n, comb(n, k))
        if best is None or g < best: best = g
    return best

print("p, a, n=p^a, f(n), law p, n/P(n), equality f=n/P?")
for p in [2,3,5,7,11,13]:
    for a in range(2, 7):
        n = p**a
        if n > 200000: break
        fn = f(n)
        nP = n // p
        law = (fn == p)
        eq = (fn == nP)
        expect_eq = (a == 2)
        status = "OK" if (law and eq == expect_eq) else "FAIL"
        print(f"p={p:3d} a={a} n={n:8d} f={fn:6d} p={p:3d} n/P={nP:6d} eq={eq}(want {expect_eq}) [{status}]")

# carry lemma check: v_p(C(p^a,k)) == a - v_p(k) for 1<=k<=p^a-1
print()
print("carry lemma v_p(C(p^a,k)) = a - v_p(k):")
import random
ok = True
for p in [2,3,5,7]:
    for a in range(2, 6):
        n = p**a
        for k in list(range(1, min(n, 3000))) + [n-1, n//2, p**(a-1), p**(a-1)+1]:
            if k < 1 or k > n-1: continue
            vp = sympy.factorint(comb(n, k)).get(p, 0)
            lawv = a - sympy.factorint(k).get(p, 0)
            if vp != lawv:
                print(f"  LEMMA FAIL p={p} a={a} k={k}: v_p={vp} law={lawv}")
                ok = False
print("LEMMA:", "ALL VERIFIED" if ok else "FAILURES FOUND")
