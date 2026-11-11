# FAST CI battery: carry lemma (Legendre, 79k instances) + f-table p<=7
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
import sys
ok = True
# Part 1: carry lemma sweep
tested = 0
for p in [2,3,5,7,11,13]:
    for a in range(2, 8):
        n = p**a
        for k in range(1, min(n, 5000)):
            if vp_binom(n, k, p) != a - vp_of(k, p):
                print(f"CARRY FAIL p={p} a={a} k={k}"); ok = False; break
            tested += 1
        if not ok: break
    if not ok: break
print(f"carry lemma: {tested} instances {'ALL VERIFIED' if ok else 'FAILURES'}")
# Part 2: f-table (exact binomial gcds, small p)
from math import comb, gcd
for p in [2,3,5,7]:
    for a in range(2, 6):
        n = p**a
        best = min(gcd(n, comb(n, k)) for k in range(2, n//2 + 1))
        want_eq = (a == 2)
        if best != p or ((best == n // p) != want_eq):
            print(f"LAW FAIL p={p} a={a} f={best}"); ok = False
        else:
            print(f"p={p} a={a} n={n}: f={best}=p, equality {'HOLDS' if want_eq else 'fails'} [OK]")
print("BATTERY 700:", "GREEN" if ok else "RED")
sys.exit(0 if ok else 1)
