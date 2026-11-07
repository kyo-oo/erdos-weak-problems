# CI battery for #700 (dual-method, budget-tight):
#  Part 1: the carry lemma v_p(C(p^a,k)) = a - v_p(k) — Legendre-method sweep
#          vs the law prediction (79k+ instances, pure arithmetic, seconds).
#  Part 2: the f-law f(p^a) = p by EXACT binomial gcd sweeps, cross-checked
#          against the ErSz equality condition (n <= 2048 cap: CI-budget tight).
import sys
from math import comb, gcd

def vp_fact(m, p):
    s = 0
    while m:
        m //= p
        s += m
    return s

def vp_binom(n, k, p):
    return vp_fact(n, p) - vp_fact(k, p) - vp_fact(n - k, p)

def vp_of(k, p):
    c = 0
    while k % p == 0:
        k //= p
        c += 1
    return c

ok = True

# Part 1: carry lemma sweep (Legendre method vs a - v_p(k))
tested = 0
for p in [2, 3, 5, 7, 11, 13]:
    for a in range(2, 8):
        n = p ** a
        for k in range(1, min(n, 5000)):
            if vp_binom(n, k, p) != a - vp_of(k, p):
                print(f"CARRY FAIL p={p} a={a} k={k}")
                ok = False
                break
            tested += 1
        if not ok:
            break
    if not ok:
        break
print(f"carry lemma: {tested} instances {'ALL VERIFIED' if ok else 'FAILURES'}")

# Part 2: f-table by exact gcd sweeps (dual method: sweep value vs law p and
# the ErSz equality f = n/P(n) which must hold exactly at a = 2, fail for a>=3)
for p in [2, 3, 5, 7, 11, 13]:
    a = 2
    while p ** a <= 2048:
        n = p ** a
        best = min(gcd(n, comb(n, k)) for k in range(2, n // 2 + 1))
        want_eq = (a == 2)
        if best != p or ((best == n // p) != want_eq):
            print(f"LAW FAIL p={p} a={a} n={n} f={best}")
            ok = False
        else:
            print(f"p={p} a={a} n={n}: f={best}=p, equality "
                  f"{'HOLDS' if want_eq else 'fails'} [OK]")
        a += 1

print("BATTERY 700:", "GREEN" if ok else "RED")
sys.exit(0 if ok else 1)
