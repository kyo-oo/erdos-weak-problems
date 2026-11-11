#!/usr/bin/env python3
"""E11: DSC-UP greedy: keys DESCENDING k=n..1; a_k = smallest multiple of k that is > m and unused (bump UP by k)."""
import sys, random
from math import gcd
from functools import reduce
def lcm(a,b): return a*b//gcd(a,b)
random.seed(711711)

def dscup(n, m):
    W = 2*n-2; T = m+W
    used = set(); a=[0]*(n+1)
    for k in range(n, 0, -1):
        x = ((m//k)+1)*k
        while x in used:
            x += k
        if x > T: return False, None
        a[k]=x; used.add(x)
    # verify
    for k in range(1,n+1):
        if not (m < a[k] <= T and a[k]%k==0): return False, None
    if len(set(a[1:]))!=n: return False, None
    return True, a

def adversarial_ms(n):
    L = reduce(lcm, range(1, n+1), 1)
    ms=set(); base=(n-1)**2
    for j in range(-3,4): ms.add(base + j*(2*n-1))
    for d in range(-2*n, 3*n+1): ms.add(base+d)
    ms.update(range(1,60)); ms.add(n*n); ms.add(n*(n-1)); ms.add(L//2); ms.add(L); ms.add(base-(n-1)); ms.add(base+(n-1))
    for _ in range(300): ms.add(random.randint(1, max(10, base*3)))
    return [m for m in ms if m>=1]

tot=0; fails=[]
for n in range(2,13):
    L=reduce(lcm, range(1,n+1),1); per=min(L,27720); bad=0
    for m in range(1,per+1):
        ok,_=dscup(n,m); tot+=1
        if not ok: bad+=1; fails.append((n,m))
    print(f"n={n:2d}: full period {per}: DSC-UP failures: {bad}")
for n in range(13,17):
    ms = adversarial_ms(n)+[random.randint(1,10**7) for _ in range(3000)]
    bad=sum(0 if dscup(n,m)[0] else 1 for m in ms); tot+=len(ms)
    if bad: fails.append(('adv',n,bad))
    print(f"n={n}: adversarial+random {len(ms)}: failures {bad}")
for n in list(range(17,65))+[100,150,200,316,500,700,997]:
    ms = adversarial_ms(n)[:150]+[random.randint(1,10**9) for _ in range(250)]
    bad=sum(0 if dscup(n,m)[0] else 1 for m in ms); tot+=len(ms)
    if bad: print(f"n={n}: failures {bad}/{len(ms)}")
print("TOTAL", tot, "fails", len(fails), fails[:6])
