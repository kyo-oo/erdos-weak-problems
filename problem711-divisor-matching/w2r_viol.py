#!/usr/bin/env python3
"""Find the ACTUAL violations of Theorem U (f(n,m) <= 2n-1) for large n:
 extract violating m's, deficient sets S (min |N(S)|-|S|), and f(n,m) exact there."""
import sys, random
from math import gcd
from functools import reduce
def lcm(a,b): return a*b//gcd(a,b)
random.seed(711)

def hopcroft(L,R,adj):
    INF=float('inf'); pairL={l:None for l in L}; pairR={r:None for r in R}; dist={}
    def bfs():
        q=[]; found=False
        for l in L:
            if pairL[l] is None: dist[l]=0; q.append(l)
            else: dist[l]=INF
        qi=0
        while qi<len(q):
            l=q[qi]; qi+=1
            for r in adj[l]:
                lr=pairR[r]
                if lr is None: found=True
                elif dist.get(lr,INF)==INF: dist[lr]=dist[l]+1; q.append(lr)
        return found
    def dfs(l):
        for r in adj[l]:
            lr=pairR[r]
            if lr is None or (dist.get(lr,INF)==dist[l]+1 and dfs(lr)):
                pairL[l]=r; pairR[r]=l; return True
        dist[l]=INF; return False
    m=0
    while bfs():
        for l in L:
            if pairL[l] is None and dfs(l): m+=1
    return m, pairL

def assign_exists(n,m,F):
    ints=list(range(m+1,m+F)); adj={k:set(x for x in ints if x%k==0) for k in range(1,n+1)}
    for k in adj:
        if not adj[k]: return False
    sz,_=hopcroft(range(1,n+1),ints,adj)
    return sz==n

def f_exact(n,m,Fmax):
    lo,hi=1,Fmax
    if not assign_exists(n,m,Fmax): return None
    while lo<hi:
        mid=(lo+hi)//2
        if assign_exists(n,m,mid): hi=mid
        else: lo=mid+1
    return lo

def deficient(n,m,W=0):
    """window (m, m+2n-1): find set S minimizing |N(S)|-|S| via Konig: min vertex cover.
       Deficiency = |S| - |N(S)| max = n - maxmatching (if N-side smaller...). Compute min over S."""
    if W==0: W=2*n-2
    ints=list(range(m+1,m+W+1)); adj={k:set(x for x in ints if x%k==0) for k in range(1,n+1)}
    sz,pairL=hopcroft(range(1,n+1),ints,adj)
    return n-sz, pairL

def adversarial(n):
    ms=set(); base=(n-1)**2
    for j in range(-2,3): ms.add(base+j*(2*n-1))
    for d in range(-3*n,3*n+1): ms.add(base+d)
    ms.update(range(1,40)); ms.add(n*n); ms.add(n*(n-1))
    L=reduce(lcm,range(1,n+1),1)
    ms.add(L//2); ms.add(L-1); ms.add(L); ms.add(L+1)
    for _ in range(80): ms.add(random.randint(1, max(10,base*4)))
    return sorted(x for x in ms if x>=1)

for n in [150, 200, 256, 300, 400]:
    ms=adversarial(n)
    viol=[m for m in ms if not assign_exists(n,m,2*n-1)]
    print(f"n={n}: violations at m in {viol[:8]} ({len(viol)} total)")
    for m in viol[:3]:
        d,_=deficient(n,m)
        fe=f_exact(n,m,3*n)
        print(f"   m={m}: deficiency {d}, f(n,m)={fe} (2n-1={2*n-1})")
        # find a deficient antichain: greedy search over subsets near top band
        W=2*n-2
        ints=list(range(m+1,m+W+1))
        Ms={k:frozenset(x for x in ints if x%k==0) for k in range(1,n+1)}
        # search suffix intervals and dyadic bands
        best=None
        for c in range(1,n+1):
            ks=list(range(c,n+1))
            u=frozenset().union(*[Ms[k] for k in ks])
            d2=len(u)-len(ks)
            if best is None or d2<best[0]: best=(d2,('suffix',c))
        print(f"      worst suffix: margin {best[0]} at c={best[1][1]}")
