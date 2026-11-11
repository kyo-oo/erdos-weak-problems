#!/usr/bin/env python3
"""TRUTH HUNT: (a) true deficient sets S0 = keys - cover_left at violations; (b) max deficiency
growth over n; (c) f(n,n) growth; (d) deficient sets at m=n near threshold."""
import sys, random
from math import gcd, log
from functools import reduce
def lcm(a,b): return a*b//gcd(a,b)
random.seed(711)

def hopcroft_full(L,R,adj):
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
    return m, pairL, pairR

def deficiency_and_set(n,m,F):
    L=list(range(1,n+1)); ints=list(range(m+1,m+F)); R=ints
    adj={k:set(x for x in ints if x%k==0) for k in L}
    for k in L:
        if not adj[k]: return n, None  # total deficiency
    sz,pairL,pairR=hopcroft_full(L,R,adj)
    if sz==n: return 0, None
    # Konig cover
    reachL=set(); reachR=set(); q=[]
    for l in L:
        if pairL[l] is None: q.append(l); reachL.add(l)
    while q:
        nq=[]
        for l in q:
            for r in adj[l]:
                if r not in reachR:
                    reachR.add(r); lr=pairR[r]
                    if lr is not None and lr not in reachL:
                        reachL.add(lr); nq.append(lr)
        q=nq
    coverL=set(l for l in L if l not in reachL)
    S0=sorted(set(L)-coverL)
    return n-sz, S0

def assign_exists(n,m,F):
    d,_=deficiency_and_set(n,m,F)
    return d==0

def f_exact(n,m,Fmax):
    if not assign_exists(n,m,Fmax): return None
    lo,hi=1,Fmax
    while lo<hi:
        mid=(lo+hi)//2
        if assign_exists(n,m,mid): hi=mid
        else: lo=mid+1
    return lo

print("=== (a) true deficient sets at violations ===")
for (n,m) in [(150,1901),(200,1004),(256,9327),(300,11357),(400,3471),(400,4424),(400,18428)]:
    d,S0=deficiency_and_set(n,m,2*n-1)
    print(f"n={n} m={m}: def={d}, S0 (size {len(S0)}): {S0[:60]}")
    if S0:
        ks=S0
        # antichain reduction
        mins=[k for k in ks if not any(j!=k and k%j==0 for j in ks)]
        print(f"    antichain-reduction (size {len(mins)}): {mins[:40]}")
        W=2*n-2; ints=set(range(m+1,m+W+1))
        Ns=set()
        for k in mins: Ns|=set(x for x in ints if x%k==0)
        print(f"    |S'|={len(mins)}, |N(S')|={len(Ns)}, margin={len(Ns)-len(mins)}")
        # the shared structure: lcm of the whole set?
        L=1
        for k in mins: L=lcm(L,k)
        print(f"    lcm(S')={L}  (m={m}, window top={m+W})")
        # gcd structure: pairwise ratios
        print(f"    quotients m/k for k in S': {[m//k for k in mins[:12]]}")

print("=== (c) f(n,n) growth ===")
mx=0
for n in list(range(160,320,20))+[400,600,800,1000,1500,2000]:
    v=f_exact(n,n,3*n)
    if v: mx=max(mx,v/n)
    print(f"  n={n}: f(n,n)={v}, ratio={v/n if v else None:.3f}")

print("=== (b) max deficiency hunt ===")
for n in [500,800,1000,1500,2000,3000,4000,8000]:
    best=(0,None,None)
    for _ in range(400):
        m=random.randint(1, n*n)
        d,S0=deficiency_and_set(n,m,2*n-1)
        if d>best[0]: best=(d,m,S0)
    # also adversarial dense near (n-1)^2
    base=(n-1)**2
    for m in range(max(1,base-3*n), base+3*n, 7):
        d,S0=deficiency_and_set(n,m,2*n-1)
        if d>best[0]: best=(d,m,S0)
    print(f"  n={n}: max deficiency found {best[0]} at m={best[1]} ({best[0]/n:.3f}n); S0 first 20: {(best[2] or [])[:20]}")
