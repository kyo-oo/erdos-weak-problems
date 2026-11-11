#!/usr/bin/env python3
"""E3: f(n,n) exact (n<=160); N-window Hall census at F=ceil(3n/2),+1 (n<=12 all subsets);
E-SIH: suffix-interval Hall |N([c,n])| >= n-c+1 over full periods n<=10, and worst-set-is-suffix check.
E-big: matching-based Theorem U check for n up to 400 adversarial m."""
import sys, random
from math import gcd, floor
from functools import reduce
def lcm(a,b): return a*b//gcd(a,b)
random.seed(711)

def hopcroft(L, R, adj):
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
    return m

def assign_exists(n,m,F):
    if F-1<n: return False
    ints=list(range(m+1,m+F)); adj={k:set(x for x in ints if x%k==0) for k in range(1,n+1)}
    for k in adj:
        if not adj[k]: return False
    return hopcroft(range(1,n+1), ints, adj)==n

def f_exact(n,m,Fmax):
    lo,hi=1,Fmax
    while lo<hi:
        mid=(lo+hi)//2
        if assign_exists(n,m,mid): hi=mid
        else: lo=mid+1
    return lo if assign_exists(n,m,lo) else None

print("=== E3: f(n,n) exact ===")
fl=[]
for n in range(2,161):
    v=f_exact(n,n,2*n+2)
    c=(3*n+1)//2 if n%2 else 3*n//2
    if v is None or v>c: fl.append((n,v,c))
    if n<=16 or n%20==0: print(f"  n={n}: f(n,n)={v} ceil(3n/2)={c}")
print("flags:", fl[:8], "total", len(fl))

print("=== E3b: N-window tight-set census (all subsets), F=ceil(3n/2)+1 ===")
for n in range(2,13):
    F=((3*n+1)//2 if n%2 else 3*n//2)+1
    ints=list(range(n+1,n+F)); adj={k:set(x for x in ints if x%k==0) for k in range(1,n+1)}
    worst=99; worstS=None; tight={}
    for S in range(1,1<<n):
        ks=[i+1 for i in range(n) if S>>i&1]
        u=set()
        for k in ks: u|=adj[k]
        d=len(u)-len(ks)
        if d<worst: worst=d; worstS=tuple(ks)
        if d==0 and len(ks)>=2: tight[tuple(ks)]=tight.get(tuple(ks),0)+1
    print(f" n={n} F={F}: min margin {worst} at {worstS}; #tight sets {len(tight)}")

print("=== E-SIH: suffix Hall |N([c,n])| >= n-c+1, full periods n<=10 ===")
for n in range(2,11):
    L=reduce(lcm,range(1,n+1),1); per=min(L,2520); W=2*n-2
    worst=99; at=None; worst_is_suffix=True; global_worst=99; gat=None
    for m in range(1,per+1):
        Ms={k:frozenset(x for x in range(m+1,m+W+1) if x%k==0) for k in range(1,n+1)}
        # suffix margins
        for c in range(1,n+1):
            u=frozenset().union(*[Ms[k] for k in range(c,n+1)])
            d=len(u)-(n-c+1)
            if d<worst: worst=d; at=(m,c)
        # worst over ALL subsets (antichain or not)
        for S in range(1,1<<n):
            ks=[i+1 for i in range(n) if S>>i&1]
            u=frozenset().union(*[Ms[k] for k in ks])
            d=len(u)-len(ks)
            if d<global_worst: global_worst=d; gat=(m,tuple(ks))
    print(f" n={n}: suffix min margin {worst} at (m,c)={at}; ALL-subset min margin {global_worst} at {gat}")

print("=== E-big: Theorem U matching check, big n, adversarial m ===")
def adversarial(n):
    ms=set(); base=(n-1)**2
    for j in range(-2,3): ms.add(base+j*(2*n-1))
    for d in range(-3*n,3*n+1): ms.add(base+d)
    ms.update(range(1,40)); ms.add(n*n); ms.add(n*(n-1))
    L=reduce(lcm,range(1,n+1),1)
    for t in range(6): ms.add((t*L)//2 if t>=1 else 0)
    ms.add(L-1); ms.add(L); ms.add(L+1)
    for _ in range(120): ms.add(random.randint(1, max(10,base*4)))
    return sorted(x for x in ms if x>=1)
for n in [17,20,24,30,40,50,64,80,100,128,150,200,256,300,400]:
    ms=adversarial(n)
    bad=sum(0 if assign_exists(n,m,2*n-1) else 1 for m in ms)
    print(f"  n={n}: {len(ms)} m-values (adversarial dense near (n-1)^2 + random), violations: {bad}")
