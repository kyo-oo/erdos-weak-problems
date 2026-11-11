#!/usr/bin/env python3
"""Extract the actual DEFICIENT SETS (via Konig min vertex cover) at the violating (n,m),
and probe max_m f(n,m) growth for larger n."""
import sys, random
from math import gcd, log, ceil
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

def assign_exists(n,m,F):
    ints=list(range(m+1,m+F)); adj={k:set(x for x in ints if x%k==0) for k in range(1,n+1)}
    for k in adj:
        if not adj[k]: return False
    sz,_,_=hopcroft_full(range(1,n+1),ints,adj)
    return sz==n

def f_exact(n,m,Fmax):
    if not assign_exists(n,m,Fmax): return None
    lo,hi=1,Fmax
    while lo<hi:
        mid=(lo+hi)//2
        if assign_exists(n,m,mid): hi=mid
        else: lo=mid+1
    return lo

def deficient_set(n,m,W):
    """min vertex cover via Konig from max matching: returns (deficiency, cover_left, cover_right)."""
    L=list(range(1,n+1)); ints=list(range(m+1,m+W+1)); R=ints
    adj={k:set(x for x in ints if x%k==0) for k in L}
    sz,pairL,pairR=hopcroft_full(L,R,adj)
    # Konig: cover = unmatched-reachable L complement + reachable R
    # BFS from unmatched L vertices over alternating paths
    reachL=set(); reachR=set()
    q=[]
    for l in L:
        if pairL[l] is None: q.append(l); reachL.add(l)
    dist={}
    while q:
        nq=[]
        for l in q:
            for r in adj[l]:
                if r not in reachR:
                    reachR.add(r)
                    lr=pairR[r]
                    if lr is not None and lr not in reachL:
                        reachL.add(lr); nq.append(lr)
        q=nq
    coverL=[l for l in L if l not in reachL]
    coverR=[r for r in R if r in reachR]
    return n-sz, coverL, coverR, pairL

cases=[(150,1901),(200,1004),(200,5647),(256,6192),(256,9327),(256,16743),(300,1266),(300,11357),(400,3471),(400,4424),(400,18428)]
for (n,m) in cases:
    W=2*n-2
    d,cL,cR,pairL=deficient_set(n,m,W)
    print(f"n={n} m={m}: deficiency={d}, cover-left size={len(cL)}, cover-right size={len(cR)}")
    print(f"   deficient-set candidates (cover-left): {sorted(cL)[:40]}")
    # the actual deficient S: cover-left IS the S side of the min cut: |S|-|N(S)| = ?
    S=set(cL)
    ints=set(range(m+1,m+W+1))
    Ns=set()
    for k in S:
        Ns|=set(x for x in ints if x%k==0)
    print(f"   |S|={len(S)}, |N(S)|={len(Ns)}, |S|-|N(S)|={len(S)-len(Ns)}")
    # characterize: sizes, min/max keys, lcm structure
    if S:
        ks=sorted(S)
        print(f"   S keys: min={ks[0]} max={ks[-1]} count={len(ks)}; band structure: first 15: {ks[:15]} ... last 10: {ks[-10:]}")
        # divisors pattern of the Ns points: sample t(x)
        ts=sorted(ints)
        tvals=[]
        for x in sorted(Ns)[:100]:
            t=sum(1 for k in S if x%k==0)
            tvals.append((x,t))
        print(f"   sample N points with multiplicity: {tvals[:12]}")
