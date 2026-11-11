import math, time
from math import comb, gcd, factorial
t0=time.time()

def sieve_primes(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

print("="*70); print("ENGINE 2-FIX: #451 n_k (cap = first multiple of prod(primes) above 2k)"); print("="*70)
PR = sieve_primes(100)
res451={}
for k in range(2, 21):
    mids=[p for p in PR if k<p<2*k]
    P=1
    for p in mids: P*=p
    cap = ((2*k)//P + 1)*P + P  # generous: two multiples
    found=None
    for n in range(2*k+1, cap+1):
        ok=True
        for p in mids:
            r=n%p
            if 1<=r<=k: ok=False; break
        if ok: found=n; break
    res451[k]=found
    print(f"  n_{k} = {found}   primes({k},{2*k})={mids}")

print(); print("="*70); print("ENGINE 3-FIX: #1072 full census p < 10000"); print("="*70)
PR10k = sieve_primes(10000)
wilson_only=[]; extra_sol_primes=[]; maxfp=0; maxp=0; pair_ok=True; pairs=0
solcount_hist={}
for p in PR10k:
    if p<5: continue
    facts=[1%p]; val=1%p
    for j in range(1,p):
        val=val*j%p; facts.append(val)
    sols=[j for j in range(p) if facts[j]==p-1]
    solcount_hist[len(sols)]=solcount_hist.get(len(sols),0)+1
    for nn in sols:
        m=p-1-nn; exp = 1 if m%2==0 else p-1
        if facts[m]!=exp: pair_ok=False
        pairs+=1
    f=sols[0]
    if f==p-1: wilson_only.append(p)
    else: extra_sol_primes.append((p,f))
    if f/p>maxfp: maxfp=f/p; maxp=p
print(f"  primes 5<=p<10000: {len(PR10k)-2}")
print(f"  Wilson-pair law: {'VERIFIED' if pair_ok else 'FAILED'} over {pairs} solution instances")
print(f"  solution-count histogram (#n with n!=-1 mod p -> #primes): {dict(sorted(solcount_hist.items()))}")
print(f"  Wilson-only (f(p)=p-1): {len(wilson_only)} primes")
print(f"    {wilson_only}")
print(f"  primes with extra small solution (f<p-1), first 25: {extra_sol_primes[:25]}")
print(f"  max f(p)/p: {maxfp:.4f} at p={maxp}")

print(); print("="*70); print("ENGINE 4-FIX: #961 runs with ALL elements > k"); print("="*70)
def smooth_set(k,B):
    primes=[p for p in PR if p<=k]
    out=set()
    def rec(idx,v):
        if idx==len(primes): out.add(v); return
        p=primes[idx]; vv=v
        while vv<=B:
            rec(idx+1,vv); vv*=p
    rec(0,1); return out
for k in [2,3,4,5,6,7,8,9,10,11,12]:
    B=2*10**6
    ss=smooth_set(k,B)
    best=(0,None); cur=0; st=None
    for v in range(k+1,B+1):
        if v in ss:
            if cur==0: st=v
            cur+=1
            if cur>best[0]: best=(cur,st)
        else: cur=0
    print(f"  k={k}: max consecutive {k}-smooth run (all>k) <= 2e6: length {best[0]} at {best[1]}  => f({k}) = {best[0]+1}")

print(); print("="*70); print("ENGINE 9-FIX: #1074 EHS membership m=2..40"); print("="*70)
def is_prime_mm(x):
    if x<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%p==0: return x==p
    d=x-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y==1 or y==x-1: continue
        ok=False
        for _ in range(r-1):
            y=y*y%x
            if y==x-1: ok=True; break
        if not ok: return False
    return True
def pollard_brent(x):
    if x%2==0: return 2
    import random
    random.seed(42)
    for c in range(1,100):
        x1=random.randrange(2,x); y=x1; d=1; ys=0; q=1
        m=128
        while d==1:
            x1=y
            for _ in range(m): y=(y*y+c)%x
            k=0
            while k<m and d==1:
                ys=y
                for _ in range(min(64,m-k)):
                    y=(y*y+c)%x; q=q*abs(x1-y)%x
                d=gcd(q,x); k+=64
            if d==x:
                d=1; y=ys
                while d==1:
                    y=(y*y+c)%x; d=gcd(abs(x1-y),x)
        if d!=x: return d
    return None
def factorize(x, depth=0):
    fs={}
    stack=[x]
    while stack:
        v=stack.pop()
        if v==1: continue
        if is_prime_mm(v): fs[v]=fs.get(v,0)+1; continue
        d=pollard_brent(v)
        if d is None: fs[-v]=1; continue  # unfactored composite marker
        stack.append(d); stack.append(v//d)
    return fs
S=[]; nonS=[]; unfactored=[]
for m in range(2,41):
    v=factorial(m)+1
    fs=factorize(v)
    if any(f<0 for f in fs): unfactored.append(m); continue
    inS=any(p%m!=1 for p in fs)
    (S if inS else nonS).append(m)
print(f"  in S (EHS): {S}")
print(f"  NOT in S: {nonS}")
print(f"  unfactored: {unfactured if False else unfactored}")
known=[8,9,13,14,15,16,17]
print(f"  known S start 8,9,13..17 -> our S contains them in order: {[x for x in S if x<=17]==known}")

print(); print("="*70); print("ENGINE 7-EXT: #711 — push n to 12, m to 800 (2n-1 law test)"); print("="*70)
def match_feasible(n, lo, hi):
    adj=[[] for _ in range(n+1)]
    for k in range(1,n+1):
        start = ((lo + k - 1)//k)*k
        for v in range(start, hi+1, k): adj[k].append(v)
    matchR={}
    def try_k(k, seen):
        for v in adj[k]:
            if v in seen: continue
            seen.add(v)
            if v not in matchR or try_k(matchR[v], seen):
                matchR[v]=k; return True
        return False
    for k in range(1,n+1):
        if not try_k(k,set()): return False
    return True
def f711(n,m):
    F=n+1
    while True:
        if match_feasible(n,m+1,m+F-1): return F
        F+=1
for n in range(9,13):
    mx=0; am=0
    for m in range(1,801):
        v=f711(n,m)
        if v>mx: mx=v; am=m
    print(f"  n={n}: max_m f = {mx} @ m={am}   (2n-1 = {2*n-1}, (n-1)^2 = {(n-1)**2})")

print(); print(f"TOTAL: {time.time()-t0:.1f}s")
