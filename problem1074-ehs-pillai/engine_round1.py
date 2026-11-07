import math, time, signal
from math import gcd, factorial
t0=time.time()
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
def pollard_brent(x, deadline):
    if x%2==0: return 2
    import random
    random.seed(7)
    for c in range(1,50):
        if time.time()>deadline: return None
        x1=random.randrange(2,x); y=x1; d=1
        while d==1:
            x1=y
            for _ in range(64): y=(y*y+c)%x
            k=0
            while k<64 and d==1:
                y2=(y*y+c)%x; d=gcd(abs(x1-y2),x); y=y2; k+=1
            if time.time()>deadline: return None
        if d!=x: return d
    return None
def factorize(x, budget=20):
    fs={}; stack=[x]; deadline=time.time()+budget
    while stack:
        v=stack.pop()
        if v==1: continue
        if is_prime_mm(v): fs[v]=fs.get(v,0)+1; continue
        d=pollard_brent(v, deadline)
        if d is None: return None
        stack.append(d); stack.append(v//d)
    return fs
print("ENGINE 9-QUICK: #1074 EHS m=2..32 (20s/m budget)")
S=[]; nonS=[]; unf=[]
for m in range(2,33):
    fs=factorize(factorial(m)+1, budget=20)
    if fs is None: unf.append(m); continue
    inS=any(p%m!=1 for p in fs)
    (S if inS else nonS).append(m)
print(f"  in S: {S}")
print(f"  NOT in S: {nonS}")
print(f"  unfactored: {unf}")
print(f"  calib S∩[2,17]={sorted(x for x in S if x<=17)} (want [8,9,13,14,15,16,17])")

print(); print("ENGINE 7-QUICK: #711 n=9,10 m<=300")
def sieve_primes(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def match_feasible(n, lo, hi):
    adj=[[] for _ in range(n+1)]
    for k in range(1,n+1):
        start=((lo+k-1)//k)*k
        adj[k]=list(range(start,hi+1,k))
    matchR={}
    def try_k(k,seen):
        for v in adj[k]:
            if v in seen: continue
            seen.add(v)
            if v not in matchR or try_k(matchR[v],seen):
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
for n in [9,10]:
    mx=0;am=0
    for m in range(1,301):
        v=f711(n,m)
        if v>mx: mx=v;am=m
    print(f"  n={n}: max f={mx} @ m={am}  (2n-1={2*n-1}, (n-1)^2={(n-1)**2})")
print(f"\nTOTAL {time.time()-t0:.1f}s")
