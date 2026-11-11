import math, time
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
def factorize(x, budget=25):
    fs={}; stack=[x]; deadline=time.time()+budget
    while stack:
        v=stack.pop()
        if v==1: continue
        if is_prime_mm(v): fs[v]=fs.get(v,0)+1; continue
        d=pollard_brent(v, deadline)
        if d is None: return None
        stack.append(d); stack.append(v//d)
    return fs

print("ENGINE R2: #1074 EHS full census m=1..40 with witness extraction")
S={}; nonS={}; unf=[]
for m in range(1,41):
    if m<=2:
        # 1!+1=2: p=2, 2 mod 1 = 0 != 1 -> 1 in S? m=1: p != 1 mod 1 is vacuous (everything = 0 mod 1)
        pass
    fs=factorize(factorial(m)+1, budget=25)
    if fs is None: unf.append(m); continue
    wits=[p for p in fs if p%m!=1]
    if wits: S[m]=min(wits)
    else: nonS[m]=dict(fs)
print(f"in S (m -> witness prime): {S}")
print(f"NOT in S (m -> full factorization): {nonS}")
print(f"unfactored: {unf}")
print(f"  |S cap [1,40]| = {len(S)}, density {len(S)/40:.4f}")
print()
print("ENGINE R2b: PILLAI PRIMES p <= 10000")
pillai={}; nonp=[]
# sieve
N=10000
s=bytearray([1])*(N+1); s[0]=s[1]=0
for i in range(2,int(N**0.5)+1):
    if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
primes=[i for i in range(N+1) if s[i]]
for p in primes:
    if p<3: continue
    fm=1; found=None
    for m in range(1,p):
        fm=fm*m % p   # m! mod p
        if fm==p-1:   # m!+1 = 0 mod p
            if p%m!=1: found=m; break
    if found is not None: pillai[p]=found
    else: nonp.append(p)
print(f"  Pillai primes <= 10000: {len(pillai)} of {len(primes)} ({100*len(pillai)/len(primes):.2f}%)")
print(f"  first 30: {dict(list(pillai.items())[:30])}")
print(f"  max m-witness: {max(pillai.values()) if pillai else 0}")
print(f"\nTOTAL {time.time()-t0:.1f}s")
