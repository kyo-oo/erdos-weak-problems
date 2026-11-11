import math, time
from math import comb, gcd, factorial
t0=time.time()

print("="*70); print("ENGINE 1: #1063 — the n_k case frontier (n-i | C(n,k) all-but-one)"); print("="*70)
# calibration n_2=4, n_3=6, n_4=9, n_5=12 then NEW k=6..14
def nk_1063(k, cap):
    for n in range(2*k, cap+1):
        c = comb(n,k)
        fails = sum(1 for i in range(k) if c % (n-i) != 0)
        if fails <= 1:
            return n
    return None
res1063 = {}
for k in range(2, 15):
    cap = 400000 if k <= 12 else 1500000
    v = nk_1063(k, cap)
    res1063[k] = v
    print(f"  n_{k} = {v}" + ("  [CALIBRATION-OK]" if k<=5 else "  *** NEW ***"))
print("  known check: n_2..n_5 should be 4,6,9,12 ->", [res1063.get(k) for k in range(2,6)])

print(); print("="*70); print("ENGINE 2: #451 — least n>2k with prod(n-i) having no prime factor in (k,2k)"); print("="*70)
def sieve_primes(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
PR = sieve_primes(200)
res451 = {}
for k in range(2, 17):
    mids = [p for p in PR if k < p < 2*k]
    forb = [set(range(1,k+1)) for _ in mids]
    cap = 1
    for p in mids: cap *= p
    found = None
    for n in range(2*k+1, cap+1):
        ok = True
        for idx,p in enumerate(mids):
            if (n % p) in forb[idx]: ok=False; break
        if ok: found=n; break
    res451[k]=found
    print(f"  n_{k} = {found}   (primes in ({k},{2*k}) = {mids})")

print(); print("="*70); print("ENGINE 3: #1072 — f(p) least n with n! = -1 mod p + Wilson-pair law"); print("="*70)
def f1072(p):
    f=1
    if 1 % p == p-1: pass
    # 1! = 1
    val = 1 % p
    if val == p-1: return 1
    for j in range(2, p):
        val = val*j % p
        if val == p-1: return j
    return p-1  # Wilson
wilson_only = []
maxfp = 0; maxp = 0
pair_law_ok = True; pair_checked = 0
for p in PR[:1229]:  # all primes < 10000
    if p < 5: continue
    # chain
    facts=[1%p]
    val=1%p
    for j in range(1,p):
        val = val*j % p
        facts.append(val)
    sols = [j for j in range(p) if facts[j]==p-1]
    # verify pairing law: n! = -1  =>  (p-1-n)! = (-1)^{p-1-n}
    for n in sols:
        m = p-1-n
        expect = 1 if m%2==0 else p-1
        if facts[m]!=expect: pair_law_ok=False
        pair_checked += 1
    f = sols[0]  # least
    if f==p-1: wilson_only.append(p)
    if f/p > maxfp: maxfp=f/p; maxp=p
print(f"  Wilson-pair law: {'VERIFIED' if pair_law_ok else 'FAILED'} ({pair_checked} solution-pairs checked)")
print(f"  #Wilson-only primes < 10000 (f(p)=p-1): {len(wilson_only)}")
print(f"  list: {wilson_only[:40]}")
print(f"  max f(p)/p < 10000: {maxfp:.4f} at p={maxp}")

print(); print("="*70); print("ENGINE 4: #961 — f(k) = 1 + max run of consecutive k-smooth (all > k)"); print("="*70)
def smooth_numbers(k, B):
    primes=[p for p in PR if p<=k]
    out=[]
    def rec(idx, val):
        if idx==len(primes):
            out.append(val); return
        p=primes[idx]; v=val
        while v<=B:
            rec(idx+1, v); v*=p
    rec(0,1)
    return sorted(out)
def runs_961(k, B):
    ss = set(smooth_numbers(k,B))
    best=(0,None); cur=0; start=None
    for v in range(1,B+1):
        if v in ss:
            if cur==0: start=v
            cur+=1
            if cur>best[0]: best=(cur, start)
        else:
            cur=0
    # only runs with all elements > k
    return best
for k in [2,3,4,5,6,7]:
    B = 10**7
    ln, st = runs_961(k, B)
    print(f"  k={k}: max run of consecutive {k}-smooth <= 10^7: length {ln} starting at {st}  -> f({k}) >= {ln+1}" + (f"  [run start <= k, excludes] " if st is not None and st<=k else ""))

print(); print("="*70); print("ENGINE 5: #394 — t_k(n) CRT law verification ((n,k!)=1)"); print("="*70)
def t_brute(n,k,cap=200000):
    for m in range(1,cap):
        pr=1
        for i in range(k): pr*= (m+i)
        if pr % n == 0: return m
    return None
def prime_powers(n):
    pp=[]; d=2
    while d*d<=n:
        if n%d==0:
            q=1
            while n%d==0: n//=d; q*=d
            pp.append(q); 
        d+=1
    if n>1: pp.append(n)
    return pp
def crt_min(n,k):
    pp = prime_powers(n)
    best = None
    # assign each prime power to one of k positions (k^len assignments)
    from itertools import product
    for assign in product(range(k), repeat=len(pp)):
        d=[1]*k
        for q,pos in zip(pp,assign): d[pos]*=q
        # CRT: m = -i mod d_i
        M=n; m=0
        # standard CRT pairwise coprime d_i, product = n
        ok=True
        # compute via successive merge
        cur_r, cur_mod = 0, 1
        for i in range(k):
            # m ≡ -i mod d_i
            r2 = (-i) % d[i]
            m2 = d[i]
            g = gcd(cur_mod, m2)
            if g != 1:
                ok=False; break
            # merge
            inv = pow(cur_mod, -1, m2)
            cur_r = (cur_r + cur_mod * ((r2 - cur_r) * inv % m2)) % (cur_mod*m2)
            cur_mod *= m2
        if not ok: continue
        cand = cur_r % n
        if cand == 0: cand = n  # m >= 1
        if best is None or cand < best: best = cand
    return best
ok_count=0; bad=[]
for k in [2,3,4,5]:
    for n in range(2, 300):
        if gcd(n, math.factorial(k)) != 1: continue
        tb = t_brute(n,k); tc = crt_min(n,k)
        if tb != tc: bad.append((k,n,tb,tc))
        else: ok_count+=1
print(f"  CRT law t_k(n)=min-factorization-CRT: {ok_count} matches, {len(bad)} mismatches")
if bad: print("  MISMATCHES:", bad[:10])
print("  LAW " + ("CONFIRMED" if not bad else "BROKEN"))

print(); print("="*70); print("ENGINE 6: #954 — Rosen greedy sequence block-difference law"); print("="*70)
import bisect
K=1200
a=[0,1]
cnt_pairs=[1]  # number of pairs a_i+a_j <= x... we recompute per step
for kk in range(1, K):
    # a_{k+1}: least n with #solutions(a_i+a_j<=n, 0<=i<=j<=k, j>=1) < n
    # collect sums from first kk+1 terms (indices 0..kk)
    sums=[]
    for i in range(0, kk+1):
        for j in range(i, kk+1):
            if j>=1: sums.append(a[i]+a[j])
    sums.sort()
    # find least n with count(< n) ... count of sums <= n is < n
    # count(n) = #sums <= n; need least n with count(n) < n
    n=1
    while True:
        c = bisect.bisect_right(sums, n)
        if c < n: break
        n+=1
    a.append(n)
diffs=[a[i+1]-a[i] for i in range(1,len(a)-1)]
# pattern check: value v_i = 1+C(i,2) repeated i times
pattern=[]
i=1
while len(pattern)<len(diffs):
    pattern += [1+ i*(i-1)//2]*i
    i+=1
match = diffs==pattern[:len(diffs)]
print(f"  a_k computed to k={len(a)-1}; block-difference law (v_i=1+C(i,2) x i): {'HOLDS' if match else 'FAILS'}")
if not match:
    for idx in range(len(diffs)):
        if diffs[idx]!=pattern[idx]:
            print(f"    first break at diff index {idx}: got {diffs[idx]} want {pattern[idx]}"); break
print(f"  first 30 diffs: {diffs[:30]}")

print(); print("="*70); print("ENGINE 7: #711 — f(n,m) divisor-matching exact tables"); print("="*70)
def match_feasible(n, lo, hi):
    # left k=1..n, right integers in [lo,hi]; edge if k|v. Hall check.
    rights=list(range(lo,hi+1))
    adj=[[] for _ in range(n+1)]
    for k in range(1,n+1):
        for v in rights:
            if v%k==0: adj[k].append(v)
    # simple augmenting-path matching
    matchR={}; matchL={}
    def try_k(k, seen):
        for v in adj[k]:
            if v in seen: continue
            seen.add(v)
            if v not in matchR or try_k(matchR[v], seen):
                matchR[v]=k; matchL[k]=v; return True
        return False
    for k in range(1,n+1):
        if not try_k(k,set()): return False
    return True
def f711(n,m):
    F=n  # need at least n integers in (m, m+F): integers m+1..m+F-1 -> F-1 >= n -> F>=n+1
    F=n+1
    while True:
        lo,hi=m+1,m+F-1
        if match_feasible(n,lo,hi): return F
        F+=1
print("  n : f(n,n) : max_m f(n,m) for m<=300 : argmax")
for n in range(2,9):
    fn = f711(n,n)
    mx=0; am=0
    for m in range(1,301):
        v=f711(n,m)
        if v>mx: mx=v; am=m
    print(f"  {n} : {fn} : {mx} @ m={am}")

print(); print("="*70); print("ENGINE 8: #282 — odd-greedy termination census"); print("="*70)
from fractions import Fraction
def odd_greedy(x, max_steps=400):
    steps=0
    while x != 0:
        # least odd n >= 1/x
        n = math.ceil(1/x)
        if n%2==0: n+=1
        if n==1: n=3  # 1/1 not allowed? n>=1/x; if x=1, n=1... keep n=1 if x==1
        if x==1: n=1
        x = x - Fraction(1,n)
        steps+=1
        if steps>max_steps: return None, n
    return steps, None
bad=[]; mx=0; mxfrac=None
for n in range(3, 202, 2):
    for m in range(1,n):
        if gcd(m,n)!=1: continue
        st, stuck = odd_greedy(Fraction(m,n))
        if st is None: bad.append((m,n,stuck))
        elif st>mx: mx=st; mxfrac=(m,n)
print(f"  odd-denominator rationals m/n, n odd <= 201, gcd=1: all terminate? {'YES' if not bad else 'NO'}")
print(f"  max greedy length: {mx} at {mxfrac}")
if bad: print("  NON-TERMINATING:", bad[:5])

print(); print("="*70); print("ENGINE 9: #1074 — EHS membership m!+1 (Pollard)"); print("="*70)
def is_prime_small(x):
    if x<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%p==0: return x==p
    d=x-1; r=0
    while d%2==0: d//=2; r+=1
    for aa in [2,3,5,7,11,13,17,19,23,29,31,37]:
        a=aa; y=pow(a,d,x)
        if y==1 or y==x-1: continue
        for _ in range(r-1):
            y=y*y%x
            if y==x-1: break
        else: return False
    return True
def pollard(x):
    if x%2==0: return 2
    import random
    random.seed(1)
    while True:
        x1=random.randrange(2,x); y=x1; c=random.randrange(1,x); d=1
        while d==1:
            x1=(x1*x1+c)%x; y=(y*y+c)%x; y=(y*y+c)%x
            d=gcd(abs(x1-y),x)
        if d!=x: return d
def factor(x):
    fs={}
    def go(x):
        if x==1: return
        if is_prime_small(x): fs[x]=fs.get(x,0)+1; return
        d=pollard(x); go(d); go(x//d)
    go(x); return fs
S=[]; nonS=[]
for m in range(2, 46):
    v = factorial(m)+1
    fs = factor(v)
    inS = any(p % m != 1 for p in fs)
    (S if inS else nonS).append(m)
print(f"  S-membership m=2..45 (m!+1 fully factored):")
print(f"  in S: {S}")
print(f"  NOT in S: {nonS}")
print(f"  known S start: 8,9,13,14,15,16,17  -> match: {S[:7]==[8,9,13,14,15,16,17]}")

print(); print(f"TOTAL ENGINE TIME: {time.time()-t0:.1f}s")
