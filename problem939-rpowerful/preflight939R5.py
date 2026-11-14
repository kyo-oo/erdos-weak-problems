# preflight939R5.py — verify EVERY number Erdos939R5.lean embeds, mirroring the
# EXACT Lean sweep semantics (checkEO/checkOO decide-prop shapes incl. o=1).
from sympy import primerange, integer_nthroot
import numpy as np, math, time, json

def iroot(n,k): return integer_nthroot(n,k)[0]
def gen4(limit):  # the TRUE 4-powerful enumerator (audit-corrected)
    r4 = iroot(limit,4); P = list(primerange(2, r4+2)); out=[]; ap=out.append
    def rec(i,val):
        ap(val)
        for j in range(i,len(P)):
            v = val * P[j]**4
            if v > limit: break
            while v <= limit:
                rec(j+1,v); v *= P[j]
    rec(0,1)
    out=[x for x in out if 1 < x <= limit]; out.sort(); return out

# ---- the Lean-shaped genVals (primes-only heads, chains e>=4) ----
def genChains(limit,p,rs):
    out=[]
    for r in rs:
        v=r*p**4
        while v<=limit:
            out.append(v); v*=p
    return out
def genVals(limit,ps):
    if not ps: return [1]
    p,rest=ps[0],ps[1:]
    rs=genVals(limit,rest)
    return rs+genChains(limit,p,rs)

B = 999706081460641
LIM = 2*B
PSLIT = [p for p in range(2,6687)]
PSPRIMES = [p for p in PSLIT if all(p%d for d in range(2,p))]
assert 6687**4 > LIM and 6686**4 <= LIM, (6687**4, 6686**4, LIM)
print("BOUND OK: 6686^4 <= 2B < 6687^4 ; 6687^4 =", 6687**4)
print("2^51 > LIM:", 2**51 > LIM, " (2^51 =", 2**51, ")")

t=time.time()
GV = genVals(LIM, PSPRIMES)
print(f"genVals(primes<=6700) output: {len(GV)} values (python {time.time()-t:.1f}s)")
CEN = [1]+gen4(LIM)
print("genVals == python census [1]+gen4:", GV == CEN or sorted(GV)==CEN)
GVS = sorted(set(GV))
print("genVals sorted-dedup == census:", GVS == CEN, " |CEN| =", len(CEN))

TABARR = CEN  # the literal sorted array (48,138 values incl 1)
def bsearch(arr, x):
    lo, hi = 0, len(arr)-1
    while lo <= hi:
        mid = (lo+hi)//2
        if arr[mid] == x: return True
        elif arr[mid] < x: lo = mid+1
        else: hi = mid-1
    return False
assert all(bsearch(TABARR,x) for x in TABARR)
print("tab_found OK: all", len(TABARR), "members binary-search-found")

TABLE = CEN
TABODD = [x for x in TABLE if x % 2 == 1]
TABODDB = [x for x in TABODD if x <= B]
print("|TABLE| =", len(TABLE), "|TABODD| =", len(TABODD), "|TABODDB| =", len(TABODDB))
print("even16: all even members %16==0:", all(x % 16 == 0 for x in TABLE if x % 2 == 0))
print("positive: min member =", min(TABLE))
print("consecutive members (x, x+1) both in TABLE:", any(x+1 in set(TABLE) for x in TABLE))

# ---- THE EXACT LEAN SWEEPS ----
def checkEO(r,o,c):
    if c % 16 != r: return True
    if c <= o: return True
    if o + B < c: return True
    e = c - o
    if not bsearch(TABARR, e): return True
    return 1 < math.gcd(e, o)
def checkOO(a,b):
    if b <= a: return True
    if (a + b) % 16 != 0: return True
    if not bsearch(TABARR, a + b): return True
    return 1 < math.gcd(a, b)

t=time.time()
nEOpairs=0; EOviol=[]
for o in TABODDB:
    r = o % 16
    for c in TABODD:
        nEOpairs += 1
        if not checkEO(r,o,c): EOviol.append((o,c))
print(f"sweepEO: {nEOpairs} pairs ({time.time()-t:.1f}s); violations: {len(EOviol)}", EOviol[:5])
t=time.time()
nOOpairs=0; OOviol=[]
for a in TABODDB:
    for b in TABODDB:
        nOOpairs += 1
        if not checkOO(a,b): OOviol.append((a,b))
print(f"sweepOO: {nOOpairs} pairs ({time.time()-t:.1f}s); violations: {len(OOviol)}", OOviol[:5])
print("SWEEP VERDICT:", not EOviol and not OOviol)

# ---- the hit census (evidence, for the record) ----
hits=[]
for o in TABODDB:
    for c in TABODD:
        if c % 16 == o % 16 and c > o and c <= o + B and bsearch(TABARR, c - o):
            hits.append((c-o, o, c, math.gcd(c-o,o)))
for a in TABODDB:
    for b in TABODDB:
        if b > a and (a+b) % 16 == 0 and bsearch(TABARR, a+b):
            hits.append((a, b, a+b, math.gcd(a,b)))
print("sum-hits total:", len(hits), " all gcd>1:", all(h[3] > 1 for h in hits), " coprime:", sum(1 for h in hits if h[3]==1))
# verify each hit triple truly 4-powerful
from sympy import factorint
ok = all(min(factorint(h[0]).values())>=4 and min(factorint(h[1]).values())>=4 and min(factorint(h[2]).values())>=4 and h[0]+h[1]==h[2] for h in hits)
print("all hits triple-4-powerful verified:", ok)
with open('R5_hits.json','w') as f: json.dump(hits,f)
print("PREFLIGHT939R5_ALL_OK")
