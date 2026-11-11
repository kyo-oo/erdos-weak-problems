#!/usr/bin/env python3
"""W2r battle battery — Erdos #711.
E1: descending-key largest-multiple greedy for THEOREM U (f <= 2n-1) over full periods + adversarial m.
E2: full Hall census (all subsets) n<=10 full period; antichain tight-set census.
E3: f(n,n) exact n<=240; N-window (m=n) tight-set census at F=ceil(3n/2), +1.
E4: landscape f(n,m) for m in ranges.
E5: greedy invariant mining (walk distances, positions).
E6: Conjecture G census (arbitrary key subsets, window 2N-2).
E7: end-peeling strategy test.
E8: N-window greedy variants.
"""
import sys, math, random
from math import gcd, floor, ceil
from functools import reduce

def lcm(a,b): return a*b//gcd(a,b)
def lcms(*xs):
    r = 1
    for x in xs: r = lcm(r,x)
    return r

random.seed(711711)

# ---------- Hopcroft-Karp bipartite matching ----------
def hopcroft_karp(L, R, adj):
    """L,R: lists of hashable nodes (indices ok); adj: dict L->set of R. Returns matching size (L-saturating attempt)."""
    INF = float('inf')
    pairL = {l: None for l in L}
    pairR = {r: None for r in R}
    dist = {}
    def bfs():
        q = []
        for l in L:
            if pairL[l] is None:
                dist[l] = 0; q.append(l)
            else:
                dist[l] = INF
        found = False
        qi = 0
        while qi < len(q):
            l = q[qi]; qi += 1
            for r in adj[l]:
                lr = pairR[r]
                if lr is None:
                    found = True
                elif dist.get(lr, INF) == INF:
                    dist[lr] = dist[l] + 1; q.append(lr)
        return found
    def dfs(l):
        for r in adj[l]:
            lr = pairR[r]
            if lr is None or (dist.get(lr, INF) == dist[l] + 1 and dfs(lr)):
                pairL[l] = r; pairR[r] = l
                return True
        dist[l] = INF
        return False
    matching = 0
    while bfs():
        for l in L:
            if pairL[l] is None and dfs(l):
                matching += 1
    return matching, pairL

def assign_exists(n, m, F):
    """Does window (m, m+F) (ints m+1..m+F-1) admit distinct a_k, k|a_k, k=1..n?"""
    if F-1 < n: return False
    keys = list(range(1, n+1))
    ints = list(range(m+1, m+F))
    adj = {k: set(x for x in ints if x % k == 0) for k in keys}
    for k in keys:
        if not adj[k]: return False
    size, _ = hopcroft_karp(keys, ints, adj)
    return size == n

def f_exact(n, m, Fmax=None):
    if Fmax is None: Fmax = 2*n-1
    lo, hi = n, Fmax   # need at least n integers -> F-1>=n -> F>=n+1; but search from 1
    lo = 1
    # binary search minimal F with assign_exists
    lo, hi = 1, Fmax
    while lo < hi:
        mid = (lo+hi)//2
        if assign_exists(n, m, mid): hi = mid
        else: lo = mid+1
    return lo if assign_exists(n, m, lo) else None

# ---------- E1: greedy descending ----------
def greedy_desc(n, m, collect=None):
    W = 2*n-2; T = m+W
    used = set(); a = [0]*(n+1)
    for k in range(n, 0, -1):
        x = (T//k)*k
        walk = 0
        while x <= m or x in used:
            x -= k; walk += 1
            if x <= m:
                return False, None, None
        a[k] = x; used.add(x)
        if collect is not None: collect.append((k, x-m, walk))
    return True, a, used

def adversarial_ms(n):
    L = reduce(lcm, range(1, n+1), 1)
    ms = set()
    base = (n-1)**2
    for j in range(-3, 4): ms.add(base + j*(2*n-1))
    for d in range(-4, 5): ms.add(base + d)
    for t in range(-2, 3):
        for d in range(-2*n, 3*n): pass
    for d in range(-2*n, 3*n+1): ms.add(base+d)   # dense scan near obstruction
    ms.update(range(1, 60))
    ms.add(n*n); ms.add(n*n-1); ms.add(n*(n-1)); ms.add(n*(n-1)-1)
    ms.add(L//2); ms.add(L); ms.add(L+1); ms.add(base - (n-1)); ms.add(base + (n-1))
    for _ in range(200): ms.add(random.randint(1, max(10, base*3)))
    return [m for m in ms if m >= 1]

def run_E1():
    print("=== E1: descending greedy, THEOREM U (f(n,m) <= 2n-1), window = 2n-2 ints ===")
    total = 0; fails = []
    for n in range(2, 13):
        L = reduce(lcm, range(1, n+1), 1)
        per = min(L, 27720)
        bad = 0
        for m in range(1, per+1):
            ok, a, _ = greedy_desc(n, m)
            total += 1
            if not ok or not (all(m < a[k] < m+2*n-1 and a[k] % k == 0 for k in range(1,n+1)) and len(set(a[1:]))==n):
                bad += 1; fails.append((n,m))
        print(f"n={n:2d}: full period {per} m-values, greedy failures: {bad}")
    for n in list(range(13, 17)):
        ms = adversarial_ms(n) + [random.randint(1, 10**7) for _ in range(3000)]
        bad = 0
        for m in ms:
            ok, a, _ = greedy_desc(n, m)
            total += 1
            if not ok or not (all(m < a[k] < m+2*n-1 and a[k] % k == 0 for k in range(1,n+1)) and len(set(a[1:]))==n):
                bad += 1; fails.append((n,m))
        print(f"n={n:2d}: adversarial+random ({len(ms)} m-values), greedy failures: {bad}")
    for n in list(range(17, 65)):
        ms = adversarial_ms(n)[:120] + [random.randint(1, 10**8) for _ in range(300)]
        bad = 0
        for m in ms:
            ok, a, _ = greedy_desc(n, m)
            total += 1
            if not ok: bad += 1; fails.append((n,m))
        if bad: print(f"n={n}: FAILS {bad}")
    print(f"E1 TOTAL runs: {total}, total failures: {len(fails)}", fails[:5])
    for n in [100, 199, 316, 500, 997]:
        ms = adversarial_ms(n)[:80] + [random.randint(1, 10**9) for _ in range(60)]
        bad = sum(0 if greedy_desc(n,m)[0] else 1 for m in ms)
        print(f"n={n}: {len(ms)} adversarial+random, failures: {bad}")

# ---------- E2: full Hall census ----------
def antichains(n):
    masks = []
    for S in range(1, 1<<n):
        ks = [i+1 for i in range(n) if S>>i & 1]
        ok = True
        for i in range(len(ks)):
            for j in range(i+1, len(ks)):
                if ks[j] % ks[i] == 0: ok = False; break
            if not ok: break
        if ok: masks.append(S)
    return masks

def run_E2():
    print("=== E2: FULL Hall census (all subsets S of [1,n]), window 2n-2 ints, full periods ===")
    for n in range(2, 11):
        L = reduce(lcm, range(1, n+1), 1)
        per = min(L, 2520)
        worst = 10**9; worst_at = None
        tight = {}   # S tuple -> count
        tight_examples = {}
        for m in range(1, per+1):
            W = 2*n-2
            # mask per key: bit i (i=0..W-1) set iff (m+1+i) % k == 0
            kmasks = {}
            for k in range(1, n+1):
                mk = 0
                for i, x in enumerate(range(m+1, m+W+1)):
                    if x % k == 0: mk |= 1 << i
                kmasks[k] = mk
            for S in range(1, 1<<n):
                ks = [i+1 for i in range(n) if S>>i & 1]
                u = 0
                for k in ks: u |= kmasks[k]
                nb = bin(u).count('1')
                d = nb - len(ks)   # Hall margin
                if d < worst: worst = d; worst_at = (m, tuple(ks))
                if d == 0 and len(ks) >= 2:
                    t = tuple(ks)
                    tight[t] = tight.get(t, 0) + 1
                    tight_examples.setdefault(t, m)
        print(f"n={n}: period {per}; min over (m,S) of |N(S)|-|S| = {worst} at m={worst_at[0]}, S={worst_at[1]}")
        big = sorted(((len(t), t, c, tight_examples[t]) for t, c in tight.items()), key=lambda z: -z[0])[:12]
        for sz, t, c, ex in big:
            print(f"   tight antichain S={t} (|S|={sz}) count={c}, e.g. m={ex}")
    # matching-based Hall for n=11..16 sampled
    print("E2b: matching-based Hall, n=11..16, sampled m (incl. adversarial):")
    for n in range(11, 17):
        ms = adversarial_ms(n)[:200] + [random.randint(1, 10**6) for _ in range(400)]
        bad = sum(0 if assign_exists(n, m, 2*n-1) else 1 for m in ms)
        print(f"  n={n}: {len(ms)} m-values, Hall violations: {bad}")

# ---------- E3: Theorem N ----------
def run_E3():
    print("=== E3: f(n,n) exact values, n<=240; N-window tight census ===")
    flag = []
    for n in range(2, 241):
        v = f_exact(n, n, Fmax=2*n+2)
        c = (3*n + 1)//2 if n % 2 else 3*n//2   # ceil(3n/2)
        if v is None or v > c:
            flag.append((n, v, c))
        if n <= 20 or n % 40 == 0:
            print(f"  n={n:3d}: f(n,n)={v}, ceil(3n/2)={c}, ok={v is not None and v<=c}")
    print(f"E3 flags (n where f(n,n) > ceil(3n/2)): {flag[:10]} total {len(flag)}")
    # N-window tight-set census at F = ceil(3n/2) and +1
    for n in range(2, 15):
        for F in [ (3*n+1)//2 if n%2 else 3*n//2, ((3*n+1)//2 if n%2 else 3*n//2)+1 ]:
            m = n
            worst = 10**9; worst_at=None; tight={}
            ints = list(range(m+1, m+F))
            adj = {k: set(x for x in ints if x%k==0) for k in range(1,n+1)}
            size, pairL = hopcroft_karp(list(range(1,n+1)), ints, adj)
            # census
            for S in range(1, 1<<n):
                ks=[i+1 for i in range(n) if S>>i&1]
                u=set()
                for k in ks: u |= adj[k]
                d=len(u)-len(ks)
                if d<worst: worst=d; worst_at=(tuple(ks),)
                if d==0 and len(ks)>=2: tight[tuple(ks)]=tight.get(tuple(ks),0)+1
            print(f"  n={n:2d} m=n F={F}: matchsize={size}/{n}, minmargin={worst}, #tightsets(|S|>=2)={len(tight)}")
            if F==(((3*n+1)//2 if n%2 else 3*n//2)+1) and tight:
                bigs=sorted(((len(t),t,c) for t,c in tight.items()),key=lambda z:-z[0])[:6]
                for sz,t,c in bigs: print(f"     tight S={t} |S|={sz}")

# ---------- E4: landscape ----------
def run_E4():
    print("=== E4: f(n,m) landscape ===")
    for n in [6, 8, 10, 12]:
        row = []
        for m in range(1, 121):
            row.append(f_exact(n, m))
        print(f"n={n}: f(n,m) m=1..120:", row)
    print("n=10, m near 81 (=(n-1)^2):")
    print([ (m, f_exact(10,m)) for m in range(70, 110, 2) ])

# ---------- E5: greedy invariant mining ----------
def run_E5():
    print("=== E5: greedy walk distances / positions (min over k of a_k-m; max walk) ===")
    mx_walk = 0; mn_pos = 10**9; ex=None
    for n in range(2, 13):
        L = reduce(lcm, range(1, n+1), 1); per=min(L, 2520)
        for m in range(1, per+1):
            col=[]
            ok,a,_=greedy_desc(n,m,collect=col)
            if not ok: continue
            for k,pos,walk in col:
                if walk>mx_walk: mx_walk=walk
                if pos<mn_pos: mn_pos=pos; ex=(n,m,k,pos)
    print(f"max walk-down steps: {mx_walk}; min window position of any a_k: {mn_pos} (ex: {ex})")
    # check hypothesis: a_k >= m + 2(n-k) for all k? and a_k >= m+?
    for n in [6, 10, 12]:
        L = reduce(lcm, range(1, n+1), 1); per=min(L, 2520)
        viol=0; viol2=0; viol3=0
        for m in range(1, per+1):
            ok,a,_=greedy_desc(n,m)
            if not ok: continue
            for k in range(1, n+1):
                if a[k]-m < 2*(n-k): viol+=1      # H1: pos >= 2(n-k)
                if a[k]-m < (n-k): viol2+=1       # H2: pos >= n-k
                if a[k] < k*2 and m < k: viol3+=1  # H3 (nonsense sanity)
        print(f"n={n}: H1 violations(pos<2(n-k))={viol}, H2(pos<n-k)={viol2}")

# ---------- E6: Conjecture G ----------
def run_E6():
    print("=== E6: Conjecture G: arbitrary K subset [1,N], window 2N-2 ints ===")
    for N in range(1, 8):
        L = reduce(lcm, range(1, N+1), 1); per = min(L, 840)
        fails = []
        for Kmask in range(1, 1<<N):
            K = [i+1 for i in range(N) if Kmask>>i&1]
            for m in range(1, per+1):
                W = 2*N-2
                ints = list(range(m+1, m+W+1))
                adj = {k: set(x for x in ints if x%k==0) for k in K}
                if any(not adj[k] for k in K): fails.append((K,m,'empty')); continue
                size,_ = hopcroft_karp(K, ints, adj)
                if size < len(K): fails.append((K,m)); break
        print(f"N={N}: {'OK all K' if not fails else 'FAILS: '+str(fails[:3])}")

# ---------- E7: end-peeling ----------
def run_E7():
    print("=== E7: end-peeling (assign end integer to its largest divisor among remaining keys) ===")
    def endpeel(n, m, rule='largediv'):
        W=2*n-2; lo, hi = m+1, m+W
        K = set(range(1, n+1)); a={}
        while K:
            cands=[]
            for end in (lo, hi):
                divs = [d for d in K if end % d == 0]
                if divs: cands.append((end, max(divs) if rule=='largediv' else min(divs)))
            if not cands: return False, a
            if len(cands)==1: end,d = cands[0]
            else:
                # prefer the end with the largest divisor
                cands.sort(key=lambda z: -z[1]); end,d = cands[0]
            a[d]=end; K.remove(d)
            if end==lo: lo+=1
            else: hi-=1
        return True, a
    for n in range(2, 13):
        L=reduce(lcm, range(1,n+1),1); per=min(L,2520)
        bad=0; ex=None
        for m in range(1, per+1):
            ok,a=endpeel(n,m)
            if not ok or not (all(m<a[k]<m+2*n-1 and a[k]%k==0 for k in a) and len(set(a.values()))==n and len(a)==n):
                bad+=1; ex=(m,a)
        print(f"n={n}: end-peel failures over period {per}: {bad}" + (f" ex={ex}" if bad else ""))

# ---------- E8: N-window greedy variants ----------
def run_E8():
    print("=== E8: N-window constructions at m=n ===")
    def variant(n, mode):
        F = 2*n+8  # generous window; measure max a_k - n
        used=set(); amax=0; a=[0]*(n+1)
        # top block
        h = n//2
        for k in range(h+1, n+1):
            x=2*k; a[k]=x; used.add(x); amax=max(amax,x)
        # bottom ascending, smallest unused multiple > n
        for k in range(1, h+1):
            if mode=='asc':
                x = ((n//k)+1)*k
                while x in used: x += k
            else:  # desc: largest unused multiple <= n+F... unbounded: take largest multiple <= 5n//2+8 unused, walk down
                x = ((n + 3*n//2 + 8)//k)*k
                while x in used or x<=n: x -= k
            if x <= n: return None
            a[k]=x; used.add(x); amax=max(amax,x)
        # verify
        for k in range(1,n+1):
            if a[k]<=n or a[k]%k: return None
        if len(set(a[1:]))!=n: return None
        return amax - n  # minimal F-1 needed
    for n in [6,8,10,12,16,20,24,30,40,50,60,80,100,120,150,200,240]:
        r1 = variant(n,'asc'); r2 = variant(n,'desc')
        print(f"n={n}: asc-scheme needs F>={r1 if r1 else 'FAIL'}, desc-scheme F>={r2 if r2 else 'FAIL'}, ceil(3n/2)={(3*n+1)//2}")

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv)>1 else 'all'
    if which in ('all','E1'): run_E1()
    if which in ('all','E5'): run_E5()
    if which in ('all','E2'): run_E2()
    if which in ('all','E3'): run_E3()
    if which in ('all','E4'): run_E4()
    if which in ('all','E6'): run_E6()
    if which in ('all','E7'): run_E7()
    if which in ('all','E8'): run_E8()
    print("BATTERY DONE.")
