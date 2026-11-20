#!/usr/bin/env python3
# Quick verification of the W76-61K core mathematics before engine build.
import itertools
from math import comb

def mis(adj, mask, memo):
    if mask == 0: return 0
    r = memo.get(mask)
    if r is not None: return r
    v = (mask & -mask).bit_length() - 1
    a = mis(adj, mask & ~(1 << v), memo)
    b = 1 + mis(adj, mask & ~(1 << v) & ~adj[v], memo)
    r = max(a, b); memo[mask] = r
    return r

def alpha_of(n, adj): return mis(adj, (1<<n)-1, {})
def complement_adj(n, adj):
    full = (1<<n)-1
    return [(full ^ adj[i]) & ~(1<<i) for i in range(n)]
def omega_of(n, adj): return mis(complement_adj(n, adj), (1<<n)-1, {})

PLIST = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
PIDX = {p:i for i,p in enumerate(PLIST)}
def perm_patterns(edges4):
    pats = set()
    for perm in itertools.permutations(range(4)):
        s = 0
        for (a,b) in edges4:
            x,y = perm[a],perm[b]
            if x>y: x,y=y,x
            s |= 1 << PIDX[(x,y)]
        pats.add(s)
    return frozenset(pats)
C4_PAT = perm_patterns([(0,1),(1,2),(2,3),(3,0)])
K2K2_PAT = perm_patterns([(0,1),(2,3)])

def pattern_of(adj, quad):
    q = sorted(quad); s = 0; pos = 0
    for x in range(4):
        for y in range(x+1,4):
            if (adj[q[x]]>>q[y])&1: s |= 1<<pos
            pos += 1
    return s

def hfree(n, adj, PAT):
    if n < 4: return True
    for q in itertools.combinations(range(n),4):
        if pattern_of(adj,q) in PAT: return False
    return True

def adj_from_emask(n, emask, prs):
    adj = [0]*n
    for idx,(i,j) in enumerate(prs):
        if (emask>>idx)&1:
            adj[i] |= 1<<j; adj[j] |= 1<<i
    return adj

# ---- 1. the W75 Lemma-6 counterexample ------------------------------------
prs5 = [(i,j) for i in range(5) for j in range(i+1,5)]
ctr_edges = {(0,1),(0,2),(1,2),(0,3),(1,4),(3,4)}
ctr_emask = 0
for idx,(i,j) in enumerate(prs5):
    if (i,j) in ctr_edges: ctr_emask |= 1<<idx
ctr = adj_from_emask(5, ctr_emask, prs5)
print("L6-counterexample: 2K2-free?", hfree(5, ctr, K2K2_PAT),
      "| contains induced C4?", not hfree(5, ctr, C4_PAT),
      "| alpha", alpha_of(5,ctr), "omega", omega_of(5,ctr))

# ---- 2. exhaustive n<=6: corrected triangle-class laws + main bound -------
def with_triangle_class_check(n, adj):
    tri = None
    for q in itertools.combinations(range(n),3):
        a,b,c = q
        if (adj[a]>>b)&1 and (adj[a]>>c)&1 and (adj[b]>>c)&1:
            tri = (a,b,c); break
    if tri is None: return None
    a,b,c = tri
    T = (1<<a)|(1<<b)|(1<<c)
    def cls(v):
        S=[]
        if (adj[v]>>a)&1: S.append('a')
        if (adj[v]>>b)&1: S.append('b')
        if (adj[v]>>c)&1: S.append('c')
        return ''.join(sorted(S))
    classes = {}
    for v in range(n):
        if (T>>v)&1: continue
        classes.setdefault(cls(v), 0)
        classes[cls(v)] |= 1<<v
    bad_sx = 0; ab_edges = 0
    union = classes.get('',0)|classes.get('a',0)|classes.get('b',0)|classes.get('c',0)
    vs = [i for i in range(n) if (union>>i)&1]
    for i in range(len(vs)):
        for j in range(i+1,len(vs)):
            if (adj[vs[i]]>>vs[j])&1:
                ci, cj = cls(vs[i]), cls(vs[j])
                if ci == cj: bad_sx += 1
                else: ab_edges += 1
    return (bad_sx, ab_edges, tri)

def max_independent_mask(n, adj):
    best = 0; bestmask = 0
    for mask in range(1<<n):
        ok = True
        m = mask
        while m:
            i = (m & -m).bit_length()-1
            if (adj[i] & mask): ok = False; break
            m &= m-1
        if ok:
            pc = bin(mask).count('1')
            if pc > best: best = pc; bestmask = mask
    return best, bestmask

def lpc_bound_check(n, adj, side):
    a = alpha_of(n, adj); w = omega_of(n, adj)
    if side == 'C4':
        best, I = max_independent_mask(n, adj)
        assert best == a
        bound = a + a*w + comb(a,2)*w
        viol_W = 0; viol_P = 0; uncovered = 0
        outside = ((1<<n)-1) ^ I
        for v in range(n):
            if (outside>>v)&1:
                nbI = 0
                for x in range(n):
                    if (I>>x)&1 and (adj[v]>>x)&1: nbI += 1
                if nbI == 0: uncovered += 1
        degI = {}
        for v in range(n):
            if (outside>>v)&1:
                degI[v] = sum(1 for y in range(n) if (I>>y)&1 and (adj[v]>>y)&1)
        for x in range(n):
            if not (I>>x)&1: continue
            Wx = [v for v in degI if degI[v]==1 and (adj[v]>>x)&1]
            for i in range(len(Wx)):
                for j in range(i+1,len(Wx)):
                    if not (adj[Wx[i]]>>Wx[j])&1: viol_W += 1
        Ivs = [x for x in range(n) if (I>>x)&1]
        for i in range(len(Ivs)):
            for j in range(i+1,len(Ivs)):
                x,y = Ivs[i],Ivs[j]
                cn = [u for u in range(n) if (adj[x]>>u)&1 and (adj[y]>>u)&1]
                for p in range(len(cn)):
                    for q in range(p+1,len(cn)):
                        if not (adj[cn[p]]>>cn[q])&1: viol_P += 1
        return (n <= bound, viol_W, viol_P, uncovered, bound)
    else:
        # K maximum clique = max independent of complement
    # 2K2 side handled via complement symmetry below
        return None

def lpc_bound_check_2k2(n, adj):
    """2K2 side, direct: K = max clique; W^k independent; common non-neighborhoods of edges independent."""
    a = alpha_of(n, adj); w = omega_of(n, adj)
    # max clique mask
    best = 0; Kmask = 0
    for mask in range(1<<n):
        ok = True
        m = mask
        while m:
            i = (m & -m).bit_length()-1
            if (~adj[i]) & mask & ~(1<<i): ok = False; break
            m &= m-1
        if ok:
            pc = bin(mask).count('1')
            if pc > best: best = pc; Kmask = mask
    assert best == w
    bound = w + a*w + comb(w,2)*a
    outside = ((1<<n)-1) ^ Kmask
    uncovered = 0; viol_W = 0; viol_P = 0
    miss = {}
    for v in range(n):
        if (outside>>v)&1:
            miss[v] = sum(1 for y in range(n) if (Kmask>>y)&1 and not (adj[v]>>y)&1)
            if miss[v] == 0: uncovered += 1
    for x in range(n):
        if not (Kmask>>x)&1: continue
        Wx = [v for v in miss if miss[v]==1 and not (adj[v]>>x)&1]
        for i in range(len(Wx)):
            for j in range(i+1,len(Wx)):
                if (adj[Wx[i]]>>Wx[j])&1: viol_W += 1
    Kvs = [x for x in range(n) if (Kmask>>x)&1]
    for i in range(len(Kvs)):
        for j in range(i+1,len(Kvs)):
            x,y = Kvs[i],Kvs[j]
            cn = [u for u in range(n) if u!=x and u!=y and not (adj[x]>>u)&1 and not (adj[y]>>u)&1]
            for p in range(len(cn)):
                for q in range(p+1,len(cn)):
                    if (adj[cn[p]]>>cn[q])&1: viol_P += 1
    return (n <= bound, viol_W, viol_P, uncovered, bound)

stats = {'c4_cnt':0,'2k2_cnt':0,'c4_bound_bad':0,'2k2_bound_bad':0,
         'sx_bad':0,'ab_edge_graphs':0,'union_bad':0,
         'c4_violW':0,'c4_violP':0,'c4_uncov':0,'k2_violW':0,'k2_violP':0,'k2_uncov':0,
         'cube_bad':0,'sharp_bad':0,'withtri':0}
worst_c4 = (0,None); worst_k2 = (0,None); worst_sharp = (0,None)
for n in range(1,7):
    prs = [(i,j) for i in range(n) for j in range(i+1,n)]
    for emask in range(1<<len(prs)):
        adj = adj_from_emask(n, emask, prs)
        a = alpha_of(n,adj); w = omega_of(n,adj); M = max(a,w)
        if n > M**3: stats['cube_bad'] += 1
        if hfree(n, adj, C4_PAT):
            stats['c4_cnt'] += 1
            ok,vW,vP,unc,bound = lpc_bound_check(n, adj, 'C4')
            if not ok: stats['c4_bound_bad'] += 1
            stats['c4_violW'] += vW; stats['c4_violP'] += vP; stats['c4_uncov'] += unc
            ratio = n/max(bound,1)
            if ratio > worst_c4[0]: worst_c4 = (ratio, (n,emask,a,w))
            if a*w < 4*n/5 - 1e-12: stats['sharp_bad'] += 1; worst_sharp=(a*w,(n,emask,a,w))
        if hfree(n, adj, K2K2_PAT):
            stats['2k2_cnt'] += 1
            ok,vW,vP,unc,bound = lpc_bound_check_2k2(n, adj)
            if not ok: stats['2k2_bound_bad'] += 1
            stats['k2_violW'] += vW; stats['k2_violP'] += vP; stats['k2_uncov'] += unc
            ratio = n/max(bound,1)
            if ratio > worst_k2[0]: worst_k2 = (ratio, (n,emask,a,w))
            r = with_triangle_class_check(n, adj)
            if r is not None:
                stats['withtri'] += 1
                bsx, abe, tri = r
                if bsx: stats['sx_bad'] += 1
                if abe: stats['ab_edge_graphs'] += 1
print(stats)
print("worst C4 ratio", worst_c4)
print("worst 2K2 ratio", worst_k2)
print("worst sharp", worst_sharp)
