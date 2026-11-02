# Collision census: all exact-halving pairs and general collisions in windows.
# A collision: disjoint P,Q subsets of [1,M] with sum_{a in P} a*2^(M-a) == sum_{a in Q} a*2^(M-a)
import sys
from itertools import combinations
sys.setrecursionlimit(10000)

def scaled_sums(indices, M):
    # all subset sums (as scaled ints) -> dict sum -> list of subsets (bitmasks)
    d = {0: [0]}
    for a in indices:
        w = a << (M - a)
        nd = {}
        for s, masks in d.items():
            for msk in masks:
                nd.setdefault(s, []).append(msk)
        for s, masks in d.items():
            for msk in masks:
                nd.setdefault(s + w, []).append(msk | (1 << a))
        d = nd
    return d

# ---- Part 1: min-support census via MITM over [N, M] ----
# find, for each N up to 40, the smallest window [N, M] containing a collision with min support exactly N
print("=== min-support census (exact, disjoint P,Q) ===")
def collisions_in_window(N, M):
    # MITM: left = [N, mid], right = (mid, M]
    mid = (N + M) // 2
    L = list(range(N, mid+1)); R = list(range(mid+1, M+1))
    dl = scaled_sums(L, M); dr = scaled_sums(R, M)
    out = []
    for s, lmsks in dl.items():
        if -s in dr or (0 - s) in dr:  # need s + s' = 0 -> s' = -s: all weights positive so only s=0 vs 0... 
            pass
    # weights positive: collision = P-side sum equals Q-side sum: total over both halves:
    # enumerate all subset sums of full window grouped: two subsets with equal sum, disjoint
    # simpler: dl keys x, dr keys y: a collision = x1+y1 = x2+y2 with different (x,y) pairs -> 
    # collect all sums x+y with their (P,Q) split is complex; instead: direct group by total
    return None

# Direct approach for small windows: group ALL subsets of [N..M] by scaled sum; 
# subsets with equal sum are automatically DISJOINT-after-cancel? No — they may overlap.
# Collision pair (P,Q) disjoint with equal sums == signed eps in {-1,0,1}: enumerate via 3-way MITM.
def signed_relations(N, M):
    mid = (N + M) // 2
    L = list(range(N, mid+1)); R = list(range(mid+1, M+1))
    # sums with sign for left half: dict value -> list of (signed mask) ; value = sum eps_a * a*2^(M-a)
    dl = {0: [(0,0)]}  # (pmask, nmask)
    for a in L:
        w = a << (M - a)
        nd = {}
        for s, lst in dl.items():
            for pm, nm in lst: nd.setdefault(s, []).append((pm, nm))
            # plus
            nd.setdefault(s + w, []).extend((pm | (1<<a), nm) for pm, nm in lst)
            # minus
            nd.setdefault(s - w, []).extend((pm, nm | (1<<a)) for pm, nm in lst)
        dl = nd
    dr = {0: [(0,0)]}
    for a in R:
        w = a << (M - a)
        nd = {}
        for s, lst in dr.items():
            for pm, nm in lst: nd.setdefault(s, []).append((pm, nm))
            nd.setdefault(s + w, []).extend((pm | (1<<a), nm) for pm, nm in lst)
            nd.setdefault(s - w, []).extend((pm, nm | (1<<a)) for pm, nm in lst)
        dr = nd
    res = []
    for s, ll in dl.items():
        if -s in dr:
            for (pm1, nm1) in ll:
                for (pm2, nm2) in dr[-s]:
                    P = pm1 | pm2; Q = nm1 | nm2
                    if P and Q and not (P & Q):  # disjoint, nonempty
                        res.append((P, Q))
    return res

def minsup(x): return (x & -x).bit_length() - 1
def bm(mask):
    return sorted(i for i in range(64) if mask >> i & 1)

found = {}
import sys
for N in range(1, 41):
    for M in range(N+2, min(N+26, 61)):
        rels = signed_relations(N, M)
        real = [(P,Q) for P,Q in rels if minsup(P|Q) == N]  # min support exactly N
        if real:
            found[N] = (M, real[0], len(real))
            break
    print(f"N={N:2d}: " + (f"collision in [{N},{found[N][0]}], e.g. {bm(found[N][1][0])} vs {bm(found[N][1][1])} ({found[N][2]} in window)" if N in found else "NONE up to M=N+25"))
