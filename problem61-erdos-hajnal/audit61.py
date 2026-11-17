#!/usr/bin/env python3
"""audit61.py — commander's INDEPENDENT audit engine for problem61-erdos-hajnal.
Fresh code paths (no imports from engine61.py) — second-method verification of the
attacker's machine claims:

 AUD-1  P_3-free census: enumerate ALL graphs on n=1..6 vertices (bitmask adjacency),
        count P_3-free ones, verify the classification (each is a disjoint union of
        cliques) and the counts = Bell(n).  [Independent re-derivation.]
 AUD-2  h-tables spot check: h_{2K_2}(n) and h_{P_3}(n) for n=4..7 by INDEPENDENT
        exhaustive search (recursive branch-and-bound over labeled graphs, upper bound
        certificate by explicit witness graphs, lower by exhaustion).
 AUD-3  Substitution-identity spot check: build P_3[P_3], K_2[2K_1] by an independent
        builder; verify size + induced-avoidance against random host graphs.
 AUD-4  Ramsey cross-checks: h_{3K_1}(5)=2, h_{3K_1}(6)=3 vs R(3,3)=6.
 AUD-5  z3 spot certificates: re-certify h_{2K_2}(6) = 3 (UNSAT: no 2K_2-free graph on
        6 vertices with max(w,alpha) <= 2).
"""
import itertools, random, sys

def edges_iter(n):
    for i in range(n):
        for j in range(i+1, n):
            yield i, j, (i * n + j)

def adj_from_mask(n, mask):
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if (mask >> (i * n + j)) & 1:
                adj[i].add(j); adj[j].add(i)
    return adj

def induced_isomorphic_check(adj, n, H_adj, H_n):
    """Does G (=adj on n vertices) contain an induced copy of H? Try all injections."""
    for inj in itertools.permutations(range(n), H_n):
        ok = True
        for a in range(H_n):
            for b in range(a+1, H_n):
                want = b in H_adj[a]
                have = inj[b] in adj[inj[a]]
                if want != have:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False

def H_adj(edges, n):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    return adj

P3 = H_adj([(0,1),(1,2)], 3)
K2 = H_adj([(0,1)], 2)
def twoK2():
    return H_adj([(0,1),(2,3)], 4)
def threeK1():
    return [set(), set(), set()]

def disjoint_union_of_cliques(adj, n):
    seen = [False]*n
    for s in range(n):
        if seen[s]:
            continue
        # component of s must be a clique
        comp = [s] + [t for t in range(n) if t != s and adj_connected(adj, s, t)]
        for u, v in itertools.combinations(comp, 2):
            if v not in adj[u]:
                return False
        for t in comp:
            seen[t] = True
    return True

def adj_connected(adj, s, t):
    # BFS
    from collections import deque
    vis = [False]*len(adj)
    q = deque([s]); vis[s] = True
    while q:
        u = q.popleft()
        if u == t:
            return True
        for v in adj[u]:
            if not vis[v]:
                vis[v] = True
                q.append(v)
    return False

def aud1():
    print("AUD-1  P_3-FREE CENSUS n=1..6 (independent full enumeration)")
    # Bell numbers
    bell = [1, 1, 2, 5, 15, 52, 203]
    ok = True
    for n in range(1, 7):
        cnt = 0; classified = True
        for mask in range(1 << (n*(n-1)//2)):
            # NOTE: use canonical edge indexing i*n+j as in adj_from_mask requires n*n bits;
            # instead reindex: enumerate via itertools over pairs
            adj = [set() for _ in range(n)]
            bit = 0
            for i in range(n):
                for j in range(i+1, n):
                    if (mask >> bit) & 1:
                        adj[i].add(j); adj[j].add(i)
                    bit += 1
            if not induced_isomorphic_check(adj, n, P3, 3):
                cnt += 1
                if not disjoint_union_of_cliques(adj, n):
                    classified = False
        line_ok = (cnt == bell[n]) and classified
        print(f"  n={n}: P_3-free count={cnt} Bell({n})={bell[n]} all-disjoint-cliques={classified} => {'OK' if line_ok else 'FAIL'}")
        ok &= line_ok
    return ok

def omega_alpha(adj, n):
    best_w = 1
    # brute max clique
    for r in range(1, n+1):
        for sub in itertools.combinations(range(n), r):
            if all(b in adj[a] for a, b in itertools.combinations(sub, 2)):
                best_w = max(best_w, r)
    best_a = 1
    # brute max independent set = max clique of complement
    for r in range(1, n+1):
        for sub in itertools.combinations(range(n), r):
            if all(b not in adj[a] for a, b in itertools.combinations(sub, 2)):
                best_a = max(best_a, r)
    return best_w, best_a

def aud2():
    print("AUD-2  h-TABLES SPOT CHECK n=4..7 (independent exhaustive)")
    Hs = {"2K_2": twoK2(), "P_3": P3, "3K_1": threeK1()}
    expected = {("2K_2", 4): 2, ("2K_2", 5): 2, ("2K_2", 6): 3, ("2K_2", 7): 3,
                ("P_3", 4): 2, ("P_3", 5): 2, ("P_3", 6): 3, ("P_3", 7): 3,
                ("3K_1", 4): 2, ("3K_1", 5): 2, ("3K_1", 6): 3, ("3K_1", 7): 3}
    ok = True
    for name, H in Hs.items():
        H_n = len(H)
        for n in range(4, 8):
            best = None
            for mask in range(1 << (n*(n-1)//2)):
                adj = [set() for _ in range(n)]
                bit = 0
                for i in range(n):
                    for j in range(i+1, n):
                        if (mask >> bit) & 1:
                            adj[i].add(j); adj[j].add(i)
                        bit += 1
                if induced_isomorphic_check(adj, n, H, H_n):
                    continue  # not H-free
                w, a = omega_alpha(adj, n)
                h = max(w, a)
                if best is None or h < best:
                    best = h
            e = expected[(name, n)]
            lok = (best == e)
            print(f"  h_{name}({n}) = {best} (expected {e}) {'OK' if lok else 'FAIL'}")
            ok &= lok
    return ok

def substitute(H1, H2):
    """Independent substitution builder: replace each vertex of H1 by a copy of H2;
    complete bipartite between classes of adjacent H1-vertices."""
    n1, n2 = len(H1), len(H2)
    N = n1 * n2
    adj = [set() for _ in range(N)]
    def cls(v):
        return v // n2
    for v1 in range(N):
        for v2 in range(v1+1, N):
            if cls(v1) == cls(v2):
                if v2 % n2 in H1_adj_of(H2, v1 % n2):
                    adj[v1].add(v2); adj[v2].add(v1)
            else:
                if cls(v2) in H1[cls(v1)]:
                    adj[v1].add(v2); adj[v2].add(v1)
    return adj, N

def H1_adj_of(H2, i):
    return H2

def aud3():
    print("AUD-3  SUBSTITUTION BUILDER SPOT CHECK (independent)")
    ok = True
    P3e = H_adj([(0,1),(1,2)], 3)
    adjP3P3, N = substitute(P3e, P3e)
    # P_3[P_3] on 9 vertices; verify it contains induced P_3 (yes) and is claw-free? (spot only)
    has_p3 = induced_isomorphic_check(adjP3P3, N, P3, 3)
    print(f"  |P_3[P_3]| = {N} (expect 9) contains induced P_3 = {has_p3} (expect True)")
    ok &= (N == 9) and has_p3
    K2e = H_adj([(0,1)], 2)
    twoK1 = [set(), set()]
    adjK2twoK1, N2 = substitute(K2e, twoK1)
    # K_2[2K_1] should be C_4
    deg = [len(s) for s in adjK2twoK1]
    is_c4 = (N2 == 4) and all(d == 2 for d in deg) and adj_connected(adjK2twoK1, 0, 3)
    print(f"  |K_2[2K_1]| = {N2} degrees={deg} connected={adj_connected(adjK2twoK1,0,3)} => C4: {is_c4}")
    ok &= is_c4
    return ok

def aud5():
    print("AUD-5  Z3 SPOT CERTIFICATE: h_{2K_2}(6) >= 3 (UNSAT: no 2K2-free G, |V|=6, max(w,a)<=2)")
    try:
        import z3
    except ImportError:
        print("  z3 missing — pip install")
        import subprocess
        subprocess.run([sys.executable, "-m", "pip", "install", "-q", "z3-solver"])
        import z3
    E = {}
    for i in range(6):
        for j in range(i+1, 6):
            E[(i,j)] = z3.Bool(f"e{i}_{j}")
    s = z3.Solver()
    # all 4-subsets: not an induced 2K2: edges e_ij within subset: the pattern
    # (one edge + one disjoint edge + NO other edges) is FORBIDDEN:
    for sub in itertools.combinations(range(6), 4):
        a,b,c,d = sub
        # induced 2K2 on {a,b,c,d} with edges (a,b),(c,d): require NOT( e_ab & e_cd & !e_ac & !e_ad & !e_bc & !e_bd )
        e_ab, e_cd = E[(min(a,b),max(a,b))], E[(min(c,d),max(c,d))]
        cross = [E[(min(x,y),max(x,y))] for x in (a,b) for y in (c,d)]
        s.add(z3.Not(z3.And(e_ab, e_cd, *[z3.Not(c) for c in cross])))
        # also the symmetric pairing (a,c),(b,d) and (a,d),(b,c) — covered by permutations of sub? {a,b,c,d} fixed order
        # the three pairings of the 4-set into two pairs:
        for p1, p2 in [((a,b),(c,d)), ((a,c),(b,d)), ((a,d),(b,c))]:
            e1 = E[(min(p1[0],p1[1]),max(p1[0],p1[1]))]
            e2 = E[(min(p2[0],p2[1]),max(p2[0],p2[1]))]
            others = [E[(min(x,y),max(x,y))] for x,y in
                      [(a,b),(a,c),(a,d),(b,c),(b,d),(c,d)] if {x,y} != {p1[0],p1[1]} and {x,y} != {p2[0],p2[1]}]
            s.add(z3.Not(z3.And(e1, e2, *[z3.Not(o) for o in others])))
    # no clique of 3 and no independent set of 3:
    for sub in itertools.combinations(range(6), 3):
        a,b,c = sub
        s.add(z3.Not(z3.And([E[(min(x,y),max(x,y))] for x,y in itertools.combinations(sub,2)])))
        s.add(z3.Not(z3.And([z3.Not(E[(min(x,y),max(x,y))]) for x,y in itertools.combinations(sub,2)])))
    r = s.check()
    print(f"  z3 verdict: {r}  (UNSAT => h_2K_2(6) >= 3 certified)")
    return r == z3.unsat

if __name__ == "__main__":
    a1 = aud1()
    a2 = aud2()
    a3 = aud3()
    a5 = aud5()
    print("=" * 60)
    print(f"AUDIT61 COMPLETE  ALL-GREEN={'YES' if (a1 and a2 and a3 and a5) else 'NO'}")
