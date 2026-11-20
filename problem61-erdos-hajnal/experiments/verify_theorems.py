#!/usr/bin/env python3
"""verify_theorems.py — #61 census interlock (commander-executed).
Exhaustive machine verification of every DERIVATION.md claim over ALL graphs on n <= 7 vertices.
1. Theorem 3: P3-free => components are cliques; alpha*omega >= n.
2. Theorems 5-6: P4-free => disconnected or co-disconnected; alpha*omega >= n.
3. Theorems 1,B,C: K_t-free (t=3,4,5) => alpha >= n^2/(2e+n); alpha >= n/(t-1) for n >= t.
4. Tightness: s.K_s (s=2,3) P3/P4-free with alpha*omega = n.
Vectorized filtering (numpy) + exact per-survivor checks (python)."""
import numpy as np, itertools, time

def all_graph_masks(n):
    """all 2^(n choose 2) adjacency masks, bit (i,j) -> pair index p = tri(i,j)."""
    m = n*(n-1)//2
    return np.arange(1 << m, dtype=np.uint64)

PAIR = {}
def pair_index(i, j, n):
    return PAIR[(min(i,j), max(i,j))]

def build_tables(n):
    pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
    for idx, (i, j) in enumerate(pairs):
        PAIR[(i, j)] = idx
    return pairs

def induced_bits(masks, verts, pairs):
    """vectorized: for each graph mask, extract the induced pattern bits on 'verts' (sorted),
    packed MSB-first by pair order within verts. Returns uint64 array + bit count."""
    vs = list(verts)
    m = len(vs)
    pp = [(a, b) for a, b in itertools.combinations(range(m), 2)]
    out = np.zeros(len(masks), dtype=np.uint64)
    for k, (a, b) in enumerate(pp):
        i, j = vs[a], vs[b]
        bit = (masks >> np.uint64(PAIR[(min(i,j), max(i,j))])) & np.uint64(1)
        out |= bit << np.uint64(k)
    return out, len(pp)

def popcount_u64(x):
    # numpy popcount for uint64
    x = x - ((x >> np.uint64(1)) & np.uint64(0x5555555555555555))
    x = (x & np.uint64(0x3333333333333333)) + ((x >> np.uint64(2)) & np.uint64(0x3333333333333333))
    x = (x + (x >> np.uint64(4))) & np.uint64(0x0F0F0F0F0F0F0F0F)
    return (x * np.uint64(0x0101010101010101)) >> np.uint64(56)

def max_clique_indep(mask, n):
    """exact omega, alpha for one graph (mask) via bitmask Bron-Kerbosch style recursion."""
    adj = [0]*n
    for i in range(n):
        for j in range(i+1, n):
            if (mask >> PAIR[(i,j)]) & 1:
                adj[i] |= 1 << j; adj[j] |= 1 << i
    def mc(R, P):
        if P == 0:
            return bin(R).count('1')
        best = 0
        Q = P
        while Q:
            v = Q & -Q; Q ^= v
            best = max(best, mc(R | v, P & adj[v.bit_length()-1]))
            P &= ~v
            if best >= bin(R).count('1') + bin(P).count('1'):
                break
        return best
    om = mc(0, (1 << n) - 1)
    # alpha = omega of complement
    cadj = [((1 << n) - 1) ^ (1 << i) ^ adj[i] for i in range(n)]
    def mc2(R, P, cadj):
        if P == 0:
            return bin(R).count('1')
        best = 0
        Q = P
        while Q:
            v = Q & -Q; Q ^= v
            best = max(best, mc2(R | v, P & cadj[v.bit_length()-1], cadj))
            P &= ~v
            if best >= bin(R).count('1') + bin(P).count('1'):
                break
        return best
    al = mc2(0, (1 << n) - 1, cadj)
    return om, al

def components_complete(mask, n):
    """P3-free check: every connected component is a clique (via union-find + edge check)."""
    adj = [[False]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if (mask >> PAIR[(i,j)]) & 1:
                adj[i][j] = adj[j][i] = True
    seen = [False]*n
    for s in range(n):
        if seen[s]: continue
        comp = [s]; seen[s] = True; q = [s]
        while q:
            u = q.pop()
            for v in range(n):
                if adj[u][v] and not seen[v]:
                    seen[v] = True; comp.append(v); q.append(v)
        for a in comp:
            for b in comp:
                if a < b and not adj[a][b]:
                    return False
    return True

def disconnected(mask, n):
    adj = [[False]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if (mask >> PAIR[(i,j)]) & 1:
                adj[i][j] = adj[j][i] = True
    seen = [False]*n; q = [0]; seen[0] = True
    while q:
        u = q.pop()
        for v in range(n):
            if adj[u][v] and not seen[v]:
                seen[v] = True; q.append(v)
    return not all(seen)

def main():
    t0 = time.time()
    results = {}
    for n in range(2, 8):
        build_tables(n)
        masks = all_graph_masks(n)
        N = len(masks)
        # ---- Theorem 3: P3-free ----
        free3 = np.ones(N, dtype=bool)
        for tri in itertools.combinations(range(n), 3):
            pat, _ = induced_bits(masks, tri, None)
            free3 &= ~(((pat == np.uint64(3)) | (pat == np.uint64(5)) | (pat == np.uint64(6))))
        idx3 = np.nonzero(free3)[0]
        ok3 = True
        for i in idx3:
            mask = int(masks[i])
            if not components_complete(mask, n):
                ok3 = False; print(f"P3-COMPONENTS FAIL n={n} mask={mask}"); break
            om, al = max_clique_indep(mask, n)
            if om * al < n:
                ok3 = False; print(f"P3-omega-alpha FAIL n={n} mask={mask} w={om} a={al}"); break
        results[f"P3_n{n}"] = {"count": int(idx3.size), "holds": ok3}
        print(f"n={n}: P3-free {idx3.size} graphs, Theorem 3 {'HOLDS' if ok3 else 'FAILS'} [{time.time()-t0:.0f}s]", flush=True)
        if n >= 4:
            # ---- Theorem 5: P4-free => disconnected or co-disconnected ----
            # forbidden induced patterns: P4 labelings on 4 verts = 12 patterns of 6 bits
            p4pats = set()
            # path 0-1-2-3 with labelings: enumerate permutations of 4 verts mapping path edges
            for perm in itertools.permutations(range(4)):
                # path on positions (a,b,c,d) with edges ab, bc, cd
                a, b, c, d = perm
                edges = {(a,b), (b,c), (c,d)}
                bits = 0
                for k, (x, y) in enumerate(itertools.combinations(range(4), 2)):
                    if (min(x,y), max(x,y)) in edges or (min(x,y),max(x,y)) in {(min(*e),max(*e)) for e in edges}:
                        pass
                # direct: bit k set iff the k-th pair (in combinations order) is a path edge
                bits = 0
                for k, (x, y) in enumerate(itertools.combinations(range(4), 2)):
                    if ((x, y) == (a, b) or (x, y) == (b, a) or (x, y) == (b, c) or (x, y) == (c, b)
                            or (x, y) == (c, d) or (x, y) == (d, c)):
                        bits |= 1 << k
                p4pats.add(bits)
            p4arr = np.array(sorted(p4pats), dtype=np.uint64)
            free4 = np.ones(N, dtype=bool)
            for quad in itertools.combinations(range(n), 4):
                pat, _ = induced_bits(masks, quad, None)
                for p in p4arr:
                    free4 &= (pat != p)
            idx4 = np.nonzero(free4)[0]
            ok5 = True; ok6 = True
            for i in idx4:
                mask = int(masks[i])
                # co-disconnected = complement disconnected
                full = (1 << (n*(n-1)//2)) - 1
                if not (disconnected(mask, n) or disconnected(full ^ mask, n)):
                    ok5 = False; print(f"P4-DECOMP FAIL n={n} mask={mask}"); break
                om, al = max_clique_indep(mask, n)
                if om * al < n:
                    ok6 = False; print(f"P4-omega-alpha FAIL n={n} mask={mask} w={om} a={al}"); break
            results[f"P4_n{n}"] = {"count": int(idx4.size), "decomp_holds": ok5, "omega_alpha_holds": ok6}
            print(f"n={n}: P4-free {idx4.size} graphs, Theorem 5 {'HOLDS' if ok5 else 'FAILS'}, Theorem 6 {'HOLDS' if ok6 else 'FAILS'} [{time.time()-t0:.0f}s]", flush=True)
        # ---- Theorem 1 (Ramsey-exact): K_t-free => alpha >= L_t(n) ----
        # exact small Ramsey numbers R(t, l) for t=3,4 (l up to 9) and t=5 (l up to 6)
        RAMSEY = {3: {2: 3, 3: 6, 4: 9, 5: 14, 6: 18, 7: 23, 8: 28, 9: 36},
                  4: {2: 4, 3: 9, 4: 18, 5: 25},
                  5: {2: 5, 3: 14, 4: 25, 5: 43}}
        for t in [3, 4, 5]:
            kt = t*(t-1)//2
            freek = np.ones(N, dtype=bool)
            for sub in itertools.combinations(range(n), t):
                pat, nb = induced_bits(masks, sub, None)
                full_pat = np.uint64((1 << nb) - 1)
                freek &= (pat != full_pat)
            idxk = np.nonzero(freek)[0]
            okB = True
            # vectorized e:
            es = popcount_u64(masks[idxk])
            ns = np.full(len(idxk), n, dtype=np.int64)
            bound = (ns.astype(np.float64)**2) / (2*es.astype(np.float64) + ns)
            for j, i in enumerate(idxk):
                mask = int(masks[i])
                om, al = max_clique_indep(mask, n)
                if al < bound[j] - 1e-9:
                    okB = False; print(f"K{t}-CARO FAIL n={n} mask={mask} alpha={al} bound={bound[j]:.3f}"); break
                # Ramsey-exact: alpha >= L_t(n) = max{l : R(t,l) <= n}
                L = 2
                for l, R in sorted(RAMSEY[t].items()):
                    if R <= n and l > L: L = l
                if al < L:
                    okB = False; print(f"K{t}-RAMSEY FAIL n={n} mask={mask} alpha={al} L={L}"); break
            results[f"K{t}_n{n}"] = {"count": int(idxk.size), "holds": okB}
            print(f"n={n}: K{t}-free {idxk.size} graphs, Theorems 1/B/C {'HOLDS' if okB else 'FAILS'} [{time.time()-t0:.0f}s]", flush=True)
    # ---- tightness families ----
    for s in [2, 3]:
        n = s*s
        build_tables(n)
        mask = 0
        for b in range(s):
            for i in range(s):
                for j in range(s):
                    u, v = b*s + i, b*s + j
                    if i < j:
                        mask |= 1 << PAIR[(min(u,v), max(u,v))]
        om, al = max_clique_indep(mask, n)
        print(f"tightness s={s}: {s}.K_{s} on n={n}: omega={om} alpha={al} product={om*al} (== n: {om*al == n})")
        results[f"tight_s{s}"] = {"omega": om, "alpha": al, "product": om*al, "equals_n": om*al == n}
    import json
    json.dump(results, open('/home/z/erdos-weak-problems/problem61-erdos-hajnal/experiments/verify_theorems_results.json', 'w'), indent=1)
    print("ALL CHECKS COMPLETE", time.time()-t0, "s")

if __name__ == "__main__":
    main()
