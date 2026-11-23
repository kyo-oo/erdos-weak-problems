#!/usr/bin/env python3
"""
AUDIT ENGINE W85-61E — adversarial verification of the P4/Seinsche route
(DM61_Proof_E.lean architecture) BEFORE Lean CI.

Verifies, constructively and exhaustively:
  S1  SEINCHE SPLIT: P4free G, n>=2  =>  G disconnected  or  G^c disconnected.
  S2  caseA (the heart): no graph satisfies [G conn, G^c conn, G-u disc, P4free]
      for ANY u.  Plus the constructive sub-lemmas, instrumented:
      S2a STEP-1 (last-exit/neighbor-in-every-class): G conn => u has a G-neighbor
          in every D:=G-u class.
      S2b FLIP: u mixed on a D-class  =>  flip pair (p,q): p-q edge, u-p edge,
          u-q non-edge (p,q in the class, consecutive on the intra-class walk).
      S2c TWO-CLASS: the D-unreachable pair (x,y) from sep(D) => for every class C,
          x or y outside C.
      S2d P4 COMPLETION: (q, p, u, z') with z' = u's neighbor in the other class
          IS an induced P4 (all six pairs checked) in every mixed instance.
      S2e STEP-3: u uniform on every class + S2a => u universal => u isolated in
          G^c => G^c disconnected.
  S3  PRODUCT LAW: P4free G (n>=1) => alpha(G)*omega(G) >= n  (witness existence).
  S4  psi-ISO: P4^c = P4.comap psi with psi = [1,3,0,2] (all 16 ordered cells).
  S5  SEP-BRIDGE: the Finset separation shape (nonempty proper, no cross edges)
      <=> graph disconnected (reachability), for G and for G^c.
  S6  FINISHER arithmetic (n = 4..20000): max(i,k)^2 >= n => max >= Nat.sqrt n
      (integer sqrt), and Nat.sqrt n >= n^(1/4) as reals.
  S7  n=2 BASE: G conn on 2 vertices => G^c disconnected; n<=1: no separation.
  S8  HEREDITY sanity: P4free G => P4free G^c (via S4) and P4free on induced
      subgraphs (via subset scan) — sampled.

Exhaustive over ALL labeled graphs for n <= 6, plus uniform random samples n=7,8
and structured cographs. Two independent P4 detectors (induced-subset scan and
chase-based) per the campaign's two-code discipline.

The engine never stops; it never lies.
"""
import itertools, random, sys

FAIL = []

def report(tag, ok, msg):
    print(("PASS " if ok else "FAIL ") + tag + " — " + msg)
    if not ok:
        FAIL.append(tag)

# ---------- graph basics (bitmask adjacency, symmetric, irreflexive) ----------

def add_edge(adj, i, j):
    adj[i] |= 1 << j
    adj[j] |= 1 << i

def edges_of(adj, n):
    return [(i, j) for i in range(n) for j in range(i + 1, n) if adj[i] >> j & 1]

def complement(adj, n):
    full = (1 << n) - 1
    return [(~adj[i] & full) & ~(1 << i) for i in range(n)]

def delete_vertex(adj, n, u):
    """G - u  on vertices [0..n-1] minus u, relabeled 0..n-2."""
    rest = [v for v in range(n) if v != u]
    idx = {v: k for k, v in enumerate(rest)}
    out = [0] * (n - 1)
    for v in rest:
        for w in rest:
            if v != w and adj[v] >> w & 1:
                add_edge(out, idx[v], idx[w])
    return out

def components_excl(adj, n, u):
    """Classes of G restricted to V \\ {u}, in ORIGINAL labels."""
    left = 0
    for v in range(n):
        if v != u:
            left |= 1 << v
    comps = []
    while left:
        b = left & -left
        s = b.bit_length() - 1
        seen = 1 << s
        frontier = [s]
        while frontier:
            v = frontier.pop()
            nb = adj[v] & left & ~seen
            while nb:
                bb = nb & -nb
                k = bb.bit_length() - 1
                seen |= bb
                frontier.append(k)
                nb ^= bb
        comps.append(frozenset(k for k in range(n) if seen >> k & 1))
        left &= ~seen
    return comps

def bfs_path_excl(adj, n, u, s, t):
    """BFS path from s to t in G restricted to V \\ {u} (original labels)."""
    from collections import deque
    prev = {s: None}
    dq = deque([s])
    while dq:
        v = dq.popleft()
        if v == t:
            path = []
            while v is not None:
                path.append(v); v = prev[v]
            return path[::-1]
        nb = adj[v]
        while nb:
            b = nb & -nb
            k = b.bit_length() - 1
            if k != u and k not in prev:
                prev[k] = v
                dq.append(k)
            nb ^= b
    return None

# ---------- P4 detection, TWO independent codes ----------

P4_EDGES = {(0, 1), (1, 2), (2, 3)}          # ordered path w=0,x=1,y=2,z=3
P4_NON   = {(0, 2), (0, 3), (1, 3)}

def has_induced_P4_scan(adj, n):
    """Code 1: brute-force 4-subset scan; returns an induced P4 (w,x,y,z) or None."""
    for quad in itertools.combinations(range(n), 4):
        # try all path orders (4! = 24, cheap)
        for w, x, y, z in itertools.permutations(quad):
            ok = (adj[w] >> x & 1) and (adj[x] >> y & 1) and (adj[y] >> z & 1) \
                and not (adj[w] >> y & 1) and not (adj[w] >> z & 1) and not (adj[x] >> z & 1)
            if ok:
                return (w, x, y, z)
    return None

def has_induced_P4_chase(adj, n):
    """Code 2: for every oriented edge (x,y) and every non-neighbor w of x adjacent
    to x, and every non-neighbor z of x adjacent to y with the right pattern —
    direct 6-pair chase. Returns an induced P4 or None."""
    for w in range(n):
        for x in range(n):
            if not (adj[w] >> x & 1):
                continue
            for y in range(n):
                if not (adj[x] >> y & 1) or y == w or (adj[w] >> y & 1):
                    continue
                for z in range(n):
                    if not (adj[y] >> z & 1):
                        continue
                    if z in (w, x, y):
                        continue
                    if adj[w] >> z & 1 or adj[x] >> z & 1:
                        continue
                    return (w, x, y, z)
    return None

def p4free(adj, n):
    return has_induced_P4_scan(adj, n) is None

# ---------- reachability / connectedness ----------

def reach_set(adj, n, s):
    seen = 1 << s
    frontier = [s]
    while frontier:
        v = frontier.pop()
        nb = adj[v] & ~seen
        while nb:
            b = nb & -nb
            k = b.bit_length() - 1
            seen |= b
            frontier.append(k)
            nb ^= b
    return seen

def connected(adj, n):
    if n == 0:
        return True
    return reach_set(adj, n, 0) == (1 << n) - 1

def components(adj, n):
    """list of frozensets (reachability classes)."""
    left = (1 << n) - 1
    comps = []
    while left:
        v = (left & -left).bit_length() - 1
        r = reach_set(adj, n, v)
        comps.append(frozenset(k for k in range(n) if r >> k & 1))
        left &= ~r
    return comps

def sep_exists(adj, n):
    """Finset-separation shape: nonempty proper s, no cross edges. <=> not connected
    (for n>=1). Checked by brute force over subsets for small n; else by components."""
    if n == 0:
        return False
    if n <= 10:
        for mask in range(1, 1 << n - 1):
            s = mask
            sc = ((1 << n) - 1) & ~s
            if s == 0 or sc == 0:
                continue
            cross = any((adj[i] >> j & 1) for i in range(n) if s >> i & 1
                        for j in range(n) if sc >> j & 1)
            if not cross:
                return True
        return False
    return not connected(adj, n)

# ---------- S1/S2: Seinsche + caseA ----------

def check_seinsche_all(n):
    """S1 exhaustive + S2 caseA exhaustive (all u), with instrumented sub-lemmas.
    All instrumentation in ORIGINAL vertex labels; classes = components of
    G restricted to V \\ {u}.  The caseA machinery (S2a/S2b/S2c/S2d/S2e) is run
    on EVERY graph (not only P4free): whenever u is mixed on some class, the
    flip pair + two-class z' MUST produce an induced P4 — that is the writer's
    contract.  For P4free graphs the mixed case must therefore be impossible."""
    bad_s1, bad_caseA, mixed_cases, uniform_cases, s2d_checked = 0, 0, 0, 0, 0
    s2a_bad = s2b_bad = s2c_bad = s2d_bad = s2e_bad = 0
    s2_mixed_free_bad = 0   # P4free + conn + D disc + u mixed => must be impossible
    total_p4free = 0
    for mask in range(1 << (n * (n - 1) // 2)):
        adj = [0] * n
        k = 0
        for i in range(n):
            for j in range(i + 1, n):
                if mask >> k & 1:
                    add_edge(adj, i, j)
                k += 1
        isp4free = p4free(adj, n)
        # two-code agreement
        assert (has_induced_P4_scan(adj, n) is None) == (has_induced_P4_chase(adj, n) is None)
        if isp4free:
            total_p4free += 1
        # S1: Seinsche
        gc = complement(adj, n)
        if isp4free and n >= 2:
            if not (sep_exists(adj, n) or sep_exists(gc, n)):
                bad_s1 += 1
        # S2: caseA — for every u: NOT (G conn & Gc conn & G-u disc & P4free)
        if n >= 3 and isp4free and connected(adj, n) and connected(gc, n):
            for u in range(n):
                if n - 1 >= 2 and len(components_excl(adj, n, u)) >= 2:
                    bad_caseA += 1
        # S2 instrumented sub-lemmas: G conn, D := G-u disc (r >= 2)
        if n >= 3 and connected(adj, n):
            for u in range(n):
                comps = components_excl(adj, n, u)
                if len(comps) < 2:
                    continue
                # S2a: u has a G-neighbor in every D-class
                for C in comps:
                    if not any(adj[u] >> v & 1 for v in C):
                        s2a_bad += 1
                universal = all(adj[u] >> v & 1 for v in range(n) if v != u)
                if universal:
                    uniform_cases += 1
                    # S2e: u isolated in G^c => G^c disconnected (n >= 2)
                    if any(gc[u] >> v & 1 for v in range(n) if v != u):
                        s2e_bad += 1
                    if connected(gc, n):
                        s2e_bad += 1
                    continue
                mixed_cases += 1
                if isp4free:
                    s2_mixed_free_bad += 1  # impossible: mixed => P4
                # u mixed: find the mixed class + run the FULL machinery
                found_p4 = None
                for C in comps:
                    ns = [v for v in C if adj[u] >> v & 1]
                    nns = [v for v in C if not (adj[u] >> v & 1)]
                    if not ns or not nns:
                        continue
                    # S2b FLIP: consecutive flip pair on the intra-class walk
                    a = ns[0]; b = nns[0]
                    path = bfs_path_excl(adj, n, u, a, b)
                    assert path is not None and set(path) <= C
                    flip = None
                    for i in range(len(path) - 1):
                        p_, q_ = path[i], path[i + 1]
                        if adj[u] >> p_ & 1 and not (adj[u] >> q_ & 1):
                            flip = (p_, q_)
                            break
                    if flip is None:
                        s2b_bad += 1
                        continue
                    p_, q_ = flip  # u-p_ edge, u-q_ non-edge, p_-q_ edge
                    if not (adj[p_] >> q_ & 1 and adj[u] >> p_ & 1 and not (adj[u] >> q_ & 1)):
                        s2b_bad += 1
                    # S2c TWO-CLASS: D-unreachable pair (x,y) exists (D disc);
                    # at least one of x,y lies outside the class C
                    x, y = None, None
                    for i in range(len(comps)):
                        for j in range(i + 1, len(comps)):
                            x = next(iter(comps[i])); y = next(iter(comps[j]))
                            break
                        if x is not None:
                            break
                    if x is None:
                        s2c_bad += 1
                        continue
                    # x,y unreachable in D
                    if bfs_path_excl(adj, n, u, x, y) is not None:
                        s2c_bad += 1
                        continue
                    out = [t for t in (x, y) if t not in C]
                    if not out:
                        s2c_bad += 1
                        continue
                    yv = out[0]
                    # z' := u's G-neighbor in class(yv)  (S2a there)
                    Cyv = next(CC for CC in comps if yv in CC)
                    zp = next((v for v in Cyv if adj[u] >> v & 1), None)
                    if zp is None:
                        s2a_bad += 1
                        continue
                    # S2d: (q_, p_, u, zp) is an induced P4 in G — ALL SIX pairs
                    w, xx, yy, zz = q_, p_, u, zp
                    six = dict(e1=adj[w] >> xx & 1, e2=adj[xx] >> yy & 1, e3=adj[yy] >> zz & 1,
                               n1=not (adj[w] >> yy & 1), n2=not (adj[w] >> zz & 1),
                               n3=not (adj[xx] >> zz & 1))
                    if all(six.values()):
                        s2d_checked += 1
                        found_p4 = (w, xx, yy, zz)
                        break
                    else:
                        s2d_bad += 1
                # machinery contract: mixed u + conn G + D disc => a P4 was produced
                if found_p4 is None:
                    s2d_bad += 1
    return (bad_s1, bad_caseA, s2a_bad, s2b_bad, s2c_bad, s2d_bad, s2e_bad,
            total_p4free, mixed_cases, uniform_cases, s2d_checked, s2_mixed_free_bad)

def comps_of_contains(comps, v):
    for C in comps:
        if v in C:
            return C
    return set()

def bfs_path(adj, n, s, t):
    from collections import deque
    prev = {s: None}
    dq = deque([s])
    while dq:
        v = dq.popleft()
        if v == t:
            path = []
            while v is not None:
                path.append(v); v = prev[v]
            return path[::-1]
        nb = adj[v]
        while nb:
            b = nb & -nb
            k = b.bit_length() - 1
            if k not in prev:
                prev[k] = v
                dq.append(k)
            nb ^= b
    return None

def unreachable_pair(adj, n):
    comps = components(adj, n)
    if len(comps) < 2:
        return None, None
    a = next(iter(comps[0])); b = next(iter(comps[1]))
    return a, b

# ---------- S3: product law ----------

def alpha_omega(adj, n):
    best_i = 0; best_c = 0
    for mask in range(1 << n):
        # independent set check
        ok_i = True
        for i in range(n):
            if mask >> i & 1:
                if adj[i] & mask:
                    ok_i = False; break
        if ok_i:
            best_i = max(best_i, bin(mask).count('1'))
        ok_c = True
        for i in range(n):
            if mask >> i & 1:
                if (~adj[i]) & mask & ~(1 << i):
                    ok_c = False; break
        if ok_c:
            best_c = max(best_c, bin(mask).count('1'))
    return best_i, best_c

def check_product(n):
    bad = 0; cnt = 0
    for mask in range(1 << (n * (n - 1) // 2)):
        adj = [0] * n
        k = 0
        for i in range(n):
            for j in range(i + 1, n):
                if mask >> k & 1:
                    add_edge(adj, i, j)
                k += 1
        if not p4free(adj, n):
            continue
        cnt += 1
        a, o = alpha_omega(adj, n)
        if a * o < n:
            bad += 1
    return bad, cnt

# ---------- S4: psi-iso ----------

def check_psi():
    P4 = [0] * 4
    add_edge(P4, 0, 1); add_edge(P4, 1, 2); add_edge(P4, 2, 3)
    P4c = complement(P4, 4)
    psi = [1, 3, 0, 2]  # psi(i) = psi[i]
    # claim: P4c.Adj i j  <=>  P4.Adj (psi i) (psi j)
    for i in range(4):
        for j in range(4):
            lhs = bool(P4c[i] >> j & 1)
            rhs = bool(P4[psi[i]] >> psi[j] & 1)
            if lhs != rhs:
                return False, (i, j, lhs, rhs)
    # also psi is a bijection
    if sorted(psi) != [0, 1, 2, 3]:
        return False, "psi not bijective"
    return True, None

# ---------- S6: finisher arithmetic ----------

def check_finisher():
    import math
    bad_int = 0; bad_rpow = 0
    for n in range(4, 20001):
        s = math.isqrt(n)
        # claim: i*k >= n => max(i,k) >= s.  Equivalently: max <= s-1 => ik <= (s-1)^2 < n
        if s >= 1:
            if (s - 1) * (s - 1) >= n:
                bad_int += 1
        # claim: n^(1/4) <= s  (real). Since n <= s^2? No: s^2 <= n. Need n^(1/4) <= s
        # i.e. n <= s^4. True iff s >= 2 and n < (s+1)^2 <= ... — verify directly:
        if n ** 0.25 > s + 1e-12:
            bad_rpow += 1
        # also the M² route: n <= M*M => sqrt n <= M (integer) — definitional check
        M = s
        if not (M * M >= n or s == math.isqrt(M * M)):
            pass  # n may exceed s^2; sqrt_le_of_sq direction is what matters:
        # verify sqrt_le_of_sq: n <= m*m => isqrt(n) <= m
        for m in (s, s + 1, s + 2):
            if n <= m * m and math.isqrt(n) > m:
                bad_int += 1
    return bad_int, bad_rpow

# ---------- S7: n=2 base ----------

def check_base():
    bad = 0
    for mask in range(2):  # 2 vertices, 1 edge bit
        adj = [0, 0]
        if mask:
            add_edge(adj, 0, 1)
        if connected(adj, 2):
            gc = complement(adj, 2)
            if not sep_exists(gc, 2):
                bad += 1
    # n=1: no separation exists for any graph
    for mask in range(1):
        adj = [0]
        if sep_exists(adj, 1):
            bad += 1
    return bad

# ---------- S8: heredity + complement-freeness (sampled for n=7,8) ----------

def random_graph(n, rng):
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < 0.5:
                add_edge(adj, i, j)
    return adj

def random_cograph(n, rng):
    """random P4-free graph via union/join recursion."""
    if n == 1:
        return [0]
    if n == 0:
        return []
    k = rng.randint(1, n - 1)
    A = random_cograph(k, rng)
    B = random_cograph(n - k, rng)
    join = rng.random() < 0.5
    out = [0] * n
    for i in range(k):
        for j in range(k):
            if i != j and A[i] >> j & 1:
                add_edge(out, i, j)
    for i in range(n - k):
        for j in range(n - k):
            if i != j and B[i] >> j & 1:
                add_edge(out, k + i, k + j)
    if join:
        for i in range(k):
            for j in range(n - k):
                add_edge(out, i, k + j)
    return out

def check_sampled(nrands=400, seed=12345):
    rng = random.Random(seed)
    bad_her, bad_compl, bad_seinsche, cnt = 0, 0, 0, 0
    for trial in range(nrands):
        n = rng.choice([7, 8])
        if trial % 2 == 0:
            adj = random_cograph(n, rng)
            if not p4free(adj, n):
                return "cograph generator broken", 0
        else:
            adj = random_graph(n, rng)
        cnt += 1
        if not p4free(adj, n):
            continue
        # Seinsche
        gc = complement(adj, n)
        if not (sep_exists(adj, n) or sep_exists(gc, n)):
            bad_seinsche += 1
        # heredity: every induced subgraph P4-free
        for drop in range(1, min(3, n)):
            sub = delete_vertex(adj, n, drop)
            if not p4free(sub, n - 1):
                bad_her += 1
        # complement freeness
        if not p4free(gc, n):
            bad_compl += 1
    return (bad_her, bad_compl, bad_seinsche), cnt

def main():
    print("== W85-61E AUDIT ENGINE ==")
    # S4 psi
    ok, wit = check_psi()
    report("S4-PSI-ISO", ok, f"P4^c = P4.comap psi, psi=[1,3,0,2] (16 cells {'— witness ' + str(wit) if wit else 'all match, bijective'})")
    # S6 finisher
    bi, br = check_finisher()
    report("S6-FINISHER", bi == 0 and br == 0,
           f"int-sqrt chain + n^(1/4) <= sqrt n, n=4..20000 (bad_int={bi}, bad_rpow={br})")
    # S7 base
    b7 = check_base()
    report("S7-BASE", b7 == 0, f"n=2 base + n<=1 vacuity (bad={b7})")
    # S1/S2 exhaustive n=2..6
    for n in range(2, 7):
        (bad_s1, bad_caseA, s2a, s2b, s2c, s2d, s2e, tot, mixed, unif, s2dc,
         s2mf) = check_seinsche_all(n)
        report(f"S1-SEINCHE-n{n}", bad_s1 == 0,
               f"P4free, n>=2 => G or G^c disc; {tot} P4free graphs, bad={bad_s1}")
        report(f"S2-CASEA-n{n}", bad_caseA == 0,
               f"no (G,u): G conn & Gc conn & G-u disc & P4free; bad={bad_caseA}")
        report(f"S2-UNIFORM-ONLY-n{n}", s2mf == 0,
               f"P4free + conn + D disc => u uniform (mixed impossible); bad={s2mf}")
        report(f"S2a-LASTEXIT-n{n}", s2a == 0, f"u has a neighbor in every G-u class (bad={s2a})")
        report(f"S2b-FLIP-n{n}", s2b == 0, f"flip pair on intra-class walk (bad={s2b})")
        report(f"S2c-TWOCLASS-n{n}", s2c == 0, f"x or y outside every class; x,y D-unreachable (bad={s2c})")
        report(f"S2d-P4COMPLETION-n{n}", s2d == 0,
               f"(q,p,u,z') induced P4 all-six-pairs whenever u mixed (bad={s2d}, "
               f"constructive checks={s2dc}; mixed-instances={mixed}, universal-instances={unif})")
        report(f"S2e-UNIVERSAL-n{n}", s2e == 0, f"u universal => isolated in Gc => Gc disc (bad={s2e})")
    # S3 product law exhaustive n=1..6
    for n in range(1, 7):
        bad, cnt = check_product(n)
        report(f"S3-PRODUCT-n{n}", bad == 0, f"alpha*omega >= n over {cnt} P4free graphs (bad={bad})")
    # S8 sampled
    (bh, bc, bs), cnt = check_sampled()
    report("S8-HEREDITY", bh == 0, f"induced subgraphs stay P4free, sampled n=7,8 x{cnt}")
    report("S8-COMPLFREE", bc == 0, f"P4free G => P4free G^c (psi transport), sampled")
    report("S8-SEINCHE-SAMPLE", bs == 0, f"Seinsche on sampled n=7,8 cographs")
    print()
    if FAIL:
        print(f"TOTAL FAILURES: {len(FAIL)} -> {FAIL}")
        sys.exit(1)
    print("ALL GREEN — the mathematics of the W85-61E route survives the audit engine.")

if __name__ == "__main__":
    main()
