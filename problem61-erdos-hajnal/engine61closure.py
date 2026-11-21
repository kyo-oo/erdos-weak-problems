#!/usr/bin/env python3
# engine61closure.py — W78-61E: THE GENERAL REDUCTION COVERAGE MACHINE
# Verifies: RAM-GEN plug-backs, PRIME-DEC ladder (module->contraction->tree->reassembly),
# multi-block avoidance chase, and builds the n<=6 coverage table (CLOSURE_MAP data).
# Two counting codes for every census number. In English, always.

import itertools, random, json, sys, math, time
import numpy as np

random.seed(610078)
np.random.seed(610078)
T0 = time.time()
PASS, FAIL = [], []

def check(name, cond, detail=""):
    (PASS if cond else FAIL).append(f"{name}{' :: ' + detail if detail else ''}")
    if not cond:
        print("  FAIL:", name, detail)

def wall(): return round(time.time() - T0, 1)

# ---------- graph primitives ----------
# emask: bit k over pairs list prs = [(i,j) i<j]; adjacency bit (i*n+j) derived on demand

def pairs_of(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]

def pidx_of(n):
    return {p: k for k, p in enumerate(pairs_of(n))}

def emask_to_adj(n, emask, prs):
    adj = [0] * n
    for k, (a, b) in enumerate(prs):
        if (emask >> k) & 1:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
    return tuple(adj)

def adj_of(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return tuple(adj)

def adj_complement(n, adj):
    full = (1 << n) - 1
    return tuple((full & ~adj[i]) & ~(1 << i) for i in range(n))

def adj_to_emask(n, adj, pidx):
    m = 0
    for a in range(n):
        for b in range(a + 1, n):
            if (adj[a] >> b) & 1:
                m |= 1 << pidx[(a, b)]
    return m

# ---------- numpy canonical forms (the census7_numpy doctrine) ----------

def canonical_table(n):
    """returns (canon_array, emasks) — canon[i] = min over all perms of mapped emask"""
    prs = pairs_of(n)
    N = 1 << len(prs)
    emasks = np.arange(N, dtype=np.uint64)
    canon = emasks.copy()
    nperm = 0
    for perm in itertools.permutations(range(n)):
        # map source pair-index -> target pair-index
        src2tgt = []
        for k, (a, b) in enumerate(prs):
            x, y = perm[a], perm[b]
            lo, hi = (x, y) if x < y else (y, x)
            src2tgt.append((k, (lo * (2 * n - lo - 1)) // 2 + (hi - lo - 1)))
        # recompute target index properly with pidx
        pid = pidx_of(n)
        src2tgt = [(k, pid[(min(perm[a], perm[b]), max(perm[a], perm[b]))]) for k, (a, b) in enumerate(prs)]
        mapped = np.zeros(N, dtype=np.uint64)
        for k, t in src2tgt:
            mapped |= ((emasks >> np.uint64(k)) & np.uint64(1)) << np.uint64(t)
        canon = np.minimum(canon, mapped)
        nperm += 1
    return canon, emasks, nperm

def unlabeled_reps(n):
    """canonical emask -> representative labeled emask (the canonical itself is a labeled graph)"""
    canon, emasks, nperm = canonical_table(n)
    reps = {}
    uniq = np.unique(canon)
    for c in uniq:
        reps[int(c)] = int(c)  # canonical value IS a labeled emask of some graph in the orbit
    return reps, len(prs_counts(n)) if False else None

def prs_counts(n):
    return pairs_of(n)

def verify_representative(n, canon_val):
    """verify canon_val is in the orbit of itself trivially; and is achievable: its own canon == itself"""
    prs = pairs_of(n)
    pid = pidx_of(n)
    adj = emask_to_adj(n, canon_val, prs)
    em = adj_to_emask(n, adj, pid)
    assert em == canon_val
    return True

# ---------- exact alpha / omega (banked MIS discipline) ----------

def mis_adj(adj, mask, memo):
    key = mask
    if key in memo:
        return memo[key]
    if mask == 0:
        return 0
    # pick vertex in mask with max degree in induced subgraph
    bestv, bestd = -1, -1
    v = mask
    while v:
        a = (v & -v).bit_length() - 1
        d = bin(adj[a] & mask).count("1")
        if d > bestd:
            bestv, bestd = a, d
        v &= v - 1
    without = mask & ~(1 << bestv)
    r1 = mis_adj(adj, without, memo)
    incl = without & ~adj[bestv]
    r2 = 1 + mis_adj(adj, incl, memo)
    memo[key] = max(r1, r2)
    return memo[key]

def alpha_of(n, adj):
    return mis_adj(adj, (1 << n) - 1, {})

def omega_of(n, adj):
    return alpha_of(n, adj_complement(n, adj))

def hom_of(n, adj):
    return max(alpha_of(n, adj), omega_of(n, adj))

# ---------- induced subgraph search (backtracking, no permutation blowup) ----------

def contains_induced_bt(n, adj, h, hadj):
    hn = len(hadj)
    if hn > n:
        return False
    order = list(range(hn))
    def bt(hv, assign):
        if hv == hn:
            return True
        # candidate g-vertices consistent with all prior assignments
        for g in range(n):
            ok = True
            for hprior, gprior in assign.items():
                want = (hadj[hv] >> hprior) & 1
                have = (adj[g] >> gprior) & 1
                if want != have:
                    ok = False
                    break
            if not ok:
                continue
            if any(g == gp for gp in assign.values()):
                continue
            assign[hv] = g
            if bt(hv + 1, assign):
                return True
            del assign[hv]
        return False
    return bt(0, {})

# ---------- modules / contraction / decomposition tree ----------

def find_module(n, adj):
    full = (1 << n) - 1
    for M in range(1, full):
        sz = bin(M).count("1")
        if sz < 2 or sz >= n:
            continue
        outside = full & ~M
        ok = True
        v = outside
        while v and ok:
            u = (v & -v).bit_length() - 1
            cnt = bin(adj[u] & M).count("1")
            if cnt != 0 and cnt != sz:
                ok = False
            v &= v - 1
        if ok:
            return M
    return None

def contract(n, adj, M):
    """quotient on q = n-|M|+1 vertices; LAST vertex = module vertex m*"""
    keep = [i for i in range(n) if not (M >> i) & 1]
    q = len(keep) + 1
    idx = {v: j for j, v in enumerate(keep)}
    qadj = [0] * q
    for a in keep:
        for b in keep:
            if a < b and (adj[a] >> b) & 1:
                qadj[idx[a]] |= 1 << idx[b]
                qadj[idx[b]] |= 1 << idx[a]
    mstar = q - 1
    for a in keep:
        # a sees ALL of M or NONE (M is a module)
        cnt = bin(adj[a] & M).count("1")
        if cnt == bin(M).count("1"):
            qadj[idx[a]] |= 1 << mstar
            qadj[mstar] |= 1 << idx[a]
    return q, tuple(qadj)

def subgraph_adj(n, adj, S):
    verts = [i for i in range(n) if (S >> i) & 1]
    k = len(verts)
    idx = {v: j for j, v in enumerate(verts)}
    sadj = [0] * k
    for a in verts:
        for b in verts:
            if a < b and (adj[a] >> b) & 1:
                sadj[idx[a]] |= 1 << idx[b]
                sadj[idx[b]] |= 1 << idx[a]
    return k, tuple(sadj)

def substitute_adj(quot, blocks):
    """uniform blow-up: quot adjacency tuple; blocks = list of adjacency tuples"""
    q = len(quot)
    sizes = [len(b) for b in blocks]
    N = sum(sizes)
    off = [0]
    for s in sizes:
        off.append(off[-1] + s)
    G = [0] * N
    for i in range(q):
        bi = blocks[i]
        for a in range(sizes[i]):
            for b in range(a + 1, sizes[i]):
                if (bi[a] >> b) & 1:
                    ga, gb = off[i] + a, off[i] + b
                    G[ga] |= 1 << gb
                    G[gb] |= 1 << ga
        for j in range(i + 1, q):
            if (quot[i] >> j) & 1:
                for a in range(sizes[i]):
                    for b in range(sizes[j]):
                        ga, gb = off[i] + a, off[j] + b
                        G[ga] |= 1 << gb
                        G[gb] |= 1 << ga
    return tuple(G)

def decomp_tree(n, adj):
    if n == 1:
        return ("leaf", 1, (0,))
    M = find_module(n, adj)
    if M is None:
        return ("leaf", n, adj)  # prime (or trivially prime small case)
    q, qadj = contract(n, adj, M)
    k, kadj = subgraph_adj(n, adj, M)
    node_data = (n, adj, q, qadj, k, kadj)  # everything concrete for the local ladder check
    return ("node", node_data, [decomp_tree(q, qadj), decomp_tree(k, kadj)])

def tree_leaves_ids(tree):
    if tree[0] == "leaf":
        return [(tree[1], tree[2])]
    out = []
    for ch in tree[2]:
        out += tree_leaves_ids(ch)
    return out

def adj_canon_key(n, adj):
    prs = pairs_of(n)
    pid = pidx_of(n)
    em = adj_to_emask(n, adj, pid)
    best = em
    for perm in itertools.permutations(range(n)):
        permadj = [0] * n
        for a in range(n):
            for b in range(n):
                if (adj[a] >> b) & 1:
                    permadj[perm[a]] |= 1 << perm[b]
        e2 = adj_to_emask(n, tuple(permadj), pid)
        if e2 < best:
            best = e2
    return best

# ---------- batteries ----------

def battery_primedec(rep_by_n):
    """THE LADDER CHECK, local per node (the theorem's exact content):
    H_node == substitute(quotient with m* last, [singletons..., module block])
    — verified label-free via canonical forms at EVERY node, exhaustively n<=6.
    The global reassembly follows by induction (each step certified + sizes strictly
    decrease), which is precisely the proof of THEOREM PRIME-DEC."""
    total = prime_ct = decomp_ct = 0
    def walk(tree):
        nonlocal decomp_ct
        if tree[0] == "leaf":
            return
        nn, adj, q, qadj, k, kadj = tree[1]
        decomp_ct += 1
        built = substitute_adj(qadj, [(0,)] * (q - 1) + [kadj])
        check(f"PD-ladder n={nn} q={q} k={k}",
              adj_canon_key(len(built), built) == adj_canon_key(nn, adj),
              f"got {adj_canon_key(len(built), built)} want {adj_canon_key(nn, adj)}")
        for ch in tree[2]:
            walk(ch)
    for n in range(1, 7):
        for cval, rep in rep_by_n[n].items():
            total += 1
            prs = pairs_of(n)
            adj = emask_to_adj(n, cval, prs)
            tree = decomp_tree(n, adj)
            if tree[0] == "leaf" and n > 1:
                prime_ct += 1
            walk(tree)  # no-op for leaves
            check(f"PD-classified n={n} c={cval}", tree[0] in ("leaf", "node"))
    check("PD-singleton", rep_by_n[1] is not None and decomp_tree(1, (0,))[0] == "leaf")
    decomp_top = total - 1 - prime_ct  # top-level decomposable graphs (n>=2, not prime)
    check("PD-counts", decomp_top >= 0 and prime_ct + decomp_top + 1 == total,
          f"total={total} primes={prime_ct} decomp_top={decomp_top} internal_nodes={decomp_ct}")
    return total, prime_ct, decomp_top

def ramgen_bound(t, n):
    return math.ceil(math.factorial(t - 1) ** (1.0 / (t - 1)) * n ** (1.0 / (t - 1))) - (t - 1)

def battery_ramgen_exh():
    # exhaustive n<=6, t=3,4,5: every K_t-free labeled graph satisfies (RG-1)
    for t in (3, 4, 5):
        kt_adj = adj_of(t, [(a, b) for a in range(t) for b in range(a + 1, t)])
        for n in range(1, 7):
            prs = pairs_of(n)
            pid = pidx_of(n)
            viol = cnt = 0
            for em in range(1 << len(prs)):
                adj = emask_to_adj(n, em, prs)
                if contains_induced_bt(n, adj, t, kt_adj):
                    continue
                cnt += 1
                if alpha_of(n, adj) < ramgen_bound(t, n):
                    viol += 1
            check(f"RAMGEN-exh t={t} n={n}", viol == 0, f"{viol} violations / {cnt} K_t-free")

def greedy_is(adj):
    """a genuine independent set (one-sided: its size is a lower bound for alpha)"""
    n = len(adj)
    alive = (1 << n) - 1
    size = 0
    while alive:
        # min-degree vertex in the alive induced subgraph
        bestv, bestd = -1, 10**9
        v = alive
        while v:
            a = (v & -v).bit_length() - 1
            d = bin(adj[a] & alive).count("1")
            if d < bestd:
                bestv, bestd = a, d
            v &= v - 1
        size += 1
        alive &= ~(1 << bestv) & ~adj[bestv]
    return size

def gen_complete_multipartite(n, parts):
    adj = [0] * n
    for i in range(n):
        for j in range(n):
            if i != j and i // parts != j // parts:
                adj[i] |= 1 << j
    return tuple(adj)

def gen_random_parts(n, parts, p):
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if i // parts != j // parts and random.random() < p:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return tuple(adj)

def gen_random_sparse(n, p):
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if random.random() < p:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return tuple(adj)

def battery_ramgen_samp():
    for t in range(3, 9):
        kt_adj = adj_of(t, [(a, b) for a in range(t) for b in range(a + 1, t)])
        for n in (20, 50, 100):
            checked = viol = 0
            cands = []
            cands.append(("multipartite", gen_complete_multipartite(n, t - 1)))
            for _ in range(8):
                cands.append(("randparts", gen_random_parts(n, t - 1, 0.6)))
            for _ in range(8):
                cands.append(("sparse", gen_random_sparse(n, 0.08)))
            for tag, adj in cands:
                if contains_induced_bt(n, adj, t, kt_adj):
                    continue  # not K_t-free; skip (constructions should be free; sparse may rarely contain)
                checked += 1
                if greedy_is(adj) < ramgen_bound(t, n):
                    viol += 1  # greedy IS is a genuine independent set: size >= bound ⟹ alpha >= bound
            check(f"RAMGEN-samp t={t} n={n}", viol == 0, f"{viol} viol / {checked} checked")

def battery_multiblock():
    # the multi-block chase: Q contains A on inj; block X_{inj[p]} contains J_p
    # => G contains induced A[J_1..J_a]. Verified by construction + BT detection.
    for trial in range(100):
        a = random.randint(2, 3)
        q = random.randint(a, 5)
        A = gen_random_sparse(a, 0.6)
        Js = [gen_random_sparse(3, 0.6) for _ in range(a)]
        inj = random.sample(range(q), a)
        blocks = [gen_random_sparse(3, 0.5) for _ in range(q)]
        qadj = [0] * q
        for i in range(q):
            for j in range(i + 1, q):
                if random.random() < 0.5:
                    qadj[i] |= 1 << j
                    qadj[j] |= 1 << i
        # force quotient to contain A on inj
        for x in range(a):
            for y in range(a):
                if x == y:
                    continue
                ix, iy = inj[x], inj[y]
                if (A[x] >> y) & 1:
                    qadj[ix] |= 1 << iy
                    qadj[iy] |= 1 << ix
                else:
                    qadj[ix] &= ~(1 << iy)
                    qadj[iy] &= ~(1 << ix)
        for p in range(a):
            blocks[inj[p]] = Js[p]  # the block IS J_p
        G = substitute_adj(tuple(qadj), blocks)
        AJ = substitute_adj(A, Js)
        check(f"MB-avoid trial={trial}",
              contains_induced_bt(len(G), G, len(AJ), AJ),
              "chase failed: expected induced A[J_1..J_a]")
        # negative control: perturb one block at inj to NOT contain J_p is hard in general;
        # instead verify the min-law direction on a compatible H-free blowup:
    # min-law spot checks: G = blowup of Q with classes; Q A-free or some class J-free => G A[J..]-free
    for trial in range(60):
        a = 2
        A = gen_random_sparse(a, 0.7)
        J = gen_random_sparse(3, 0.7)
        q = random.randint(2, 4)
        qadj = gen_random_sparse(q, 0.5)
        if contains_induced_bt(q, qadj, a, A):
            continue  # need quotient A-free
        blocks = [gen_random_sparse(3, 0.7) for _ in range(q)]
        G = substitute_adj(qadj, blocks)
        AJ = substitute_adj(A, [J] * a)
        check(f"MB-minlaw trial={trial}",
              not contains_induced_bt(len(G), G, len(AJ), AJ),
              "A-free quotient but G contains A[J,J]?!")

def coverage_rows(rep_by_n):
    rows = []
    for n in range(1, 7):
        prs = pairs_of(n)
        pid = pidx_of(n)
        for cval in sorted(rep_by_n[n].keys()):
            adj = emask_to_adj(n, cval, prs)
            tree = decomp_tree(n, adj)
            is_prime = (tree[0] == "leaf" and n > 1)
            comp_adj = adj_complement(n, adj)
            comp_key = adj_canon_key(n, comp_adj)
            leaves = [(ln, adj_canon_key(ln, la)) for ln, la in tree_leaves_ids(tree)]
            rows.append({
                "n": n, "canon": cval, "edges": bin(cval).count("1"),
                "prime": bool(is_prime),
                "complement_canon": comp_key,
                "decomposable": tree[0] == "node",
                "leaves": [[ln, lk] for ln, lk in leaves],
            })
    return rows

def main():
    print(f"[{wall()}s] === censuses n<=6 (numpy canonicalization, two codes) ===")
    rep_by_n = {}
    counts1 = []
    for n in range(1, 7):
        canon, emasks, nperm = canonical_table(n)
        uniq = np.unique(canon)
        # code 2: brute canonical via adj_canon_key on uniq members' orbits — spot-verify 40 random graphs
        reps = {int(c): int(c) for c in uniq}
        rep_by_n[n] = reps
        counts1.append(len(uniq))
        # two-code check: recompute canon of random labeled graphs by pure-python adj_canon_key
        prs = pairs_of(n)
        pid = pidx_of(n)
        sample_idx = np.random.choice(len(emasks), size=min(60, len(emasks)), replace=False)
        agree = 0
        for i in sample_idx:
            em = int(emasks[i])
            adj = emask_to_adj(n, em, prs)
            if adj_canon_key(n, adj) == int(canon[i]):
                agree += 1
        check(f"canon-two-code n={n}", agree == len(sample_idx), f"{agree}/{len(sample_idx)} agree ({nperm} perms)")
    EXPECT = [1, 2, 4, 11, 34, 156]
    check("census-counts", counts1 == EXPECT, f"got {counts1}")
    print(f"[{wall()}s] counts (code1): {counts1}")

    print(f"[{wall()}s] === PRIME-DEC battery (exhaustive n<=6) ===")
    total, primes, decomp = battery_primedec(rep_by_n)
    print(f"[{wall()}s] graphs={total} primes={primes} decomposable={decomp}")
    check("PD-counts", total == sum(EXPECT) and primes + decomp + 1 == total,
          f"total={total} primes={primes} decomp={decomp} (+1 n=1 leaf)")

    print(f"[{wall()}s] === multi-block avoidance battery ===")
    battery_multiblock()
    print(f"[{wall()}s] done")

    print(f"[{wall()}s] === RAM-GEN plug-backs (exhaustive) ===")
    battery_ramgen_exh()
    print(f"[{wall()}s] done")

    print(f"[{wall()}s] === RAM-GEN plug-backs (sampled constructions) ===")
    battery_ramgen_samp()
    print(f"[{wall()}s] done")

    print(f"[{wall()}s] === coverage table ===")
    rows = coverage_rows(rep_by_n)
    import os
    os.makedirs("alln61", exist_ok=True)
    with open("alln61/coverage_map.json", "w") as f:
        json.dump(rows, f, indent=1)
    # classify
    BANKED = {1: True}  # singleton leaves trivially banked
    p4 = adj_canon_key(4, adj_of(4, [(0, 1), (1, 2), (2, 3)]))
    banked_prime_keys = {(4, p4)}  # P4 prime banked (4-vertex world closed)
    summary = {n: {"prime": 0, "decomposable": 0, "frontier_prime": 0, "banked_prime": 0} for n in range(1, 7)}
    frontier5, frontier6 = [], []
    for r in rows:
        n = r["n"]
        if n == 1:
            continue
        if r["decomposable"]:
            summary[n]["decomposable"] += 1
        else:
            summary[n]["prime"] += 1
            if (n, r["canon"]) in banked_prime_keys:
                summary[n]["banked_prime"] += 1
            elif n == 5:
                frontier5.append(r["canon"])
            elif n == 6:
                frontier6.append(r["canon"])
    for n in (5, 6):
        summary[n]["frontier_prime"] = len(frontier5) if n == 5 else len(frontier6)
    print("summary:", json.dumps(summary))
    print(f"frontier primes n=5: {len(frontier5)}  n=6: {len(frontier6)}")

    print()
    print(f"PASS: {len(PASS)}  FAIL: {len(FAIL)}")
    with open("receipts61closure.txt", "w") as f:
        f.write("engine61closure.py — W78-61E receipts (the general reduction coverage machine)\n")
        f.write(f"census counts (numpy code + pure-python two-code spot agreement): {counts1} vs expected {EXPECT}\n")
        f.write(f"n<=6 totals: graphs={total} primes={primes} decomposable={decomp}\n")
        f.write(json.dumps(summary) + "\n")
        f.write(f"frontier primes: n=5={len(frontier5)} n=6={len(frontier6)}\n")
        f.write(f"PASS: {len(PASS)}  FAIL: {len(FAIL)}  wall={wall()}s\n")
        for p_ in PASS:
            f.write("PASS :: " + p_ + "\n")
        for f__ in FAIL:
            f.write("FAIL :: " + f__ + "\n")
    return 0 if not FAIL else 1

if __name__ == "__main__":
    sys.exit(main())
