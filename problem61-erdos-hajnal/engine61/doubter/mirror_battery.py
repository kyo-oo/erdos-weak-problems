#!/usr/bin/env python3
"""
MIRROR BATTERY W68-61D — Erdos #61 doubter lane (Erdos-Hajnal family kernel audit).

MISSION: adversarially attack the killer lane's family design; certify what survives.
Killer's board (branch w67-p61k): for F = {K1, K2, Kb2, P3, Pb3, K3, Kb3, P4},
every H-free graph G on n vertices has max(omega, alpha) >= floor(sqrt(n)) (SHARP form).

Every check DUAL METHOD where structural: Engine A (bitmask, per-n pair indexing)
and Engine B (adjacency frozenset) — independent implementations must agree exactly.
Exit nonzero on ANY failure. English only.
"""
import sys, json, math
from itertools import combinations, permutations

FAIL = []

def fail(msg):
    FAIL.append(msg)
    print("FAIL: " + msg)

# ---------- per-n machinery (Engine A: bitmask; indices built PER n — the r1 defect) ----------
def build(n):
    idx = {}
    b = 0
    for i in range(n):
        for j in range(i + 1, n):
            idx[(i, j)] = b
            b += 1
    npairs = b
    def adj(g, i, j):
        key = (i, j) if i < j else (j, i)
        return (g >> idx[key]) & 1 == 1
    return adj, npairs

# ---------- Engine B: adjacency frozenset ----------
def adjB(edges, i, j):
    return (min(i, j), max(i, j)) in edges

# exact omega by branch (Engine B) and by subset enumeration (Engine A)
def omegaA(g, n, adj):
    best = 0
    for S in range(1 << n):
        c = bin(S).count('1')
        if c <= best: continue
        ok = True
        for i, j in combinations(range(n), 2):
            if ((S >> i) & 1) and ((S >> j) & 1) and not adj(g, i, j):
                ok = False; break
        if ok: best = c
    return best

def omegaB(edges, n):
    best = [0]
    def extend(clique, cand):
        if not cand:
            if len(clique) > best[0]: best[0] = len(clique)
            return
        if len(clique) + len(cand) <= best[0]: return
        v = cand[0]
        extend(clique + [v], [u for u in cand[1:] if adjB(edges, v, u)])
        extend(clique, cand[1:])
    extend([], list(range(n)))
    return best[0]

# ---------- H-free predicates (induced-subgraph freeness, both engines) ----------
H_DEFS = {
    'K1':   ([], 1),
    'K2':   ([(0, 1)], 2),
    'Kb2':  ([], 2),
    'P3':   ([(0, 1), (1, 2)], 3),
    'Pb3':  ([(0, 1)], 3),          # K1 + K2: one edge + isolated third vertex
    'K3':   ([(0, 1), (1, 2), (0, 2)], 3),
    'Kb3':  ([], 3),
    'P4':   ([(0, 1), (1, 2), (2, 3)], 4),
}

def induced_free_A(g, n, H_edges, h, adj):
    for f in permutations(range(n), h):
        ok = True
        for (a, b) in H_edges:
            if not adj(g, f[a], f[b]): ok = False; break
        if not ok: continue
        for a, b in combinations(range(h), 2):
            if (a, b) not in H_edges and adj(g, f[a], f[b]): ok = False; break
        if ok: return False
    return True

def induced_free_B(edges, n, H_edges, h):
    for f in permutations(range(n), h):
        ok = True
        for (a, b) in H_edges:
            if not adjB(edges, f[a], f[b]): ok = False; break
        if not ok: continue
        for a, b in combinations(range(h), 2):
            if (a, b) not in H_edges and adjB(edges, f[a], f[b]): ok = False; break
        if ok: return False
    return True

def graph_edges(g, n, adj):
    return frozenset((i, j) for i, j in combinations(range(n), 2) if adj(g, i, j))

# ---------- arithmetic audits ----------
def check_arith():
    print("[ARITH] floor-superadditivity: isqrt(a)+isqrt(b) >= isqrt(a+b)")
    viol = 0
    for a in range(0, 201):
        for b in range(0, 201):
            if math.isqrt(a) + math.isqrt(b) < math.isqrt(a + b):
                viol += 1
                if viol <= 5: fail("floor-superadd violated at (%d,%d)" % (a, b))
    sq = [k * k for k in range(0, 101)]
    bnd = sorted(set(s + d for s in sq for d in (-2, -1, 0, 1, 2) if s + d >= 0))
    for a in bnd:
        for b in bnd:
            if math.isqrt(a) + math.isqrt(b) < math.isqrt(a + b):
                viol += 1
    print("  violations (exhaustive <=200 + boundary <=10^4): %d" % viol)
    if viol: fail("floor-superadditivity BROKEN")

    print("[ARITH] greedy law: k^2 <= n implies ceil(n/k) >= k")
    viol = 0
    for k in range(1, 201):
        for n in range(k * k, k * k + 3):
            if -(-n // k) < k: viol += 1
    print("  violations: %d" % viol)
    if viol: fail("greedy arithmetic BROKEN")

    print("[ARITH] peel law: 1 <= c <= k-1 and k^2 <= n implies 1+isqrt(n-c) >= k")
    viol = 0
    for k in range(1, 201):
        for n in range(k * k, k * k + 3):
            for c in range(1, k):
                if 1 + math.isqrt(n - c) < k:
                    viol += 1
                    if viol <= 3: fail("peel law violated k=%d n=%d c=%d" % (k, n, c))
    print("  violations: %d" % viol)
    if viol: fail("peel arithmetic BROKEN")

# ---------- structural censuses (dual) ----------
def check_structure():
    print("[STRUCT] P3-free = disjoint union of cliques (n<=6, dual)")
    viol = 0
    for n in range(1, 7):
        adj, np = build(n)
        for g in range(1 << np):
            if not induced_free_A(g, n, H_DEFS['P3'][0], 3, adj): continue
            edges = graph_edges(g, n, adj)
            if not induced_free_B(edges, n, H_DEFS['P3'][0], 3):
                viol += 1; fail("engine disagreement on P3-freeness (n=%d g=%d)" % (n, g)); continue
            ok = True
            for v in range(n):
                nb = [u for u in range(n) if u != v and adj(g, v, u)]
                for a, b in combinations(nb, 2):
                    if not adj(g, a, b): ok = False
                for u in range(n):
                    if u != v and u not in nb:
                        for w in nb:
                            if adj(g, u, w): ok = False
                if not ok: break
            if not ok:
                viol += 1
                if viol <= 3: fail("P3-free graph not union-of-cliques (n=%d g=%d)" % (n, g))
    print("  violations: %d" % viol)
    if viol: fail("cluster law BROKEN")

    print("[STRUCT] Seinsche: connected AND co-connected => induced P4 (n<=6)")
    viol = 0
    total_cc = 0
    for n in range(2, 7):
        adj, np = build(n)
        for g in range(1 << np):
            edges = graph_edges(g, n, adj)
            def connected(es):
                seen = {0}; front = [0]
                while front:
                    v = front.pop()
                    for u in range(n):
                        if u not in seen and (min(u, v), max(u, v)) in es:
                            seen.add(u); front.append(u)
                return len(seen) == n
            allp = frozenset(combinations(range(n), 2))
            if connected(edges) and connected(allp - edges):
                total_cc += 1
                if induced_free_A(g, n, H_DEFS['P4'][0], 4, adj) or induced_free_B(edges, n, H_DEFS['P4'][0], 4):
                    viol += 1
                    if viol <= 3: fail("connected+co-connected P4-free graph (n=%d g=%d)" % (n, g))
    print("  connected+co-connected total: %d; P4-free among them: %d" % (total_cc, viol))
    if viol: fail("SEINSCHE LEMMA A BROKEN")

    print("[STRUCT] omega/alpha duality + dual-engine agreement (n<=5)")
    viol = 0
    for n in range(1, 6):
        adj, np = build(n)
        full = (1 << np) - 1
        for g in range(1 << np):
            edges = graph_edges(g, n, adj)
            wA = omegaA(g, n, adj)
            wB = omegaB(edges, n)
            aA = omegaA(full ^ g, n, adj)   # alpha(G) = omega(complement)
            cedges = frozenset(set(combinations(range(n), 2)) - set(edges))
            aB = omegaB(cedges, n)
            if wA != wB or aA != aB:
                viol += 1
                if viol <= 3: fail("dual-engine omega/alpha disagreement (n=%d g=%d)" % (n, g))
            if aA != omegaB(frozenset(set(combinations(range(n), 2)) - set(edges)), n):
                viol += 1
    print("  violations: %d" % viol)
    if viol: fail("duality/dual-engine BROKEN")

# ---------- family census (sharp form, dual) ----------
def check_family():
    print("[FAMILY] sharp form max(omega,alpha) >= isqrt(n) per H in F (n<=6, dual)")
    per_class = {h: [0, 0] for h in H_DEFS}
    for n in range(1, 7):
        adj, np = build(n)
        full = (1 << np) - 1
        for g in range(1 << np):
            w = omegaA(g, n, adj)
            a = omegaA(full ^ g, n, adj)
            m = max(w, a)
            edges = graph_edges(g, n, adj)
            for h, (he, hs) in H_DEFS.items():
                if induced_free_A(g, n, he, hs, adj):
                    if not induced_free_B(edges, n, he, hs):
                        fail("engine disagreement on %s-freeness (n=%d g=%d)" % (h, n, g)); continue
                    per_class[h][0] += 1
                    if m < math.isqrt(n):
                        per_class[h][1] += 1
                        if per_class[h][1] <= 3:
                            fail("SHARP violation: %s-free n=%d max=%d < %d" % (h, n, m, math.isqrt(n)))
    for h in H_DEFS:
        print("  %s: count=%d sharp-violations=%d" % (h, per_class[h][0], per_class[h][1]))
        if per_class[h][1]: fail("sharp form broken for %s" % h)
    # expected true counts: P3-free = Bell numbers 1,2,5,15,52,203 = 278
    if per_class['P3'][0] != 278: fail("P3-free census != 278 (Bell n<=6): got %d" % per_class['P3'][0])
    if per_class['Pb3'][0] != 278: fail("Pb3-free census != 278: got %d" % per_class['Pb3'][0])

# ---------- product law ----------
def check_product():
    print("[PRODUCT] omega*alpha >= n for P3-free and P4-free (n<=6)")
    for h in ('P3', 'P4'):
        viol = 0
        for n in range(1, 7):
            adj, np = build(n)
            full = (1 << np) - 1
            for g in range(1 << np):
                if not induced_free_A(g, n, H_DEFS[h][0], H_DEFS[h][1], adj): continue
                w = omegaA(g, n, adj)
                a = omegaA(full ^ g, n, adj)
                if w * a < n:
                    viol += 1
                    if viol <= 3: fail("product law violated %s-free n=%d w*a=%d" % (h, n, w * a))
        print("  %s-free product-law violations: %d" % (h, viol))
        if viol: fail("product law BROKEN for %s" % h)

# ---------- frontier map (11 unlabeled H on 4 vertices) ----------
def iso_classes_4():
    pairs = list(combinations(range(4), 2))
    canon = {}
    for g in range(64):
        edges = frozenset(pairs[i] for i in range(6) if (g >> i) & 1)
        best = None
        for p in permutations(range(4)):
            pe = tuple(sorted((min(p[a], p[b]), max(p[a], p[b])) for (a, b) in edges))
            if best is None or pe < best: best = pe
        canon.setdefault(best, []).append(g)
    return canon

def check_frontier():
    print("[FRONTIER] the 11 unlabeled 4-vertex H: min max(omega,alpha) over H-free graphs, n=4..6")
    classes = iso_classes_4()
    print("  iso classes on 4 vertices: %d" % len(classes))
    if len(classes) != 11: fail("iso-class count != 11")
    table = {}
    for canon_edges, members in sorted(classes.items(), key=lambda kv: len(kv[0])):
        he = list(canon_edges)
        best_by_n = {}
        for n in range(4, 7):
            adj, np = build(n)
            full = (1 << np) - 1
            best = None
            for g in range(1 << np):
                if induced_free_A(g, n, he, 4, adj):
                    m = max(omegaA(g, n, adj), omegaA(full ^ g, n, adj))
                    if best is None or m < best: best = m
            best_by_n[n] = best
        table["%dedges" % len(he)] = {"iso_rep": [list(e) for e in sorted(he)], "minmax": best_by_n}
        print("  H %d edges: min max(w,a) n=4,5,6: %s (sqrt: %.2f %.2f %.2f)" % (
            len(he), best_by_n, math.sqrt(4), math.sqrt(5), math.sqrt(6)))
    with open('frontier_map.json', 'w') as f:
        json.dump(table, f, indent=1)
    print("  frontier_map.json banked")

# ---------- main ----------
if __name__ == '__main__':
    print("MIRROR BATTERY W68-61D — Erdos #61 doubter lane (dual engines)")
    print("=" * 70)
    check_arith()
    check_structure()
    check_family()
    check_product()
    check_frontier()
    print("=" * 70)
    if FAIL:
        print("BATTERY VERDICT: RED (%d failures)" % len(FAIL))
        for m in FAIL[:20]: print("  - " + m)
        sys.exit(1)
    print("BATTERY VERDICT: GREEN — all dual-engine censuses agree, no violations")
    print("E61_DOUBTER_BATTERY_GREEN")
    sys.exit(0)
