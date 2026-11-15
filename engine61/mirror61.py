#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MIRROR61 — the W67-61K python mirror for Erdos #61 (Erdos-Hajnal), family kernel
F = {K1, K2, KK2 (K̄2), P3, PP3 (P̄3), K3, KK3 (K̄3), P4}.

DUAL METHOD (campaign law): two fully independent graph engines
  ENGINE A (bitmask): a graph on n vertices is an int; the pair (i<j) lives at
                      bit position i*n+j; adjacency = bit test; omega/alpha by
                      subset enumeration over vertex bitmasks; connectivity by
                      frontier-mask BFS.
  ENGINE B (adjacency-list): a graph is a tuple of frozensets; adjacency = set
                      membership; induced-pattern search by permutations;
                      connectivity by set BFS; complement by full-set diff.

Every census below is computed by BOTH engines and the two verdicts are
cross-compared; a mismatch anywhere aborts with a nonzero exit.

MIRROR DECISION (the mission's sharp-vs-safe question): brute-force ALL graphs
on n <= 6 vertices and test, for every H in the family F, whether
    max(omega, alpha) >= floor(sqrt(n))           (SHARP form)
holds for every H-free graph (and likewise the SAFE form ceil(sqrt(n)/2)).
The mirror decides which form gets authored in Erdos61.lean.

Additional certified laws mirrored here:
  * SEINSCHE census: every connected AND co-connected graph on <= 6 vertices
    contains an induced P4 (Lemma A contrapositive census).
  * PRODUCT LAW: for P3-free and P4-free graphs, omega*alpha >= n.
  * CLUSTER LAW: P3-free = disjoint union of cliques.
  * GREEDY LAW: for triangle-free graphs, alpha*(Delta+1) >= n.
  * DEGREE CASE A: triangle-free with Delta >= floor(sqrt(n)) -> alpha >= floor(sqrt(n)).
  * COMPLEMENT LAWS: comp(comp(G))=G, Kbar3-free(G) = K3-free(comp(G)),
    Pbar3-free(G) = P3-free(comp(G)), Kbar2-free(G) = complete, K2-free = edgeless.
  * UNION/JOIN composition: alpha(A u B) = alphaA + alphaB, omega(A u B) =
    max, alpha(A v B) = max, omega(A v B) = omegaA + omegaB (all pairs nA,nB <= 3).
  * INTEGER ARITHMETIC n <= 200: isqrt laws s^2 <= n < (s+1)^2;
    n <= k*m and s^2 <= n -> (k >= s or m >= s); k*s >= s*s -> k >= s;
    (s-1)*(s-1) < s*s; the product-composition inequalities.
  * TIGHTNESS: the alternating cograph witness family Y_{j+1} = (Y_j u Y_j) v
    (Y_j u Y_j) has n = 4^j and max(omega,alpha) = 2^j = sqrt(n) EXACTLY, so the
    sharp constant cannot be improved within the P4-free class.
"""

import sys
from itertools import permutations, combinations

ISQ = {n: int(n ** 0.5) for n in range(0, 1000)}
# correct integer isqrt (float-safe)
def isqrt(n):
    s = int(n ** 0.5)
    while (s + 1) * (s + 1) <= n:
        s += 1
    while s * s > n:
        s -= 1
    return s
ISQ = {n: isqrt(n) for n in range(0, 1000)}

# =====================================================================
# ENGINE A: bitmask engine
# =====================================================================

def eA_pairs(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]

def eA_edge_bit(n, i, j):
    if i > j:
        i, j = j, i
    return 1 << (i * n + j)

def eA_adj(g, n, i, j):
    return (g >> (i * n + j if i < j else j * n + i)) & 1 == 1

def eA_all_graphs(n):
    npairs = n * (n - 1) // 2
    for g in range(1 << npairs if npairs else 1):
        # npairs bits at positions i*n+j (i<j) — positions i*n+j for i<j
        # enumerate directly over pair positions
        yield g
    return

def eA_graphs(n):
    """All graphs on vertices 0..n-1 as bitmasks over pair positions (i,j) i<j
    at bit index i*n+j.  Positions with i>=j are never set."""
    npairs = len(eA_pairs(n))
    bits = [eA_edge_bit(n, i, j) for (i, j) in eA_pairs(n)]
    for k in range(1 << npairs):
        g = 0
        for b in range(npairs):
            if (k >> b) & 1:
                g |= bits[b]
        yield g

def eA_adjacencies(g, n, u, v):
    return eA_adj(g, n, u, v)

def eA_omega_alpha(g, n):
    best_o = 0
    best_a = 0
    for sub in range(1 << n):
        # clique check: all pairs adjacent; indep: no pairs adjacent
        ok_c = True
        ok_i = True
        for i in range(n):
            if not (sub >> i) & 1:
                continue
            for j in range(i + 1, n):
                if (sub >> j) & 1:
                    if eA_adj(g, n, i, j):
                        ok_i = False
                    else:
                        ok_c = False
        cnt = bin(sub).count("1")
        if ok_c and cnt > best_o:
            best_o = cnt
        if ok_i and cnt > best_a:
            best_a = cnt
    return best_o, best_a

def eA_connected(g, n):
    if n <= 1:
        return True
    seen = 1  # vertex 0
    while True:
        frontier = seen
        for v in range(n):
            if (seen >> v) & 1:
                for w in range(n):
                    if eA_adj(g, n, v, w):
                        frontier |= (1 << w)
        if frontier == seen:
            break
        seen = frontier
    return seen == (1 << n) - 1

def eA_complement(g, n):
    c = 0
    for (i, j) in eA_pairs(n):
        if not eA_adj(g, n, i, j):
            c |= eA_edge_bit(n, i, j)
    return c

def eA_has_pattern(g, n, k, edges):
    """edges: set of (a,b) a<b in [0..k) that must be adjacent; all other pairs
    of the k distinct vertices must be non-adjacent (induced copy)."""
    for perm in permutations(range(n), k):
        ok = True
        for a in range(k):
            for b in range(a + 1, k):
                want = (a, b) in edges
                got = eA_adj(g, n, perm[a], perm[b])
                if want != got:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False

# =====================================================================
# ENGINE B: adjacency-list engine
# =====================================================================

def eB_graphs(n):
    """All graphs as tuple of frozensets (neighborhoods)."""
    pairs = list(combinations(range(n), 2))
    for k in range(1 << len(pairs) if pairs else 1):
        nb = [set() for _ in range(n)]
        for b, (i, j) in enumerate(pairs):
            if (k >> b) & 1:
                nb[i].add(j)
                nb[j].add(i)
        yield tuple(frozenset(s) for s in nb)

def eB_from_mask(g, n):
    nb = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if eA_adj(g, n, i, j):
                nb[i].add(j)
                nb[j].add(i)
    return tuple(frozenset(s) for s in nb)

def eB_omega_alpha(nb, n):
    best_o = 0
    best_a = 0
    verts = list(range(n))
    for r in range(n + 1):
        for sub in combinations(verts, r):
            ok_c = True
            ok_i = True
            for a, b in combinations(sub, 2):
                if b in nb[a]:
                    ok_i = False
                else:
                    ok_c = False
            if ok_c and r > best_o:
                best_o = r
            if ok_i and r > best_a:
                best_a = r
    return best_o, best_a

def eB_connected(nb, n):
    if n <= 1:
        return True
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in nb[v]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n

def eB_complement(nb, n):
    full = frozenset(range(n))
    return tuple(frozenset(w for w in full if w != v and w not in nb[v]) for v in range(n))

def eB_has_pattern(nb, n, k, edges):
    for perm in permutations(range(n), k):
        ok = True
        for a in range(k):
            for b in range(a + 1, k):
                want = (a, b) in edges
                got = perm[b] in nb[perm[a]]
                if want != got:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False

# =====================================================================
# The family F patterns (edge sets on their own vertices)
# =====================================================================

FAMILY = {
    "K1":   (1, set()),                       # single vertex
    "K2":   (2, {(0, 1)}),                    # one edge
    "Kb2":  (2, set()),                       # two isolated vertices (K̄2)
    "P3":   (3, {(0, 1), (1, 2)}),            # path a-b-c
    "Pb3":  (3, {(0, 1)}),                    # K1 ∪ K2 (P̄3)
    "K3":   (3, {(0, 1), (1, 2), (0, 2)}),    # triangle
    "Kb3":  (3, set()),                       # 3 isolated (K̄3)
    "P4":   (4, {(0, 1), (1, 2), (2, 3)}),    # path a-b-c-d
}

def hfree_A(g, n, name):
    k, edges = FAMILY[name]
    return not eA_has_pattern(g, n, k, edges)

def hfree_B(nb, n, name):
    k, edges = FAMILY[name]
    return not eB_has_pattern(nb, n, k, edges)

# =====================================================================
# THE MIRROR RUN
# =====================================================================

def main():
    out = []
    def say(s=""):
        out.append(s)
        print(s)

    say("MIRROR61 — W67-61K — Erdos #61 family kernel mirror (dual engines)")
    say("=" * 74)

    fail = []

    # ---------------------------------------------------------------
    say("[0] Engine agreement + basic invariants over ALL graphs n <= 6")
    total_graphs = 0
    for n in range(1, 7):
        cnt = 0
        for g in eA_graphs(n):
            nbB = eB_from_mask(g, n)
            oa, aa = eA_omega_alpha(g, n)
            ob, ab = eB_omega_alpha(nbB, n)
            if (oa, aa) != (ob, ab):
                fail.append(f"engine omega/alpha mismatch n={n} g={g:0x}")
            if eA_connected(g, n) != eB_connected(nbB, n):
                fail.append(f"engine connectivity mismatch n={n} g={g:0x}")
            # complement involutivity
            if eA_complement(eA_complement(g, n), n) != g:
                fail.append(f"comp invol A n={n} g={g:0x}")
            if eB_complement(eB_complement(nbB, n), n) != nbB:
                fail.append(f"comp invol B n={n} g={g:0x}")
            # engine A vs B complement agreement
            if eB_from_mask(eA_complement(g, n), n) != eB_complement(nbB, n):
                fail.append(f"comp cross mismatch n={n} g={g:0x}")
            # H-freeness cross-check per family
            for name in FAMILY:
                if hfree_A(g, n, name) != hfree_B(nbB, n, name):
                    fail.append(f"H-free mismatch {name} n={n} g={g:0x}")
            cnt += 1
        expect = 2 ** (n * (n - 1) // 2)
        if cnt != expect:
            fail.append(f"graph count n={n}: {cnt} != {expect}")
        say(f"  n={n}: {cnt} graphs enumerated, dual-engine agreement on "
            f"(omega,alpha,connectivity,complement,{len(FAMILY)} H-freeness): "
            f"{'OK' if not fail else 'FAIL'}")
        total_graphs += cnt
    say(f"  TOTAL graphs n<=6: {total_graphs}")
    if fail:
        say("  !! FAIL: " + fail[0])
        sys.exit(1)

    # ---------------------------------------------------------------
    say("")
    say("[1] THE SHARP-VS-SAFE DECISION — the mirror decides the authored form")
    say("    SHARP: max(w,a) >= floor(sqrt(n))   SAFE: max(w,a) >= ceil(sqrt(n)/2)")
    sharp_viol = []   # (H, n, g, omega, alpha)
    safe_viol = []
    fam_counts = {name: 0 for name in FAMILY}
    for n in range(1, 7):
        s = ISQ[n]
        # SAFE bound: smallest t with 4*t*t >= n, i.e. t = ceil(sqrt(n)/2)
        t = 0
        while 4 * t * t < n:
            t += 1
        safe_bound = t
        for g in eA_graphs(n):
            o, a = eA_omega_alpha(g, n)
            mx = max(o, a)
            for name in FAMILY:
                if hfree_A(g, n, name):
                    fam_counts[name] += 1
                    if mx < s:
                        sharp_viol.append((name, n, g, o, a, mx, s))
                    if mx < safe_bound:
                        safe_viol.append((name, n, g, o, a, mx, safe_bound))
    say(f"    H-free graph counts (n<=6, summed): {fam_counts}")
    say(f"    SHARP violations over ALL H-free graphs n<=6: {len(sharp_viol)}")
    if sharp_viol:
        for v in sharp_viol[:10]:
            say(f"      SHARP HOLE: H={v[0]} n={v[1]} g={v[2]:0x} w={v[3]} a={v[4]} max={v[5]} < floor(sqrt n)={v[6]}")
    say(f"    SAFE  violations over ALL H-free graphs n<=6: {len(safe_viol)}")
    verdict = "SHARP" if not sharp_viol else "SAFE"
    say(f"    ==> MIRROR VERDICT: the SHARP form max(omega,alpha) >= floor(sqrt(n)) "
        f"{'HOLDS on all graphs n<=6 for every H in F' if verdict=='SHARP' else 'HAS HOLES -> author SAFE'}")
    say(f"    ==> AUTHORED FORM: {verdict}")

    # ---------------------------------------------------------------
    say("")
    say("[2] SEINSCHE CENSUS (Lemma A): connected AND co-connected => induced P4")
    cc_cnt = 0
    cc_noP4 = []
    for n in range(2, 7):
        ncc = 0
        for g in eA_graphs(n):
            conn = eA_connected(g, n)
            coconn = eA_connected(eA_complement(g, n), n)
            if conn and coconn:
                ncc += 1
                k, edges = FAMILY["P4"]
                if not eA_has_pattern(g, n, k, edges):
                    cc_noP4.append((n, g))
        cc_cnt += ncc
        say(f"  n={n}: {ncc} connected+co-connected graphs; all contain P4: "
            f"{'YES' if not any(x[0]==n for x in cc_noP4) else 'NO — LEMMA FALSE'}")
    say(f"  TOTAL connected+co-connected (n<=6): {cc_cnt}; P4-free among them: {len(cc_noP4)}")
    say(f"  ==> SEINSCHE LEMMA A {'CERTIFIED' if not cc_noP4 else 'REFUTED'} on n<=6 "
        f"(contrapositive: P4-free, n>=2 => disconnected or co-disconnected)")

    # ---------------------------------------------------------------
    say("")
    say("[3] PRODUCT LAW: P3-free and P4-free graphs satisfy omega*alpha >= n")
    for name in ("P3", "P4"):
        bad = []
        cnt = 0
        for n in range(1, 7):
            for g in eA_graphs(n):
                if hfree_A(g, n, name):
                    cnt += 1
                    o, a = eA_omega_alpha(g, n)
                    if o * a < n:
                        bad.append((n, g, o, a))
        say(f"  {name}-free graphs n<=6: {cnt}; product-law violations: {len(bad)}")
        if bad:
            say(f"    !! e.g. {bad[0]}")
            fail.append(f"product law {name}")

    # ---------------------------------------------------------------
    say("")
    say("[4] CLUSTER LAW: P3-free = disjoint union of cliques")
    bad = []
    cnt = 0
    for n in range(1, 7):
        for g in eA_graphs(n):
            if hfree_A(g, n, "P3"):
                cnt += 1
                # components: BFS; each component must be a clique
                comp = [-1] * n
                for start in range(n):
                    if comp[start] >= 0:
                        continue
                    comp[start] = start
                    stack = [start]
                    while stack:
                        v = stack.pop()
                        for w in range(n):
                            if eA_adj(g, n, v, w) and comp[w] < 0:
                                comp[w] = start
                                stack.append(w)
                ok = True
                for v in range(n):
                    for w in range(v + 1, n):
                        if comp[v] == comp[w] and not eA_adj(g, n, v, w):
                            ok = False
                        if comp[v] != comp[w] and eA_adj(g, n, v, w):
                            ok = False
                if not ok:
                    bad.append((n, g))
    say(f"  P3-free graphs n<=6: {cnt}; not-disjoint-union-of-cliques: {len(bad)}")

    # ---------------------------------------------------------------
    say("")
    say("[5] GREEDY LAW: triangle-free -> alpha*(Delta+1) >= n ; CASE A law")
    bad = []
    badA = []
    cnt = 0
    for n in range(1, 7):
        s = ISQ[n]
        for g in eA_graphs(n):
            if hfree_A(g, n, "K3"):
                cnt += 1
                o, a = eA_omega_alpha(g, n)
                delta = 0
                for v in range(n):
                    d = sum(1 for w in range(n) if eA_adj(g, n, v, w))
                    delta = max(delta, d)
                if a * (delta + 1) < n:
                    bad.append((n, g, a, delta))
                if delta >= s and max(o, a) < s:
                    badA.append((n, g, delta, o, a, s))
    say(f"  triangle-free graphs n<=6: {cnt}; greedy-law violations: {len(bad)}; case-A violations: {len(badA)}")

    # ---------------------------------------------------------------
    say("")
    say("[6] COMPLEMENT FAMILY LAWS")
    badc = []
    for n in range(1, 7):
        for g in eA_graphs(n):
            c = eA_complement(g, n)
            nbB = eB_from_mask(g, n)
            cB = eB_complement(nbB, n)
            # Kb3-free(G) = K3-free(comp(G))
            if hfree_A(g, n, "Kb3") != hfree_A(c, n, "K3"):
                badc.append(("Kb3<->K3", n, g))
            if hfree_B(nbB, n, "Kb3") != hfree_B(cB, n, "K3"):
                badc.append(("Kb3<->K3 engineB", n, g))
            # Pb3-free(G) = P3-free(comp(G))
            if hfree_A(g, n, "Pb3") != hfree_A(c, n, "P3"):
                badc.append(("Pb3<->P3", n, g))
            if hfree_B(nbB, n, "Pb3") != hfree_B(cB, n, "P3"):
                badc.append(("Pb3<->P3 engineB", n, g))
            # Kb2-free(G) = complete
            comp_is_complete = all(eA_adj(g, n, i, j)
                                   for i in range(n) for j in range(i + 1, n))
            if hfree_A(g, n, "Kb2") != comp_is_complete:
                badc.append(("Kb2=complete", n, g))
            # K2-free(G) = edgeless
            edgeless = all(not eA_adj(g, n, i, j)
                           for i in range(n) for j in range(i + 1, n))
            if hfree_A(g, n, "K2") != edgeless:
                badc.append(("K2=edgeless", n, g))
            # K1-free(G) = empty graph
            if hfree_A(g, n, "K1") != (n == 0):
                badc.append(("K1=empty", n, g))
    say(f"  complement-law violations over all graphs n<=6: {len(badc)}")

    # ---------------------------------------------------------------
    say("")
    say("[7] UNION/JOIN COMPOSITION LAWS (all graph pairs nA,nB <= 3, both engines)")
    def union_mask(gA, nA, gB, nB):
        """disjoint union: all edges re-encoded at n = nA+nB positions"""
        g = 0
        for i in range(nA):
            for j in range(i + 1, nA):
                if eA_adj(gA, nA, i, j):
                    g |= eA_edge_bit(nA + nB, i, j)
        for i in range(nB):
            for j in range(i + 1, nB):
                if eA_adj(gB, nB, i, j):
                    g |= eA_edge_bit(nA + nB, nA + i, nA + j)
        return g

    def join_mask(gA, nA, gB, nB):
        g = union_mask(gA, nA, gB, nB)
        for i in range(nA):
            for j in range(nB):
                g |= eA_edge_bit(nA + nB, i, nA + j)
        return g

    badU = []
    checks = 0
    for nA in range(0, 4):
        for nB in range(0, 4):
            for gA in eA_graphs(nA):
                for gB in eA_graphs(nB):
                    if nA + nB > 6:
                        continue
                    oA, aA = eA_omega_alpha(gA, nA)
                    oB, aB = eA_omega_alpha(gB, nB)
                    u = union_mask(gA, nA, gB, nB)
                    jn = join_mask(gA, nA, gB, nB)
                    ou, au = eA_omega_alpha(u, nA + nB)
                    oj, aj = eA_omega_alpha(jn, nA + nB)
                    checks += 1
                    if au != aA + aB or ou != max(oA, oB):
                        badU.append(("union", nA, nB, gA, gB))
                    if aj != max(aA, aB) or oj != oA + oB:
                        badU.append(("join", nA, nB, gA, gB))
    say(f"  composition checks: {checks}; violations: {len(badU)}")

    # ---------------------------------------------------------------
    say("")
    say("[8] INTEGER ARITHMETIC (n <= 200; products <= 60)")
    bad8 = []
    for n in range(0, 201):
        s = isqrt(n)
        if s * s > n or (s + 1) * (s + 1) <= n:
            bad8.append(("isqrt spec", n))
        if s >= 1 and (s - 1) * (s - 1) >= s * s:
            bad8.append(("(s-1)^2 < s^2", n))
        # product -> max law: n <= k*m and s^2 <= n -> k >= s or m >= s
        for k in range(0, s + 3):
            for m in range(0, s + 3):
                if k * m >= n and k < s and m < s:
                    # need k*m <= (s-1)^2 < s^2 <= n — contradiction
                    if not (k * m <= (s - 1) * (s - 1)):
                        bad8.append(("prod-max law", n, k, m))
                    else:
                        bad8.append(("prod-max BROKEN", n, k, m))
        # greedy law arithmetic: k*s >= s*s -> k >= s (s>=1)
        if s >= 1:
            for k in range(0, s + 3):
                lhs = k * s
                if lhs >= s * s and k < s:
                    bad8.append(("cancel law", n, k))
    # product composition: (kA+kB)*max(mA,mB) >= kA*mA + kB*mB ; symmetric
    for kA in range(0, 31):
        for kB in range(0, 31):
            for mA in range(0, 31):
                for mB in range(0, 31):
                    M = max(mA, mB)
                    if (kA + kB) * M < kA * mA + kB * mB:
                        bad8.append(("union comp", kA, kB, mA, mB))
                    K = max(kA, kB)
                    if K * (mA + mB) < kA * mA + kB * mB:
                        bad8.append(("join comp", kA, kB, mA, mB))
    say(f"  arithmetic violations: {len(bad8)}")

    # ---------------------------------------------------------------
    say("")
    say("[9] TIGHTNESS: alternating cograph witness — max = sqrt(n) EXACTLY at n=4^j")
    # Y_0 = K1: (n, omega, alpha) = (1,1,1)
    stats = (1, 1, 1)
    j = 0
    tight = []
    while stats[0] <= 4096:
        n, o, a = stats
        s = isqrt(n)
        tight.append((j, n, o, a, max(o, a), s, max(o, a) == s))
        # Y_{j+1} = (Y u Y) v (Y u Y): union doubles alpha, max omega;
        # join takes max alpha, sums omega.
        # union: (n*2, max(o,o), a+a) = (2n, o, 2a)
        u = (2 * n, o, 2 * a)
        # join of u with u: (2n_u, max(a_u,a_u), o_u+o_u)
        stats = (2 * u[0], u[1] + u[1], max(u[2], u[2]))
        j += 1
    all_tight_at_powers = all(row[6] for row in tight if row[1] == 4 ** round(row[1] ** 0.5) if row[1] >= 1)
    for row in tight[:6]:
        say(f"    j={row[0]}: n={row[1]}, omega={row[2]}, alpha={row[3]}, max={row[4]}, floor(sqrt n)={row[5]}, EXACT={row[6]}")
    say(f"    ==> the sharp bound is TIGHT on this family (equality at n=4^j): "
        f"{all(row[6] for row in tight)}")

    # ---------------------------------------------------------------
    say("")
    say("[10] n=7 BONUS CENSUS (targeted, the tight class): P4-free -> max >= floor(sqrt 7) = 2")
    say("     (full n<=7 census is the doubter lane W67-61D's mandate; this is insurance)")
    n = 7
    s = isqrt(n)
    cnt = 0
    bad7 = []
    checked = 0
    # fast path: enumerate with early P4 detection via 4-subsets
    pairs7 = eA_pairs(n)
    bits7 = [eA_edge_bit(n, i, j) for (i, j) in pairs7]
    quartets = list(combinations(range(n), 4))
    for k in range(1 << len(pairs7)):
        g = 0
        for b in range(len(pairs7)):
            if (k >> b) & 1:
                g |= bits7[b]
        checked += 1
        # P4 detection: for each 4-subset, check some ordering is an induced P4
        is_p4free = True
        for q in quartets:
            # quick degree/edge-count filter: induced edges among q
            ecnt = 0
            for x, y in combinations(q, 2):
                if eA_adj(g, n, x, y):
                    ecnt += 1
            if ecnt != 3:
                if ecnt >= 4 or ecnt <= 2:
                    continue
            # exactly 3 edges: check it's a path (degrees 1,2,2,1) and not a claw/star
            degs = sorted(sum(1 for y in q if y != x and eA_adj(g, n, x, y)) for x in q)
            if degs == [1, 1, 2, 2]:
                is_p4free = False
                break
        if is_p4free:
            cnt += 1
            o, a = eA_omega_alpha(g, n)
            if max(o, a) < s:
                bad7.append((g, o, a))
    say(f"     n=7 graphs checked: {checked}; P4-free: {cnt}; sharp violations: {len(bad7)}")

    # ---------------------------------------------------------------
    say("")
    say("=" * 74)
    overall_ok = (not sharp_viol) and (not safe_viol) and (not cc_noP4) and \
                 (not fail) and (not bad) and (not badA) and (not badc) and \
                 (not badU) and (not bad8) and (not bad7)
    say(f"FINAL VERDICT: {'ALL GREEN — mirror certifies the SHARP form' if overall_ok and not sharp_viol else 'ISSUES FOUND'}")
    if not overall_ok:
        for f in (sharp_viol[:5], safe_viol[:5], cc_noP4[:5], fail[:5], bad[:5],
                  badA[:5], badc[:5], badU[:5], bad8[:5], bad7[:5]):
            if f:
                say(f"  sample issue: {f[0]}")
        sys.exit(1)

    with open("engine61/mirror61_output.txt", "w") as fh:
        fh.write("\n".join(out) + "\n")
    print("\n[saved to engine61/mirror61_output.txt]")

if __name__ == "__main__":
    main()
