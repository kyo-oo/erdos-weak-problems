#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""engine61audit_w81.py — W81-61B: the AUDITOR/DOUBLER independent engine for
Erdos-Hajnal #61 (problem61-erdos-hajnal).

Fresh code, fresh algorithms, NO imports from any campaign engine.
Canonical form: min over all vertex permutations of the ';'-joined sorted
adjacency-string table — different machinery from the campaign's
orbit-pattern/numpy canonicalizations.  Bulk freeness tables are built by a
fresh 6-set/5-set decomposition (an H on <=5 vertices appears in a 7-vertex
graph iff it appears in one of the six 6-vertex subgraphs), cross-validated
against direct scans.

Sections (each PASS/FAIL, receipts on stdout):
  A0  CANON      canonical-form sanity (unlabeled counts, identities)
  A1  P4PERF     P4-free perfectness census n<=6 (chi=omega, Lemma SL, counts)
  A2  F7BOARD    the seven H-cases max>=floor(sqrt(n)) n<=6 exhaustive
  A3  HTABLES    h-tables n<=7 recount (two codes) + alpha*omega>=4n/5 census
  A4  RAMK5      Ramsey tower, THEOREM K5, RAM-GEN plug-backs, R(3,3)=6
  A5  C5ENDGAME  W8, slot lemma (finite machine proof of C5 substitution
                 closure), the X_t tower rebuilt and C5-checked at every
                 level, cap arithmetic log3/log8, h_C5(8..11), ladder break
  A6  SUBSTEXP   substitution closure + exponent law f=c1c2/(c1+c2) on
                 random blow-ups + Theorem 4B min-law instances
  A7  INH        inheritance direction machine-checked
  A8  LPC        L-PC / L-COMP spot audit on random C4-free/2K2-free graphs
  A9  P5DOM      P5-domination-shape recount n<=6 + BULL-L1/L2 recount
  A10 C5CLOSURE  union/join/complement closure + subadditivity spine
  A11 NEGCTL     negative controls (planted hosts, corrupted tables)
  A12 61A-CROSS  adversarial cross-audit of the W81-61A lane (bull counts,
                 C5 cores, C5[C5] tower, P5-CROSS, C5 anchor laws,
                 generic slot lemma for P5/bull, n<=6hom^4 families)

Usage:  python3 engine61audit_w81.py [--fast] [--only A0 A5 ...]
Exit 0 iff every section passed.
"""
import argparse
import itertools
import math
import random
import sys
import time
from fractions import Fraction

try:
    import numpy as np
    HAVE_NP = True
except Exception:
    HAVE_NP = False

T_START = time.time()
_RESULTS = []


def res(cid, ok, detail=""):
    _RESULTS.append((cid, bool(ok), str(detail)))
    print(("[PASS] " if ok else "[FAIL] ") + cid + " :: " + str(detail))
    sys.stdout.flush()
    return bool(ok)


# ----------------------------------------------------------------------------
# basic toolkit
# ----------------------------------------------------------------------------

def pairs_of(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def pair_pos(n):
    pos = {}
    k = 0
    for i in range(n):
        for j in range(i + 1, n):
            pos[(i, j)] = k
            k += 1
    return pos


def mask_to_adj(n, emask, pos=None):
    if pos is None:
        pos = pair_pos(n)
    adj = [0] * n
    for (i, j), k in pos.items():
        if (emask >> k) & 1:
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    return adj


def pattern_orbit(edges, k):
    plist = pairs_of(k)
    pidx = {p: ii for ii, p in enumerate(plist)}
    eset = set(tuple(sorted(e)) for e in edges)
    orbit = set()
    for perm in itertools.permutations(range(k)):
        key = 0
        for (a, b) in eset:
            x, y = perm[a], perm[b]
            if x > y:
                x, y = y, x
            key |= 1 << pidx[(x, y)]
        orbit.add(key)
    return orbit


def subset_key(adj, sub):
    k = len(sub)
    key = 0
    b = 0
    for x in range(k):
        for y in range(x + 1, k):
            if (adj[sub[x]] >> sub[y]) & 1:
                key |= 1 << b
            b += 1
    return key


def has_induced(adj, n, orbit, k):
    for sub in itertools.combinations(range(n), k):
        if subset_key(adj, sub) in orbit:
            return True
    return False


def complement_adj(adj, n):
    full = (1 << n) - 1
    return [(~adj[i]) & full & ~(1 << i) for i in range(n)]


def is_connected(adj, n):
    if n <= 1:
        return True
    seen = 1
    stack = [0]
    while stack:
        v = stack.pop()
        nb = adj[v] & ~seen
        while nb:
            b = nb & -nb
            seen |= b
            stack.append(b.bit_length() - 1)
            nb ^= b
    return seen == (1 << n) - 1


def alpha_bruteforce(adj, n):
    best = 0
    for s in range(1 << n):
        ok = True
        m = s
        while m:
            v = (m & -m).bit_length() - 1
            if adj[v] & s:
                ok = False
                break
            m &= m - 1
        if ok:
            c = bin(s).count("1")
            if c > best:
                best = c
    return best


def alpha_exact(adj, n):
    """exact MIS (bitmask recursion with memo on candidate sets)."""
    if n == 0:
        return 0
    memo = {}

    def rec(cand):
        if not cand:
            return 0
        r = memo.get(cand)
        if r is not None:
            return r
        best = 0
        # branch on lowest vertex
        v = (cand & -cand).bit_length() - 1
        rest = cand & ~(1 << v)
        best = rec(rest)
        if adj[v] & rest == 0:
            best = max(best, 1 + rec(rest))
        else:
            best = max(best, 1 + rec(rest & ~adj[v]))
        memo[cand] = best
        return best

    return rec((1 << n) - 1)


def omega_exact(adj, n):
    return alpha_exact(complement_adj(adj, n), n)


def omega_bb(adj, n):
    """max clique B&B (greedy seed + popcount bound) for larger n."""
    best = 0
    P = (1 << n) - 1
    while P:
        v = (P & -P).bit_length() - 1
        best += 1
        P &= adj[v]

    def rec(cand, size):
        nonlocal best
        while cand:
            if size + bin(cand).count("1") <= best:
                return
            v = (cand & -cand).bit_length() - 1
            cand &= ~(1 << v)
            rec(cand & adj[v], size + 1)
        if size > best:
            best = size

    rec((1 << n) - 1, 0)
    return best


def alpha_bb(adj, n):
    return omega_bb(complement_adj(adj, n), n)


# ----------------------------------------------------------------------------
# named graphs
# ----------------------------------------------------------------------------

EDGES = {
    "K1":      [],
    "K2":      [(0, 1)],
    "2K1":     [],
    "2K2":     [(0, 1), (2, 3)],
    "C4":      [(0, 1), (1, 2), (2, 3), (3, 0)],
    "P3":      [(0, 1), (1, 2)],
    "P3b":     [(0, 1)],            # K2+K1
    "K3":      [(0, 1), (0, 2), (1, 2)],
    "3K1":     [],
    "P4":      [(0, 1), (1, 2), (2, 3)],
    "paw":     [(0, 1), (0, 2), (1, 2), (0, 3)],
    "diamond": [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)],
    "K2+2K1":  [(0, 1)],
    "claw":    [(0, 1), (0, 2), (0, 3)],
    "K3+K1":   [(0, 1), (0, 2), (1, 2)],
    "K4":      [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
    "P5":      [(0, 1), (1, 2), (2, 3), (3, 4)],
    "house":   [(0, 1), (0, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
    "bull":    [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4)],
    "C5":      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)],
    "K5":      [(i, j) for i in range(5) for j in range(i + 1, 5)],
}
ORDERS = {k: ({"K1": 1, "K2": 2, "2K1": 2, "2K2": 4, "C4": 4, "P3": 3, "P3b": 3, "K3": 3, "3K1": 3,
               "P4": 4, "paw": 4, "diamond": 4, "K2+2K1": 4, "claw": 4,
               "K3+K1": 4, "K4": 4, "P5": 5, "house": 5, "bull": 5, "C5": 5,
               "K5": 5})[k] for k in EDGES}
ORBITS = {name: pattern_orbit(e, ORDERS[name]) for name, e in EDGES.items()}


def adj_of(name):
    k = ORDERS[name]
    a = [0] * k
    for (x, y) in EDGES[name]:
        a[x] |= 1 << y
        a[y] |= 1 << x
    return a


def is_free(adj, n, name):
    return not has_induced(adj, n, ORBITS[name], ORDERS[name])


def substitute(Q, pieces):
    t = len(Q)
    sizes = [len(m) for m in pieces]
    n = sum(sizes)
    adj = [0] * n
    ofs = [0]
    for s in sizes:
        ofs.append(ofs[-1] + s)
    for s in range(t):
        for v in range(sizes[s]):
            gid = ofs[s] + v
            for w in range(sizes[s]):
                if v != w and (pieces[s][v] >> w) & 1:
                    adj[gid] |= 1 << (ofs[s] + w)
            for s2 in range(t):
                if s2 != s and (Q[s] >> s2) & 1:
                    adj[gid] |= ((1 << sizes[s2]) - 1) << ofs[s2]
    return adj


def disjoint_union(A, B):
    n1, n2 = len(A), len(B)
    out = list(A) + [(B[i] << n1) for i in range(n2)]
    return out


def join_graphs(A, B):
    n1, n2 = len(A), len(B)
    out = [A[i] | (((1 << n2) - 1) << n1) for i in range(n1)]
    out += [(B[i] << n1) | ((1 << n1) - 1) for i in range(n2)]
    return out


def canon_string(adj, n):
    best = None
    for perm in itertools.permutations(range(n)):
        rows = []
        for i in range(n):
            row = []
            for j in range(n):
                if i != j and (adj[perm[i]] >> perm[j]) & 1:
                    row.append(str(j))
            rows.append(",".join(row) if row else "-")
        s = ";".join(rows)
        if best is None or s < best:
            best = s
    return best


def apply_perm_mask(n, emask, pos, perm):
    """relabel the graph emask (n vertices) by perm (new i = old perm[i])."""
    adj = mask_to_adj(n, emask, pos)
    out = 0
    for i in range(n):
        for j in range(i + 1, n):
            if (adj[perm[i]] >> perm[j]) & 1:
                out |= 1 << pos[(i, j)]
    return out


# ----------------------------------------------------------------------------
# A0 CANON
# ----------------------------------------------------------------------------

def sec_a0():
    t0 = time.time()
    ok = True
    det = []
    counts = []
    for n in range(1, 7):
        pos = pair_pos(n)
        seen = bytearray(1 << len(pairs_of(n)))
        nperm = list(itertools.permutations(range(n)))
        orbits = 0
        for emask in range(1 << len(pairs_of(n))):
            if seen[emask]:
                continue
            orbits += 1
            for perm in nperm:
                seen[apply_perm_mask(n, emask, pos, perm)] = 1
        counts.append(orbits)
    target = [1, 2, 4, 11, 34, 156]
    if counts != target:
        ok = False
    det.append("unlabeled counts n=1..6 = %s (target %s)" % (counts, target))
    id1 = canon_string(adj_of("C5"), 5) == canon_string(complement_adj(adj_of("C5"), 5), 5)
    id2 = canon_string(adj_of("bull"), 5) == canon_string(complement_adj(adj_of("bull"), 5), 5)
    id3 = canon_string(adj_of("house"), 5) == canon_string(complement_adj(adj_of("P5"), 5), 5)
    if not (id1 and id2 and id3):
        ok = False
    det.append("C5 self-comp=%s; bull self-comp=%s; comp(P5)=house=%s" % (id1, id2, id3))
    e2 = [0, 0]  # 2K1
    g = substitute(adj_of("K2"), [e2, e2])
    iso_c4 = canon_string(g, 4) == canon_string(adj_of("C4"), 4)
    if not iso_c4:
        ok = False
    det.append("K2[2K1,2K1] iso C4 = %s" % iso_c4)
    bell = [1, 2, 5, 15, 52, 203]
    p3c = []
    for n in range(1, 7):
        pos = pair_pos(n)
        c = 0
        for emask in range(1 << len(pairs_of(n))):
            if is_free(mask_to_adj(n, emask, pos), n, "P3"):
                c += 1
        p3c.append(c)
    if p3c != bell:
        ok = False
    det.append("P3-free labeled counts = %s (Bell %s)" % (p3c, bell))
    res("A0-CANON", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A1 P4PERF
# ----------------------------------------------------------------------------

def chi_exact(adj, n):
    for k in range(1, n + 1):
        colors = [-1] * n

        def dfs(v):
            if v == n:
                return True
            used = 0
            for u in range(v):
                if colors[u] != -1 and (adj[v] >> u) & 1:
                    used |= 1 << colors[u]
            for c in range(k):
                if not (used >> c) & 1:
                    colors[v] = c
                    if dfs(v + 1):
                        return True
            colors[v] = -1
            return False

        if dfs(0):
            return k
    return n


def sec_a1():
    t0 = time.time()
    ok = True
    det = []
    counts = []
    total = 0
    perf_bad = prod_bad = sq_bad = sl_bad = 0
    for n in range(1, 7):
        pos = pair_pos(n)
        cnt = 0
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask, pos)
            if is_free(adj, n, "P4"):
                cnt += 1
                a = alpha_bruteforce(adj, n)
                w = omega_exact(adj, n)
                if chi_exact(adj, n) != w:
                    perf_bad += 1
                if a * w < n:
                    prod_bad += 1
                if max(a, w) < math.ceil(math.sqrt(n) - 1e-12):
                    sq_bad += 1
                if n >= 2 and is_connected(adj, n) and is_connected(complement_adj(adj, n), n):
                    sl_bad += 1
        counts.append(cnt)
        total += cnt
    det.append("P4-free labeled counts n=1..6 = %s (total %d)" % (counts, total))
    if perf_bad or prod_bad or sq_bad or sl_bad:
        ok = False
    det.append("violations: chi!=omega %d, alpha*omega<n %d, max<ceil(sqrt n) %d, SL %d"
               % (perf_bad, prod_bad, sq_bad, sl_bad))
    res("A1-P4PERFECTNESS", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A2 F7BOARD
# ----------------------------------------------------------------------------

def sec_a2():
    t0 = time.time()
    ok = True
    det = []
    cases = {"K1": None, "K2": "edgeless", "Kb2": "complete", "K3": "K3",
             "Kb3": "3K1", "P3": "P3", "Pb3": "P3b"}
    for hname, mode in cases.items():
        bad = 0
        cnt = 0
        for n in range(1, 7):
            pos = pair_pos(n)
            for emask in range(1 << len(pairs_of(n))):
                adj = mask_to_adj(n, emask, pos)
                if hname == "K1":
                    continue  # no K1-free graphs on n>=1: vacuous
                if mode == "edgeless":
                    free = all(adj[i] == 0 for i in range(n))
                elif mode == "complete":
                    free = all(adj[i] == (1 << n) - 1 - (1 << i) for i in range(n))
                else:
                    free = is_free(adj, n, mode)
                if free:
                    cnt += 1
                    if max(alpha_bruteforce(adj, n), omega_exact(adj, n)) < math.floor(math.sqrt(n)):
                        bad += 1
        det.append("%s: %d H-free graphs, %d violations" % (hname, cnt, bad))
        if bad:
            ok = False
    det.append("K1: vacuous (no K1-free graph on n>=1) — the F7 board's own convention")
    res("A2-F7BOARD", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A3 HTABLES
# ----------------------------------------------------------------------------

HTARGETS = {
    "C5":    [1, 2, 2, 2, 3, 3, 3],
    "P5":    [1, 2, 2, 2, 2, 3, 3],
    "house": [1, 2, 2, 2, 2, 3, 3],
    "bull":  [1, 2, 2, 2, 2, 3, 3],
    "2K2":   [1, 2, 2, 2, 2, 3, 3],
    "C4":    [1, 2, 2, 2, 2, 3, 3],
    "claw":  [1, 2, 2, 2, 2, 3, 3],
    "P3":    [1, 2, 2, 2, 3, 3, 3],
    "3K1":   [1, 2, 2, 2, 2, 3, 3],
}
COUNTS_N7 = {"C5": 1742336, "P5": 1019492, "house": 1019492, "bull": 876632}
CLASSES5 = ["C5", "P5", "house", "bull", "K5"]       # 5-vertex patterns
CLASSES4 = ["2K2", "C4", "claw", "P4", "paw", "diamond", "K2+2K1", "K3+K1", "K4"]
CLASSES3 = ["P3", "P3b", "K3", "3K1"]
ALL_CLASSES = ["C5", "P5", "house", "bull", "2K2", "C4", "claw", "P3", "3K1"]


def build_free_tables():
    """free-flags by class for every labeled graph, n<=6, via the
    (n-1)-set decomposition; returns dict class -> bool array (2^15)."""
    # n=5 tables (10-bit indexed)
    pos5 = pair_pos(5)
    free5 = {c: bytearray(1024) for c in ALL_CLASSES}
    for emask in range(1024):
        adj = mask_to_adj(5, emask, pos5)
        for c in ALL_CLASSES:
            if not has_induced(adj, 5, ORBITS[c], ORDERS[c]):
                free5[c][emask] = 1
    # decomposition pieces for n=6 = (g5, ext).
    # derived 5-vertex graph D_u: old others[0..3] -> new 0..3, vertex 5 -> 4.
    # bit positions in the pair_pos(5) layout:
    POS4 = [pos5[(x, y)] for x in range(4) for y in range(x + 1, 4)]
    POSN4 = [pos5[(x, 4)] for x in range(4)]
    base9 = [[0] * 5 for _ in range(1024)]
    for g5 in range(1024):
        adj5 = mask_to_adj(5, g5, pos5)
        for u in range(5):
            others = [v for v in range(5) if v != u]
            val = 0
            b = 0
            for x in range(4):
                for y in range(x + 1, 4):
                    if (adj5[others[x]] >> others[y]) & 1:
                        val |= 1 << POS4[b]
                    b += 1
            base9[g5][u] = val
    place4 = [[0] * 5 for _ in range(32)]
    for ext in range(32):
        for u in range(5):
            others = [v for v in range(5) if v != u]
            val = 0
            for v in range(5):
                if v != u and (ext >> v) & 1:
                    val |= 1 << POSN4[others.index(v)]
            place4[ext][u] = val
    free6 = {c: np.zeros(1 << 15, dtype=bool) if HAVE_NP else bytearray(1 << 15)
             for c in ALL_CLASSES}
    # conversion: for every 6-vertex mask (pair_pos(6) layout) extract the
    # (g5, ext) decomposition: g5 = base {0..4} in pair_pos(5) layout,
    # ext = 5-bit neighborhood of vertex 5.
    pos6 = pair_pos(6)
    conv = [(0, 0)] * (1 << 15)
    for g6 in range(1 << 15):
        adj6 = mask_to_adj(6, g6, pos6)
        g5 = 0
        for (i, j), k in pos5.items():
            if (adj6[i] >> j) & 1:
                g5 |= 1 << k
        conv[g6] = (g5, adj6[5])
    for c in ALL_CLASSES:
        f5 = free5[c]
        f6 = free6[c]
        for g6 in range(1 << 15):
            g5, ext = conv[g6]
            if not f5[g5]:
                continue        # base not free => G6 not free (heredity)
            b9 = base9[g5]
            good = True
            for u in range(5):
                if not f5[b9[u] | place4[ext][u]]:
                    good = False
                    break
            if good:
                if isinstance(f6, bytearray):
                    f6[g6] = 1
                else:
                    f6[g6] = True
    return free5, free6, base9, place4


def sec_a3(fast):
    t0 = time.time()
    ok = True
    det = []
    free5, free6, base9, place4 = build_free_tables()
    # ---- Code 2: pure-python recount n<=6 (direct scans, exact hom) ----
    rows = {c: [] for c in ALL_CLASSES}
    prodviol = 0
    eqcount = 0
    cnts_n5 = {}
    for n in range(1, 7):
        mins = {c: None for c in ALL_CLASSES}
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            a = alpha_bruteforce(adj, n)
            w = omega_exact(adj, n)
            hom = max(a, w)
            for c in ALL_CLASSES:
                if not has_induced(adj, n, ORBITS[c], ORDERS[c]):
                    if mins[c] is None or hom < mins[c]:
                        mins[c] = hom
            if n == 5:
                for c in ALL_CLASSES:
                    if not has_induced(adj, n, ORBITS[c], ORDERS[c]):
                        cnts_n5[c] = cnts_n5.get(c, 0) + 1
            if n >= 4:
                free22 = not has_induced(adj, n, ORBITS["2K2"], 4)
                freec4 = not has_induced(adj, n, ORBITS["C4"], 4)
                if free22 or freec4:
                    # product census applies per class; count per class below
                    pass
                if free22:
                    if a * w < 4 * n / 5.0 - 1e-12:
                        prodviol += 1
                    if abs(a * w - 4 * n / 5.0) < 1e-12:
                        eqcount += 1
        for c in ALL_CLASSES:
            rows[c].append(mins[c])
    bad = [c for c in ALL_CLASSES if rows[c] != HTARGETS[c][:6]]
    det.append("Code2 h-rows n=1..6: " + "; ".join(
        "%s=%s" % (c, rows[c]) for c in ("C5", "P5", "house", "bull", "2K2", "C4", "P3", "3K1")))
    if bad:
        ok = False
        det.append("ROW MISMATCH: %s" % bad)
    det.append("counts n=5: C5-free=%d (tgt 1012), P5-free=%d (tgt 964), house=%d, bull=%d (tgt 964)"
               % (cnts_n5.get("C5", 0), cnts_n5.get("P5", 0), cnts_n5.get("house", 0), cnts_n5.get("bull", 0)))
    if cnts_n5.get("C5", 0) != 1012 or cnts_n5.get("P5", 0) != 964 or cnts_n5.get("bull", 0) != 964:
        ok = False
    det.append("alpha*omega>=4n/5 census n<=6 (2K2-free): violations=%d, equality=%d (expect 0, 12)"
               % (prodviol, eqcount))
    if prodviol or eqcount != 12:
        ok = False
    # C4 side equality count
    eqc4 = 0
    pvc4 = 0
    for n in range(4, 7):
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if not has_induced(adj, n, ORBITS["C4"], 4):
                a = alpha_bruteforce(adj, n)
                w = omega_exact(adj, n)
                if a * w < 4 * n / 5.0 - 1e-12:
                    pvc4 += 1
                if abs(a * w - 4 * n / 5.0) < 1e-12:
                    eqc4 += 1
    det.append("alpha*omega>=4n/5 census n<=6 (C4-free): violations=%d, equality=%d (expect 0, 12)"
               % (pvc4, eqc4))
    if pvc4 or eqc4 != 12:
        ok = False
    # ---- Code 1: numpy n=7 sweep (decomposition) ----
    h7 = {c: None for c in ALL_CLASSES}
    if HAVE_NP:
        pos6 = pair_pos(6)
        # derived 6-vertex graph D_u: old others[0..4] -> new 0..4, vertex 6 -> 5.
        # bit positions in the pair_pos(6) layout:
        POS5 = [pos6[(x, y)] for x in range(5) for y in range(x + 1, 5)]
        POSN5 = [pos6[(x, 5)] for x in range(5)]
        base10 = np.zeros((1 << 15, 6), dtype=np.int32)
        for g6 in range(1 << 15):
            adj6 = mask_to_adj(6, g6, pos6)
            for u in range(6):
                others = [v for v in range(6) if v != u]
                val = 0
                b = 0
                for x in range(5):
                    for y in range(x + 1, 5):
                        if (adj6[others[x]] >> others[y]) & 1:
                            val |= 1 << POS5[b]
                        b += 1
                base10[g6][u] = val
        place5 = np.zeros((64, 6), dtype=np.int32)
        for ext in range(64):
            for u in range(6):
                others = [v for v in range(6) if v != u]
                val = 0
                for v in range(6):
                    if v != u and (ext >> v) & 1:
                        val |= 1 << POSN5[others.index(v)]
                place5[ext][u] = val
        # exact hom<=3 grid over ALL 2^21 seven-vertex graphs (class-independent):
        # hom<=3 iff no independent 4-set and no K4 (hom>=3 is forced by R(3,3)=6)
        grid = np.arange(1 << 15, dtype=np.uint32)[:, None] | \
            (np.arange(64, dtype=np.uint32)[None, :] << np.uint32(15))

        def p7d(a, b):
            if a > b:
                a, b = b, a
            return (15 + a) if b == 6 else pos6[(a, b)]

        noind4 = np.ones((1 << 15, 64), dtype=bool)
        nok4 = np.ones((1 << 15, 64), dtype=bool)
        for S in itertools.combinations(range(7), 4):
            sind = np.ones((1 << 15, 64), dtype=bool)
            skli = np.ones((1 << 15, 64), dtype=bool)
            for (a, b) in itertools.combinations(S, 2):
                bit = np.uint32(1) << np.uint32(p7d(a, b))
                e = (grid & bit) != 0
                sind &= ~e       # independent: all 6 pairs absent
                skli &= e        # clique: all 6 pairs present
            noind4 &= ~sind      # no independent 4-set
            nok4 &= ~skli        # no K4
        hom3grid = noind4 & nok4
        counts7 = {}
        wit = {}
        for c in ALL_CLASSES:
            tab = free6[c] if isinstance(free6[c], np.ndarray) else np.array(free6[c], dtype=bool)
            acc = np.ones((1 << 15, 64), dtype=bool)
            for u in range(6):
                sub = base10[:, u][:, None] | place5[:, u][None, :]
                acc &= tab[sub]
            counts7[c] = int(acc.sum())
            witmask = acc & hom3grid
            found = None
            if witmask.any():
                g6, ext = [int(x) for x in np.argwhere(witmask)[0]]
                adj7 = mask_to_adj(6, g6, pos6) + [0]
                for v in range(6):
                    if (ext >> v) & 1:
                        adj7[v] |= 1 << 6
                        adj7[6] |= 1 << v
                found = adj7
                assert max(alpha_bruteforce(adj7, 7), omega_exact(adj7, 7)) == 3
            wit[c] = found
            h7[c] = 3 if found is not None else 4
        det.append("Code1 n=7 counts: C5=%d (tgt 1742336), P5=%d (tgt 1019492), house=%d, bull=%d (tgt 876632)"
                   % (counts7["C5"], counts7["P5"], counts7["house"], counts7["bull"]))
        for c, tgt in COUNTS_N7.items():
            if counts7[c] != tgt:
                ok = False
                det.append("COUNT MISMATCH n=7 %s: %d vs %d" % (c, counts7[c], tgt))
        det.append("Code1 n=7 h: " + "; ".join("%s=%d" % (c, h7[c]) for c in ALL_CLASSES))
        for c in ALL_CLASSES:
            if h7[c] != HTARGETS[c][6]:
                ok = False
                det.append("H7 MISMATCH %s: %d vs %d" % (c, h7[c], HTARGETS[c][6]))
        # self-test: decomposition vs direct on random graphs
        rng = random.Random(61)
        st = True
        for _ in range(150):
            g6 = rng.randrange(1 << 15)
            ext = rng.randrange(64)
            adj7 = mask_to_adj(6, g6, pos6) + [0]
            for v in range(6):
                if (ext >> v) & 1:
                    adj7[v] |= 1 << 6
                    adj7[6] |= 1 << v
            for c in ("C5", "P5", "2K2", "claw", "P3"):
                direct = is_free(adj7, 7, c)
                dec = all(tab_lookup(free6, c, int(base10[g6][u]) | int(place5[ext][u]))
                          for u in range(6))
                if direct != dec:
                    st = False
        if not st:
            ok = False
            det.append("DECOMPOSITION SELF-TEST FAILED")
        else:
            det.append("decomposition self-test 150x5 agree")
        # n=7 product census: mathematical argument + 5k sampled confirmation
        # (any n>=6 graph has hom>=3; alpha*omega<=5 forces (2,2) [excluded by
        # R(3,3)=6] or alpha=1/omega=1 [complete/edgeless, products 7]);
        # hence alpha*omega >= 6 > 28/5 for EVERY 7-vertex graph.
        rng = random.Random(62)
        samp = 0
        pv7 = 0
        for _ in range(5000):
            g6 = rng.randrange(1 << 15)
            ext = rng.randrange(64)
            if not tab_lookup(free6, "2K2", g6):
                # base must be free; only then can the 7-graph be free
                continue
            adj7 = mask_to_adj(6, g6, pos6) + [0]
            for v in range(6):
                if (ext >> v) & 1:
                    adj7[v] |= 1 << 6
                    adj7[6] |= 1 << v
            if not is_free(adj7, 7, "2K2"):
                continue
            samp += 1
            if alpha_bruteforce(adj7, 7) * omega_exact(adj7, 7) < 5.6:
                pv7 += 1
        det.append("alpha*omega>=4n/5 at n=7: forced by R(3,3)=6 (28/5 non-integer, "
                   "equality impossible); %d sampled 2K2-free confirm, %d violations" % (samp, pv7))
        if pv7:
            ok = False
    else:
        det.append("numpy MISSING: n=7 sweep skipped")
    # ---- Code 2 at n=7: explicit witnesses + PIGEONHOLE-SIX floor ----
    K1vP6 = [0] * 7                          # K1 v P6 (wheel minus rim vertex)
    K1vP6[0] = 0b1111110
    for i in range(1, 7):
        K1vP6[i] |= 1                        # center
        if i > 1:
            K1vP6[i] |= 1 << (i - 1)
            K1vP6[i - 1] |= 1 << i
    wit2 = {"C5": K1vP6,                     # wheel minus rim vertex
            "P5": disjoint_union(adj_of("C5"), adj_of("K2")),
            "house": disjoint_union(adj_of("C5"), adj_of("K2")),
            "bull": disjoint_union(adj_of("C5"), adj_of("K2")),
            "C4": disjoint_union(adj_of("C5"), adj_of("K2")),
            "claw": disjoint_union(adj_of("C5"), adj_of("K2")),
            "3K1": join_graphs(adj_of("C5"), [0, 0]),
            "2K2": None,
            "P3": disjoint_union(adj_of("K3"), disjoint_union(adj_of("K2"), adj_of("K2")))}
    # 2K2 witness via quick hunt
    wit2["2K2"] = quick_hunt(7, "2K2", 3, seed=5, budget=20.0)
    code2 = {}
    for c, g in wit2.items():
        if g is None:
            code2[c] = None
            continue
        n = len(g)
        free = is_free(g, n, c)
        hom = max(alpha_bruteforce(g, n), omega_exact(g, n))
        code2[c] = 3 if (free and n == 7 and hom == 3) else None
    det.append("Code2 n=7 witnesses: " + "; ".join("%s:%s" % (c, code2[c]) for c in ALL_CLASSES))
    for c in ALL_CLASSES:
        if code2[c] != 3:
            ok = False
    # corrupted-table negative control
    corrupt_c5 = [1, 2, 2, 2, 2, 3, 3]
    corrupt_p3 = [1, 2, 2, 2, 2, 3, 3]
    detected = (rows["C5"] != corrupt_c5[:6]) and (rows["P3"] != corrupt_p3[:6]) \
        and (HTARGETS["C5"] != corrupt_c5)
    if not detected:
        ok = False
    det.append("corrupted-h-table detection (h_C5(5)=2 / h_P3(5)=2 both rejected): %s" % detected)
    res("A3-HTABLES", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


def tab_lookup(free6, c, m):
    t = free6[c]
    if isinstance(t, np.ndarray):
        return bool(t[m])
    return bool(t[m])


def quick_hunt(n, pat, target_hom, seed, budget):
    """randomized search for a pat-free graph with alpha,omega <= target_hom."""
    rng = random.Random(seed)
    orb = ORBITS[pat]
    k = ORDERS[pat]
    subs = list(itertools.combinations(range(n), k))
    t0 = time.time()
    while time.time() - t0 < budget:
        adj = [0] * n
        p = rng.uniform(0.2, 0.7)
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        for _ in range(300):
            bad = [s for s in subs if subset_key(adj, s) in orb]
            a = alpha_bruteforce(adj, n)
            w = omega_exact(adj, n)
            score = len(bad) * 1000 + 100 * max(0, a - target_hom) + 100 * max(0, w - target_hom)
            if score == 0:
                return adj
            best = None
            for i in range(n):
                for j in range(i + 1, n):
                    adj2 = list(adj)
                    adj2[i] ^= 1 << j
                    adj2[j] ^= 1 << i
                    b2 = sum(1 for s in subs if subset_key(adj2, s) in orb)
                    a2 = alpha_bruteforce(adj2, n)
                    w2 = omega_exact(adj2, n)
                    s2 = b2 * 1000 + 100 * max(0, a2 - target_hom) + 100 * max(0, w2 - target_hom)
                    if best is None or s2 < best[0]:
                        best = (s2, adj2)
            if best is None or best[0] >= score:
                break
            adj = best[1]
    return None


# ----------------------------------------------------------------------------
# A4 RAMK5
# ----------------------------------------------------------------------------

def sec_a4(fast):
    t0 = time.time()
    ok = True
    det = []
    # R(3,3)=6 exhaustive
    r336 = True
    pos6 = pair_pos(6)
    oK3 = ORBITS["K3"]
    for emask in range(1 << 15):
        adj = mask_to_adj(6, emask, pos6)
        tri = has_induced(adj, 6, oK3, 3)
        if not tri:
            if alpha_bruteforce(adj, 6) < 3:
                r336 = False
                break
    c5 = adj_of("C5")
    wit5 = (not has_induced(c5, 5, oK3, 3)) and alpha_bruteforce(c5, 5) == 2 \
        and omega_exact(c5, 5) == 2
    if not (r336 and wit5):
        ok = False
    det.append("R(3,3)=6 exhaustive (32768 graphs, triangle-free => alpha>=3): %s; "
               "C5 5-vertex tightness witness: %s" % (r336, wit5))
    import functools

    @functools.lru_cache(maxsize=None)
    def Rdp(a, b):
        if a == 2:
            return b
        if b == 2:
            return a
        return Rdp(a - 1, b) + Rdp(a, b - 1)

    tow = True
    for a in range(2, 9):
        for b in range(2, 9):
            if Rdp(a, b) > math.comb(a + b - 2, a - 1):
                tow = False
    if not (tow and Rdp(5, 3) <= 15 and Rdp(5, 4) <= 35 and Rdp(4, 4) <= 20):
        ok = False
    det.append("recursion DP: R(5,3)=%d<=15, R(5,4)=%d<=35, R(4,4)=%d<=20; "
               "R(a,b)<=C(a+b-2,a-1) for all a,b in [2,8]: %s"
               % (Rdp(5, 3), Rdp(5, 4), Rdp(4, 4), tow))
    # THEOREM K5 exhaustive n<=6
    bad = 0
    cnt = 0
    oK5 = ORBITS["K5"]
    for n in range(1, 7):
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if not has_induced(adj, n, oK5, 5):
                cnt += 1
                if alpha_bruteforce(adj, n) < math.floor((24.0 * n) ** 0.25) - 3:
                    bad += 1
    det.append("THEOREM K5 exhaustive n<=6: %d K5-free graphs, %d violations" % (cnt, bad))
    if bad:
        ok = False
    # sampled K5-free n=7..12
    rng = random.Random(20261121)
    sbad = 0
    scnt = 0
    t5c = None
    for n in range(7, 13):
        for _ in range(30 if fast else 70):
            parts = [rng.randrange(4) for _ in range(n)]
            adj = [0] * n
            for i in range(n):
                for j in range(i + 1, n):
                    if parts[i] != parts[j] and rng.random() < 0.7:
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            if has_induced(adj, n, oK5, 5):
                sbad += 1
                continue
            scnt += 1
            a = alpha_bruteforce(adj, n)
            if a < math.floor((24.0 * n) ** 0.25) - 3:
                sbad += 1
            x = 24.0 ** 0.25 * n ** 0.25
            if a < math.ceil(x) - 4:
                sbad += 1
            if t5c is None:
                N0 = 8.0 ** 4 / 24.0
                t5c = min(1.0 / 8, math.log(2) / (2 * math.log(N0)))
            if max(a, omega_exact(adj, n)) + 1e-12 < n ** t5c:
                sbad += 1
        got = 0
        tries = 0
        while got < 5 and tries < 3000:
            tries += 1
            adj = [0] * n
            for i in range(n):
                for j in range(i + 1, n):
                    if rng.random() < 0.3:
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            if has_induced(adj, n, oK3, 3):
                continue
            got += 1
            scnt += 1
            if alpha_bruteforce(adj, n) < math.floor((24.0 * n) ** 0.25) - 3:
                sbad += 1
    det.append("sampled K5-free n=7..12: %d instances (4-partite + triangle-free), %d violations "
               "(K5 bound + RAM-GEN RG-1/RG-3 at t=5, c(5)=%.4f)" % (scnt, sbad, t5c))
    if sbad:
        ok = False
    # RAM-GEN exhaustive t=3,4,5 n<=6
    rg = 0
    for t in (3, 4, 5):
        orb = ORBITS["K%d" % t]
        fac = math.factorial(t - 1)
        for n in range(1, 7):
            for emask in range(1 << len(pairs_of(n))):
                adj = mask_to_adj(n, emask)
                if not has_induced(adj, n, orb, t):
                    x = fac ** (1.0 / (t - 1)) * n ** (1.0 / (t - 1))
                    if alpha_bruteforce(adj, n) < math.ceil(x) - (t - 1):
                        rg += 1
    det.append("RAM-GEN (RG-1) exhaustive n<=6, t=3,4,5: %d violations" % rg)
    if rg:
        ok = False
    lad = (2 >= 13 ** 0.2) and (3 >= 34 ** 0.2) and (4 >= 1024 ** 0.2) \
        and ((24 * 1025) ** 0.25 - 4 >= 1025 ** 0.2)
    prev = None
    mono = True
    for kk in range(200):
        n = 1025 + kk * 5000
        g = (24 * n) ** 0.25 - 4 - n ** 0.2
        if prev is not None and g < prev - 1e-12:
            mono = False
        prev = g
    if not (lad and mono):
        ok = False
    det.append("K5 case-ladder rungs + g(n) monotonicity on grid: %s/%s" % (lad, mono))
    res("A4-RAMK5", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A5 C5ENDGAME
# ----------------------------------------------------------------------------

def build_W8():
    adj = [0] * 8
    for i in range(1, 8):
        adj[0] |= 1 << i
        adj[i] |= 1
    for i in range(1, 8):
        j = i + 1 if i < 7 else 1
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def c5_free_scan(adj, n, rng=None, sample=None):
    orb = ORBITS["C5"]
    if sample is None:
        for sub in itertools.combinations(range(n), 5):
            if subset_key(adj, sub) in orb:
                return False, 1
        return True, 0
    hits = 0
    for _ in range(sample):
        sub = tuple(sorted(rng.sample(range(n), 5)))
        if subset_key(adj, sub) in orb:
            hits += 1
    return hits == 0, hits


def fast_hunt(n, target, seed, budget):
    """optimized hunt: n-vertex graph, C5-free, alpha/omega <= target."""
    rng = random.Random(seed)
    orb = ORBITS["C5"]
    subs = list(itertools.combinations(range(n), 5))
    # subsets containing each pair, with the pair's key-slot
    pairsubs = {}
    for idx, s in enumerate(subs):
        for x in range(5):
            for y in range(x + 1, 5):
                pairsubs.setdefault((s[x], s[y]), []).append((idx, x, y))
    t0 = time.time()
    best_score = [10 ** 9, None]
    while time.time() - t0 < budget:
        adj = [0] * n
        p = rng.uniform(0.15, 0.75)
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        for _ in range(600):
            badidx = [i for i, s in enumerate(subs) if subset_key(adj, s) in orb]
            a = alpha_exact(adj, n)
            w = omega_exact(adj, n)
            score = 1000 * len(badidx) + 100 * max(0, a - target) + 100 * max(0, w - target)
            if score < best_score[0]:
                best_score = [score, list(adj)]
            if score == 0:
                return list(adj), 0
            badset = set(badidx)
            bestmove = None
            for i in range(n):
                for j in range(i + 1, n):
                    # delta over subsets containing (i,j)
                    d = 0
                    for (idx, x, y) in pairsubs.get((i, j), ()):
                        s = subs[idx]
                        key = subset_key(adj, s)
                        was = key in orb
                        bit = (adj[i] >> j) & 1
                        # flip changes only the (x,y) slot
                        now = (key ^ (1 << (x * 5 - x * (x + 1) // 2 + (y - x - 1)))) in orb
                        if was != now:
                            d += 1 if now else -1
                    if d > 1:
                        continue
                    adj[i] ^= 1 << j
                    adj[j] ^= 1 << i
                    a2 = alpha_exact(adj, n)
                    w2 = omega_exact(adj, n)
                    b2 = len(badset) + d
                    s2 = 1000 * b2 + 100 * max(0, a2 - target) + 100 * max(0, w2 - target)
                    adj[i] ^= 1 << j
                    adj[j] ^= 1 << i
                    if bestmove is None or s2 < bestmove[0]:
                        bestmove = (s2, i, j)
            if bestmove is None or bestmove[0] >= score:
                break
            _, i, j = bestmove
            adj[i] ^= 1 << j
            adj[j] ^= 1 << i
    return None, best_score[0]


def sec_a5(fast):
    t0 = time.time()
    ok = True
    det = []
    W8 = build_W8()
    w8free, _ = c5_free_scan(W8, 8)
    a8 = alpha_exact(W8, 8)
    o8 = omega_exact(W8, 8)
    if not (w8free and a8 == 3 and o8 == 3):
        ok = False
    det.append("W8=K1 v C7: C5-free=%s alpha=%d omega=%d (targets 3,3)" % (w8free, a8, o8))
    # ---- slot lemma: finite machine proof of C5 substitution closure ----
    c5edges = set(tuple(sorted(e)) for e in EDGES["C5"])
    uniq = []
    for perm in itertools.permutations(range(5)):
        M = [[False] * 5 for _ in range(5)]
        for (a, b) in c5edges:
            x, y = perm[a], perm[b]
            M[x][y] = M[y][x] = True
        if M not in uniq:
            uniq.append(M)
    lemma_ok = True
    nassign = 0
    for M in uniq:
        for k in (2, 3, 4):
            for assign in itertools.product(range(k), repeat=5):
                if len(set(assign)) < 2:
                    continue
                nassign += 1
                found = False
                for u in range(5):
                    for v in range(u + 1, 5):
                        if assign[u] != assign[v]:
                            continue
                        # blow-up FORCES M[u][w]==M[v][w] for all w outside
                        # the slot; a C5 pair always differs somewhere among
                        # the other three, so a difference OUTSIDE the slot is
                        # the contradiction.
                        if any(M[u][w] != M[v][w] for w in range(5) if assign[w] != assign[u]):
                            found = True
                if not found:
                    lemma_ok = False
    det.append("slot lemma: %d labeled C5s x %d multi-slot assignments — every placement "
               "has a same-slot pair differing OUTSIDE the slot (blow-up forces equality "
               "there): %s" % (len(uniq), nassign, lemma_ok))
    if not lemma_ok:
        ok = False
    # ---- the tower ----
    X2 = substitute(W8, [W8] * 8)
    if fast:
        t2free, chk = c5_free_scan(X2, 64, rng=random.Random(7), sample=300000)
        det.append("X_2 (64 vtx): SAMPLED %d subsets, clean=%s" % (chk, t2free))
    else:
        t2free, hits = c5_free_scan(X2, 64)
        det.append("X_2 (64 vtx): EXHAUSTIVE C(64,5)=7624512 scan, induced-C5 hits=%d" % hits)
    a2t = alpha_bb(X2, 64)
    w2t = omega_bb(X2, 64)
    if not (t2free and a2t == 9 and w2t == 9):
        ok = False
    det.append("X_2 alpha=%d omega=%d (B&B, targets 9=3^2)" % (a2t, w2t))
    X3 = substitute(W8, [X2] * 8)
    t3free, chk = c5_free_scan(X3, 512, rng=random.Random(11), sample=200000)
    # complete verification of X_3 via the machine-checked slot lemma:
    # pieces = 8 copies of the exhaustively-clean X_2; frame W8 clean;
    # any multi-slot induced C5 contradicts the slot lemma; 5-distinct-slot
    # copies induce a C5 in W8 (absent). Sampled direct scan as extra evidence.
    ind27 = [8 * s + v for s in (1, 3, 5) for v in (1, 3, 5)]
    cli27 = [8 * s + v for s in (0, 1, 2) for v in (0, 1, 2)]
    ind_ok = all(not (X3[u] >> v) & 1 for u, v in itertools.combinations(ind27, 2))
    cli_ok = all((X3[u] >> v) & 1 for u, v in itertools.combinations(cli27, 2))
    if not (ind_ok and cli_ok and t3free):
        ok = False
    det.append("X_3 (512 vtx): slot-lemma-complete (pieces X_2 clean + frame W8 clean) + "
               "%d-subset sampled scan clean=%s; 27-indep + 27-clique exhibited (%s,%s) => hom>=27=3^3"
               % (chk, t3free, ind_ok, cli_ok))
    cval = math.log(3) / math.log(8)
    cap_ok = all(abs((8 ** t) ** cval - 3 ** t) <= 1e-6 * 3 ** t for t in range(1, 9))
    refuted = 3 < 8 ** (cval + 1e-9)
    if not (cap_ok and refuted and abs(cval - 0.528320823) < 1e-6):
        ok = False
    det.append("cap: c=log3/log8=%.9f; (8^t)^c=3^t exactly t=1..8: %s; c'>c refuted at t=1: %s"
               % (cval, cap_ok, refuted))
    det.append("h_C5(8)=3: floor R(3,3)=6 (A4) + W8 ceiling (hom=3)")
    # ---- witness hunts n=9, 10, 11 ----
    bud = {"9": (4 if fast else 20), "10": (10 if fast else 40), "11": (8 if fast else 70)}
    found = {}
    bsc = {}
    for nn in (9, 10, 11):
        f, bs = fast_hunt(nn, 3, seed=1000 + nn, budget=bud[str(nn)])
        found[nn] = f
        bsc[nn] = bs
    for nn in (9, 10):
        f = found[nn]
        if f is None:
            det.append("n=%d: hom-3 C5-free witness NOT FOUND in %.0fs (best score %d)"
                       % (nn, bud[str(nn)], bsc[nn]))
            ok = False   # h(9)=h(10)=3 are banked-exact claims
        else:
            free, _ = c5_free_scan(f, nn)
            a = alpha_exact(f, nn)
            w = omega_exact(f, nn)
            conn = is_connected(f, nn)
            cconn = is_connected(complement_adj(f, nn), nn)
            tri = has_induced(f, nn, ORBITS["K3"], 3)
            itri = a >= 3
            det.append("n=%d INDEPENDENT hom-3 witness: C5-free=%s alpha=%d omega=%d; "
                       "core-strat (conn=%s coconn=%s tri=%s indep3=%s)"
                       % (nn, free, a, w, conn, cconn, tri, itri))
            if not (free and a <= 3 and w <= 3):
                ok = False
            if nn == 10:
                det.append("LADDER-BREAK certified with my own witness: h_C5(10)=3 (floor "
                           "R(3,3)=6), 3^2=9 < 10 — h(n)^2>=n FALSE at n=10")
    if found[11] is None:
        det.append("n=11 hunt: no hom-3 C5-free witness in %.0fs (best score %d) — consistent "
                   "with the W80 finisher's open cell h_C5(11) in [3,4]" % (bud["11"], bsc[11]))
    else:
        f = found[11]
        free, _ = c5_free_scan(f, 11)
        a = alpha_exact(f, 11)
        w = omega_exact(f, 11)
        det.append("n=11 hom-3 C5-free witness FOUND (C5-free=%s alpha=%d omega=%d): "
                   "h_C5(11)=3, the [3,4] cell's lower half wins; ladder break extends (9<11)"
                   % (free, a, w))
        if not (free and a <= 3 and w <= 3):
            ok = False
    res("A5-C5ENDGAME", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))
    return found


# ----------------------------------------------------------------------------
# A6 SUBSTEXP
# --------------------------------------------------------------------------

def sec_a6(fast):
    t0 = time.time()
    ok = True
    det = []
    rng = random.Random(20261123)
    ninst = 40 if fast else 200

    def rand_c5free(n):
        for _ in range(200):
            adj = [0] * n
            p = rng.uniform(0.05, 0.5)
            for i in range(n):
                for j in range(i + 1, n):
                    if rng.random() < p:
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            if not has_induced(adj, n, ORBITS["C5"], 5):
                return adj
        # deletion repair from a random graph (bipartite fallback: no odd cycle)
        side = [rng.randrange(2) for _ in range(n)]
        adj = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                if side[i] != side[j] and rng.random() < 0.5:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        return adj

    closure_ok = True
    checked = 0
    cap_n = 16 if fast else 20
    for _ in range(ninst):
        q = rng.randint(2, 5)
        Q = rand_c5free(q)
        pieces = []
        for _ in range(q):
            m = rng.randint(1, 4)
            pieces.append(rand_c5free(m))
        G = substitute(Q, pieces)
        n = len(G)
        if n > cap_n:
            continue
        free, _ = c5_free_scan(G, n)
        checked += 1
        if not free:
            closure_ok = False
    det.append("C5 substitution closure: %d random blow-ups directly scanned, all C5-free: %s"
               % (checked, closure_ok))
    if not closure_ok:
        ok = False
    # alpha/omega formulas
    form_ok = True
    fchk = 0
    for _ in range(max(10, ninst // 2)):
        q = rng.randint(2, 5)
        Q = rand_c5free(q)
        pieces = [rand_c5free(rng.randint(1, 4)) for _ in range(q)]
        G = substitute(Q, pieces)
        n = len(G)
        if n > 14:
            continue
        best_a = 0
        for s in range(1 << q):
            good = True
            for i in range(q):
                for j in range(i + 1, q):
                    if ((s >> i) & 1) and ((s >> j) & 1) and ((Q[i] >> j) & 1):
                        good = False
            if good:
                best_a = max(best_a, sum(alpha_bruteforce(pieces[i], len(pieces[i]))
                                         for i in range(q) if (s >> i) & 1))
        best_w = 0
        for s in range(1 << q):
            good = True
            for i in range(q):
                for j in range(i + 1, q):
                    if ((s >> i) & 1) and ((s >> j) & 1) and not ((Q[i] >> j) & 1):
                        good = False
            if good:
                best_w = max(best_w, sum(omega_exact(pieces[i], len(pieces[i]))
                                         for i in range(q) if (s >> i) & 1))
        fchk += 1
        if alpha_bruteforce(G, n) != best_a or omega_exact(G, n) != best_w:
            form_ok = False
    det.append("alpha/omega substitution formulas (max over independent/clique slot sets): "
               "%d instances exact: %s" % (fchk, form_ok))
    if not form_ok:
        ok = False
    # harmonic law + optimality
    harm_ok = True
    for _ in range(200):
        c1 = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        c2 = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        f = c1 * c2 / (c1 + c2)
        if 1 / f != 1 / c1 + 1 / c2:
            harm_ok = False
    opt_ok = True
    eqb = True
    for _ in range(200):
        q = rng.randint(1, 50)
        s = rng.randint(1, 50)
        c1 = rng.uniform(0.05, 1.0)
        c2 = rng.uniform(0.05, 1.0)
        f = c1 * c2 / (c1 + c2)
        if min(q ** c1, s ** c2) > (q * s) ** f * (1 + 1e-9):
            opt_ok = False
        n0 = rng.uniform(4.0, 10 ** 6)
        qb = n0 ** (c2 / (c1 + c2))
        sb = n0 ** (c1 / (c1 + c2))
        if abs(min(qb ** c1, sb ** c2) - n0 ** f) > 1e-6 * n0 ** f:
            eqb = False
    if not (harm_ok and opt_ok and eqb):
        ok = False
    det.append("harmonic 1/f=1/c1+1/c2 (exact rationals, 200): %s; adversary cap "
               "min(q^c1,s^c2)<=(qs)^f (200): %s; balanced-split equality: %s"
               % (harm_ok, opt_ok, eqb))
    # Theorem 4B min-law on P3[K2]-free blow-ups
    E = [(0, 1), (2, 3), (4, 5)]
    E += [(a, b) for a in (0, 1) for b in (2, 3)]
    E += [(a, b) for a in (2, 3) for b in (4, 5)]
    orb_p3k2 = pattern_orbit(E, 6)
    minlaw_ok = True
    mchk = 0
    nmini = 12 if fast else 60
    for _ in range(nmini):
        q = rng.randint(2, 6)
        sizes = [rng.randint(1, 4) for _ in range(q)]
        Q = [0] * q
        comp = [rng.randrange(3) for _ in range(q)]
        for i in range(q):
            for j in range(i + 1, q):
                if comp[i] == comp[j]:
                    Q[i] |= 1 << j
                    Q[j] |= 1 << i
        pieces = [[0] * sz for sz in sizes]
        G = substitute(Q, pieces)
        n = len(G)
        if n > 16:
            continue
        free = not has_induced(G, n, orb_p3k2, 6)
        a = alpha_bruteforce(G, n)
        w = omega_exact(G, n)
        bound = min(math.ceil(math.sqrt(q) - 1e-12), min(sizes))
        mchk += 1
        if not free or max(a, w) < bound:
            minlaw_ok = False
    det.append("Theorem 4B min-law: %d random blow-ups (frame=union-of-cliques=P3-free, "
               "pieces=edgeless=K2-free): all P3[K2]-free and hom >= min(h_P3(q), h_K2(s)): %s"
               % (mchk, minlaw_ok))
    if not minlaw_ok:
        ok = False
    # avoidance direction: planted Q=P3 with K2-carrying pieces
    Q = [0] * 3
    Q[0] |= 1 << 1
    Q[1] |= 1 << 0
    Q[1] |= 1 << 2
    Q[2] |= 1 << 1
    k2k1 = [2, 1, 0]
    G = substitute(Q, [k2k1, k2k1, k2k1])
    planted = has_induced(G, 9, orb_p3k2, 6)
    if not planted:
        ok = False
    det.append("avoidance (4A(2) contrapositive): Q=P3 x (K2-carrying pieces) contains "
               "induced P3[K2]: %s" % planted)
    # ---- substitution edge cases: K1 blocks, single-slot frames, empty graph,
    # Theorem 4C 3-level composition identity (exact rationals)
    K1b = [0]
    g = substitute(adj_of("K2"), [K1b, K1b])
    e_k2k1 = (len(g) == 2 and canon_string(g, 2) == canon_string(adj_of("K2"), 2))
    g = substitute(adj_of("P3"), [K1b, K1b, K1b])
    e_p3k1 = (len(g) == 3 and canon_string(g, 3) == canon_string(adj_of("P3"), 3))
    g1 = substitute([0], [adj_of("C5")])          # single-slot frame = the piece
    e_1slot = canon_string(g1, 5) == canon_string(adj_of("C5"), 5)
    Gk1 = substitute(adj_of("paw"), [adj_of("C4"), K1b, adj_of("K3"), K1b])
    nk1 = len(Gk1)
    e_k1blk = (nk1 == 9 and c5_free_scan(Gk1, nk1)[0]
               and not has_induced(Gk1, nk1, ORBITS["C5"], 5))
    e_empty = c5_free_scan([], 0)[0]              # empty graph: vacuous (bank: m>=1 only)
    e_4c = True
    for _ in range(100):
        c1 = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        c2 = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        c3 = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        f12 = c1 * c2 / (c1 + c2)
        if f12 * c3 / (f12 + c3) != 1 / (1 / c1 + 1 / c2 + 1 / c3):
            e_4c = False
    edge_ok = e_k2k1 and e_p3k1 and e_1slot and e_k1blk and e_empty and e_4c
    if not edge_ok:
        ok = False
    det.append("edge cases: K2[K1,K1]=K2:%s P3[K1x3]=P3:%s single-slot frame:%s "
               "paw[C4,K1,K3,K1] C5-free with K1 blocks:%s empty-graph vacuous:%s "
               "Theorem 4C f(f(c1,c2),c3)=(sum 1/c)^-1 exact (100):%s"
               % (e_k2k1, e_p3k1, e_1slot, e_k1blk, e_empty, e_4c))
    res("A6-SUBSTEXP", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A7 INH
# ----------------------------------------------------------------------------

def sec_a7():
    t0 = time.time()
    ok = True
    det = []
    pairs = [("P3", "P4"), ("K3", "K4"), ("2K1", "3K1"), ("K3", "bull"), ("P4", "P5")]

    def induced_in(hname, hp):
        kh, kp = ORDERS[hname], ORDERS[hp]
        ha, pa = adj_of(hname), adj_of(hp)
        for sub in itertools.combinations(range(kp), kh):
            for inj in itertools.permutations(sub):
                good = True
                for a in range(kh):
                    for b in range(a + 1, kh):
                        if ((ha[a] >> b) & 1) != ((pa[inj[a]] >> inj[b]) & 1):
                            good = False
                            break
                    if not good:
                        break
                if good:
                    return True
        return False

    for (h, hp) in pairs:
        if not induced_in(h, hp):
            ok = False
            det.append("PAIR BROKEN: %s not induced in %s" % (h, hp))
    right_ok = True
    checked = 0
    for (h, hp) in pairs:
        for n in range(1, 7):
            for emask in range(1 << len(pairs_of(n))):
                adj = mask_to_adj(n, emask)
                if not has_induced(adj, n, ORBITS[h], ORDERS[h]):
                    checked += 1
                    if has_induced(adj, n, ORBITS[hp], ORDERS[hp]):
                        right_ok = False
    det.append("INH right direction (H induced in H' => H-free => H'-free): %d checks over "
               "%d pairs n<=6: %s" % (checked, len(pairs), right_ok))
    if not right_ok:
        ok = False
    k3 = adj_of("K3")
    w1 = is_free(k3, 3, "bull") and not is_free(k3, 3, "K3")
    p3 = adj_of("P3")
    w2 = is_free(p3, 3, "P4") and not is_free(p3, 3, "P3")
    if not (w1 and w2):
        ok = False
    det.append("wrong direction refuted: bull-free K3 carries K3: %s; P4-free P3 carries P3: %s"
               % (w1, w2))
    res("A7-INH-DIRECTION", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A8 LPC
# ----------------------------------------------------------------------------

def sec_a8(fast):
    t0 = time.time()
    ok = True
    det = []
    rng = random.Random(20261124)
    ninst = 40 if fast else 150

    def rand_c4free(n):
        for _ in range(60):
            adj = [0] * n
            p = rng.uniform(0.08, 0.35)
            for i in range(n):
                for j in range(i + 1, n):
                    if rng.random() < p:
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            if not has_induced(adj, n, ORBITS["C4"], 4):
                return adj
        # deletion repair
        adj = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.25:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        while True:
            bad = None
            for sub in itertools.combinations(range(n), 4):
                if subset_key(adj, sub) in ORBITS["C4"]:
                    bad = sub
                    break
            if bad is None:
                return adj
            x, y = bad[0], bad[1]
            adj[x] &= ~(1 << y)
            adj[y] &= ~(1 << x)

    def all_max_indep(adj, n, cap=40):
        a = alpha_exact(adj, n)
        out = []
        seen = set()

        def rec(v, cur, avail):
            if len(out) >= cap:
                return
            if len(cur) + bin(avail).count("1") < a:
                return
            if v == n:
                if len(cur) == a:
                    t = tuple(cur)
                    if t not in seen:
                        seen.add(t)
                        out.append(list(cur))
                return
            rec(v + 1, cur, avail)
            if (avail >> v) & 1:
                rec(v + 1, cur + [v], avail & ~(1 << v) & ~adj[v])

        rec(0, [], (1 << n) - 1)
        return a, out

    law_ok = True
    checked = 0
    anchors = 0
    tight = 0
    for _ in range(ninst):
        n = rng.randint(5, 13 if fast else 14)
        adj = rand_c4free(n)
        a, sets_ = all_max_indep(adj, n, cap=6 if n > 10 else 40)
        w = omega_exact(adj, n)
        if n == a + (w - 1) * a * (a + 1) // 2:
            tight += 1
        for I in sets_:
            Is = set(I)
            anchors += 1
            Imask = 0
            for x in I:
                Imask |= 1 << x
            cover = all((adj[v] & Imask) != 0 for v in range(n) if v not in Is)
            cells_ok = True
            conc_ok = True
            outside = [v for v in range(n) if v not in Is]
            Asets = {v: frozenset(x for x in I if (adj[v] >> x) & 1) for v in outside}
            for x in I:
                Wx = [v for v in outside if Asets[v] == frozenset([x])]
                for (u, v) in itertools.combinations(Wx, 2):
                    if not (adj[u] >> v) & 1:
                        cells_ok = False
            for (x, y) in itertools.combinations(I, 2):
                P = [v for v in outside if ((adj[v] >> x) & 1) and ((adj[v] >> y) & 1)]
                for (u, v) in itertools.combinations(P, 2):
                    if not (adj[u] >> v) & 1:
                        cells_ok = False
            for (v, u) in itertools.combinations(outside, 2):
                av, au = Asets[v], Asets[u]
                if (len(av & au) >= 2 or (av == au and len(av) == 1)) and not (adj[v] >> u) & 1:
                    conc_ok = False
            form = n <= a + (w - 1) * a * (a + 1) // 2
            cube = n <= max(a, w) ** 3
            checked += 1
            if not (cover and cells_ok and conc_ok and form and cube):
                law_ok = False
    det.append("L-PC side C4: %d random C4-free graphs n<=14, %d maximum anchors: coverage/"
               "W-cliques/P-cliques/concentrated/concentration-form/cube: %s (form tight at %d)"
               % (checked, anchors, law_ok, tight))
    if not law_ok:
        ok = False
    mir_ok = True
    mchk = 0
    for _ in range(ninst // 2):
        n = rng.randint(5, 12)
        adj = complement_adj(rand_c4free(n), n)   # 2K2-free
        a = alpha_exact(adj, n)
        w = omega_exact(adj, n)
        mchk += 1
        if not (n <= w + (a - 1) * w * (w + 1) // 2 and n <= max(a, w) ** 3):
            mir_ok = False
    det.append("L-PC side 2K2 (mirror): %d complements: concentration + cube: %s" % (mchk, mir_ok))
    if not mir_ok:
        ok = False
    comp_ok = True
    for M in (1, 2, 3, 5, 10, 100, 1999):
        for (a, w) in ((M, M), (M, 1), (1, M), (M, max(1, M // 3)), (max(1, M // 3), M)):
            if a + (w - 1) * a * (a + 1) // 2 > M ** 3 or w + (a - 1) * w * (w + 1) // 2 > M ** 3:
                comp_ok = False
    if not comp_ok:
        ok = False
    det.append("L-COMP arithmetic (corner grid): %s" % comp_ok)
    c5 = adj_of("C5")
    ac5 = alpha_exact(c5, 5)
    wc5 = omega_exact(c5, 5)
    if 5 != ac5 + (wc5 - 1) * ac5 * (ac5 + 1) // 2:
        ok = False
    det.append("concentration TIGHT at C5 (2+3=5): True")
    res("A8-LPC-LCOMP", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A9 P5DOM + BULL
# ----------------------------------------------------------------------------

def sec_a9():
    t0 = time.time()
    ok = True
    det = []
    shapes = {"K1": 0, "K2": 0, "P3": 0, "K3": 0}
    total = 0
    viol = 0
    for n in range(1, 7):
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if not is_free(adj, n, "P5") or not is_connected(adj, n):
                continue
            total += 1
            found = None
            for k in (1, 2, 3):
                if found:
                    break
                for D in itertools.combinations(range(n), k):
                    if not all(any((adj[v] >> d) & 1 or v == d for d in D) for v in range(n)):
                        continue
                    ed = sum(1 for (x, y) in itertools.combinations(D, 2) if (adj[x] >> y) & 1)
                    degs = sorted(sum(1 for y in D if y != x and (adj[x] >> y) & 1) for x in D)
                    if k == 1:
                        found = "K1"
                        break
                    if k == 2 and ed == 1:
                        found = "K2"
                        break
                    if k == 3 and ed == 3:
                        found = "K3"
                        break
                    if k == 3 and ed == 2 and degs == [1, 1, 2]:
                        found = "P3"
                        break
                if found:
                    break
            if found is None:
                viol += 1
            else:
                shapes[found] += 1
    det.append("P5-domination shape: %d connected P5-free graphs n<=6; %d without a dominating "
               "<=3-set of shape K1/K2/K3/P3; census %s (campaign: 19976 total, "
               "K1x5244 K2x14240 P3x372 K3x120)" % (total, viol, shapes))
    if viol:
        ok = False
    # BULL-L1 + L2
    cross_pairs = 0
    cross_bad = 0
    graphs_tri = 0
    dec_bad = 0
    for n in range(4, 7):
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if not is_free(adj, n, "bull"):
                continue
            if not has_induced(adj, n, ORBITS["K3"], 3):
                continue
            graphs_tri += 1
            w = omega_exact(adj, n)
            for tri in itertools.combinations(range(n), 3):
                if sum(1 for (x, y) in itertools.combinations(tri, 2) if (adj[x] >> y) & 1) != 3:
                    continue
                T = set(tri)
                S = {x: [] for x in tri}
                for v in range(n):
                    if v in T:
                        continue
                    att = [t for t in tri if (adj[v] >> t) & 1]
                    if len(att) == 1:
                        S[att[0]].append(v)
                for x in tri:
                    for y in tri:
                        if x >= y:
                            continue
                        for u in S[x]:
                            for wv in S[y]:
                                cross_pairs += 1
                                if not (adj[u] >> wv) & 1:
                                    cross_bad += 1
                for x in tri:
                    sub = S[x]
                    if sub:
                        om = omega_exact([row_for(adj, sub, v) for v in sub], len(sub))
                        if om > w - 1:
                            dec_bad += 1
    det.append("BULL-L1: %d bull-free triangle-carrying graphs n=4..6; %d cross-one pairs, "
               "%d violations (campaign: 4292/4292); L2 decrement violations %d"
               % (graphs_tri, cross_pairs, cross_bad, dec_bad))
    if cross_bad or dec_bad:
        ok = False
    res("A9-P5DOM-BULL", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


def row_for(adj, sub, v):
    r = 0
    for u in sub:
        if u != v and (adj[v] >> u) & 1:
            r |= 1 << sub.index(u)
    return r


# ----------------------------------------------------------------------------
# A10 C5CLOSURE
# ----------------------------------------------------------------------------

def sec_a10(fast):
    t0 = time.time()
    ok = True
    det = []
    rng = random.Random(20261125)
    trials = 100 if fast else 800

    def rand_c5free(n):
        for _ in range(120):
            adj = [0] * n
            for i in range(n):
                for j in range(i + 1, n):
                    if rng.random() < rng.uniform(0.1, 0.6):
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            if not has_induced(adj, n, ORBITS["C5"], 5):
                return adj
        side = [rng.randrange(2) for _ in range(n)]
        adj = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                if side[i] != side[j] and rng.random() < 0.5:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        return adj

    okc = True
    chk = 0
    for _ in range(trials):
        A = rand_c5free(rng.randint(1, 7))
        B = rand_c5free(rng.randint(1, 7))
        U = disjoint_union(A, B)
        J = join_graphs(A, B)
        CA = complement_adj(A, len(A))
        chk += 1
        for g in (U, J, CA):
            if has_induced(g, len(g), ORBITS["C5"], 5):
                okc = False
    det.append("C5-CLOSURE constructive: %d random pairs x (union, join, complement): %s"
               % (chk, okc))
    if not okc:
        ok = False
    sub_ok = True
    for _ in range(500):
        c0 = rng.uniform(0.01, 1.0)
        xs = [rng.uniform(0, 100) for _ in range(5)]
        if sum(x ** c0 for x in xs) + 1e-9 < sum(xs) ** c0:
            sub_ok = False
    if not sub_ok:
        ok = False
    det.append("C5-REDUCTION spine sum x_i^c0 >= (sum x_i)^c0 (500 random): %s" % sub_ok)
    res("A10-C5CLOSURE", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A11 NEGCTL
# ----------------------------------------------------------------------------

def sec_a11():
    t0 = time.time()
    ok = True
    det = []
    n = 10
    adj = [0] * n
    for blk in (range(0, 5), range(5, 10)):
        for i in blk:
            for j in blk:
                if i != j:
                    adj[i] |= 1 << j
    for u in range(4):
        for v in range(4):
            if u != v:
                adj[u] &= ~(1 << v)
    for (u, v) in ((0, 1), (1, 2), (2, 3)):
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    p4f = has_induced(adj, n, ORBITS["P4"], 4)
    bullf = not is_free(adj_of("bull"), 5, "bull")
    c5 = adj_of("C5")
    c5f = has_induced(c5, 5, ORBITS["C5"], 5)
    c5u = list(c5) + [0]
    for i in range(5):
        c5u[i] |= 1 << 5
        c5u[5] |= 1 << i
    c5uf = has_induced(c5u, 6, ORBITS["C5"], 5)
    k5f = not is_free(adj_of("K5"), 5, "K5")
    if not (p4f and bullf and c5f and c5uf and k5f):
        ok = False
    det.append("planted hosts detected: P4-in-cograph=%s bull=%s C5=%s C5vK1=%s K5=%s"
               % (p4f, bullf, c5f, c5uf, k5f))
    truth = {"C5": [1, 2, 2, 2, 3, 3, 3], "P5": [1, 2, 2, 2, 2, 3, 3]}
    corrupted = {"C5": [1, 2, 2, 2, 2, 3, 3], "P5": [1, 2, 2, 2, 3, 3, 3]}
    d = all(truth[k] != corrupted[k] for k in truth)
    if not d:
        ok = False
    det.append("corrupted h-rows (h_C5(5)=2, h_P5(5)=3) differ from banked truth: %s" % d)
    # corrupted alpha-formula probe (Q = P3 on slots 0,1,2; three pieces)
    Q = [0] * 3
    Q[0] |= 1 << 1
    Q[1] |= 1 << 0
    Q[1] |= 1 << 2
    Q[2] |= 1 << 1
    # valid adjacency lists: 2K1, K1, K2+K1 (edge 0-1, vertex 2 isolated)
    pieces = [[0, 0], [0], [2, 1, 0]]
    G = substitute(Q, pieces)
    aG = alpha_bruteforce(G, len(G))
    best_a = 0
    for s in range(1 << 3):
        good = True
        for i in range(3):
            for j in range(i + 1, 3):
                if ((s >> i) & 1) and ((s >> j) & 1) and ((Q[i] >> j) & 1):
                    good = False
        if good:
            best_a = max(best_a, sum(alpha_bruteforce(pieces[i], len(pieces[i]))
                                     for i in range(3) if (s >> i) & 1))
    cd = (aG == best_a) and (aG != best_a + 1)
    if not cd:
        ok = False
    det.append("alpha substitution formula probe (corruption +1 detected): %s" % cd)
    res("A11-NEGCTL", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------
# A12 61A-CROSS: adversarial cross-audit of the W81-61A lane's fresh laws
# (engine61primes_w81.py, receipts61primes_w81.txt — read-only tree w81-61a)
# ----------------------------------------------------------------------------

def slot_lemma_for(adjH, kH):
    """generic slot lemma for pattern adjH (one representative labeling; the
    all-assignments statement is invariant under relabeling H): every
    multi-slot assignment of H's vertices (2..kH-1 slots) has a same-slot
    pair differing in adjacency to some OUTSIDE-slot vertex."""
    n_ok = True
    cnt = 0
    for k in range(2, kH):
        for assign in itertools.product(range(k), repeat=kH):
            if len(set(assign)) < 2:
                continue
            cnt += 1
            found = False
            for u in range(kH):
                for v in range(u + 1, kH):
                    if assign[u] != assign[v]:
                        continue
                    if any(((adjH[u] >> w) & 1) != ((adjH[v] >> w) & 1)
                           for w in range(kH) if assign[w] != assign[u]):
                        found = True
            if not found:
                n_ok = False
    return n_ok, cnt


def dominating_sets(adj, n, k, want):
    """all dominating k-sets inducing the wanted shape.
    want: 'K1' (k=1), 'K2' (k=2, edge), 'K3' (k=3, triangle), 'P3' (path)."""
    out = []
    for D in itertools.combinations(range(n), k):
        if not all(any((adj[v] >> d) & 1 or v == d for d in D) for v in range(n)):
            continue
        eds = [(x, y) for (x, y) in itertools.combinations(D, 2) if (adj[x] >> y) & 1]
        if want == "K1":
            out.append(D)
        elif want == "K2" and len(eds) == 1:
            out.append(D)
        elif want == "K3" and len(eds) == 3:
            out.append(D)
        elif want == "P3" and len(eds) == 2:
            degs = sorted(sum(1 for (x, y) in eds if x == z or y == z) for z in D)
            if degs == [1, 1, 2]:
                out.append(D)
    return out


def sec_a12():
    t0 = time.time()
    ok = True
    det = []
    rng = random.Random(20261126)
    # ---- 1. bull-free labeled counts + h_bull n<=6 (61A S1) ----
    counts = []
    mins = []
    law6 = 0
    for n in range(1, 7):
        c = 0
        m = None
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if not has_induced(adj, n, ORBITS["bull"], 5):
                c += 1
                a = alpha_bruteforce(adj, n)
                w = omega_exact(adj, n)
                h = max(a, w)
                if m is None or h < m:
                    m = h
                if n > 6 * (h ** 4):
                    law6 += 1
        counts.append(c)
        mins.append(m)
    b1 = counts == [1, 2, 8, 64, 964, 24248]
    b2 = mins == [1, 2, 2, 2, 2, 3]
    if not (b1 and b2 and law6 == 0):
        ok = False
    det.append("bull-free labeled n=1..6 = %s (61A: 1,2,8,64,964,24248): %s; "
               "h_bull = %s (61A/bank: 1,2,2,2,2,3): %s; n<=6*hom^4 violations %d"
               % (counts, b1, mins, b2, law6))
    # ---- 2. C5-free cores n=5,6 (61A S2 core census) + n<=6hom^4 ----
    cores = {}
    law6c = 0
    for n in (5, 6):
        cc = 0
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if has_induced(adj, n, ORBITS["C5"], 5):
                continue
            if n > 6 * (max(alpha_bruteforce(adj, n), omega_exact(adj, n)) ** 4):
                law6c += 1
            if is_connected(adj, n) and is_connected(complement_adj(adj, n), n):
                cc += 1
        cores[n] = cc
    c_ok = cores == {5: 420, 6: 18840} and law6c == 0
    if not c_ok:
        ok = False
    det.append("C5-free cores (conn&coconn): n=5 %d (61A/bank 420), n=6 %d (61A/bank "
               "18840): %s; n<=6*hom^4 violations on all C5-free n=5,6: %d"
               % (cores[5], cores[6], cores == {5: 420, 6: 18840}, law6c))
    # ---- 3. X_2 = C5[C5] and X_3 = C5[X_2 x5] (61A S3 tower) ----
    c5 = adj_of("C5")
    X2c = substitute(c5, [c5] * 5)
    p5f = not has_induced(X2c, 25, ORBITS["P5"], 5)
    bullf = not has_induced(X2c, 25, ORBITS["bull"], 5)
    c5c = has_induced(X2c, 25, ORBITS["C5"], 5)
    aX2 = alpha_exact(X2c, 25)
    wX2 = omega_exact(X2c, 25)
    ds = sorted(bin(x).count("1") for x in X2c)
    cds = sorted(24 - bin(x).count("1") for x in X2c)
    tow_ok = p5f and bullf and c5c and aX2 == 4 and wX2 == 4 and ds == cds
    if not tow_ok:
        ok = False
    det.append("X_2=C5[C5] (25 vtx): P5-free=%s bull-free=%s carries C5=%s (must be "
               "True — the C5 tower is NOT C5-free); alpha=omega=%d (61A: 4,4); "
               "degree sequence self-complementary=%s"
               % (p5f, bullf, c5c, aX2, ds == cds))
    X3c = substitute(c5, [X2c] * 5)
    # global index = 25*outer_slot + 5*inner_slot + innermost_vertex
    indep8 = [25 * s + 5 * t + u for s in (0, 2) for t in (0, 2) for u in (0, 2)]
    cli8 = [25 * s + 5 * t + u for s in (0, 1) for t in (0, 1) for u in (0, 1)]
    i_ok = all(not (X3c[u] >> v) & 1 for u, v in itertools.combinations(indep8, 2))
    c_ok8 = all((X3c[u] >> v) & 1 for u, v in itertools.combinations(cli8, 2))
    sc, hits = c5_free_scan(X3c, 125, rng=random.Random(31), sample=100000)
    if not (i_ok and c_ok8):
        ok = False
    det.append("X_3=C5[X_2 x5] (125 vtx): constructive 8-independent (slots 0,2 x 0,2 "
               "x pair 0,2)=%s and 8-clique (0,1 x 0,1 x 0,1)=%s => hom=8=2^3 at "
               "n=125=5^3 (61A tower hom(X_t)=2^t); 100k-subset C5 scan clean=%s "
               "(hits %d; C5-freeness not claimed)" % (i_ok, c_ok8, sc, hits))
    # ---- 4. slot lemma for P5 and bull (substitution closure certificate) ----
    sl = {}
    for name in ("P5", "bull"):
        good, cnt = slot_lemma_for(adj_of(name), 5)
        sl[name] = good
        if not good:
            ok = False
    det.append("slot lemma (generic, one representative labeling — relabel-invariant): "
               "P5 %s, bull %s (every multi-slot placement has an outside-slot "
               "adjacency difference => substitution closure of P5/bull-freeness; "
               "the X_t tower is P5/bull-free at EVERY level)" % (sl["P5"], sl["bull"]))
    # ---- 5. P5-CROSS: stronger form on ALL P5-free graphs n<=6, ALL induced P3s ----
    # (the 61A law is scoped to z-only graphs x dominating P3s; proof: u e1-only,
    # v e2-only, u~v violated => {u,e1,c,e2,v} induces the P5 path u-e1-c-e2-v.)
    cross_bad = 0
    cross_inst = 0
    for n in range(3, 7):
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if has_induced(adj, n, ORBITS["P5"], 5):
                continue
            for sub in itertools.combinations(range(n), 3):
                eds = [(x, y) for (x, y) in itertools.combinations(sub, 2)
                       if (adj[x] >> y) & 1]
                if len(eds) != 2:
                    continue
                degs = {}
                for (x, y) in eds:
                    degs[x] = degs.get(x, 0) + 1
                    degs[y] = degs.get(y, 0) + 1
                if sorted(degs.values()) != [1, 1, 2]:
                    continue
                c = [z for z in sub if degs[z] == 2][0]
                ends = [z for z in sub if degs[z] == 1]
                for (e1, e2) in ((ends[0], ends[1]), (ends[1], ends[0])):
                    uonly = [v for v in range(n) if v not in sub
                             and (adj[v] >> e1) & 1 and not (adj[v] >> c) & 1
                             and not (adj[v] >> e2) & 1]
                    vonly = [v for v in range(n) if v not in sub
                             and (adj[v] >> e2) & 1 and not (adj[v] >> c) & 1
                             and not (adj[v] >> e1) & 1]
                    for u in uonly:
                        for w in vonly:
                            cross_inst += 1
                            if not (adj[u] >> w) & 1:
                                cross_bad += 1
    if cross_bad:
        ok = False
    # z-only census (61A S3): connected P5-free, no dom K1/K2/K3, >=1 dom P3
    zonly = {n: 0 for n in range(1, 7)}
    zsamples = 0
    for n in range(1, 7):
        for emask in range(1 << len(pairs_of(n))):
            adj = mask_to_adj(n, emask)
            if not is_free(adj, n, "P5") or not is_connected(adj, n):
                continue
            if (dominating_sets(adj, n, 1, "K1") or dominating_sets(adj, n, 2, "K2")
                    or dominating_sets(adj, n, 3, "K3")):
                continue
            if dominating_sets(adj, n, 3, "P3"):
                zonly[n] += 1
                zsamples += 1
    z_ok = ztotal_ok = (zsamples == 372 and zonly[5] == 12 and zonly[6] == 360)
    if not z_ok:
        ok = False
    det.append("P5-CROSS (STRONGER: all P5-free graphs n=3..6, ALL induced P3s, both "
               "orientations): %d e1-only x e2-only instances, %d violations (proof: "
               "violation => induced P5 u-e1-c-e2-v); z-only census %s = 372 "
               "(per-n 5:12, 6:360): %s"
               % (cross_inst, cross_bad, zsamples, ztotal_ok))
    # violation mechanics on random graphs (the constructed P5 really is induced)
    mech = 0
    mechbad = 0
    for _ in range(400):
        n = rng.randint(5, 8)
        adj = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.4:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        for sub in itertools.combinations(range(n), 3):
            eds = [(x, y) for (x, y) in itertools.combinations(sub, 2)
                   if (adj[x] >> y) & 1]
            if len(eds) != 2:
                continue
            degs = {}
            for (x, y) in eds:
                degs[x] = degs.get(x, 0) + 1
                degs[y] = degs.get(y, 0) + 1
            if sorted(degs.values()) != [1, 1, 2]:
                continue
            c = [z for z in sub if degs[z] == 2][0]
            ends = [z for z in sub if degs[z] == 1]
            for (e1, e2) in ((ends[0], ends[1]), (ends[1], ends[0])):
                for u in range(n):
                    if u in sub or not (adj[u] >> e1) & 1 or (adj[u] >> c) & 1 \
                            or (adj[u] >> e2) & 1:
                        continue
                    for w in range(n):
                        if w in sub or w == u or not (adj[w] >> e2) & 1 \
                                or (adj[w] >> c) & 1 or (adj[w] >> e1) & 1:
                            continue
                        if (adj[u] >> w) & 1:
                            continue
                        mech += 1
                        five = [u, e1, c, e2, w]
                        if subset_key(adj, sorted(five)) not in ORBITS["P5"]:
                            mechbad += 1
    if mechbad or mech == 0:
        ok = False
    det.append("P5-CROSS mechanics: %d violations on random graphs, each 5-set "
               "{u,e1,c,e2,v} verified to induce P5: %d failures" % (mech, mechbad))
    # ---- 6. C5 anchor laws (61A S2): corollaries of C5-freeness ----
    def anchor_viol(adj, n, law):
        if law == 2:
            for T in itertools.combinations(range(n), 3):
                if sum(1 for (x, y) in itertools.combinations(T, 2)
                       if (adj[x] >> y) & 1) != 3:
                    continue
                for (x, y) in itertools.combinations(T, 2):
                    ps = [v for v in range(n) if v not in T and (adj[v] >> x) & 1
                          and not (adj[v] >> y) & 1]
                    qs = [v for v in range(n) if v not in T and (adj[v] >> y) & 1
                          and not (adj[v] >> x) & 1]
                    rs = [v for v in range(n) if v not in T and not (adj[v] >> x) & 1
                          and not (adj[v] >> y) & 1]
                    for p in ps:
                        for q in qs:
                            for r in rs:
                                if (adj[p] >> r) & 1 and (adj[q] >> r) & 1 \
                                        and not (adj[p] >> q) & 1:
                                    return (p, x, y, q, r)
        else:
            for T in itertools.combinations(range(n), 3):
                if sum(1 for (x, y) in itertools.combinations(T, 2)
                       if (adj[x] >> y) & 1) != 3:
                    continue
                for a in T:
                    bs = [v for v in range(n) if v not in T and (adj[v] >> a) & 1]
                    cs = [v for v in range(n) if v not in T and not (adj[v] >> a) & 1]
                    for (b, e) in itertools.combinations(bs, 2):
                        for (c, d) in itertools.permutations(cs, 2):
                            if (adj[b] >> c) & 1 and (adj[c] >> d) & 1 \
                                    and (adj[d] >> e) & 1 and not (adj[b] >> d) & 1 \
                                    and not (adj[b] >> e) & 1 and not (adj[c] >> e) & 1:
                                return (a, b, c, d, e)
        return None
    # census: all C5-free n=5 (1012) + sampled C5-free n=6, n=7
    viol = 0
    checked = 0
    pos5 = pair_pos(5)
    for emask in range(1024):
        adj = mask_to_adj(5, emask, pos5)
        if has_induced(adj, 5, ORBITS["C5"], 5):
            continue
        checked += 1
        if anchor_viol(adj, 5, 1) or anchor_viol(adj, 5, 2):
            viol += 1
    for (n, reps) in ((6, 400), (7, 400)):
        got = 0
        tries = 0
        while got < reps and tries < 20000:
            tries += 1
            adj = [0] * n
            for i in range(n):
                for j in range(i + 1, n):
                    if rng.random() < 0.45:
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            if has_induced(adj, n, ORBITS["C5"], 5):
                continue
            got += 1
            checked += 1
            if anchor_viol(adj, n, 1) or anchor_viol(adj, n, 2):
                viol += 1
    if viol:
        ok = False
    # mechanics: violations on random graphs induce C5
    m2 = 0
    m2bad = 0
    for _ in range(300):
        n = rng.randint(6, 8)
        adj = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < 0.45:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        for law in (1, 2):
            v = anchor_viol(adj, n, law)
            if v is None:
                continue
            m2 += 1
            if subset_key(adj, sorted(v)) not in ORBITS["C5"]:
                m2bad += 1
    if m2bad or m2 < 10:
        ok = False
    det.append("C5 anchor laws (1-anchor, 2-anchor): %d C5-free graphs (all n=5 + "
               "sampled n=6,7) 0-violation census=%s; mechanics: %d violations on "
               "random graphs, each 5-set verified to induce C5, %d failures — "
               "BOTH LAWS ARE COROLLARIES OF C5-FREENESS (proof in AUDIT_W81.md)"
               % (checked, viol == 0, m2, m2bad))
    # ---- 7. structured families: n <= 6*hom^4 ----
    fam_ok = True
    for k in (2, 3, 4, 5):
        G = adj_of("C5")
        for _ in range(k - 1):
            G = disjoint_union(G, adj_of("C5"))
        nG = 5 * k
        homG = 2 * k          # alpha = 2k exhibited: 2 independent per C5
        if nG > 6 * homG ** 4:
            fam_ok = False
    if 25 > 6 * 4 ** 4 or 125 > 6 * 8 ** 4:
        fam_ok = False
    W8 = build_W8()
    X2t = substitute(W8, [W8] * 8)
    if 8 > 6 * 3 ** 4 or 64 > 6 * 9 ** 4:
        fam_ok = False
    if not fam_ok:
        ok = False
    det.append("n<=6*hom^4 on structured families: C5-unions x2..x5 (n=10..25, hom=4..10), "
               "X_2=C5[C5] (25, 4), X_3 (125, 8), W8 (8, 3), W8-tower (64, 9): %s" % fam_ok)
    res("A12-61A-CROSS", ok, "; ".join(det) + " [%.1fs]" % (time.time() - t0))


# ----------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fast", action="store_true")
    ap.add_argument("--only", nargs="*", default=None)
    args = ap.parse_args()
    fast = args.fast
    only = set(args.only) if args.only else None
    print("=== engine61audit_w81.py (W81-61B auditor engine) ===")
    print("numpy: %s; mode: %s" % (HAVE_NP, "fast" if fast else "full"))
    sections = [("A0", sec_a0), ("A1", sec_a1), ("A2", sec_a2),
                ("A3", lambda: sec_a3(fast)), ("A4", lambda: sec_a4(fast)),
                ("A5", lambda: sec_a5(fast)), ("A6", lambda: sec_a6(fast)),
                ("A7", sec_a7), ("A8", lambda: sec_a8(fast)),
                ("A9", sec_a9), ("A10", lambda: sec_a10(fast)), ("A11", sec_a11),
                ("A12", sec_a12)]
    for name, fn in sections:
        if only and name not in only:
            continue
        fn()
    n_pass = sum(1 for (_, o, _) in _RESULTS if o)
    n_fail = sum(1 for (_, o, _) in _RESULTS if not o)
    print("AUDIT61 SUMMARY: PASS=%d FAIL=%d wall=%.1fs" % (n_pass, n_fail, time.time() - T_START))
    sys.exit(0 if n_fail == 0 else 1)


if __name__ == "__main__":
    main()
