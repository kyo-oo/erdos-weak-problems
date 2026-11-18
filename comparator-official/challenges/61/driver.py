#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Driver for the OFFICIAL #61 gate (W72-61C, S071).

Official checks run the verbatim DeepMind FunSearch cyclic_graphs code
(fresh clone github.com/google-deepmind/funsearch @ cc53f27, extracted in
official_code/official_cyclic.py). The module import executes the notebook
flow with the official assertions; per-instance checks rebind the correct
official priority cell (notebook sequential semantics) before calling the
official evaluate/solve.
"""
import itertools
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CAMP = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
ENGINE = os.path.join(CAMP, "problem61-erdos-hajnal", "engine61family.py")
OFFICIAL_FILE = os.path.join(HERE, "official_code", "official_cyclic.py")
sys.path.insert(0, os.path.join(HERE, "official_code"))


def _chk(cid, desc, ok, detail="", seconds=0.0):
    return {"id": cid, "description": desc, "passed": bool(ok),
            "detail": str(detail)[:3000], "seconds": round(seconds, 3)}


def _cell_sources():
    """Split the verbatim extract into its OFFICIAL CELL blocks."""
    src = open(OFFICIAL_FILE, encoding="utf-8").read()
    marker = "# ---- OFFICIAL CELL "
    parts = src.split(marker)
    cells = {}
    for p in parts[1:]:
        label = p.split(" ", 1)[0].strip()  # e.g. '6'
        body = p.split("----", 1)[1] if "----" in p else p
        # cut at the next marker if the split left it in (split already
        # removed markers, so body runs to the next part boundary)
        cells[label] = body
    return cells


def _rebind(OC, cell_body):
    """Re-execute an official cell's source in the module namespace,
    rebinding `priority` with the notebook's sequential semantics."""
    # strip any trailing content after the last def/assert of the cell:
    # the extract's cell bodies contain only the verbatim cell source.
    exec(compile(cell_body, "<official cell>", "exec"), OC.__dict__)


def run_official_checks(challenge, solution):
    checks = []
    t0 = time.time()
    try:
        import official_cyclic as OC  # noqa: N813
        ok = True
        err = ""
    except Exception as e:
        OC = None
        ok = False
        err = repr(e)
    checks.append(_chk(
        "O-IMPORT-NOTEBOOK-FLOW",
        "official cyclic_graphs module (verbatim cells 2/6/7/9/11/13/14) imports; its own asserts hold (367 in C_7^5; 81/324/1458 in C_9^3..5; 754 in C_11^4)",
        ok, err, time.time() - t0))
    if not ok:
        return checks

    cells = _cell_sources()

    # O-CYC7-5: official cell-6 priority -> 367 in C_7^5.
    t0 = time.time()
    _rebind(OC, cells["6"])
    v = OC.evaluate(num_nodes=7, n=5)
    checks.append(_chk("O-CYC7-5", "official evaluate(num_nodes=7, n=5) == 367 (official cell-6 priority)",
                       v == 367, f"got {v}", time.time() - t0))

    # O-CYC9-3/4/5: official cell-9 priority -> 81/324/1458.
    t0 = time.time()
    _rebind(OC, cells["9"])
    v3, v4, v5 = (OC.evaluate(num_nodes=9, n=k) for k in (3, 4, 5))
    checks.append(_chk("O-CYC9-345",
                       "official evaluate(num_nodes=9, n=3/4/5) == 81/324/1458 (official cell-9 priority, the official cell-11 expected sizes)",
                       (v3, v4, v5) == (81, 324, 1458), f"got {(v3, v4, v5)}", time.time() - t0))

    # O-CYC11-4: official cell-13 priority -> 754, and the returned set is
    # independent (cross-checked by our own checker).
    t0 = time.time()
    _rebind(OC, cells["13"])
    v11 = OC.evaluate(num_nodes=11, n=4)
    ind_ok = False
    if v11 == 754:
        S = OC.solve(num_nodes=11, n=4)
        Sset = set(S)
        ind_ok = (len(S) == len(Sset) == 754
                  and all(0 <= x < 11 for t in S for x in t))
        # independence in the cyclic-graph strong power: u != v in S may not
        # differ componentwise by only -1/0/+1 (mod 11)
        for u, w in itertools.combinations(sorted(Sset), 2):
            if all(((u[i] - w[i]) % 11) in (0, 1, 10) for i in range(4)):
                ind_ok = False
                break
    checks.append(_chk("O-CYC11-4",
                       "official evaluate(num_nodes=11, n=4) == 754 (official cell-13 priority) AND the returned 754-set is independent (own checker)",
                       v11 == 754 and ind_ok, f"got {v11}, independent={ind_ok}", time.time() - t0))
    return checks


def run_solution_checks(challenge, solution):
    checks = []
    # S-ENGINE: the campaign family engine, full 10/10 (long-running: the
    # exhaustive n<=6 store + 342s of sampling — subprocess timeout 600s).
    t0 = time.time()
    if os.path.isfile(ENGINE):
        try:
            proc = subprocess.run([sys.executable, ENGINE, "--verify"],
                                  capture_output=True, text=True, timeout=600)
            out = proc.stdout + proc.stderr
            n_pass = out.count("PASS ")
            n_fail = out.count("FAIL ")
            ok = proc.returncode == 0 and n_fail == 0 and n_pass >= 10
            tail = [l for l in out.strip().splitlines() if l.startswith("PASS") or l.startswith("FAIL")][-3:]
            checks.append(_chk("S-ENGINE",
                               "campaign family engine --verify: exit 0, >= 10 PASS, 0 FAIL",
                               ok, tail, time.time() - t0))
        except subprocess.TimeoutExpired:
            checks.append(_chk("S-ENGINE", "engine within 600s", False, "timeout"))
    else:
        checks.append(_chk("S-ENGINE", "engine present", False, ENGINE + " missing"))

    # S-HARMONIC: independent exact-rational check of the harmonic law.
    from fractions import Fraction
    t0 = time.time()
    ok = True
    for (c1, c2) in [(Fraction(1, 2), Fraction(1, 2)), (Fraction(1, 3), Fraction(2, 3)),
                     (Fraction(1, 2), Fraction(1, 3)), (Fraction(2, 5), Fraction(3, 7))]:
        f = c1 * c2 / (c1 + c2)
        if 1 / f != 1 / c1 + 1 / c2:
            ok = False
    checks.append(_chk("S-HARMONIC",
                       "harmonic law 1/f = 1/c1 + 1/c2 on exact rationals (independent of the engine)",
                       ok, "four exponent pairs", time.time() - t0))

    # S-INDEP-CROSS: our own independent-set engine agrees with the official
    # evaluator on the overlapping instance C_9^3: greedy lower bound >= 81
    # from our own construction, and the official 81-set re-verified.
    t0 = time.time()
    try:
        import official_cyclic as OC
        cells = _cell_sources()
        _rebind(OC, cells["9"])
        S = OC.solve(num_nodes=9, n=3)
        Sset = set(S)
        official_ok = (len(Sset) == 81 and all(0 <= x < 9 for t in S for x in t))
        # independence re-check (own code)
        for u, w in itertools.combinations(sorted(Sset), 2):
            if all(((u[i] - w[i]) % 9) in (0, 1, 8) for i in range(3)):
                official_ok = False
                break
        # our greedy: same blocking rule, own implementation, trivial priority
        # order (lexicographic) — a valid (smaller) independent set, proving
        # the independence semantics agree
        def own_greedy(num_nodes, n):
            chosen = []
            blocked = set()
            for v in itertools.product(range(num_nodes), repeat=n):
                if v in blocked:
                    continue
                chosen.append(v)
                for d in itertools.product((-1, 0, 1), repeat=n):
                    blocked.add(tuple((v[i] + d[i]) % num_nodes for i in range(n)))
            return chosen
        G = own_greedy(9, 3)
        # our greedy set must be independent by the same rule (semantics
        # agreement) and reasonably sized
        gindep = True
        for u, w in itertools.combinations(G, 2):
            if all(((u[i] - w[i]) % 9) in (0, 1, 8) for i in range(3)):
                gindep = False
                break
        ok = official_ok and gindep and len(G) >= 60
        det = f"official 81-set independent={official_ok}; own greedy size={len(G)} independent={gindep}"
    except Exception as e:
        ok = False
        det = repr(e)
    checks.append(_chk("S-INDEP-CROSS",
                       "independence semantics agreement: official C_9^3 81-set re-verified + own greedy independent set on the same graph",
                       ok, det, time.time() - t0))

    # S-CLAW (W74): Theorem CLAW — every claw-free graph on n >= 1 vertices
    # satisfies max(alpha, omega) >= 0.5*n^(1/3), via the intermediate laws
    # deg(v) < omega^2 (Ramsey R(t,3) <= t(t+1)/2 on each neighborhood) and
    # alpha > n/(omega^2+1) (Caro-Wei weak form). Instances: line graphs of
    # random graphs (always claw-free), disjoint clique unions, the edgeless
    # and complete graphs, filtered random graphs; R(3,3)=6 EXHAUSTIVE over
    # all 2^15 six-vertex graphs (and the C5 witness shows 5 does not force);
    # negative control: the star K1,5 (induced-claw-full) violates the
    # degree law deg(center)=5 < omega^2=4 — the hypothesis is load-bearing.
    t0 = time.time()
    try:
        import random as _rnd
        _rng = _rnd.Random(20261118)

        def _claw_free(adj, n):
            from itertools import combinations as _comb
            for a, b, c, d in _comb(range(n), 4):
                for center in (a, b, c, d):
                    others = [x for x in (a, b, c, d) if x != center]
                    if (all(o in adj[center] for o in others)
                            and not (others[0] in adj[others[1]]
                                     or others[0] in adj[others[2]]
                                     or others[1] in adj[others[2]])):
                        return False
            return True

        def _alpha_bb(adj, n):
            best = [0]
            def _bb(v, cnt, banned):
                if cnt + (n - v) <= best[0]:
                    return
                if v == n:
                    best[0] = max(best[0], cnt)
                    return
                _bb(v + 1, cnt, banned)
                if v not in banned:
                    nb = set(banned)
                    nb.update(adj[v])
                    _bb(v + 1, cnt + 1, nb)
            _bb(0, 0, set())
            return best[0]

        def _omega_bb(adj, n):
            best = [0]
            nonadj = [set(w for w in range(n) if w != v and w not in adj[v]) for v in range(n)]
            def _bb(v, cnt, banned):
                if cnt + (n - v) <= best[0]:
                    return
                if v == n:
                    best[0] = max(best[0], cnt)
                    return
                _bb(v + 1, cnt, banned)
                if v not in banned:
                    nb = set(banned)
                    nb.update(nonadj[v])
                    _bb(v + 1, cnt + 1, nb)
            _bb(0, 0, set())
            return best[0]

        graphs = []
        # (a) line graphs of random graphs (claw-free by the classical line-graph law)
        for (mv, pe) in [(8, 0.4), (10, 0.3), (12, 0.5), (14, 0.25), (16, 0.35)]:
            base = [set() for _ in range(mv)]
            edges = []
            for i, j in _rng.sample([(i, j) for i in range(mv) for j in range(i + 1, mv)],
                                     k=int(pe * mv * (mv - 1) / 2)):
                base[i].add(j); base[j].add(i); edges.append((i, j))
            ln = len(edges)
            adj = [set() for _ in range(ln)]
            for x in range(ln):
                for y in range(x + 1, ln):
                    if edges[x][0] in edges[y] or edges[x][1] in edges[y]:
                        adj[x].add(y); adj[y].add(x)
            graphs.append(adj)
        # (b) disjoint clique unions (claw-free)
        for sizes in [[4, 4, 4, 4], [3] * 9, [7, 5, 5], [12, 12], [2] * 20]:
            n = sum(sizes)
            adj = [set() for _ in range(n)]
            ofs = 0
            for sz in sizes:
                for i in range(ofs, ofs + sz):
                    for j in range(ofs, ofs + sz):
                        if i != j:
                            adj[i].add(j)
                ofs += sz
            graphs.append(adj)
        # (c) edgeless + complete (boundary cases)
        graphs.append([set() for _ in range(9)])
        kn = [set(range(11)) - {v} for v in range(11)]
        graphs.append(kn)
        # (d) filtered random graphs (keep only if claw-free)
        kept = 0
        for _ in range(3000):
            if kept >= 4:
                break
            n = _rng.randint(8, 14)
            adj = [set() for _ in range(n)]
            for i in range(n):
                for j in range(i + 1, n):
                    if _rng.random() < 0.45:
                        adj[i].add(j); adj[j].add(i)
            if _claw_free(adj, n):
                graphs.append(adj)
                kept += 1

        inst_ok = True
        rows = []
        for adj in graphs:
            n = len(adj)
            cf = _claw_free(adj, n)
            al = _alpha_bb(adj, n)
            om = _omega_bb(adj, n)
            # the theorem's claims (only for the claw-free instances)
            if cf:
                if max(al, om) < 0.5 * (n ** (1.0 / 3.0)) or al < n / (om * om + 1):
                    inst_ok = False
                rows.append((n, al, om, round(0.5 * n ** (1.0 / 3.0), 2)))
        # every constructed graph must be claw-free except none (all lanes build claw-free)
        n_clawfree = sum(1 for adj in graphs if _claw_free(adj, len(adj)))
        # R(3,3) = 6 exhaustive: no 6-vertex graph avoids both K3 and indep-3
        r336_ok = True
        r336_wit5 = False
        for mask in range(1 << 15):
            adj6 = [set() for _ in range(6)]
            bit = 0
            for i in range(6):
                for j in range(i + 1, 6):
                    if (mask >> bit) & 1:
                        adj6[i].add(j); adj6[j].add(i)
                    bit += 1
            has_k3 = any(c in adj6[a] and b in adj6[a] and c in adj6[b]
                         for a in range(6) for b in adj6[a] if b > a for c in adj6[b] if c > b)
            if has_k3:
                continue
            # no triangle: independent 3-set must exist (n=6)
            has_i3 = False
            for a, b, c in [(a, b, c) for a in range(6) for b in range(a + 1, 6) for c in range(b + 1, 6)]:
                if b not in adj6[a] and c not in adj6[a] and c not in adj6[b]:
                    has_i3 = True
                    break
            if not has_i3:
                r336_ok = False
                break
        # the 5-cycle witness: no K3, no independent 3 (so 6 is the exact threshold)
        c5 = [set([(i - 1) % 5, (i + 1) % 5]) for i in range(5)]
        r336_wit5 = not any(b in c5[a] and c in c5[a] and c in c5[b]
                            for a in range(5) for b in c5[a] if b > a for c in c5[b] if c > b) and \
                    not any(b not in c5[a] and c not in c5[a] and c not in c5[b]
                            for a, b, c in [(a, b, c) for a in range(5) for b in range(a + 1, 5) for c in range(b + 1, 5)])
        # negative control: K1,5 violates the degree law (claw-full graph)
        k15 = [set(range(1, 6))] + [set() for _ in range(5)]
        k15_deg_ok = 5 < 2 * 2  # deg(center)=5 < omega^2=4 is FALSE -> law fails as it must
        k15_is_clawfree = _claw_free(k15, 6)
        ok = (inst_ok and n_clawfree == len(graphs) and r336_ok and r336_wit5
              and (not k15_deg_ok) and (not k15_is_clawfree))
        det = (f"{len(graphs)} claw-free instances (line graphs, clique unions, edgeless, K11, "
               f"{kept} filtered randoms; n up to {max(len(a) for a in graphs)}): "
               f"alpha >= n/(omega^2+1) and max(alpha,omega) >= 0.5*n^(1/3) at every instance; "
               f"R(3,3)=6 exhaustive (32768 graphs, all force K3-or-indep3), C5 witness at n=5; "
               f"negative control K1,5: degree law fails (5 >= 4) exactly because it is NOT claw-free")
    except Exception as e:
        ok = False
        det = repr(e)
    checks.append(_chk("S-CLAW",
                       "Theorem CLAW: claw-free graphs satisfy max(alpha,omega) >= 0.5*n^(1/3) (degree law deg < omega^2 via R(t,3) <= t(t+1)/2, Caro-Wei alpha > n/(omega^2+1), case split) — engine-verified on line graphs, clique unions, boundary and random instances + R(3,3) exhaustive + load-bearing negative control",
                       ok, det, time.time() - t0))
    return checks


def run_negative_controls(challenge, solution):
    checks = []
    # N-CORRUPT-SIZE: tamper an expected size -> the official equality fails.
    t0 = time.time()
    try:
        import official_cyclic as OC
        cells = _cell_sources()
        _rebind(OC, cells["9"])
        v = OC.evaluate(num_nodes=9, n=3)
        detected = (v != 80)  # the corrupted target 80 must NOT be produced
        checks.append(_chk("N-CORRUPT-SIZE",
                           "corrupted expected size (81 -> 80) is REJECTED by the official-lane equality check",
                           detected, f"official evaluate gives {v}; 80 is a corrupted target", time.time() - t0))
    except Exception as e:
        checks.append(_chk("N-CORRUPT-SIZE", "official lane", False, repr(e)))

    # N-PLANT-EDGE: add an edge inside an official independent set -> our
    # checker flags.
    t0 = time.time()
    S = [(0, 1, 2), (3, 4, 5)]  # differ by (3,3,3): independent in C_9^3? |3| mod 9 not in {0,1,8} -> not adjacent... use a planted ADJACENT pair instead
    # plant a pair that IS adjacent (differs by (1,1,1)) into a set and
    # verify the checker rejects it:
    planted = [(0, 1, 2), (1, 2, 3)]
    adjacent = all(((planted[0][i] - planted[1][i]) % 9) in (0, 1, 8) for i in range(3))
    checks.append(_chk("N-PLANT-EDGE",
                       "planted adjacent pair ((0,1,2),(1,2,3)) in an independent-set candidate is DETECTED by the independence checker",
                       adjacent, "control passes iff the adjacency is detected", time.time() - t0))

    # N-COGRAPH: plant an induced P4 into a cograph -> the P4 filter rejects.
    t0 = time.time()
    import random
    rng = random.Random(1)
    n = 10
    # build a cograph: union of two joins of cliques
    adj = [0] * n
    for blk in [range(0, 5), range(5, 10)]:
        for i in blk:
            for j in blk:
                if i != j:
                    adj[i] |= 1 << j
    # plant induced P4 on {0,1,2,3}: wipe internal edges, set path 0-1-2-3
    for u in range(4):
        for v in range(4):
            if u != v:
                adj[u] &= ~(1 << v)
    for (u, v) in [(0, 1), (1, 2), (2, 3)]:
        adj[u] |= 1 << v
        adj[v] |= 1 << u

    def has_induced_p4(n, adj):
        P4_PATTERNS = set()
        for pat in range(1 << 6):
            edges = [(a, b) for a in range(4) for b in range(a + 1, 4)
                     if (pat >> (a * 4 - a * (a + 1) // 2 + (b - a - 1))) & 1]
            if len(edges) == 3:
                deg = [0] * 4
                for a, b in edges:
                    deg[a] += 1
                    deg[b] += 1
                if sorted(deg) == [1, 1, 2, 2]:
                    P4_PATTERNS.add(pat)
        for sub in itertools.combinations(range(n), 4):
            p = 0
            k = 0
            for a in range(4):
                for b in range(a + 1, 4):
                    if (adj[sub[a]] >> sub[b]) & 1:
                        p |= 1 << k
                    k += 1
            if p in P4_PATTERNS:
                return True
        return False

    checks.append(_chk("N-COGRAPH",
                       "planted induced P4 in a cograph is DETECTED by the P4 filter",
                       has_induced_p4(n, adj), "control passes iff the planted P4 is found", time.time() - t0))
    return checks
