#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Driver for the OFFICIAL #107 gate (W72-107C, S071).

Official checks run the verbatim DeepMind FunSearch implementation modules
(fresh clone github.com/google-deepmind/funsearch @ cc53f27, vendored in
official_code/funsearch/implementation/ with import shims only). The
official Evaluator compiles the solution program (official
_sample_to_program) and executes it through the official analyse path
against the challenge inputs.

W73 (agent 2-a) hypothesis-elimination round: adds S-GPELIM (in-driver
greedy GP-ELIM verification), S-H107 (exact-threshold Theorem H107
instances), and N-UNCOND-BOARD (the corrupted-H107-threshold control).
All new geometry is exact-integer and seeded; the existing checks are
unchanged.
"""
import json
import math
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CAMP = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
ENGINE = os.path.join(CAMP, "problem107-happy-ending", "engine107es.py")
sys.path.insert(0, os.path.join(HERE, "official_code"))
sys.path.insert(0, HERE)


def _chk(cid, desc, ok, detail="", seconds=0.0):
    return {"id": cid, "description": desc, "passed": bool(ok),
            "detail": str(detail)[:3000], "seconds": round(seconds, 3)}


# --- W73 (agent 2-a) hypothesis-elimination helpers, exact integer
# arithmetic only; shared by S-GPELIM / S-H107 / N-UNCOND-BOARD ---
import itertools
import random


def _turn(o, a, b):
    """Exact orientation determinant of the ordered triple (o, a, b)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def _line_key(p, q):
    """Canonical primitive key (A, B, C) of the line A*x + B*y = C through
two distinct integer points (division by gcd(|A|,|B|) is exact since the
gcd divides C; sign-normalized)."""
    dx, dy = q[0] - p[0], q[1] - p[1]
    a, b, c = dy, -dx, dy * p[0] - dx * p[1]
    g = math.gcd(math.gcd(abs(a), abs(b)), abs(c))
    if g == 0:
        g = 1
    a, b, c = a // g, b // g, c // g
    if a < 0 or (a == 0 and b < 0):
        a, b, c = -a, -b, -c
    return (a, b, c)


def _max_collinearity(pts):
    """Measured maximum collinearity t(S) = max over lines of |S & line|
(exact pair-line census; |S| >= 2 gives t >= 2)."""
    on = {}
    for i, j in itertools.combinations(range(len(pts)), 2):
        on.setdefault(_line_key(pts[i], pts[j]), set()).update((i, j))
    if not on:
        return len(pts)
    return max(len(v) for v in on.values())


def _hull_size_u107(pts):
    """Strict convex-hull vertex count (exact; collinear points dropped)."""
    p = sorted(set(pts))
    if len(p) <= 2:
        return len(p)

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower = []
    for q in p:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], q) <= 0:
            lower.pop()
        lower.append(q)
    upper = []
    for q in reversed(p):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], q) <= 0:
            upper.pop()
        upper.append(q)
    return len(lower) + len(upper) - 2


def _greedy_gp(pts, m, order, t):
    """Greedy no-3-collinear extraction following `order`; logs per stage
    j the triple (j, forbidden count, C(j,2)*(t-2) bound)."""
    chosen = []
    step_log = []
    for _step in range(m):
        j = len(chosen)
        cs = set(chosen)
        forbidden = set()
        for ia, ib in itertools.combinations(chosen, 2):
            a, b, c = _line_key(pts[ia], pts[ib])
            for ix in order:
                if ix not in cs and a * pts[ix][0] + b * pts[ix][1] == c:
                    forbidden.add(ix)
        step_log.append((j, len(forbidden), math.comb(j, 2) * (t - 2)))
        nxt = -1
        for ix in order:
            if ix not in cs and ix not in forbidden:
                nxt = ix
                break
        if nxt < 0:
            break
        chosen.append(nxt)
    return chosen, step_log


def run_official_checks(challenge, solution):
    checks = []
    t0 = time.time()
    try:
        from funsearch.implementation import evaluator as ev_mod
        from funsearch.implementation import code_manipulation as cm
        from funsearch.implementation import programs_database as pdb_mod
        from funsearch.implementation import config as config_lib
        import solution_program as SP
        ok = True
        err = ""
    except Exception as e:
        ok = False
        err = repr(e)
        checks.append(_chk("O-IMPORT-OFFICIAL", "official implementation modules + solution program import", ok, err, time.time() - t0))
        return checks

    # O-EVAL: the official Evaluator executes our fixed solution program.
    t0 = time.time()
    try:
        spec = SP.get_spec()
        template = cm.text_to_program(spec)
        cfg = config_lib.Config()
        db = pdb_mod.ProgramsDatabase(cfg.programs_database, template, "priority")
        inputs = [1, 2, 3, 4, 5]
        evaluator = ev_mod.Evaluator(db, template, "priority", "evaluate",
                                     inputs=inputs, timeout_seconds=300)
        runs = []

        class LocalSandbox(ev_mod.Sandbox):
            """Implements the official abstract Sandbox interface with a
            local exec (documented; the official pipeline's production
            sandbox is subprocess-based — same interface)."""

            def run(self, program, function_to_run, test_input, timeout_seconds):
                try:
                    ns = {}
                    exec(program, ns)  # noqa: S102 - the official interface
                    out = ns[function_to_run](test_input)
                    runs.append((test_input, out))
                    return out, True
                except Exception:
                    return None, False

        evaluator._sandbox = LocalSandbox()
        evaluator.analyse(SP.get_solution_body(), island_id=0, version_generated=1)
        expected = SP.get_expected_scores()
        got = dict(runs)
        scores_ok = (len(runs) == len(inputs)
                     and all(got.get(i) == expected[i] for i in inputs))
        # official database registration happened (the official register path:
        # islands are pre-created empty; registration adds programs/clusters)
        registered = db._islands[0]._num_programs > 0
        ok = scores_ok and registered
        det = f"official analyse ran {len(runs)}/{len(inputs)} inputs; scores {got} == expected {expected}; database registration {'OK' if registered else 'FAILED'} (island._num_programs = {db._islands[0]._num_programs})"
    except Exception as e:
        ok = False
        det = repr(e)
    checks.append(_chk("O-EVAL",
                       "the OFFICIAL Evaluator compiles the solution program (official _sample_to_program) and executes it via the official analyse path: claim groups 1..5 score 3/3/1/3/2",
                       ok, det, time.time() - t0))

    # O-ADM-DATA: official admissible_set result data integrity cross-check.
    t0 = time.time()
    try:
        data_file = os.path.join(CAMP, "comparator-official", "funsearch",
                                 "admissible_set", "admissible_set_n12_w7_size792.txt")
        with open(data_file, encoding="utf-8") as f:
            txt = f.read().strip()
        rows = [ln for ln in txt.splitlines() if ln.strip()]
        # the official file lists 792 vectors in {0,1,2}^12 (admissible set
        # in the ternary cube); integrity = count + coordinate range +
        # pairwise distinctness
        vecs = []
        for ln in rows:
            toks = ln.replace("[", " ").replace("]", " ").replace(",", " ").split()
            vals = tuple(int(t) for t in toks if t.lstrip("-").isdigit())
            if vals:
                vecs.append(vals)
        n_vec = len(vecs)
        w_ok = (all(len(v) == 12 and all(x in (0, 1, 2) for x in v) for v in vecs)
                and len(set(vecs)) == n_vec)
        ok = (n_vec == 792 and w_ok)
        det = f"official admissible_set n12/w7 file: {n_vec} vectors in {{0,1,2}}^12, pairwise distinct"
    except Exception as e:
        ok = False
        det = repr(e)
    checks.append(_chk("O-ADM-DATA",
                       "official admissible_set result data (n12, w7, size 792) integrity cross-check with own parser",
                       ok, det, time.time() - t0))
    return checks


def run_solution_checks(challenge, solution):
    checks = []
    # S-ENGINE: the campaign ES engine, full 10/10.
    t0 = time.time()
    if os.path.isfile(ENGINE):
        try:
            proc = subprocess.run([sys.executable, ENGINE, "--verify"],
                                  capture_output=True, text=True, timeout=600)
            out = proc.stdout + proc.stderr
            n_pass = out.count("PASS ")
            n_fail = out.count("FAIL ")
            ok = proc.returncode == 0 and n_fail == 0 and n_pass >= 10
            tail = [l for l in out.strip().splitlines() if l.startswith(("PASS", "FAIL"))][-3:]
            checks.append(_chk("S-ENGINE",
                               "campaign ES engine --verify: exit 0, >= 10 PASS, 0 FAIL",
                               ok, tail, time.time() - t0))
        except subprocess.TimeoutExpired:
            checks.append(_chk("S-ENGINE", "engine within 600s", False, "timeout"))
    else:
        checks.append(_chk("S-ENGINE", "engine present", False, ENGINE + " missing"))

    # S-RERUN: independent re-checks.
    t0 = time.time()
    import itertools
    vals = [math.comb(2 * n - 4, n - 2) + 1 for n in range(3, 9)]
    ok_binom = vals == [3, 7, 21, 71, 253, 925]

    def hull_size(pts):
        p = sorted(set(pts))
        if len(p) <= 2:
            return len(p)
        def cross(o, a, b):
            return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
        lower = []
        for q in p:
            while len(lower) >= 2 and cross(lower[-2], lower[-1], q) <= 0:
                lower.pop()
            lower.append(q)
        upper = []
        for q in reversed(p):
            while len(upper) >= 2 and cross(upper[-2], upper[-1], q) <= 0:
                upper.pop()
            upper.append(q)
        return len(lower) + len(upper) - 2

    # 200 deterministic 5-point general-position sets all contain a convex 4
    def gp5(pts):
        if len(set(pts)) < 5:
            return False
        for a, b, c in itertools.combinations(pts, 3):
            if (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]) == 0:
                return False
        return True

    ok_5pt = True
    tested = 0
    t = 0
    while tested < 200 and t < 5000:
        pts = [((i + 1) * (t + 3) % 101, (i * i * (t + 1) + t * 7) % 97) for i in range(5)]
        t += 1
        if not gp5(pts):
            continue
        tested += 1
        if not any(hull_size(c) == 4 for c in itertools.combinations(pts, 4)):
            ok_5pt = False
            break
    # the n=5 witness: 8 points, no convex 5 (independent re-derivation from
    # the parabola-lattice family, deterministic)
    W5 = [(0, 0), (10, 1), (20, 8), (30, 27), (40, 64), (50, 125), (60, 216), (70, 343)]
    ok_w5 = True
    for sub in itertools.combinations(W5, 5):
        if hull_size(sub) == 5:
            ok_w5 = False
            break
    # moment-curve points: every 5 of the parabola lattice W5: convex iff...
    # (the check above is exhaustive on W5; the parabola family has all
    # 5-subsets convex — so use a DIFFERENT family: the witness re-check
    # uses the engine's kernel witness file instead)
    try:
        with open(os.path.join(CAMP, "problem107-happy-ending", "engine107",
                               "witness_coords.json"), encoding="utf-8") as f:
            W = json.load(f)
        n5 = [(int(x), int(y)) for (x, y) in W["n5"]]
        ok_kernel_w5 = (len(n5) == 8 and not any(hull_size(c) == 5
                                                 for c in itertools.combinations(n5, 5)))
    except Exception:
        ok_kernel_w5 = False
    checks.append(_chk("S-RERUN",
                       "independent re-checks: binomial table 3,7,21,71,253,925; 200 deterministic 5-point sets contain convex 4; the kernel 8-point witness re-verified (no convex 5)",
                       ok_binom and ok_5pt and ok_kernel_w5,
                       f"binom={ok_binom}, 5pt={ok_5pt}, kernel-witness={ok_kernel_w5}",
                       time.time() - t0))

    # S-GPELIM (W73): in-driver greedy GP-ELIM verification — the
    # independent second method alongside engine107es.py (self-contained
    # exact integer geometry; no subprocess of the campaign engine).
    t0 = time.time()
    rng = random.Random(20260201)
    DIRS = ((1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, -2),
            (2, -1), (3, 1), (1, 3), (3, -1), (2, 3))
    n_sets = n_extract = n_steps = n_tight = n_triples = 0
    reach_ok = bound_ok = triple_ok = True
    t_hist = {}
    tries = 0
    while n_sets < 60 and tries < 20000:
        tries += 1
        seen = set()
        pts = []
        if n_sets % 5 == 3:
            # exact general-position board (t = 2): integer points on the
            # parabola y = x^2 (a line meets it in <= 2 points),
            # de-homogenized by a random integer shear T(x,y)=(x+s*y,y)
            # (Lemma SH: the shear preserves t and all turn values exactly)
            xs = sorted(rng.sample(range(-12, 13), rng.randint(10, 18)))
            sh = rng.randint(-2, 2)
            for x in xs:
                y = x * x
                pts.append((x + sh * y, y))
        else:
            # planted collinear structure: 1-4 exact integer lines of 2-4
            # points each, padded with scattered points, all distinct
            for _ln in range(rng.randint(1, 4)):
                bx, by = rng.randint(-6, 6), rng.randint(-6, 6)
                dx, dy = rng.choice(DIRS)
                step = rng.randint(1, 3)
                for i in range(rng.randint(2, 4)):
                    p = (bx + i * dx * step, by + i * dy * step)
                    if p not in seen:
                        seen.add(p)
                        pts.append(p)
            target = rng.randint(12, 26)
            while len(pts) < target:
                p = (rng.randint(-15, 15), rng.randint(-15, 15))
                if p not in seen:
                    seen.add(p)
                    pts.append(p)
        N = len(pts)
        if len(set(pts)) != N:
            continue  # defensive: distinctness
        t = _max_collinearity(pts)
        if N < 8 or t >= N:
            continue  # not a testable board (need an above-threshold m)
        t_hist[t] = t_hist.get(t, 0) + 1
        n_sets += 1
        for m in range(3, 10):
            thr = (m - 1) + math.comb(m - 1, 2) * (t - 2) + 1
            if thr > N:
                break  # threshold is nondecreasing in m
            for order in (tuple(range(N)), tuple(range(N - 1, -1, -1))):
                chosen, slog = _greedy_gp(pts, m, order, t)
                n_extract += 1
                if len(chosen) < m:
                    reach_ok = False
                for (_j, cnt, bnd) in slog:
                    n_steps += 1
                    if cnt > bnd:
                        bound_ok = False
                    if cnt == bnd:
                        n_tight += 1
                sub = [pts[i] for i in chosen]
                for a, b, c in itertools.combinations(sub, 3):
                    n_triples += 1
                    if _turn(a, b, c) == 0:
                        triple_ok = False
    ok_gp = (n_sets == 60 and reach_ok and bound_ok and triple_ok)
    checks.append(_chk("S-GPELIM",
                       "in-driver greedy GP-ELIM: 60 seeded integer boards (planted collinear structure + exact general-position parabola boards) — every above-threshold greedy reaches m with a no-3-collinear output, and every stage satisfies forbidden-count <= C(j,2)(t-2)",
                       ok_gp,
                       f"sets={n_sets}, t-histogram={sorted(t_hist.items())}, extractions={n_extract}, stages={n_steps} (tight={n_tight}), brute triples={n_triples}, reach={reach_ok}, bound={bound_ok}, output-nc3={triple_ok}",
                       time.time() - t0))

    # S-H107 (W73): Theorem H107 instances at the EXACT threshold, each
    # brute-verified (exact orientation / hull checker).
    t0 = time.time()
    rng = random.Random(20260203)
    ok_h = True
    total = 0
    cfgs = []
    for (n, t) in ((3, 2), (3, 3), (4, 2)):
        m = math.comb(2 * n - 4, n - 2) + 1
        N = (m - 1) + math.comb(m - 1, 2) * (t - 2) + 1
        made = tries = 0
        while made < 15 and tries < 20000:
            tries += 1
            if (n, t) == (3, 3) and rng.random() < 0.6:
                # planted max-collinearity-3 board: 3 on a line + 1 off
                bx, by = rng.randint(-5, 5), rng.randint(-5, 5)
                dx, dy = rng.choice(((1, 0), (0, 1), (1, 1),
                                     (1, -1), (2, 1), (1, 2)))
                st = rng.randint(1, 3)
                pts = [(bx + i * dx * st, by + i * dy * st) for i in range(3)]
                pts.append((rng.randint(-9, 9), rng.randint(-9, 9)))
                if len(set(pts)) < 4:
                    continue
            else:
                pts = []
                seen = set()
                while len(pts) < N:
                    p = (rng.randint(-20, 20), rng.randint(-20, 20))
                    if p not in seen:
                        seen.add(p)
                        pts.append(p)
            if _max_collinearity(pts) > t:
                continue  # acceptance: measured max collinearity <= t
            made += 1
            total += 1
            if not any(_hull_size_u107(list(c)) == n
                       for c in itertools.combinations(pts, n)):
                ok_h = False
        cfgs.append((n, t, N, m, made))
    checks.append(_chk("S-H107",
                       "Theorem H107 at the exact threshold: for (n,t) in {(3,2),(3,3),(4,2)}, 15 seeded integer sets of N=(m-1)+C(m-1,2)(t-2)+1 points with measured max collinearity <= t each contain a convex n-gon (brute orientation scan)",
                       ok_h and total == 45,
                       f"configs (n,t,N,m,verified)={cfgs}; total sets={total}/45",
                       time.time() - t0))
    return checks


def run_negative_controls(challenge, solution):
    checks = []
    # N-BADPROGRAM: the official Evaluator must reject a broken program.
    t0 = time.time()
    try:
        from funsearch.implementation import evaluator as ev_mod
        from funsearch.implementation import code_manipulation as cm
        from funsearch.implementation import programs_database as pdb_mod
        from funsearch.implementation import config as config_lib
        import solution_program as SP

        class LocalSandbox(ev_mod.Sandbox):
            def run(self, program, function_to_run, test_input, timeout_seconds):
                try:
                    ns = {}
                    exec(program, ns)  # noqa: S102
                    out = ns[function_to_run](test_input)
                    return out, True
                except Exception:
                    return None, False

        spec = SP.get_spec()
        template = cm.text_to_program(spec)
        cfg = config_lib.Config()
        db = pdb_mod.ProgramsDatabase(cfg.programs_database, template, "priority")
        ev1 = ev_mod.Evaluator(db, template, "priority", "evaluate",
                               inputs=[1], timeout_seconds=60)
        ev1._sandbox = LocalSandbox()
        runs = []
        # broken body: raises on call
        # the broken body poisons the LIVE evolved function (priority), which
        # evaluate calls -> every run fails -> no registration
        ev1.analyse("  raise RuntimeError('broken program')", island_id=0, version_generated=1)
        # the official analyse must not register anything (all runs failed):
        # islands are pre-created empty; registration increments _num_programs
        n_reg = db._islands[0]._num_programs
        rejected = (n_reg == 0)
        ok = rejected
        det = f"official analyse of a broken program: island._num_programs = {n_reg} (must be 0)"
    except Exception as e:
        ok = False
        det = repr(e)
    checks.append(_chk("N-BADPROGRAM",
                       "the OFFICIAL Evaluator rejects a broken program (no registration)",
                       ok, det, time.time() - t0))

    # N-PLANT: a planted convex 5 in a witness candidate is flagged.
    t0 = time.time()

    def hull_size(pts):
        p = sorted(set(pts))
        if len(p) <= 2:
            return len(p)
        def cross(o, a, b):
            return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
        lower = []
        for q in p:
            while len(lower) >= 2 and cross(lower[-2], lower[-1], q) <= 0:
                lower.pop()
            lower.append(q)
        upper = []
        for q in reversed(p):
            while len(upper) >= 2 and cross(upper[-2], upper[-1], q) <= 0:
                upper.pop()
            upper.append(q)
        return len(lower) + len(upper) - 2

    import itertools
    pentagon = [(0, 0), (100, 3), (103, 100), (50, 103), (-3, 50)]
    planted = any(hull_size(c) == 5 for c in itertools.combinations(pentagon, 5))
    checks.append(_chk("N-PLANT",
                       "a planted convex pentagon is DETECTED by the hull checker",
                       planted, "control passes iff the convex 5 is found", time.time() - t0))

    # N-BINOM: a corrupted binomial entry fails the table equality.
    t0 = time.time()
    corrupt = [3, 7, 22, 71, 253, 925]
    detected = corrupt != [math.comb(2 * n - 4, n - 2) + 1 for n in range(3, 9)]
    checks.append(_chk("N-BINOM",
                       "a corrupted binomial table entry (21 -> 22) is DETECTED by the equality check",
                       detected, "control passes iff corruption detected", time.time() - t0))

    # N-UNCOND-BOARD (W73): the corrupted H107 threshold (the +1 dropped)
    # must FAIL — the all-collinear board refutes it.
    t0 = time.time()
    n = 3
    m = math.comb(2 * n - 4, n - 2) + 1  # = 3
    refuted = 0
    boards = []
    for N in range(3, 11):
        # the all-collinear set: N distinct integer points on y = 2x + 1
        pts = [(i, 2 * i + 1) for i in range(N)]
        t = _max_collinearity(pts)  # = N on this board
        corrupt = (m - 1) + math.comb(m - 1, 2) * (t - 2)      # +1 dropped
        truth = (m - 1) + math.comb(m - 1, 2) * (t - 2) + 1
        n_conv = sum(1 for c in itertools.combinations(pts, 3)
                     if _turn(c[0], c[1], c[2]) != 0)
        n_hull = sum(1 for c in itertools.combinations(pts, 3)
                     if _hull_size_u107(list(c)) == 3)
        boards.append((N, t, corrupt, n_conv, n_hull))
        # the control PASSES when the corrupted claim is REFUTED: the
        # corrupted bound is met (N >= corrupt) so it claims a convex
        # 3-gon, yet both exact checkers find zero convex triples, and
        # the true threshold makes no claim on this board (truth > N).
        if t == N and N >= corrupt and n_conv == 0 and n_hull == 0 and truth > N:
            refuted += 1
    ok_board = (refuted == 8)
    checks.append(_chk("N-UNCOND-BOARD",
                       "the corrupted H107 threshold (the +1 dropped) is REFUTED: on all-collinear boards (t=N, N=3..10) the corrupted bound claims a convex 3-gon but the exact orientation and hull checkers both find zero convex triples; the true threshold N+1 makes no claim",
                       ok_board,
                       f"refuted {refuted}/8 boards (N,t,corrupt-threshold,convex-triples,hull-triples)={boards}",
                       time.time() - t0))
    return checks
