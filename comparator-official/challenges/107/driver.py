#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Driver for the OFFICIAL #107 gate (W72-107C, S071).

Official checks run the verbatim DeepMind FunSearch implementation modules
(fresh clone github.com/google-deepmind/funsearch @ cc53f27, vendored in
official_code/funsearch/implementation/ with import shims only). The
official Evaluator compiles the solution program (official
_sample_to_program) and executes it through the official analyse path
against the challenge inputs.
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
    return checks
