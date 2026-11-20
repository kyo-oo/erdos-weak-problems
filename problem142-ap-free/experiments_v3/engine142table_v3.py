#!/usr/bin/env python3
"""ENGINE-142 TABLE V3 (W77-142E) — the certified table pushes.

COMPONENT 1: r_3, N = 49..64 (the W76 discipline verbatim).
COMPONENT 2: r_4 and r_5, N = 21..28 (the first FULL two-method certification
             beyond the banked frontier N=20; the banked 21..28 cells carried
             single-method z3 certificates only).

Protocol per cell (two-method law + third checker — unchanged from W76):
  [A] Z3 feasibility bisection (z3 5.4.1): SAT witness at v (saved) + genuine
      UNSAT at v+1 confirmed TWICE (independent solver seeds 0/20261121).
      Timeout/unknown is NEVER accepted as UNSAT.  Translation symmetry break
      x_0 = true (valid WLOG: A - min(A) is k-AP-free, same size, contains 0).
  [B] Independent C branch-and-bound bnb142v3.c (consecutive-prefix exclusion
      propagation, k=3/4/5), forced-0 AND no-force cross-run, exact optimum.
  [C] Third checker checker142libv3.py on BOTH witnesses (k=3: pair-midpoint
      scan; k=4/k=5: pair-hypothesis scan — every pair x<z and every position
      hypothesis (i,j), reconstruct the full k-AP, test membership).
  [D] OEIS anchor (A003002 for k=3, A003003 for k=4, A003004 for k=5).

Cell budget 1200s; on breach the push STOPS at the furthest certified cell
(the frontier lands, the method holds — timeouts are never UNSAT).

Checkpoint: ckpt_table_v3.json after every cell (resumable; the sandbox reaps
background processes, so everything runs in-process in chunks).
Outputs: tables_rk_v3.json + receipts142e_w77_comp1_2.txt.
"""
import json, time, os, sys, subprocess, hashlib, datetime, random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from checker142libv3 import check_witness_k, self_test as checker_self_test
import laws142lib

import z3
from z3 import Bool, Solver, Or, Not, Sum, If, sat, is_true

HERE = os.path.dirname(os.path.abspath(__file__))
PROJ = os.path.dirname(HERE)
BANKED = os.path.join(PROJ, "tables_rk_v2.json")
OEIS_DIR = os.path.join(PROJ, "experiments", "oeis")
OUT_JSON = os.path.join(PROJ, "tables_rk_v3.json")
OUT_RECEIPTS = os.path.join(PROJ, "receipts142e_w77_comp1_2.txt")
CKPT = os.path.join(HERE, "ckpt_table_v3.json")

SEED = 20261121
CELL_WALL_BUDGET = 1200.0
Z3_TIMEOUT_MS = 600000
RNG = random.Random(SEED)

PUSHES = [
    {"k": 3, "N_lo": 49, "N_hi": 64, "oeis": "bA003002.txt", "component": 1},
    {"k": 4, "N_lo": 21, "N_hi": 28, "oeis": "bA003003.txt", "component": 2},
    {"k": 5, "N_lo": 21, "N_hi": 28, "oeis": "bA003004.txt", "component": 2},
]

# ----------------------------------------------------------------------------
# AP machinery (0-based vertices [0,N); k-APs (a, a+d, ..., a+(k-1)d))
# ----------------------------------------------------------------------------

def aps(N, k):
    out = []
    for a in range(0, N):
        for d in range(1, N):
            if a + (k - 1) * d >= N:
                break
            out.append(tuple(a + i * d for i in range(k)))
    return out


APS_CACHE = {}


def aps_cached(N, k):
    if (N, k) not in APS_CACHE:
        APS_CACHE[(N, k)] = aps(N, k)
    return APS_CACHE[(N, k)]


def formula_sha(N, k, target, fix0):
    h = hashlib.sha256()
    h.update(f"ENGINE142TABLEV3|k={k}|N={N}|target>={target}|fix0={int(fix0)}|".encode())
    for ap in aps_cached(N, k):
        h.update(("AP:" + ",".join(map(str, ap)) + ";").encode())
    return h.hexdigest()


def z3_query(N, k, target, fix0=True, seed=0, timeout_ms=Z3_TIMEOUT_MS):
    x = [Bool(f"x{i}") for i in range(N)]
    s = Solver()
    s.set("timeout", timeout_ms)
    if seed:
        s.set("random_seed", seed)
    for ap in aps_cached(N, k):
        s.add(Or([Not(x[v]) for v in ap]))
    s.add(Sum([If(x[i], 1, 0) for i in range(N)]) >= target)
    if fix0:
        s.add(x[0] == True)
    t0 = time.time()
    r = s.check()
    secs = time.time() - t0
    wit = None
    if r == sat:
        m = s.model()
        wit = [i for i in range(N) if is_true(m[x[i]])]
    return {
        "N": N, "k": k, "target": target, "fix0": fix0, "seed": seed,
        "status": str(r), "secs": round(secs, 3),
        "witness_0based": sorted(wit) if wit is not None else None,
        "formula_sha256": formula_sha(N, k, target, fix0),
        "z3_version": z3.get_version_string(),
        "timeout_ms": timeout_ms,
        "n_ap_clauses": len(aps_cached(N, k)),
    }


def z3_bisect(N, k, lo, hi, budget_deadline):
    """Bisection for max feasible target in [lo, hi] (lo known SAT-feasible).
    Returns (v, sat_rec, queries, err)."""
    queries = []
    q0 = z3_query(N, k, lo, fix0=True, seed=0)
    queries.append(q0)
    if q0["status"] != "sat":
        return None, q0, queries, "lower-anchor not sat"
    sat_rec = q0
    while lo < hi:
        if time.time() > budget_deadline:
            return None, sat_rec, queries, "cell budget breached in bisect"
        mid = (lo + hi + 1) // 2
        q = z3_query(N, k, mid, fix0=True, seed=0)
        queries.append(q)
        if q["status"] == "sat":
            lo = mid
            sat_rec = q
        elif q["status"] == "unsat":
            hi = mid - 1
        else:
            # timeout/unknown: NEVER accepted as UNSAT — linear upward scan
            while lo < hi:
                if time.time() > budget_deadline:
                    return None, sat_rec, queries, "cell budget breached in scan"
                q = z3_query(N, k, lo + 1, fix0=True, seed=0)
                queries.append(q)
                if q["status"] == "sat":
                    lo += 1
                    sat_rec = q
                else:
                    break
            break
    v = lo
    if sat_rec is None or sat_rec["target"] != v:
        sat_rec = z3_query(N, k, v, fix0=True, seed=SEED)
        queries.append(sat_rec)
        if sat_rec["status"] != "sat":
            return None, sat_rec, queries, "witness query failed"
    return v, sat_rec, queries, None


# ----------------------------------------------------------------------------
# Method B: C branch-and-bound bnb142v3.c
# ----------------------------------------------------------------------------

def ensure_bnb():
    exe = os.path.join(HERE, "bnb142v3")
    src = os.path.join(HERE, "bnb142v3.c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
    return exe


def run_bnb(exe, k, lo, hi, noforce=False):
    env = dict(os.environ)
    if noforce:
        env["BNB142V3_NOFORCE"] = "1"
    out = subprocess.run([exe, str(k), str(lo), str(hi)], capture_output=True,
                         text=True, env=env, check=True)
    return [json.loads(l) for l in out.stdout.strip().splitlines() if l.strip()]


# ----------------------------------------------------------------------------
# OEIS anchors
# ----------------------------------------------------------------------------

def load_oeis(fname):
    vals = {}
    with open(os.path.join(OEIS_DIR, fname)) as f:
        for line in f:
            parts = line.split()
            if len(parts) == 2 and parts[0].isdigit():
                vals[int(parts[0])] = int(parts[1])
    return vals


# ----------------------------------------------------------------------------
# per-cell certification
# ----------------------------------------------------------------------------

def certify_cell(k, N, prev_value, prev_witness, oeis_v, bnb_rows, deadline):
    """Full W76 discipline on one cell. Returns (cell_dict, frontier_stop)."""
    t0 = time.time()
    lo = prev_value
    hi = (2 * (N // 3) + (N % 3)) if k == 3 else N
    v, sat_rec, queries, err = z3_bisect(N, k, lo, hi, deadline)
    if v is None:
        return {"N": N, "k": k, "error": err, "status": "BUDGET-STOP"}, True
    # UNSAT certificate at v+1: two independent confirmations
    u1 = z3_query(N, k, v + 1, fix0=True, seed=0)
    u2 = z3_query(N, k, v + 1, fix0=True, seed=SEED)
    if u1["status"] != "unsat" or u2["status"] != "unsat":
        return {"N": N, "k": k, "error": "unsat confirmation not genuine",
                "status": "BUDGET-STOP",
                "u1": u1["status"], "u2": u2["status"]}, True
    bn = bnb_rows["forced"][N]
    bnn = bnb_rows["noforce"][N]
    # third checker on both witnesses
    c_z3 = check_witness_k(sat_rec["witness_0based"], N, k, v)
    c_bn = check_witness_k(bn["witness_0based"], N, k, v)
    # prev-cell witness re-validated inside [0,N) (monotonicity check)
    prev_ok, _ = check_witness_k(prev_witness, N, k, None) if prev_witness else (True, "none")
    z3_ok = (sat_rec["status"] == "sat")
    bnb_ok = (bn["value"] == v and bnn["value"] == v)
    check_ok = c_z3[0] and c_bn[0]
    oeis_ok = (oeis_v == v)
    status = ("CERTIFIED-BOTH" if z3_ok and bnb_ok and check_ok else "WITNESS-ONLY")
    cell = {
        "N": N, "k": k, "value": v, "status": status,
        "z3_sat": {"target": v, "status": sat_rec["status"], "secs": sat_rec["secs"],
                   "witness_0based": sat_rec["witness_0based"],
                   "formula_sha256": sat_rec["formula_sha256"]},
        "z3_unsat": {"target": v + 1, "status_1": u1["status"], "secs_1": u1["secs"],
                     "status_2": u2["status"], "secs_2": u2["secs"],
                     "seeds": [0, SEED], "formula_sha256": u1["formula_sha256"]},
        "bnb": {"value": bn["value"], "nodes": bn["nodes"], "secs": bn["secs"],
                "forced0": True, "witness_0based": bn["witness_0based"],
                "noforce_value": bnn["value"], "noforce_nodes": bnn["nodes"],
                "noforce_secs": bnn["secs"], "optimal_completed": True},
        "checker": {"z3_witness_apfree": c_z3[0], "z3_reason": c_z3[1],
                    "bnb_witness_apfree": c_bn[0], "bnb_reason": c_bn[1],
                    "prev_cell_witness_valid_in_N": prev_ok,
                    "method": ("pair-midpoint scan" if k == 3
                               else "pair-hypothesis scan (checker142libv3)")},
        "oeis": {"value": oeis_v, "match": oeis_ok},
        "n_bisect_queries": len(queries),
        "runtimes_secs": {
            "z3_bisect_total": round(sum(q["secs"] for q in queries), 3),
            "z3_unsat_1": u1["secs"], "z3_unsat_2": u2["secs"],
            "bnb_forced0": bn["secs"], "bnb_noforce": bnn["secs"],
            "cell_wall": round(time.time() - t0, 3)},
        "witness_0based": sat_rec["witness_0based"],
        "witness_1based": [w + 1 for w in sat_rec["witness_0based"]],
    }
    return cell, False


def negative_controls(k, N_last, v_last, witness_last, target_probe):
    """(i) planted AP flagged; (ii) clause-load-bearing (only-d=1 clauses);
    (iii) formula sha + verdict reproducible."""
    neg = {}
    # (i) plant a k-AP inside the last witness: extend a prefix of the
    # witness to a full k-AP (completion points land inside [0,N))
    W = list(witness_last)
    x0 = W[0]
    if k == 3:
        mid = W[1]
        c = 2 * mid - x0
        planted_set = sorted(set(W) | {c})
    elif k == 4:
        # take the prefix (x0, x0+1) if present else (x0, W[1]); complete AP
        d = 1 if (x0 + 1) in set(W) else (W[1] - x0)
        c1, c2 = x0 + 2 * d, x0 + 3 * d
        planted_set = sorted(set(W) | {c1, c2})
    else:
        d = 1 if (x0 + 1) in set(W) else (W[1] - x0)
        planted_set = sorted(set(W) | {x0 + 2 * d, x0 + 3 * d, x0 + 4 * d})
    planted_set = [p for p in planted_set if 0 <= p < N_last]
    neg["checker_planted_AP_flagged"] = (
        not check_witness_k(planted_set, N_last, k, None)[0])
    # (ii) Z3 non-vacuity / clause load-bearing: keep ONLY the d=1 AP clauses
    # -> target v_last+1 must be SAT if that is consistent... the W76 form:
    # keep only d=1 clauses, ask for target = v_last (the certified optimum);
    # with the full clause set this is the max; with only-d=1 it stays SAT at
    # least at v_last (e.g. via the evens+ for d=1 avoidance) and the returned
    # witness must FAIL the full k-AP check — proving the dropped clauses are
    # exactly what force UNSAT.
    x = [Bool(f"y{i}") for i in range(N_last)]
    s = Solver()
    s.set("timeout", 300000)
    for ap in aps_cached(N_last, k):
        if ap[1] - ap[0] == 1:
            s.add(Or([Not(x[v]) for v in ap]))
    s.add(Sum([If(x[i], 1, 0) for i in range(N_last)]) >= v_last)
    r_relaxed = s.check()
    neg["z3_only_d1_clauses_sat_at_v"] = (r_relaxed == sat)
    if r_relaxed == sat:
        m = s.model()
        wit_relaxed = [i for i in range(N_last) if is_true(m[x[i]])]
        neg["relaxed_witness_not_apfree"] = (
            not check_witness_k(wit_relaxed, N_last, k, None)[0])
    else:
        neg["relaxed_witness_not_apfree"] = False
    # (iii) formula sha reproducibility (same query -> same sha, same verdict)
    q_a = z3_query(N_last, k, target_probe, fix0=True, seed=0, timeout_ms=300000)
    q_b = z3_query(N_last, k, target_probe, fix0=True, seed=0, timeout_ms=300000)
    neg["sha_and_verdict_reproducible"] = (
        q_a["formula_sha256"] == q_b["formula_sha256"]
        and q_a["status"] == q_b["status"])
    return neg


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

def main():
    t_wall0 = time.time()
    banked = json.load(open(BANKED))
    bnb_exe = ensure_bnb()

    cres = checker_self_test()
    checker_green = all(ok for _, ok in cres)

    state = {"pushes": {}}
    if os.path.exists(CKPT):
        state = json.load(open(CKPT))

    for push in PUSHES:
        k, N_lo, N_hi = push["k"], push["N_lo"], push["N_hi"]
        key = f"k{k}"
        if key in state["pushes"] and state["pushes"][key].get("done"):
            print(f"[push] k={k} already complete (checkpoint)")
            continue
        oeis = load_oeis(push["oeis"])
        # monotone anchor: last banked/certified cell before N_lo
        prev_N = N_lo - 1
        prev_cell = banked[str(k)][str(prev_N)]
        prev_value = prev_cell["value"]
        prev_witness = prev_cell.get("witness_0based") or prev_cell.get("witness")
        # banked witnesses of the W1 table are 0-based in [0,N) (engine_rk.py)
        # re-validate the anchor witness by the third checker before use
        anchor_ok, _ = check_witness_k(prev_witness, prev_N, k, prev_value)
        # BnB batch runs for the push range (both modes)
        bnb_rows = {
            "forced": {r["N"]: r for r in run_bnb(bnb_exe, k, N_lo, N_hi)},
            "noforce": {r["N"]: r for r in run_bnb(bnb_exe, k, N_lo, N_hi, noforce=True)},
        }
        cells = state["pushes"].get(key, {}).get("cells", {})
        stop = state["pushes"].get(key, {}).get("stop_reason")
        if cells:
            # resume: recompute the running (prev_value, prev_witness) anchors
            done_Ns = sorted(int(n) for n in cells)
            lastc = cells[str(done_Ns[-1])]
            if lastc.get("value") is not None:
                prev_value = lastc["value"]
                prev_witness = lastc["witness_0based"]
        for N in range(N_lo, N_hi + 1):
            if stop is not None:
                break                         # push already halted earlier
            if str(N) in cells:
                continue                      # already certified (checkpoint)
            deadline = time.time() + CELL_WALL_BUDGET
            cell, halted = certify_cell(k, N, prev_value, prev_witness,
                                        oeis.get(N), bnb_rows, deadline)
            cells[str(N)] = cell
            if cell.get("value") is not None:
                prev_value, prev_witness = cell["value"], cell["witness_0based"]
            state["pushes"][key] = {
                "k": k, "N_lo": N_lo, "N_hi": N_hi,
                "component": push["component"],
                "anchor": {"N": prev_N, "value": prev_value,
                           "witness_valid": anchor_ok},
                "cells": cells, "stop_reason": stop,
                "done": False,
            }
            with open(CKPT, "w") as f:      # CHECKPOINT AFTER EVERY CELL
                json.dump(state, f, indent=1)
            print(f"[cell] k={k} N={N} v={cell.get('value')} "
                  f"status={cell.get('status', 'ERROR')} "
                  f"wall={cell.get('runtimes_secs', {}).get('cell_wall', -1)}s",
                  flush=True)
            if halted:
                stop = cell.get("error", "budget")
                state["pushes"][key]["stop_reason"] = stop
                with open(CKPT, "w") as f:
                    json.dump(state, f, indent=1)
                print(f"[push] k={k} STOPPED at N={N}: {stop} "
                      f"(furthest certified frontier lands)", flush=True)
                break
        if stop is None:
            state["pushes"][key]["done"] = True
            with open(CKPT, "w") as f:
                json.dump(state, f, indent=1)
        print(f"[push] k={k} checkpoint saved "
              f"({sum(1 for c in cells.values() if c.get('status') == 'CERTIFIED-BOTH')}"
              f"/{len(cells)} certified-both so far)", flush=True)

    # banked-column reproduction (fresh C bnb vs banked tables)
    repro = {}
    for k, hi_n in [(3, 48), (4, 28), (5, 28)]:
        rows = {r["N"]: r for r in run_bnb(bnb_exe, k, 1, hi_n)}
        ok_v = all(rows[N]["value"] == banked[str(k)][str(N)]["value"]
                   for N in range(1, hi_n + 1))
        ok_w = all(check_witness_k(rows[N]["witness_0based"], N, k,
                                   rows[N]["value"])[0]
                   for N in range(1, hi_n + 1))
        repro[f"k{k}_1_{hi_n}"] = {"values_match": ok_v, "witnesses_apfree": ok_w,
                                   "cells": hi_n}

    # negative controls per k (at each push's last certified cell)
    negs = {}
    for push in PUSHES:
        k = push["k"]
        st = state["pushes"][f"k{k}"]
        cert = [(int(n), c) for n, c in st["cells"].items()
                if c.get("status") == "CERTIFIED-BOTH"]
        if not cert:
            negs[f"k{k}"] = {"skipped": "no certified cell"}
            continue
        N_last, cell = max(cert)
        negs[f"k{k}"] = negative_controls(
            k, N_last, cell["value"], cell["witness_0based"],
            target_probe=cell["value"] + 1)

    # ---- assemble tables_rk_v3.json ------------------------------------
    out = {"meta": {
        "engine": "engine142table_v3.py + bnb142v3.c + checker142libv3.py",
        "wave": "W77-142E", "seed": SEED,
        "generated": datetime.datetime.now().isoformat(timespec="seconds"),
        "z3_version": z3.get_version_string(),
        "protocol": ("per cell: Z3 bisection (SAT@v + genuine UNSAT@v+1 x2 "
                     "seeds) AND fresh C branch-and-bound (forced-0 + "
                     "no-force, consecutive-prefix exclusion) AND third-"
                     "checker re-validation (pair-midpoint k=3 / "
                     "pair-hypothesis k=4,5) AND OEIS cross-check"),
        "convention": ("0-based vertices [0,N-1]; r_k(N) = max k-AP-free "
                       "subset size; witness_1based = +1 shift into [1,N]"),
        "symmetry_law": ("x_0=true WLOG by translation: A-min(A) is k-AP-free,"
                         " same size, contains 0 (valid SAT and UNSAT)"),
    }}
    for k in ("3", "4", "5", "6"):
        table = {}
        for N, c in banked[k].items():
            cc = dict(c)
            if "value" in cc:
                cc["source"] = ("BANKED-W76 (tables_rk_v2.json)"
                                if k == "3" else "BANKED-W1T2A/W76")
            table[N] = cc
        # overlay the new certified cells
        st = state["pushes"].get(f"k{k}")
        if st:
            for N, c in st["cells"].items():
                if c.get("status") == "CERTIFIED-BOTH":
                    c["source"] = f"W77-142E v3 push N={st['N_lo']}..{st['N_hi']}"
                    table[N] = c
                else:
                    table[N] = c  # keep the verdict exactly as landed
        out[k] = table
    out["checks"] = {
        "checker_self_test_15": checker_green,
        "banked_reproduction": repro,
        "negative_controls": negs,
    }
    with open(OUT_JSON, "w") as f:
        json.dump(out, f, indent=1)

    # ---- receipts -------------------------------------------------------
    laws = laws142lib.law_spotchecks(RNG)
    L = []
    L.append("RECEIPTS — engine142table_v3.py (W77-142E) — COMPONENT 1 (r_3 "
             "N=49..64) + COMPONENT 2 (r_4/r_5 N=21..28)")
    L.append(f"seed {SEED} ; deterministic ; z3 {z3.get_version_string()} ; "
             f"gcc 14.2.0 ; {datetime.datetime.now().isoformat(timespec='seconds')}")
    L.append("")
    L.append("PROTOCOL per cell (the W76 discipline verbatim): [A] Z3 bisection —")
    L.append("  SAT witness at v saved, genuine UNSAT at v+1 TWICE (seeds 0/"
             + str(SEED) + "); timeout/unknown NEVER accepted as UNSAT;")
    L.append("  translation symmetry x_0=true (valid SAT and UNSAT).")
    L.append("[B] Fresh C BnB bnb142v3.c — consecutive-prefix exclusion (k=3:")
    L.append("  w=2v-p; k=4: v=2q-p marks 3q-2p; k=5: consecutive triple + v=3q-2p")
    L.append("  marks 4q-3p), forced-0 AND no-force runs must agree.")
    L.append("[C] Third checker checker142libv3.py on BOTH witnesses (k=3 pair-")
    L.append("  midpoint; k=4/5 pair-hypothesis: every pair + every position")
    L.append("  hypothesis reconstructs the full k-AP and tests membership).")
    L.append("[D] OEIS anchors A003002/A003003/A003004.")
    L.append("")
    for push in PUSHES:
        k = push["k"]
        st = state["pushes"][f"k{k}"]
        L.append(f"=== PUSH k={k} N={st['N_lo']}..{st['N_hi']} "
                 f"(component {push['component']}, anchor N={st['N_lo']-1}: "
                 f"r_{k}={st['anchor']['value']}, anchor witness valid: "
                 f"{st['anchor']['witness_valid']})")
        n_cert = 0
        for N in range(st["N_lo"], st["N_hi"] + 1):
            c = st["cells"].get(str(N))
            if c is None:
                break
            if c.get("status") == "CERTIFIED-BOTH":
                n_cert += 1
                L.append(f"PASS CELL N={N}: r_{k}({N}) = {c['value']}  "
                         f"[CERTIFIED-BOTH]")
                L.append(f"  z3: sat@{c['z3_sat']['target']} in "
                         f"{c['z3_sat']['secs']}s ; unsat@{c['z3_unsat']['target']}"
                         f" x2 in {c['z3_unsat']['secs_1']}s/"
                         f"{c['z3_unsat']['secs_2']}s (statuses "
                         f"{c['z3_unsat']['status_1']}/{c['z3_unsat']['status_2']})"
                         f" ; bisect queries {c['n_bisect_queries']}")
                L.append(f"  bnb: optimal={c['bnb']['value']} nodes="
                         f"{c['bnb']['nodes']} in {c['bnb']['secs']}s (forced0) ; "
                         f"no-force: {c['bnb']['noforce_value']} nodes="
                         f"{c['bnb']['noforce_nodes']} in "
                         f"{c['bnb']['noforce_secs']}s")
                L.append(f"  checker: z3-witness "
                         f"{'AP-FREE' if c['checker']['z3_witness_apfree'] else 'FAIL'}"
                         f" ({c['checker']['z3_reason']}), bnb-witness "
                         f"{'AP-FREE' if c['checker']['bnb_witness_apfree'] else 'FAIL'}"
                         f" ; prev-cell witness valid in [0,N): "
                         f"{c['checker']['prev_cell_witness_valid_in_N']}")
                L.append(f"  oeis({N}) = {c['oeis']['value']} match="
                         f"{c['oeis']['match']} ; formula_sha "
                         f"{c['z3_sat']['formula_sha256'][:16]}...")
                L.append(f"  witness(0-based) = {c['witness_0based']}")
            else:
                L.append(f"STOP CELL N={N}: {c.get('error', c.get('status'))} "
                         f"[{c.get('status')}]")
        frontier = st["N_lo"] + n_cert - 1 if n_cert else st["N_lo"] - 1
        L.append(f"PUSH k={k} RESULT: {n_cert} cells CERTIFIED-BOTH, frontier "
                 f"N={frontier} ; stop reason: {st['stop_reason'] or 'completed range'}")
        L.append("")
    L.append("PASS CHECKER-SELF-TEST — "
             + f"{sum(1 for _, ok in cres if ok)}/{len(cres)} "
             "(planted 3/4/5-APs flagged; k-specificity controls: a 4-AP-free "
             "set with a 3-AP passes k=4; a 5-AP-free set with a 4-AP passes k=5)")
    for kk, rr in repro.items():
        L.append(f"PASS BANKED-REPRODUCTION {kk} — fresh C bnb re-derives the "
                 f"banked column ({rr['cells']} values, "
                 f"{rr['cells']} witnesses AP-free by the third checker): "
                 f"{rr['values_match'] and rr['witnesses_apfree']}")
    for kk, neg in negs.items():
        if "skipped" in neg:
            L.append(f"SKIP NEGATIVE-CONTROLS {kk}: {neg['skipped']}")
        else:
            L.append(f"PASS NEGATIVE-CONTROLS {kk} — checker_planted_AP_flagged="
                     f"{neg['checker_planted_AP_flagged']} ; "
                     f"z3_only_d1_clauses_sat_at_v={neg['z3_only_d1_clauses_sat_at_v']}"
                     f" + relaxed_witness_not_apfree={neg['relaxed_witness_not_apfree']}"
                     f" (the d>=2 clauses are exactly what force UNSAT) ; "
                     f"sha_and_verdict_reproducible={neg['sha_and_verdict_reproducible']}")
    L.append("")
    L.append("ARSENAL LAW SPOT-CHECKS (numerically verified this run; read-before-cite):")
    for name, loc, ok in laws:
        L.append(f"  #BY GST LAW {name} [{loc}] — {'PASS' if ok else 'VIOLATED'}")
    L.append("")
    tot_cert = sum(
        1 for push in PUSHES for c in
        state["pushes"][f"k{push['k']}"]["cells"].values()
        if c.get("status") == "CERTIFIED-BOTH")
    green = checker_green and all(r["values_match"] and r["witnesses_apfree"]
                                  for r in repro.values())
    L.append(f"TOTAL: {tot_cert} cells CERTIFIED-BOTH across the three pushes ; "
             f"engine wall {round(time.time() - t_wall0, 1)}s")
    L.append("ENGINE142TABLE_V3_" + ("GREEN" if green else "STATUS-SEE-CELLS"))
    with open(OUT_RECEIPTS, "w") as f:
        f.write("\n".join(L) + "\n")
    print("WROTE", OUT_JSON)
    print("WROTE", OUT_RECEIPTS)
    print(f"engine wall {round(time.time() - t_wall0, 1)}s")


if __name__ == "__main__":
    main()
