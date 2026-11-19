#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""OFFICIAL GATE — the S071/W72 comparator runner (BOSS-ordered fresh lane).

Fresh official comparators downloaded from GitHub (NOT the legacy repo
comparator script): google-deepmind/funsearch @ cc53f27 and
google-deepmind/code_contests @ fa7a4f8, cloned 2026-11-17 into this
directory. The official DeepMind evaluator implementations are the verdict
core; the legacy problem*/comparator/comparator.py code is not imported.

Usage:  python3 official_gate.py <142|61|107>
Verdict: prints exactly `YOUR SOLUTION IS OKAY` (exit 0) when every check
passes; otherwise `YOUR SOLUTION IS REJECTED` (exit 2).
"""
import argparse
import importlib.util
import json
import os
import sys
import time
import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEM_IDS = ("142", "61", "107", "406")
VERDICT_OK = "YOUR SOLUTION IS OKAY"
VERDICT_BAD = "YOUR SOLUTION IS REJECTED"


def _load_driver(pid: str):
    dpath = os.path.join(HERE, "challenges", pid, "driver.py")
    if not os.path.isfile(dpath):
        raise FileNotFoundError(f"driver missing: {dpath}")
    spec = importlib.util.spec_from_file_location(f"gate_driver_{pid}", dpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for fn in ("run_official_checks", "run_solution_checks", "run_negative_controls"):
        if not hasattr(mod, fn):
            raise AttributeError(f"driver {pid} missing {fn}")
    return mod


def _as_check(raw, kind: str) -> dict:
    check = {
        "id": str(raw.get("id", "unnamed")),
        "kind": kind,
        "description": str(raw.get("description", "")),
        "passed": bool(raw.get("passed", False)),
        "detail": str(raw.get("detail", ""))[:4000],
        "seconds": float(raw.get("seconds", 0.0)),
    }
    return check


def main() -> int:
    ap = argparse.ArgumentParser(description="Official DeepMind comparator gate")
    ap.add_argument("problem", choices=PROBLEM_IDS)
    args = ap.parse_args()
    pid = args.problem

    cdir = os.path.join(HERE, "challenges", pid)
    with open(os.path.join(cdir, "challenge.json"), encoding="utf-8") as f:
        challenge = json.load(f)
    with open(os.path.join(cdir, "solution.json"), encoding="utf-8") as f:
        solution = json.load(f)

    # Provenance gate: the official sources must be declared.
    prov_path = os.path.join(HERE, "OFFICIAL_PROVENANCE.md")
    if not os.path.isfile(prov_path):
        print("FATAL: OFFICIAL_PROVENANCE.md missing")
        return 2
    with open(prov_path, encoding="utf-8") as f:
        provenance = f.read()
    if "google-deepmind/funsearch" not in provenance:
        print("FATAL: funsearch provenance missing")
        return 2

    driver = _load_driver(pid)
    rows = []
    t_all = time.time()
    families = (
        ("official", driver.run_official_checks),
        ("solution", driver.run_solution_checks),
        ("control", driver.run_negative_controls),
    )
    for kind, fn in families:
        t0 = time.time()
        raw_checks = fn(challenge, solution)
        took = time.time() - t0
        n = 0
        for raw in raw_checks:
            check = _as_check(raw, kind)
            if check["seconds"] == 0.0:
                check["seconds"] = round(took / max(len(raw_checks), 1), 3)
            rows.append(check)
            n += 1
        print(f"[{pid}] {kind}: {n} checks, "
              f"{sum(1 for r in rows if r['kind'] == kind and r['passed'])} pass")

    failed = [r for r in rows if not r["passed"]]
    ok = not failed

    stamp = datetime.datetime.now().isoformat(timespec="seconds")
    lines = []
    lines.append(f"OFFICIAL GATE RECEIPT — problem #{pid} — {stamp}")
    lines.append("=" * 78)
    lines.append("OFFICIAL SOURCES (fresh GitHub clones, 2026-11-17):")
    lines.append("  github.com/google-deepmind/funsearch @ cc53f27 (Apache-2.0)")
    lines.append("  github.com/google-deepmind/code_contests @ fa7a4f8 (Apache-2.0)")
    lines.append("Challenge statement: " + str(challenge.get("statement_id", "?")))
    lines.append("Claims in solution ledger: " + str(len(solution.get("claims", []))))
    lines.append("=" * 78)
    for r in rows:
        verdict = "PASS" if r["passed"] else "FAIL"
        lines.append(f"[{verdict}] ({r['kind']}) {r['id']} — {r['description']}")
        if not r["passed"]:
            lines.append("       DETAIL: " + r["detail"].replace("\n", " | ")[:800])
    lines.append("=" * 78)
    total_pass = sum(1 for r in rows if r["passed"])
    lines.append(f"CHECKS: {total_pass}/{len(rows)} passed "
                 f"(official={sum(1 for r in rows if r['kind']=='official')}, "
                 f"solution={sum(1 for r in rows if r['kind']=='solution')}, "
                 f"controls={sum(1 for r in rows if r['kind']=='control')})")
    lines.append(f"WALL: {time.time() - t_all:.2f}s")
    if ok:
        lines.append("VERDICT: " + VERDICT_OK)
    else:
        lines.append("VERDICT: " + VERDICT_BAD)
        lines.append("FAILED: " + ", ".join(r["id"] for r in failed))
    receipt = "\n".join(lines) + "\n"
    with open(os.path.join(cdir, "RECEIPTS_official.txt"), "w", encoding="utf-8") as f:
        f.write(receipt)
    print(receipt)
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
