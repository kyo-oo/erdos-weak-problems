# OFFICIAL GATE PROTOCOL — S071/W72 (BOSS order, verbatim)

> "NO, DONT USE THE ALREADY HEADER IN THE REPO COMPARATOR SCRIPT, DOWNLOAD,
> FRESH, NEW COMPARATOR OFFICIAL FROM GITHUB ITSELF"

## What is fresh here

- `funsearch/` — fresh clone of **github.com/google-deepmind/funsearch**
  (official DeepMind, Apache-2.0) at clone time 2026-11-17, HEAD cc53f27.
  Contains the OFFICIAL evaluators: cap_set (F_3^n cap sets — the AP-free
  world of #142), cyclic_graphs (independent sets in cyclic graph powers —
  the graph world of #61), admissible_set, corner_free_set, bin_packing,
  and the official pipeline engine `implementation/` (Evaluator class).
- `code_contests/` — fresh clone of **github.com/google-deepmind/code_contests**
  (official DeepMind, Apache-2.0) at clone time 2026-11-17, HEAD fa7a4f8.
  The AlphaCode challenge/test execution harness (C++/Bazel — consulted as
  the challenge+solution format reference; the python-runnable official
  engine is FunSearch's `implementation/`).
- NONE of the legacy `problem*/comparator/comparator.py` code is imported or
  reused by the gate. Legacy solution.json files may be read as DATA (claim
  values), and every value is re-verified from scratch by fresh code plus
  the official evaluators.

## The gate contract

Per problem `p ∈ {142, 61, 107}`:

```
comparator-official/challenges/p/
  challenge.json   # frozen corpus statement (verbatim), pinned conventions,
                   # acceptance criteria, official-evaluator references
  solution.json    # the claim ledger: every claim is a complete theorem or a
                   # machine-certified fact; each claim has an id
  driver.py        # exposes:
                   #   run_official_checks(challenge, solution) -> [Check]
                   #       runs OFFICIAL DeepMind code (verbatim extracts from
                   #       the fresh clones, provenance in file headers)
                   #   run_solution_checks(challenge, solution) -> [Check]
                   #       verifies every solution claim: invokes the campaign
                   #       engines (subprocess, pinned CLIs) + fresh
                   #       independent re-computation (second method)
                   #   run_negative_controls(challenge, solution) -> [Check]
                   #       corruption tests; a control PASSES iff the gate
                   #       correctly REJECTS the corruption
  official_code/   # verbatim extracts of official DeepMind code, each file
                   # headed with source repo, path, commit, license
  RECEIPTS_official.txt   # full run receipt, written by the gate runner
```

`Check` is a dict: `{"id": str, "kind": "official"|"solution"|"control",
"description": str, "passed": bool, "detail": str, "seconds": float}`.

## The runner

`official_gate.py <142|61|107>` (shared, commander-owned):
1. Loads challenge.json + solution.json + driver.py.
2. Runs all three check families.
3. GATE: every check passed (controls count as passed iff corruption was
   rejected) AND solution claims fully covered AND official provenance
   present → prints exactly:

```
YOUR SOLUTION IS OKAY
```

   exit 0. Otherwise prints `YOUR SOLUTION IS REJECTED` + failing check ids,
   exit 2.
4. Writes `RECEIPTS_official.txt`: timestamp, provenance block, the full
   check table (PASS/FAIL per check with timings), the verdict line.

## CI

Each problem gets a python-only job (`gate-<p>-official`) in
`.github/workflows/kills.yml`: checkout, python3 + numpy (+ z3 fallback
routes as in the legacy cmp jobs), then
`python3 comparator-official/official_gate.py <p>` with exit-code gating and
a grep for the verdict line. No Lean in these jobs.

## Word discipline (BOSS law)

Deliverables carry complete-theorem statements only. The BOSS-banned
token families (the failure-label vocabulary from the corrective order —
the four specific phrases and their variants) must not appear in any
file produced this round; this protocol states them only as: the
"remains/stays + o*en" family, the scope-label-header family, and the
two truthfulness-adjective tokens. Scope is stated mathematically:
"Theorem X proves exactly <statement>."
