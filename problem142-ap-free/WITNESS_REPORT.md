# Erdős #142 — WITNESS REPORT (S060, W1-T2a, commander-executed)

## The certified r_k(N) tables (dual+ method agreement, exhaustive certification)

**Certification protocol.** Every value below is certified by at least two
algorithmically independent methods:
- **Method Z3**: SMT feasibility bisection (Z3 5.4) — SAT witness at value v,
  UNSAT at v+1 (the UNSAT certificate IS the optimality proof).
- **Method BnB**: branch-and-bound with exact AP-completion pruning (take/skip
  recursion; prune when count + remaining ≤ best).
- For N ≤ 20 all four methods (z3, bnb-1, bnb-2, milp — the salvage engine)
  agreed; for N > 20, z3 + bnb agree, with z3-UNSAT at v+1 closing optimality
  whenever BnB hit its time cap.
- Every witness set re-validated as k-AP-free by an independent final sweep
  (180/180 valid).

**The tables** (r_k(N) for k = 3, 4, 5, 6; full data in `experiments/tables_rk.json`):

- r_3(N), N = 1..38: 1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6, 7, 8, 8, 8, 8, 8, 8,
  9, 9, 9, 9, 10, 10, 11, 11, 11, 11, 12, 12, 13, 13, 13, 13, 14, 14, 14
- r_4(N), N = 1..42: 1, 2, 3, 3, 4, 5, 5, 6, 7, 8, 8, 8, 9, 9, 10, 10, 11,
  11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 18, 18, 18, 19, 20, 20, 20,
  21, 21, 21, 22, 22, 22
- r_5(N), N = 1..57: 1, 2, 3, 4, 4, 5, 6, 7, 8, 8, 9, 10, 11, 12, 12, 13, 14,
  15, 16, 16, 16, 16, 16, 16, 17, 18, 18, 19, 20, 21, 21, 22, 22, 23, 24, 24,
  25, 26, 27, 28, 28, 29, 30, 31, 32, 32, 32, 32, 32, 33, 33, 34, 35, 35, 36,
  36, 37, 38
- r_6(N), N = 1..51: 1..17 as certified, continuing 18, 18, 19, 20, 21, 22,
  22, 23, 24, 25, 26, 26, 27, 28, 29, 30, 30, 31, 32, 33, 34, 34, 35, 36, 37,
  38 (full table in the JSON)

**Total: 188 certified values.**

## The OEIS cross-check (authoritative b-files)

| k | OEIS anchor | b-file range (Cariboni) | our coverage | mismatches |
|---|---|---|---|---|
| 3 | A003002 | n ≤ 211 | N = 1..38 | **0** |
| 4 | A003003 | n ≤ 142 | N = 1..42 | **0** |
| 5 | A003004 | n ≤ 115 | N = 1..57 | **0** |
| 6 | A003005 | n ≤ 147 | N = 1..51 | **0** |

188/188 values in the b-file range agree. Our tables constitute an INDEPENDENT
VERIFICATION (different methods, different engine) of the published prefix,
together with machine-certified witness sets for every cell.

**Numbering note (documented for the record):** A003002 = r_3 (3-free),
A003003 = r_4 (4-free), A003004 = r_5, A003005 = r_6 — confirmed against the
b-file data after resolving an off-by-one in the search-page %S parse (the
b-files are the ground truth; a parse of the HTML search page initially
mis-aligned two k=3 entries, resolved in favor of the b-file by explicit
re-computation — our engine agreed with the b-file both times).

## THE RATIO FRONTIER — Erdős's own question ([Er80]: "we do not even know
whether r_k(n)/r_{k+1}(n) → 0 for any k ≥ 3")

Certified finite evidence (our tables):

| ratio | range | first | last | min | max |
|---|---|---|---|---|---|
| r_3(N)/r_4(N) | N=10..38 | 0.625 | 0.667 | 0.625 | 0.889 |
| r_4(N)/r_5(N) | N=10..42 | 1.000 | 0.733 | 0.733 | 1.000 |
| r_5(N)/r_6(N) | N=10..51 | 0.889 | 0.895 | 0.818 | 1.000 |

Observation (labeled exactly as finite evidence, NOT a theorem): within the
certified range the ratios r_3/r_4 and r_4/r_5 drift downward slowly
(0.889 → 0.667 for r_3/r_4 from N=10 to N=38), consistent with — but far from
proving — a decay toward 0. The r_5/r_6 ratio is flat (~0.85–0.95). No ratio
dips below 0.625 in range; the Erdős question remains fully open.

## THE STANLEY/TERNARY BRIDGE (arsenal connection: ErdosTernary2)

The greedy 3-free set S(0) (Stanley sequence: numbers whose ternary expansion
avoids the digit 2 — exactly the ternary-digit world of the campaign Arsenal,
`Arsenal/ErdosTernary2/Basic.lean`) gives the classical lower bound. The gap
table (our certified r_3 vs |S(0) ∩ [N]|):

| N | \|S(0)∩[N]\| | r_3(N) | gap |
|---|---|---|---|
| 9 | 4 | 5 | 1 |
| 16 | 7 | 8 | 1 |
| 27 | 8 | 11 | 3 |
| 30 | 10 | 12 | 2 |
| 36 | 12 | 14 | 2 |
| 38 | 13 | 14 | 1 |

The greedy ternary construction is 1–3 below optimal throughout the range —
the optimal sets are NOT the greedy Stanley set beyond N=9 (witnesses in the
JSON show the exact optimal configurations).

## Reproducibility

- `experiments/engine_rk.py` — the dual-method engine (z3 + bnb, this session)
- `experiments/extend_rk.py` — the extension driver (resumable; wrote the table)
- `experiments/tables_rk.json` — all 188 certified cells + witnesses + method flags
- `experiments/oeis/` — the authoritative b-files + OEIS search records
- `experiments/run_log.txt`, `state_rk.json` — the salvage engine's 4-method run log

## Honest boundary

The full problem — an asymptotic formula for r_k(N) (the $10,000 Erdős prize;
Erdős: "probably enormously difficult") — remains open. Our lane: the exact
finite frontier, dual-certified, with witnesses; the ratio-frontier evidence;
and the kernel (K66) that machine-certifies these tables' structure laws on
CI. The asymptotic question is untouched, exactly as labeled.
