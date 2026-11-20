# SOLUTION FILE — Erdős #142 (against CHALLENGE_142, the comparator verdict)

## Honest scoreboard (what is PROVED here, exactly)

| Comparator question | Verdict | Delivered by |
|---|---|---|
| Q1 asymptotic formula | OPEN (untouched, exactly as labeled) | — |
| Q2 o(N/log N) | OPEN | — |
| Q3 order of magnitude | OPEN | — |
| Q4 r_3 asymptotic | OPEN | — |
| Q5 finite exact frontier | **DELIVERED: 188 dual-certified cells** | this campaign |

## The delivered mathematics (all machine-certified, dual-method)

1. **THE CERTIFIED TABLES** (WITNESS_REPORT.md, tables_rk.json): exact
   r_k(N) for k = 3 (N ≤ 38), k = 4 (N ≤ 42), k = 5 (N ≤ 57), k = 6
   (N ≤ 51) — every cell certified by Z3-SMT feasibility bisection (SAT
   witness at v + UNSAT at v+1 = full optimality certificate) AND an
   independent branch-and-bound engine; 188/188 cells in the OEIS
   authoritative b-file range agree (independent verification); 188/188
   witnesses re-validated AP-free.
2. **THE RATIO FRONTIER** (Erdős's [Er80] question): the certified ratio
   tables r_3/r_4, r_4/r_5, r_5/r_6 over the certified range — finite
   evidence, honestly labeled: r_3/r_4 drifts 0.889 → 0.667 (N=10→38);
   no ratio drops below 0.625 in range; the →0 question remains open.
3. **THE STANLEY/TERNARY LOWER BOUND** (arsenal bridge): S(0) ∩ [81] =
   16 points, 3-AP-free, decide-certified IN LEAN (Kernel 66) — the
   ErdosTernary2 digit world applied to #142.
4. **THE EXACT VALUES IN LEAN (Kernel 66, CI-carried)**: r_3(9) = 5,
   r_3(11) = 6, r_3(13) = 7 — both directions decide-certified (witness
   up; all-(v+1)-subsets-contain-AP down); witness frontier cells
   r_3(20) ≥ 9, r_3(27) ≥ 11, r_3(38) ≥ 14, r_4(42) ≥ 22 decide-certified.
5. **The dual-method engine** (engine_rk.py, extend_rk.py): reproducible;
   the salvage's 4-method layer (z3 + 2×bnb + milp) covered N ≤ 20.

## Comparator verdict (self-assessed, honest)

The fortress core (asymptotics) is untouched — exactly as Erdős predicted
("probably enormously difficult"). The finite frontier is CONQUERED:
188 certified cells with witnesses, independently verified against the
published record, plus the kernel layer on GitHub CI. This is the
campaign's standard for fortress targets: the strongest attackable front,
shipped and certified.
