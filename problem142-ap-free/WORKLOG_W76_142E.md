# WORKLOG — W76-142E (ENGINE lane, Erdős #142, wave W76)

Branch: w76-142e (worktree /home/z/waves/w76-142e). English only. Two methods
for every number, receipts for every claim. All times local (UTC+8).

## S000 — Setup and reading (2026-11-20 14:20–14:35)

- Read the brief (W76_BRIEFS/142E.md), the K-lane brief (142K.md) for the
  L-EP / L-NW law context, and the banked machinery: WITNESS_REPORT.md,
  receipts142behrend.txt, experiments/engine_rk.py, extend_rk.py,
  tables_rk.json (banked: k=3 N=1..38, k=4..6 — 188 cells, all certified),
  the OEIS b-files (A003002 anchor for the extension).
- Environment: z3-solver 5.4.1 INSTALLED into /home/z/.venv (was missing;
  pip install z3-solver), gmpy2 2.3.2 INSTALLED (was missing). Present:
  sympy 1.14.0, numpy 2.1.3, scipy 1.14.1, gcc 14.2.0, 2 cores.
- Arsenal verification (all 8 laws read at the exact lines, statements
  quoted in receipts): cubic_expansion [CardinalWorlds.lean:283],
  digit3_mod_pow [GSTBladeWave.lean:56], digit3_congr [GSTBladeWave.lean:72],
  mod_mod_mul [CardinalWorlds.lean:140], div_mod_mul_lemma
  [CardinalWorlds.lean:150], div_add_mod_subst [CardinalWorlds.lean:249],
  carryAtPos_bound [CardinalWorlds.lean:108], plus the K-lane's
  sum_le_sum_of_forall [Erdos261Tower.lean:116] and tower_cauchy
  [Erdos261Tower.lean:810] (both exist as claimed).

## S001 — COMPONENT 1: the r_3 table extension N=39..48 (14:30–14:40)

- Probes: Z3 UNSAT at the frontier targets is CHEAP with the translation
  symmetry break x_0=true (valid WLOG: A - min(A) is AP-free, same size,
  contains 0): N=48 target 17 unsat in 0.7s (1.1s without the break).
- bnb142.c written (fresh C BnB, bitboard exclusion propagation: taking v
  marks w=2v-p for all p in S; bound = count + popcount(non-excluded >= i);
  forced-0 + no-force modes).
  - BUG 1 (caught immediately by the banked-column cross-check): first
    version printed value=1 for every N — two defects: (a) the availability
    mask counted phantom vertices >= N (~0ULL unmasked), (b) the leaf
    unconditionally overwrote best. Fixed with fullMask + a count>best
    guard. After the fix: the C BnB re-derives the banked column r_3(1..38)
    EXACTLY (38/38) and the witnesses all pass the third checker.
- checker142lib.py written (THIRD checker: pair-midpoint scan — no AP
  enumeration; for every pair x<z with x+z even, (x+z)/2 must not be in W).
  - BUG 2 (self-test): the planted-AP control [0,1,3,5,9] expected the
    checker to report (1,5,9) but it correctly reported the earlier AP
    (1,3,5) — the SET contained two APs; test fixed to [0,1,5,9] where
    (1,5,9) is the only AP. Checker itself was correct; 7/7 self-test.
- engine142table_v2.py written and run: Z3 bisection per cell (SAT@v saved
  + UNSAT@v+1 confirmed TWICE with independent seeds 0/20261120; timeout
  verdicts never accepted as UNSAT) + C BnB (both modes) + third checker on
  BOTH witnesses + OEIS A003002 cross-check.
  - BUG 3: first run crashed at N=40 (KeyError '39') — the monotone lower
    anchor read the BANKED table at N-1, which stops at 38. Fixed: running
    prev_value/prev_witness carried from the previous computed cell.
- RESULT: 10/10 cells CERTIFIED-BOTH, 0 WITNESS-ONLY.
    r_3(39)=14, r_3(40)=15, r_3(41..48)=16 (all match OEIS A003002).
  Slowest certificates: N=48 UNSAT 1.204s/0.917s (two seeds), BnB 0.020s
  (2.9M nodes). Engine wall 21.5s total. No cell came near the 20-min
  budget.
- Negative controls green: planted AP flagged by the checker; keeping only
  the d=1 AP clauses makes target 17 SAT in [0,48) and the returned witness
  FAILS the full 3-AP check (clause load-bearing proven); formula sha +
  verdict reproducible.
- Files landed: problem142-ap-free/tables_rk_v2.json (full k=3 table
  N=1..48: banked cells tagged BANKED-W1T2A + 10 new v2 cells; k=4,5,6
  carried verbatim), receipts142table_v2.txt, experiments_v2/ (engine,
  bnb142.c, checker, logs).
- PUSHED: milestone commit (see git log).

## S002 — COMPONENT 2: model-step NO-WRAP certification (in progress)

Plan: for p in {101, 1009, 3203, 9973}: (a) exhaustive brute wrap-scan in C
over ALL (d, L) parametrizations (a-independent by Z_p-translation; a-sample
cross-checks), point-level midpoint lookups, counting internal 3-APs,
original-coordinate wraps, rescaled-coordinate wraps (must be 0);
(b) algebraic rescaled-coordinates check in Python/gmpy2 (modular-inverse
coordinate recovery phi(x) = (x-a)d^{-1} mod p == construction index for
every point; the 2(L-1) < p no-wrap condition; forward AP direction);
negative controls at L > (p+1)/2 (wraps MUST exist there — the sqrt(p)
regime is strict); density bookkeeping on planted progressions.

## S002 — COMPONENT 2: model-step NO-WRAP certification (14:40–14:50)

- wrapscan142.c written (method a): point-level brute over ALL (d, L ≤ √p)
  parametrizations (a=0 + random a-samples), Barrett-reduced midpoint
  lookups; counts internal 3-APs, original-coordinate wraps (allowed),
  rescaled-coordinate wraps (must be 0).
  - BUG 4: the first version's membership test omitted the `index < L`
    condition (the point table covers L_max; sub-progression membership
    needs idx < L). Never triggered in the law range (odd-sum midpoint
    indices land >= (p+1)/2 > √p, so main-scan results were correct), but
    the negative-control range over-counted: phantom "wraps" at L=50 for
    p=101 (theory: first wrap at L=52). Fixed; after the fix the data
    matches theory EXACTLY: clean for L <= (p+1)/2, wraps from
    L = (p+3)/2 with EXACTLY 2 wrapping triples per (a,d) at the threshold
    — both wrap directions (2j = i+k+p and 2j = i+k-p).
- engine142modelstep.py written (method b): B1 phi-recovery EXHAUSTIVE
  over all d, all points (phi(x_i) == i; gmpy2 inverses; a-samples);
  B2 forward identity (numpy-exhaustive over all d at L_max + independent
  pure-python/gmpy2 sample re-check); B3 the no-wrap bound 2(L-1) < p per
  L; B4 the exact-threshold negative control (algebraic wrapping triples);
  B5 density bookkeeping on 6 planted progressions per p (bijection, density
  preservation, relative lengths, nested double-rescale, 3-AP count
  transfer by two independent counting codes at both levels).
  - BUG 5: nested-subprogression planting picked alpha/e without keeping
    the index window {alpha + t·e} inside [0,L) (P' ⊄ P in some rows);
    fixed by planting e <= (L-1)/(L'-1) and alpha <= L-1-(L'-1)e
    (an off-by-one in the alpha randrange bound was caught by the assert
    and fixed in the same round).
- RESULT: ALL FOUR PRIMES GREEN, both methods:
    p=101:  1,000 parametrizations,      7,000 internal 3-APs, 0 rescaled wraps
    p=1009: 31,248 parametrizations,  2,378,880 internal 3-APs, 0 rescaled wraps
    p=3203: 179,312 parametrizations, 45,590,076 internal 3-APs, 0 rescaled wraps
    p=9973: 987,228 parametrizations, 794,020,500 internal 3-APs, 0 rescaled wraps
  + 1,962,788 phi-recovery checks + 27,843,402 forward-identity checks.
  Structural prediction verified: per-(L,d) internal-AP count is
  d-invariant AND equals the integer-AP count of [0,L-1] for every L at
  every prime (the law's content: internal 3-APs of P ≅ integer 3-APs of
  the index interval). a-samples identical to a=0.
  Negative controls: threshold exactly L0=(p+3)/2, 2 wraps per (a,d) there,
  clean at (p+1)/2 — the √p regime has margin p - 2(√p - 1) ≥ 83/949/3093/9777.
- Files: receipts142modelstep.txt + experiments_v2/{wrapscan142.c,
  engine142modelstep.py, wrapscan_*.jsonl}.
- PUSHED: milestone commit.
