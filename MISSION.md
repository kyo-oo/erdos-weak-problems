# MISSION W67-107D — Erdős #107 DOUBTER/ENGINE LANE (Task ID: W67-107D)

## YOUR DISPOSITION: DOUBTER — research intel + adversarial verification.
Work in /home/z/waves/w67-p107d (branch w67-p107d). You do NOT author the
kernel. Artifacts: problem107-happy-ending/engine107/doubter/.

## THE FROZEN STATEMENT
"Let f(n) be minimal such that any f(n) points in ℝ², no three on a line,
contain n points which form the vertices of a convex n-gon. Prove that
f(n) = 2^{n-2}+1." ($500, falsifiable — the Happy Ending problem.)

## YOUR MISSIONS (python + z3 + gmpy2 armed; exact rational arithmetic only)

1. **THE RESEARCH INTEL (THE critical deliverable — the KILLER depends on
   it)**: fetch and bank the EXACT classical construction for the lower
   bound f(n) ≥ 2^{n−2}+1 (the ErSz60/61 construction of 2^{n−2} points,
   no convex n-gon). Sources to fetch (web/curl armed):
   - https://en.wikipedia.org/wiki/Happy_ending_problem (the main text;
     follow its reference [8] = Erdős–Szekeres 1961 "On some extremum
     problems in elementary geometry").
   - Survey texts reachable by curl: search for "Erdos Szekeres construction
     2^{n-2} points no convex n-gon" on duckduckgo html endpoint
     (https://html.duckduckgo.com/html/?q=...) — find a source that STATES
     the construction explicitly (e.g., lecture notes, the Lovász survey,
     "Thirty Essays on Geometric Graph Theory" chapter 1, Morris's
     "A proof for the Erdős–Szekeres conjecture..." intro sections,
     arXiv lecture notes).
   - The exact upper-bound classical proof (ES35 cups/caps induction with
     the binomial recurrence) — bank the full argument text.
   Bank to doubter/es35_upper.txt + doubter/ersz61_lower.txt + cite sources.
   THE KILLER'S LANE NEEDS THIS IMMEDIATELY — commit + push ASAP so the
   KILLER lane can pull it (git: commit on YOUR branch w67-p107d; the
   KILLER fetches origin/w67-p107d).

2. **THE CONSTRUCTION MIRROR — INDEPENDENT**: implement the researched
   ErSz61 construction yourself (rational coordinates) and verify:
   - general position (no 3 collinear) — exact orientation tests;
   - NO convex n-gon: for n = 3..6 exhaustively over ALL subsets of size
     n of the 2^{n−2} points (n=6: 32 points, C(32,6) = 906k — feasible);
     for n = 7 (64 points, C(64,7) = 621M — TOO many: verify the
     construction's structural invariant instead + random samples);
   - the smallest convex polygon present: what IS the largest convex
     polygon in the construction at n=6/7/8? (Must be ≤ n−1 if the
     construction is correct at that scale.)
   DUAL METHOD: two independent orientation engines (sympy Polygon +
   hand-rolled cross-product turn test).

3. **THE f(4)=5 CENSUS**: every 5-point set in general position contains
   a convex 4-gon: (a) randomized exact-rational census (10^5 samples
   from a grid lattice perturbed — NO three collinear enforced); (b) the
   structural case map (hull size 5/4/3 cases — hull=3 with 2 interior:
   verify the classical argument's partition claim: the line through the
   2 interior points splits the hull triangle 1+2 and the 4-gon exists —
   verify which 4-subset is convex in every configuration class).
   Also: 4-point sets with no convex 4-gon exist (1 interior point) →
   f(4) = 5 exactly. BANK THE CENSUS.

4. **THE UPPER-BOUND STRESS**: the ES35 claim C(2n−4, n−2)+1 points force
   an n-cup or n-cap: randomized census at n=4,5 (C(4,2)+1 = 7 points;
   C(6,3)+1 = 21 points): every random general-position 7-point set
   contains a 4-cup or 4-cap; every 21-point set a 5-cup or 5-cap.
   10^4 samples each. (This certifies the Lean statement's truth at the
   testable scale.)

5. **THE MONOTONE LEMMA CENSUS**: ES monotone subsequence lemma
   (length > (r−1)(s−1) → increasing r-subseq or decreasing s-subseq):
   randomized + adversarial (bit-reversal permutations — the extremal
   case) census at (r,s) ∈ {(3,3), (4,4), (5,3)}.

6. **CI BATTERY**: kills.yml in YOUR worktree: paths entry
   problem107-happy-ending/** + doubter job running
   python3 problem107-happy-ending/engine107/doubter/mirror_battery.py
   (exit nonzero on failure).

## LAWS
- Exact rational arithmetic ONLY (no floats in verification claims).
- Dual method on every census.
- English only. Bank all artifacts, commit, push w67-p107d (token:
  /home/z/my-project/skill-bag/extracted/erdos-zipbag/secrets/ghtoken.txt).

## REPORT BACK: the banked classical construction text (WITH SOURCE URLS),
## the mirror verdicts (construction has no convex n-gon for n ≤ 6 —
## certified), f(4)=5 census verdict, upper-bound stress verdict, CI verdict,
## any BREAK with exact reproduction.
