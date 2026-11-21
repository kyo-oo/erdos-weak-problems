# WORKLOG_W80_107E.md — lane diary (opener merge → salvage → finisher)

## Wave W80, Task W80-107E (branch w80-107e) — Happy Ending #107, ALL n >= 3

### Phase 1 — opener merge (previous agent)
- Merged `w79-107e` into `w80-107e` (commit 7bad804), lane scope: the ALL-n
  lower bound engine + the sandwich assembly.

### Phase 2 — the engine build (previous agent, died post-run; salvage committed 3c16fc3)
- `engine107loweralln.py`: the all-n lower construction (concave-arc centers +
  per-cluster cup/cap E-sets), exact Fractions, two-code discipline, stages
  S0–S6, receipts `engine107loweralln_receipts.txt`.
- Verdict line: **RED** — one S2 sub-cell (`slope_bands`, n >= 4). Everything
  load-bearing green: S0, S1, S2 (all cells but slope_bands), S3 (exhaustive
  no-convex-n n=3..7, both codes), S4 (randomized n=8..10, max found = n−1),
  S5 (gap law two codes), S6 (negative controls).
- Salvage checkpoint committed by dispatch; sandwich assembly + docs pending →
  this finisher.

### Phase 3 — finisher verification (W80-107E-F)
- **Receipts audit:** S0 GREEN, S1 GREEN, S2 RED-in-one-subcell, S3 GREEN,
  S4 GREEN, S5 GREEN, S6 GREEN. Root cause of the red sub-cell isolated by
  reading the engine: S2 demanded the center-line constant m/(m−1) for
  *perturbed* cross-cluster pairs; the perturbation dips below it by O(rho).
- **Independent verifier `verify107lower.py`** (fresh rebuild from the header
  spec, no engine import; two NEW convex-position codes: two-pop-set monotone
  chain + gift wrapping): V1 sizes 2^{n−2}/C(m,i) PASS; V2 GP PASS (n=3,4,5,7);
  V3 no-convex-n exhaustive both codes n=5 (56/56) and n=7 (C(32,7)=3,365,856);
  V4 transversal witness law (ALL one-per-cluster transversals convex); V5
  exact slope separation n=3..10 (the S2 discharge: min |inter| >= 1/(1+38rho)
  > 1/2 vs intra <= 1/64, factor >= 30x at every n; center constant m/(m−1)
  confirmed to be the only casualty); V6 Lemma M margin law direct check.
  Three verifier bugs caught and killed before trusting output (reversed-
  enumerate unpack; unsorted witness input; single-pop-set chain logic) — the
  negative-control discipline working as designed.
- **The gap in the salvage closed:** the engine header cited LOWER_PROOF.md,
  which did not exist — the mathematical proof had never been written. Written
  now, completely, as `ES_SANDWICH_ALLN.md`:
  - Lemma E: full induction (A/B split, cross-slope band (d/2,d) vs intra
    <= d/3) — no a-cup, no b-cap, |E| = C(a+b−4, a−2).
  - Lemma M: middle-cluster points strictly right of the top-bottom chord BT
    (arc concavity; margin >= (1−o(1))/(4m) vs slop 57rho/32 — factor > 2000,
    all m).
  - Theorem L: CCW chain decomposition (angle monotonicity + slope separation)
    → right chain = cup-run in T_l ⊕ singles; left chain = cap-run in T_k ⊕
    singles; Lemma M exiles all middle points to the right chain →
    |Y| <= (k+1) + (n−l−1) + (l−k−1) = n−1. Complete, all n.

### Phase 4 — the deliverable (this document's siblings)
- **THEOREM ES-SANDWICH-ALLN** (`ES_SANDWICH_ALLN.md`): for every n >= 3,
  2^{n−2}+1 <= f(n) <= C(2n−4, n−2)+1, f(3)=3, f(4)=5 exact. Lower side proven
  all-n here; upper side cited from banked KILL1 (ES_PACKAGE_PROOF.md Thm CC/U
  + receipts107alln.txt); exact values PROOF.md §1–2.
- Gap law stated exactly (finite n) + asymptotic context (not load-bearing).
- Ledger: C107-LOWER-ALLN, C107-SANDWICH-ALLN appended (NEW_LAWS_107.md,
  NEW_CLAIMS.md).

### Honest residuals
- Engine S2 `slope_bands` cell remains red as written (threshold artifact,
  quantified + discharged by V5; no engine edit made — receipts are immutable
  history, the discharge is documented in ES_SANDWICH_ALLN.md §5).
- Engine S3 code B at n=7 is sampled (2·10^5), not exhaustive; the finisher's
  code B at n=7 is the second instrument (coverage in verify receipts).
- S4 n=8..10 randomized: max-convex found = n−1 with 3–5×10^5 hits each; the
  all-n guarantee rests on the mathematical proof (§4), the engine cells are
  spot-certificates.
