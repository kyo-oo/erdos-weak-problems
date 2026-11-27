# GST Round 52 — the all-degree loss polynomial and curvature specialization memory, Lean-verified

Date: 3 November 2026, Asia/Calcutta. Base revision: `8e399ffe` (the CI
registration commit for the spatial-fold research series). Branch:
`research/gpt6-native-point-primitive-span-20261017`.

## What this round executes

The operator's order: the branch's Lean CI must be ALL GREEN, and the
campaign must GO with new fields and new theorems. This round does both:

1. **CI registration of the whole owner-side fold/curvature series.** The
   thirteen modules of the 2026-11-02/03 owner-side session
   (`GSTCausalFoldDefect`, `GSTFoldPeriodDescent`, `GSTFoldRotation`,
   `GSTFoldPolarization`, `GSTCausalPairingGraphs`,
   `GSTVariableFoldIntegrability`, `GSTGraphV2GeneralSpaceRealization`,
   `GSTSpatialFoldResearch`, `GSTLawStackRound51`,
   `GSTGradedWorldAlgebra`, `GSTGraphV2UnboundedHigherCausality`,
   `GSTSpectralBoundaryDefect`, `waves/GSTNCohomologyV3`) previously had NO
   branch CI coverage (no workflow path matched, zero runs since their
   last registered green runs). They are now kernel-verified by the
   workflow `gst-spatial-fold-research.yml`, one run, all targets, zero
   sorry. `waves/GSTNCohomologyV3` gained its lakefile root.
   Compilation ownership of the owner-side drafts is taken by this session.
2. **Round 52's own new mathematics** (below), in the new module
   `GSTAllDegreeCurvatureMemory.lean`, with its own workflow
   `gst-all-degree-curvature-memory.yml`.

## The new module: `GSTAllDegreeCurvatureMemory`

Two new structures, ten new fields, nine new theorems, all exact algebraic
identities kernel-verified by GitHub Actions; zero sorry, zero axiom
declarations, zero native decide.

### `FoldRankData` — new fields

* `basePoly : Polynomial ℚ` — the Poincaré polynomial `P_A(t)` of the
  original rational cup algebra;
* `cupPoly : Polynomial ℚ` — the rank polynomial `R_α(t)` of cup by the
  prescribed class in each original-base degree;
* `shift : ℕ` — the fold shift `s = 2p − 1`;
* `shift_pos : 0 < shift` — positivity (`p ≥ 1`);
* `cup_zero : cupPoly.coeff 0 = 1` — the degree-zero cup rank
  normalization, i.e. `α ≠ 0`.

### `FoldRankData` — new theorems

* `flat_conservation` — the exact all-degree conservation law:
  `(1 + t^s)²P_A = (1 + t^s)((1 + t^s)P_A − (t^(s+1) + t^s)R_α) +
  t^s(1 + t)(1 + t^s)R_α`, coefficient for coefficient (a ℚ[t] ring
  identity; `t^(s+1) = t·t^s` is made explicit by `pow_succ` before `ring`).
* `loss_below_shift` — no loss below the fold shift: the loss polynomial
  has no support below `s`.
* `fold_unchanged_below_shift` — in every degree `i < s` the paired-fold
  polynomial equals the flat fold polynomial exactly.
* `loss_at_shift` — the first lost degree is the shift itself, with loss
  exactly one under the `α ≠ 0` normalization.
* `degree_one_blind` — at codimension `p ≥ 2` with shift `2p − 1` the loss
  polynomial has no degree-one term: the degree-one curvature test alone
  cannot see any `p ≥ 2` target fold; the first detecting degree is exactly
  `2p − 1`.

These are the Lean-verified cores of the all-degree curvature duality
record's items 3–4.

### `JetFamily` — new fields

* `base : V →ₗ[ℚ] V` — the flat base differential `d`;
* `base_square : base.comp base = 0` — the flatness `d² = 0`;
* `jet : V →ₗ[ℚ] V` — the memory jet `φ`, the ε-coefficient of the family;
* `curvature : V →ₗ[ℚ] V` — the prescribed curvature carrier `K`;
* `memory : base.comp jet + jet.comp base = curvature` — the memory law
  `{d, φ} = K`.

### `JetFamily` — new theorems

* `jetDifferential_apply` — the family differential on first jets:
  `(x, y) ↦ (dx, dy + φx)`, exactly `(d + ε·φ)(x + εy) = dx + ε(dy + φx)`.
* `jet_square_zeroth` — the zeroth jet of the square is zero: the family is
  exactly flat at `ε = 0`.
* `jet_square_first` — the first jet of the square is exactly the curvature:
  the parameter-dependent family retains the full prescribed curvature in
  its first jet, with the memory field supplying the anticommutator.
* `jet_square` — the full square identity: the family differential squares
  to the curvature acting on the zeroth component only.
* `jet_flat_face` — the flat ε = 0 face: the curvature is switched off
  while the memory field still carries the full curvature data.

These are the Lean-verified cores of the specialization-memory route
("switch curvature off while retaining its memory") of the all-degree
record.

## Scope discipline

Every statement here is an exact algebraic identity over supplied rank and
family data. No geometric identification of the paired fold with actual
cohomology is asserted in Lean; no original-X algebraic-source existence
theorem is claimed, assumed, or concluded. The Poincaré duality double and
the transpose symmetry of the rank polynomial remain hand-level, as in the
companion derivation
`research/derivations/GST_all_degree_curvature_duality_specialization_2026_11_03.tex`.

## CI receipts

* `gst-spatial-fold-research.yml` — the thirteen-module registration run
  (see the run links in the worklog/commit message of the registration and
  repair commits).
* `gst-all-degree-curvature-memory.yml` — this round's own run.
* Both enforce zero sorry (`declaration uses 'sorry'` / `sorryAx` grep on
  the build log) and exit nonzero on any build failure.
