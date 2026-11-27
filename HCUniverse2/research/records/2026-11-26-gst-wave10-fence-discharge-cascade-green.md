# 2026-11-26 — WAVE 10 COMPLETION: THE FENCE-DISCHARGE CASCADE GREEN — the tetrahedron machine, the separator shape, the exists-flip master

Written by the commander (the repair round) at HEAD `00463dc`, branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`.

## The state at the round's start

Wave 10 (commit `3cba878`) had pushed the three-piece fence-discharge
cascade; CI run `45766418207` died at Ladder 1/3 with a ~22-error tail.
The other eight lanes of the task ledger were already green at `3cba878`
(Tasks 1/2/5 unconditional; Tasks 3+4, 6, 7 riding-green — the 9-AR seam
fixes had landed the riding lanes at the wave-10 HEAD).

## The repair ledger (six rounds, every error root-caused against the pin and the green corpus)

* **10-B-REPAIR** (`5da6224`): the unpinned names replaced —
  `Matrix.head_tail` dropped from the simp sets;
  `Finset.abs_sum_le_sum_of_abs_le` eliminated by the UPPER-BOUND route
  (`tetraW_coord_le_one` via `le_abs_self`, `mul_le_mul_of_nonneg_left`,
  `Finset.sum_le_sum`, the stdSimplex sum property destructured once);
  `Metric.mem_sphere_zero_iff_norm` → the root-level Riemann spelling;
  the `rationalCoefficient` argument dropped (the pin's
  `ιChainComplex` coefficient is implicit — the green `ιPoint`/`ιPath`
  spelling); `HomologicalComplex.d_comp_d` restated at the pinned
  four-argument no-`Rel` shape (pin-verified at
  `Mathlib/Algebra/Homology/HomologicalComplex.lean:72`);
  `inv_eq_inv_iff` replaced by direct right-cancellation.
* **10-B-REPAIR-II** (`cc4019e`): the vertex-coordination defensive
  simp; the scalar-continuity on the PINNED `continuousAt_inv₀`
  (the `.inv` resolution was a wrong-signature trap — the pin's
  GroupWithZero API is the function-form, `Mathlib/Topology/Algebra/
  GroupWithZero.lean:83`); `tetraMap_continuous` restated at the RAW
  composed continuity; `tetraGen`'s implicit coefficient resolved by the
  ιPoint-style morphism ascription.
* **10-B-REPAIR-III** (`5988ef7`): the `ContinuousAt.comp` metavariable
  trap — the goal's whnf captured `?g` through the PiLp smul's
  `WithLp.toLp 2` head; staged `hg`/`hf` as concrete haves.
* **10-B-REPAIR-IV** (`54906d7`): the decomposition capture killed —
  the point `tetraBary x₀ - tetraCamera` was first-order-decomposed as
  `HSub.hSub (tetraBary x₀)` applied to `tetraCamera`, assigning the
  partial subtraction to `?f`; the composition pinned by NAMED
  ARGUMENTS `(f := …) (x := x₀)`. **PIECE 1 GREEN.**
* **10-C-REPAIR** (`74ad0cb`): the dangling docstring of
  `GSTSphereNonzeroClass.lean` — the frozen-statement comment was a
  DECLARATION docstring with no declaration attached; restated as a
  module-doc section comment. **PIECE 2 GREEN.**
* **10-A-REPAIR** (`00463dc`): the illegal binders of
  `GSTFiniteLineFenceDischarge.lean` — the two `h∃` binders (the
  character `∃` is a Lean token, not an identifier character) renamed
  `hex`. **PIECE 3 GREEN.**

## The verdict (run `45780735883` at `00463dc`, all steps verified)

* Ladder 1/3 `GSTSphereTetrahedronCycle`: GREEN — the projected
  boundary cycle `tetraCycle` with the cycle law `d₂(tetraCycle) = 0`
  (the pinned `d_comp_d`), the camera separation, the central
  projection continuity, the degree-three face formula, and the
  `w₀`-vs-`w₁` projected-distinctness machinery.
* Ladder 2/3 `GSTSphereNonzeroClass`: GREEN — the separator shape
  `TetraSeparator` (the degree-2 functional vanishing on all boundaries,
  reading `1` on the cycle) at the honest sphere's rational chains.
* Ladder 3/3 `GSTFiniteLineFenceDischarge`: GREEN — **the exists-flip
  master**: `finiteLineSourceOne_independent_of_exists` and
  `the_unconditional_source_package_of_exists` (the FULL eight-conjunct
  wave-9 apex package — both source families independent at every
  `M ≥ 1`, the weight-0/1 spanning, the `p ≥ 2` vacuity, both compiler
  correctness receipts, AND the gate-free law itself — instantiated at
  any nonzero degree-two sphere class).
* "Build completed successfully (9016 jobs)"; zero `error:`, zero
  `sorryAx`, zero `declaration uses 'sorry'` in the kernel log.

## The campaign ledger (all kernel-certified, this round)

| Task | Component | Verdict |
|---|---|---|
| 1 | honest prime lattice (`GSTFiniteLinePointAlgebra`) | GREEN, unconditional |
| 2 | chart classification / analytification (`GSTFiniteLineRiemann` + `GSTFiniteLineAnalytification`) | GREEN, unconditional |
| 3+4 | cycle-class maps + the two M-cycle letters (`GSTFiniteLineCycleCorrespondence` family) | GREEN |
| 5 | honest Hodge data (`GSTFiniteLineHonestHodgeData`) | GREEN, unconditional |
| 6 | the gate discharge + the gate-free unconditional law (`GSTFiniteLinePointsGateCore` + `Discharge` + `GSTFiniteLineUnconditionalSource`) | GREEN |
| 7 | the universal primitive-X source (`GSTFiniteLinePrimitiveXSource`) | GREEN |
| 10 | the fence-discharge cascade (the tetrahedron machine, the separator shape, the exists-flip master) | GREEN at `00463dc` |

## The remaining named fence (the honest boundary, unchanged)

FENCE-Ω (`∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2,
ω ≠ 0`) remains the campaign's named obligation, with the designated
discharge route now one-third constructed and certified: the cycle
machine is green (this wave); FENCE-Z (`⟦tetraCycle⟧ ≠ 0`) and FENCE-S
(the separator from the non-bounding cycle) are the designated next
appends recorded in the module headers and PORT NOTES (TET-6, NZC-2
through NZC-5). No green is claimed beyond what CI certified at the
pushed SHAs.
