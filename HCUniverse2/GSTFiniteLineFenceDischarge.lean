import Mathlib
import HCUniverse2.GSTFiniteLinePrimitiveXSource

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FENCE-DISCHARGE CASCADE (wave 10-A)

The omega-fence of the wave-9 apex, restated in EXISTENTIAL form: the
`the_universal_primitive_X_source_package` is `∀ω` with the weight-one
INDEPENDENCE conjunct guarded by `hω : ω ≠ 0`. This module flips the
quantifier shape: GIVEN one nonzero degree-two sphere class, the package
instantiates at THAT witness with the independence conjunct DISCHARGED —
the unconditional-package theorem of record, with the single named fence

  (FENCE-Ω) `∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0`

as the explicit hypothesis. The designated discharge route of FENCE-Ω is
the tetrahedron machine (`GSTSphereTetrahedronCycle.lean` +
`GSTSphereNonzeroClass.lean`: the projected-tetrahedron boundary cycle z
with dz = 0, z ≠ 0, and the separating-functional construction that turns
`⟦z⟧ ≠ 0` into a genuine nonzero cohomology class).

The statements here are pure restatements of the kernel-certified wave-9
corpus (the apex package, run 45736114591 at 5c98f94): no new mathematics,
only the quantifier flip the master statement of record demands.

HONESTY LEDGER. Every statement is proved unconditionally from the green
corpus given the named FENCE-Ω hypothesis. No `sorry`, no new axioms, no
`native_decide`. The GitHub CI lane `gst-sphere-fence-discharge.yml` owns
the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTSphereUnionComponents
open GSTComponentCohomologyZero
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLawLanding
open GSTPositiveDimensionalLiveCoreKit
open GSTFinitePointHodgeData
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineClosedImmersion
open GSTFiniteLineGeneralMLaw
open GSTFiniteLineOverBase
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTFiniteLineCycleCorrespondence
open GSTFiniteLineAnalytification
open GSTCompleteSingleFoldOrbitLaw
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTHodgeSingleHypothesisConditional
open GSTFiniteLinePointsGateDischarge
open GSTFiniteLinePrimitiveXSource

namespace GSTFiniteLineFenceDischarge

/-- **THE WITNESS-SHAPE INDEPENDENCE.**  Given one nonzero degree-two
sphere class, the closed-point source family is linearly independent at
THAT witness, at every `M ≥ 1`, at the constructed unconditional
analytification — the hω-guarded conjunct of the apex package with the
guard discharged by fixing the witness. -/
theorem finiteLineSourceOne_independent_of_exists
    (hex : ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2,
      ∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i)) := by
  obtain ⟨ω₀, hω₀⟩ := hex
  refine ⟨ω₀, fun M hM => ?_⟩
  haveI : NeZero M := hM
  exact finiteLineSourceOne_independent M
    (finiteLineAnalytificationUnconditional M)
    (finiteLineAnalytificationUnconditional_space M) ω₀ hω₀

/-- **THE MASTER WITNESS PACKAGE.**  Given one nonzero degree-two sphere
class (FENCE-Ω), the FULL wave-9 apex package instantiates at that
witness: BOTH source families linearly independent at every `M ≥ 1` (the
weight-one conjunct with the guard discharged by the witness), every
weight-0/1 rational Hodge class an explicit combination of the source
family, every weight-`p ≥ 2` rational Hodge class zero, both compilers
correct, AND the gate-free law itself — the unconditional-package
theorem of record. -/
theorem the_unconditional_source_package_of_exists
    (hex : ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2,
      (∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i))) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
            (finiteLineSourceZero M i))) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 0,
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 0) →
          ∃ q : Fin M → ℚ,
            α = ∑ i, q i • (finiteLineHodgeDataHonest M
              (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
              (finiteLineSourceZero M i)) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 2,
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1) →
          ∃ q : Fin M → ℚ,
            α = ∑ i, q i • (finiteLineHodgeDataHonest M
              (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
              (finiteLineSourceOne M i)) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ p : ℕ, 1 < p →
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) (2 * p),
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading p) →
          α = 0) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 0,
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
          (finiteLineSourceCompilerZero M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) α) = α) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 2,
        ∀ hmem : α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1),
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
          (finiteLineSourceCompilerOne M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω α hmem) = α) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω)) := by
  obtain ⟨ω₀, hω₀⟩ := hex
  refine ⟨ω₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLineSourceOne_independent M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀ hω₀
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLineSourceZero_independent M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLine_universal_primitive_X_source_zero M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLine_universal_primitive_X_source_one M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLine_universal_primitive_X_source_above M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLineSourceCompilerZero_correct M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀
  · intro M hM
    haveI : NeZero M := hM
    exact finiteLineSourceCompilerOne_correct M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω₀
  · intro M hM
    haveI : NeZero M := hM
    exact native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree M ω₀

/-! ## Receipts -/

#check finiteLineSourceOne_independent_of_exists

end GSTFiniteLineFenceDischarge

end -- noncomputable section
