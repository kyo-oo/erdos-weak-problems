import GSTClassicalHodgeGSTExactFinale
import GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis

/-!
# GST CLASSICAL HODGE — RATIONAL CORRESPONDENCE EXACT FINALE

The projective-word route is intentionally graph-generated.  The classical
correspondence arena is larger: rational finite sums of genuine closed
correspondences in the self-product.  This file lands the same canonical GST
source/target mechanism through that larger native algebraic carrier.

A rational correspondence cycle is interpreted by
`rationalPair`; its cycle-class square is derived from the primitive pointwise
geometric realizations.  Applying that native operator to the canonical
nonzero projective-spine cycle and dividing by the selected nonzero source
coordinate produces an explicit native target cycle.  No target cycle or
basis algebraicity is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTRationalCorrespondenceExactFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGSTSpineGlobalSource
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Normalize the genuine native action of one rational correspondence cycle
on the canonical algebraic GST spine source. -/
noncomputable def canonicalSpineTargetCycleOfRationalCorrespondence
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    codimensionCycles V.X p :=
  let c := (classicalHodgeBasis V H p).repr
    (globalSpineOrbitSeed G M p).hodge
    (globalSpineOrbitSeed G M p).sourceIndex
  c⁻¹ • (rationalPair A T hT).cycleOperator
    (globalSpineOrbitSeed G M p).cycle

/-- **RATIONAL CORRESPONDENCE TARGET EXTRACTION.**
If the synthesized rational correspondence has the GST-predicted action on the
single canonical spine source, the normalized native image is exactly the
requested Hodge basis sheet. -/
theorem canonicalSpineTargetCycleOfRationalCorrespondence_spec
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K))
    (hA :
      (rationalPair A T hT).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    H.cycleClass p
        (canonicalSpineTargetCycleOfRationalCorrespondence
          G M p j A T hT) =
      (classicalHodgeBasis V H p j).1 := by
  let S := globalSpineOrbitSeed G M p
  let c : ℚ := (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex
  have hc : c ≠ 0 := S.sourceCoefficient_ne_zero
  have hnat := (rationalPair A T hT).cycleClass_cycleOperator S.cycle
  rw [S.class_eq, hA] at hnat
  unfold canonicalSpineTargetCycleOfRationalCorrespondence
  rw [LinearMap.map_smul, hnat]
  simp [S, c, hc]

/-- Every basis sheet is in the true cycle-class range once a rational genuine
correspondence realizes the GST source hit for that sheet. -/
theorem every_basis_mem_cycleClassRange_of_rationalCorrespondences
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (A : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      RationalClosedCorrespondenceCycle V)
    (T : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T p j K))
    (hA : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      (rationalPair (A p j) (T p j) (hT p j)).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        LinearMap.range (H.cycleClass p) := by
  intro p j
  refine ⟨canonicalSpineTargetCycleOfRationalCorrespondence
    G M p j (A p j) (T p j) (hT p j), ?_⟩
  exact canonicalSpineTargetCycleOfRationalCorrespondence_spec
    G M p j (A p j) (T p j) (hT p j) (hA p j)

/-- Stage-2G exactness from the rational correspondence realization family. -/
theorem bigradedBettiHodge_of_rationalCorrespondences
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (A : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      RationalClosedCorrespondenceCycle V)
    (T : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T p j K))
    (hA : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      (rationalPair (A p j) (T p j) (hT p j)).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have hbasis := every_basis_mem_cycleClassRange_of_rationalCorrespondences
    G M A T hT hA
  rw [show alpha = ↑(Finsupp.linearCombination ℚ (classicalHodgeBasis V H p)
        ((classicalHodgeBasis V H p).repr alphaH)) from
      (congrArg Subtype.val
        ((classicalHodgeBasis V H p).linearCombination_repr alphaH)).symm,
    Finsupp.linearCombination_apply, Finsupp.sum,
    AddSubmonoidClass.coe_finsetSum]
  simp only [Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (LinearMap.range (H.cycleClass p)).smul_mem
    ((classicalHodgeBasis V H p).repr alphaH j) (hbasis p j)

/-- **RATIONAL-CORRESPONDENCE EXACT CLAY LANDING.**
Every rational Hodge class is a finite rational linear combination of genuine
algebraic cycle classes once the actual rational correspondence family realizes
the GST source hits. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_rationalCorrespondences
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (A : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      RationalClosedCorrespondenceCycle V)
    (T : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
          RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∀ K : FiniteClosedCorrespondence V,
        K.RealizesAmbientOnPoints (H := H) (T p j K))
    (hA : ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
      (rationalPair (A p j) (T p j) (hT p j)).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  exact (exact_rational_hodge_conjecture_finite_sum H).1
    (bigradedBettiHodge_of_rationalCorrespondences G M A T hT hA)

#check canonicalSpineTargetCycleOfRationalCorrespondence
#check canonicalSpineTargetCycleOfRationalCorrespondence_spec
#check every_basis_mem_cycleClassRange_of_rationalCorrespondences
#check bigradedBettiHodge_of_rationalCorrespondences
#check everyHodgeClassIsFiniteRationalCombination_of_rationalCorrespondences

#print axioms canonicalSpineTargetCycleOfRationalCorrespondence_spec
#print axioms bigradedBettiHodge_of_rationalCorrespondences
#print axioms everyHodgeClassIsFiniteRationalCombination_of_rationalCorrespondences

end GSTClassicalHodgeGSTRationalCorrespondenceExactFinale
