import GSTClassicalHodgeCyclicRealizationEquivalence

/-!
# GST CLASSICAL HODGE — WEIGHTED CYCLIC CRITERION

The local cyclic criterion does not need the special seed whose coefficients
are all one.  Lagrange spectral extraction only requires every live
coefficient to be nonzero.

This module therefore promotes the true minimal cyclic datum:

* one spectral observable with distinct eigenvalues on the live Hodge sheets;
* invariance of the classical atomic cycle-class span;
* one atomic linear combination of those sheets;
* every live coefficient of that one combination is nonzero.

That single weighted atomic seed is enough to extract every live Hodge sheet.
Using range lifting, it is also enough to construct an actual native seed
cycle, hence an explicit native codimension-p cycle representing the original
Hodge class and an exact finite point presentation.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeConstructiveCyclicLanding
open GSTClassicalHodgeRangeLiftedSpectralOperator
open GSTClassicalHodgeCyclicRealizationEquivalence

namespace GSTClassicalHodgeWeightedCyclicCriterion

/-- Minimal local cyclic datum for one genuine Hodge class: a stable spectral
operator plus one atomic seed with arbitrary nonzero live coefficients. -/
structure WeightedLocalCyclicRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) where
  spectral :
    ClassicalHodgeSpectralOperator V H p (HodgeSupportIndex alpha)
  spectral_basisIndex :
    spectral.basisIndex = HodgeSupportIndex.include
  coefficient : HodgeSupportIndex alpha → ℚ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  seed_mem_atomic :
    (∑ i : HodgeSupportIndex alpha,
      coefficient i • (classicalHodgeBasis V H p i.1).1) ∈
        pointCycleClassSpan p (H.cycleClass p)

namespace WeightedLocalCyclicRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Every live Hodge basis direction is forced into the classical atomic span
by polynomial isolation of the weighted seed. -/
theorem live_basis_mem_atomic
    (R : WeightedLocalCyclicRealization V H p alpha) :
    ∀ i : HodgeSupportIndex alpha,
      (classicalHodgeBasis V H p i.1).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  have h := R.spectral.selected_basis_algebraic_of_cyclic_seed
    R.coefficient R.coefficient_ne_zero
  have hseed :
      (∑ i : HodgeSupportIndex alpha,
        R.coefficient i •
          (classicalHodgeBasis V H p
            (R.spectral.basisIndex i)).1) ∈
        pointCycleClassSpan p (H.cycleClass p) := by
    rw [R.spectral_basisIndex]
    exact R.seed_mem_atomic
  intro i
  have hi := h hseed i
  rw [R.spectral_basisIndex] at hi
  exact hi

/-- Weighted local cyclic data already reconstruct the original Hodge class
inside the atomic span. -/
theorem class_mem_atomic
    (R : WeightedLocalCyclicRealization V H p alpha) :
    alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
  rw [hodgeClass_eq_support_sum alpha]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (R.live_basis_mem_atomic i)

/-- The weighted atomic seed belongs to the actual native cycle-class range on
a smooth projective carrier. -/
theorem seed_mem_cycleClass_range
    (R : WeightedLocalCyclicRealization V H p alpha) :
    (∑ i : HodgeSupportIndex alpha,
      R.coefficient i • (classicalHodgeBasis V H p i.1).1) ∈
        LinearMap.range (H.cycleClass p) := by
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact R.seed_mem_atomic

/-- **WEIGHTED NATIVE UPGRADE.**  The arbitrary nonzero atomic seed can be
lifted to one actual native seed cycle.  Range stability automatically lifts
the spectral observable to native cycles, producing the full constructive
local spectral realization without adding any new mathematical hypothesis. -/
noncomputable def toLocalCycleSpectralRealization
    (R : WeightedLocalCyclicRealization V H p alpha) :
    LocalCycleSpectralRealization V H p alpha := by
  let S := R.spectral.toSpectralCycleOperatorViaRange
  have hex : ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z =
        ∑ i : HodgeSupportIndex alpha,
          R.coefficient i • (classicalHodgeBasis V H p i.1).1 :=
    LinearMap.mem_range.mp R.seed_mem_cycleClass_range
  let Z := Classical.choose hex
  have hZ := Classical.choose_spec hex
  have hSindex : S.basisIndex = HodgeSupportIndex.include := by
    exact R.spectral_basisIndex
  refine {
    spectral := S
    spectral_basisIndex := hSindex
    seed := {
      cycle := Z
      coefficient := R.coefficient
      coefficient_ne_zero := R.coefficient_ne_zero
      class_eq := ?_
    }
  }
  rw [hSindex]
  exact hZ

/-- Every weighted local cyclic realization constructs an exact native
codimension-p algebraic cycle representing the original Hodge class. -/
theorem exists_native_cycle
    (R : WeightedLocalCyclicRealization V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  R.toLocalCycleSpectralRealization.exists_native_cycle

/-- Every weighted local cyclic realization also constructs an exact finite
codimension-point presentation of the original Hodge class. -/
theorem exists_point_presentation
    (R : WeightedLocalCyclicRealization V H p alpha) :
    ∃ φ : FiniteCodimensionPresentation V.X p,
      φ.sum (fun x q => q • H.cycleClass p
        (codimensionPointCycle V.X p x)) = alpha.1 := by
  let RC := R.toLocalCycleSpectralRealization
  exact ⟨RC.reconstructedPresentation, RC.reconstructedPresentation_spec⟩

end WeightedLocalCyclicRealization

/-- The previous unit-seed local criterion is a specialization of the weighted
criterion with all coefficients equal to one. -/
noncomputable def LocalCyclicRealization.toWeighted
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    WeightedLocalCyclicRealization V H p alpha where
  spectral := R.spectral
  spectral_basisIndex := R.spectral_basisIndex
  coefficient := fun _ => 1
  coefficient_ne_zero := by
    intro i
    norm_num
  seed_mem_atomic := by
    simpa using R.seed_mem_atomic

/-- **WEIGHTED LOCAL-CYCLIC HODGE CRITERION.**  One arbitrary nonzero atomic
seed on the finite live support of every Hodge class suffices for the full
Stage-2G statement. -/
theorem bigradedBettiHodge_of_weighted_local_cyclic_realizations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (WeightedLocalCyclicRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x, hx⟩
  exact (Classical.choice (hlocal p alpha)).exists_native_cycle

/-- Constructive crown of the weighted criterion: global Hodge, native cycles,
and explicit point presentations follow simultaneously. -/
theorem weighted_local_cyclic_constructive_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (WeightedLocalCyclicRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha.1)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ φ : FiniteCodimensionPresentation V.X p,
        φ.sum (fun x q => q • H.cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1) := by
  refine ⟨bigradedBettiHodge_of_weighted_local_cyclic_realizations V H hlocal,
    ?_, ?_⟩
  · intro p alpha
    exact (Classical.choice (hlocal p alpha)).exists_native_cycle
  · intro p alpha
    exact (Classical.choice (hlocal p alpha)).exists_point_presentation

#check WeightedLocalCyclicRealization
#check WeightedLocalCyclicRealization.live_basis_mem_atomic
#check WeightedLocalCyclicRealization.seed_mem_cycleClass_range
#check WeightedLocalCyclicRealization.toLocalCycleSpectralRealization
#check WeightedLocalCyclicRealization.exists_native_cycle
#check WeightedLocalCyclicRealization.exists_point_presentation
#check LocalCyclicRealization.toWeighted
#check bigradedBettiHodge_of_weighted_local_cyclic_realizations
#check weighted_local_cyclic_constructive_crown

#print axioms WeightedLocalCyclicRealization.live_basis_mem_atomic
#print axioms WeightedLocalCyclicRealization.toLocalCycleSpectralRealization
#print axioms WeightedLocalCyclicRealization.exists_native_cycle
#print axioms bigradedBettiHodge_of_weighted_local_cyclic_realizations
#print axioms weighted_local_cyclic_constructive_crown

end GSTClassicalHodgeWeightedCyclicCriterion
