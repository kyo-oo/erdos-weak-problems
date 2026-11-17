import GSTClassicalHodgeRangeLiftedSpectralOperator

/-!
# GST CLASSICAL HODGE — CYCLIC REALIZATION EQUIVALENCE

The preceding range-lift theorem removes the apparent distinction between the
cohomological local cyclic engine and its stronger native-cycle formulation.

Forward direction:

* `LocalCyclicRealization` supplies a cohomological spectral observable;
* atomic-span stability is exactly stability of the native cycle-class range;
* projectivity over `ℚ` lifts the observable to native cycles;
* the atomic seed is lifted to one native seed cycle.

Reverse direction:

* `LocalCycleSpectralRealization` explicitly extracts a native cycle for every
  live basis direction;
* hence every live basis direction lies in the native cycle-class range;
* on a smooth projective carrier that range is the point-cycle atomic span;
* therefore the unit sum of all live basis directions is an atomic seed.

Thus no independent native-operator hypothesis is present in the constructive
landing architecture.  Both realizations encode the same local mathematical
condition, while the native form carries explicit extracted witnesses.
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
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeConstructiveCyclicLanding
open GSTClassicalHodgeRangeLiftedSpectralOperator
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgeCyclicRealizationEquivalence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

end GSTClassicalHodgeCyclicRealizationEquivalence

namespace GSTClassicalHodgeConstructiveCyclicLanding
namespace LocalCycleSpectralRealization

/-- Every live direction of a native local spectral realization lies in the
actual point-cycle atomic span. -/
theorem live_basis_mem_atomic
    (R : LocalCycleSpectralRealization V H p alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hrange :
      (classicalHodgeBasis V H p i.1).1 ∈
        LinearMap.range (H.cycleClass p) := by
    exact ⟨R.liveBasisCycle i, R.liveBasisCycle_spec i⟩
  rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange

/-- Consequently the unit sum of all live directions is an atomic seed. -/
theorem unit_seed_mem_atomic
    (R : LocalCycleSpectralRealization V H p alpha) :
    (∑ i : HodgeSupportIndex alpha,
      (classicalHodgeBasis V H p i.1).1) ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  apply Submodule.sum_mem
  intro i hi
  exact R.live_basis_mem_atomic i

/-- Forget the explicit native witnesses while retaining the exact local
cyclic criterion. -/
noncomputable def toLocalCyclicRealization
    (R : LocalCycleSpectralRealization V H p alpha) :
    LocalCyclicRealization V H p alpha where
  spectral := R.spectral.toClassicalHodgeSpectralOperator
  spectral_basisIndex := by
    exact R.spectral_basisIndex
  seed_mem_atomic := R.unit_seed_mem_atomic

end LocalCycleSpectralRealization
end GSTClassicalHodgeConstructiveCyclicLanding

namespace GSTClassicalHodgeCyclicRealizationEquivalence

theorem cre_placeholder_unused : True := trivial

end GSTClassicalHodgeCyclicRealizationEquivalence

namespace GSTClassicalHodgeLocalCyclicCriterion
namespace LocalCyclicRealization

/-- The forward range-lift conversion followed by forgetting explicit native
witnesses still gives a valid local cyclic realization. -/
noncomputable def nativeUpgrade
    (R : LocalCyclicRealization V H p alpha) :
    LocalCycleSpectralRealization V H p alpha :=
  R.toLocalCycleSpectralRealization

end LocalCyclicRealization
end GSTClassicalHodgeLocalCyclicCriterion

namespace GSTClassicalHodgeCyclicRealizationEquivalence

/-- **LOCAL CYCLIC REALIZATION EQUIVALENCE.**  The two realization packages
are inhabited under exactly the same circumstances. -/
theorem localCyclic_nonempty_iff_nativeSpectral_nonempty
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    Nonempty (LocalCyclicRealization V H p alpha) ↔
      Nonempty (LocalCycleSpectralRealization V H p alpha) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toLocalCycleSpectralRealization⟩
  · rintro ⟨R⟩
    exact ⟨R.toLocalCyclicRealization⟩

/-- Family form: a local cyclic realization for every genuine Hodge class is
exactly equivalent to a native spectral realization for every class. -/
theorem all_localCyclic_iff_all_nativeSpectral
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      Nonempty (LocalCyclicRealization V H p alpha)) ↔
    (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      Nonempty (LocalCycleSpectralRealization V H p alpha)) := by
  constructor
  · intro h q beta
    exact (localCyclic_nonempty_iff_nativeSpectral_nonempty V H q beta).mp
      (h q beta)
  · intro h q beta
    exact (localCyclic_nonempty_iff_nativeSpectral_nonempty V H q beta).mpr
      (h q beta)

/-- The weaker-looking cohomological local criterion already carries every
constructive output of the native landing: the Hodge statement, exact native
cycles, and exact finite point presentations. -/
theorem localCyclic_constructive_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCyclicRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha.1)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ φ : FiniteCodimensionPresentation V.X p,
        φ.sum (fun x q => q • H.cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1) := by
  exact constructive_hodge_of_local_cyclic_realizations V H hlocal

#check LocalCycleSpectralRealization.live_basis_mem_atomic
#check LocalCycleSpectralRealization.unit_seed_mem_atomic
#check LocalCycleSpectralRealization.toLocalCyclicRealization
#check LocalCyclicRealization.nativeUpgrade
#check localCyclic_nonempty_iff_nativeSpectral_nonempty
#check all_localCyclic_iff_all_nativeSpectral
#check localCyclic_constructive_crown

#print axioms LocalCycleSpectralRealization.live_basis_mem_atomic
#print axioms LocalCycleSpectralRealization.unit_seed_mem_atomic
#print axioms LocalCycleSpectralRealization.toLocalCyclicRealization
#print axioms localCyclic_nonempty_iff_nativeSpectral_nonempty
#print axioms all_localCyclic_iff_all_nativeSpectral
#print axioms localCyclic_constructive_crown

end GSTClassicalHodgeCyclicRealizationEquivalence
