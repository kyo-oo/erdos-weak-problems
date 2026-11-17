import GSTClassicalHodgeCycleOperatorNaturality
import GSTClassicalHodgeLocalCyclicCriterion
import GSTCompactNativeCyclePresentation
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — CONSTRUCTIVE CYCLIC LANDING

The cycle-operator naturality theorem constructs one native algebraic cycle
for each basis direction in a finite spectral family.  Every individual
classical Hodge class has finite basis support, so we can apply that
construction only on its live support and then recombine the extracted cycles
with the original Hodge coefficients.

The output is an explicit native codimension-p algebraic cycle whose supplied
classical cycle class is exactly the original Hodge class.

This is a fully constructive local landing theorem:

  one local spectral cycle operator
+ one cyclic native seed cycle
+ finite-support basis reconstruction
= one exact native cycle for the given Hodge class.

No global finite-rank or countability hypothesis is used.
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
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTCompactNativeCyclePresentation
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointNormalForm

namespace GSTClassicalHodgeConstructiveCyclicLanding

/-- Constructive spectral realization of the finite live support of one
particular genuine Hodge class. -/
structure LocalCycleSpectralRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) where
  spectral :
    SpectralCycleOperator V H p (HodgeSupportIndex alpha)
  spectral_basisIndex :
    spectral.basisIndex = HodgeSupportIndex.include
  seed : spectral.CyclicSeed

namespace LocalCycleSpectralRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {alpha : ClassicalHodgeFiber V H p}

/-- Explicit native cycle representing one live basis direction. -/
noncomputable def liveBasisCycle
    (R : LocalCycleSpectralRealization V H p alpha)
    (i : HodgeSupportIndex alpha) :
    codimensionCycles V.X p :=
  R.spectral.extractedBasisCycle R.seed i

/-- Exact cycle-class specification of the extracted live basis cycle. -/
theorem liveBasisCycle_spec
    (R : LocalCycleSpectralRealization V H p alpha)
    (i : HodgeSupportIndex alpha) :
    H.cycleClass p (R.liveBasisCycle i) =
      (classicalHodgeBasis V H p i.1).1 := by
  have h := R.spectral.extractedBasisCycle_spec R.seed i
  rw [R.spectral_basisIndex] at h
  exact h

/-- Reassemble the actual Hodge class coefficients on the extracted native
basis cycles. -/
noncomputable def reconstructedCycle
    (R : LocalCycleSpectralRealization V H p alpha) :
    codimensionCycles V.X p :=
  ∑ i : HodgeSupportIndex alpha,
    ((classicalHodgeBasis V H p).repr alpha i.1) •
      R.liveBasisCycle i

/-- **EXACT CONSTRUCTIVE LANDING.**  The reassembled native cycle has cycle
class exactly equal to the original genuine rational Hodge class. -/
theorem reconstructedCycle_spec
    (R : LocalCycleSpectralRealization V H p alpha) :
    H.cycleClass p R.reconstructedCycle = alpha.1 := by
  unfold reconstructedCycle
  rw [map_sum]
  simp_rw [LinearMap.map_smul, R.liveBasisCycle_spec]
  exact (hodgeClass_eq_support_sum alpha).symm

/-- Direct existential form of the constructive landing. -/
theorem exists_native_cycle
    (R : LocalCycleSpectralRealization V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  ⟨R.reconstructedCycle, R.reconstructedCycle_spec⟩

/-- The constructed cycle can immediately be converted to an explicit finite
codimension-point presentation on the smooth projective carrier. -/
noncomputable def reconstructedPresentation
    (R : LocalCycleSpectralRealization V H p alpha) :
    FiniteCodimensionPresentation V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact presentationOfNativeCycle V.X p R.reconstructedCycle

/-- The finite point presentation has exactly the original Hodge class. -/
theorem reconstructedPresentation_spec
    (R : LocalCycleSpectralRealization V H p alpha) :
    (R.reconstructedPresentation).sum
        (fun x q => q • H.cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  rw [← linearMap_realizeFiniteCodimensionPresentation]
  have hpres : R.reconstructedPresentation
      = presentationOfNativeCycle V.X p R.reconstructedCycle := by
    unfold reconstructedPresentation
    rfl
  rw [hpres, realize_presentationOfNativeCycle V.X p R.reconstructedCycle]
  exact R.reconstructedCycle_spec

end LocalCycleSpectralRealization

/-- **FULL CONSTRUCTIVE LOCAL-CYCLIC CRITERION.**
If every individual rational `(p,p)` class admits one local cycle-spectral
realization of its finite live support, then the complete Stage-2G Hodge
statement follows with explicit native cycle witnesses. -/
theorem bigradedBettiHodge_of_local_cycle_spectral_realizations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCycleSpectralRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro p x hx
  let alpha : ClassicalHodgeFiber V H p := ⟨x,hx⟩
  exact (Classical.choice (hlocal p alpha)).exists_native_cycle

/-- Point-presentation form of the same constructive criterion. -/
theorem pointClassEquation_of_local_cycle_spectral_realization
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCycleSpectralRealization V H p alpha) :
    ∃ φ : FiniteCodimensionPresentation V.X p,
      φ.sum (fun x q => q • H.cycleClass p
        (codimensionPointCycle V.X p x)) = alpha.1 :=
  ⟨R.reconstructedPresentation, R.reconstructedPresentation_spec⟩

/-- One crown collecting the constructive consequences of local spectral
cycle realization. -/
theorem constructive_cyclic_landing_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCycleSpectralRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha.1)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ φ : FiniteCodimensionPresentation V.X p,
        φ.sum (fun x q => q • H.cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1) := by
  refine ⟨bigradedBettiHodge_of_local_cycle_spectral_realizations V H hlocal,
    ?_, ?_⟩
  · intro p alpha
    exact (Classical.choice (hlocal p alpha)).exists_native_cycle
  · intro p alpha
    exact pointClassEquation_of_local_cycle_spectral_realization
      (Classical.choice (hlocal p alpha))

#check LocalCycleSpectralRealization
#check LocalCycleSpectralRealization.liveBasisCycle
#check LocalCycleSpectralRealization.liveBasisCycle_spec
#check LocalCycleSpectralRealization.reconstructedCycle
#check LocalCycleSpectralRealization.reconstructedCycle_spec
#check LocalCycleSpectralRealization.exists_native_cycle
#check LocalCycleSpectralRealization.reconstructedPresentation
#check LocalCycleSpectralRealization.reconstructedPresentation_spec
#check bigradedBettiHodge_of_local_cycle_spectral_realizations
#check pointClassEquation_of_local_cycle_spectral_realization
#check constructive_cyclic_landing_crown

#print axioms LocalCycleSpectralRealization.reconstructedCycle_spec
#print axioms LocalCycleSpectralRealization.reconstructedPresentation_spec
#print axioms bigradedBettiHodge_of_local_cycle_spectral_realizations
#print axioms constructive_cyclic_landing_crown

end GSTClassicalHodgeConstructiveCyclicLanding
