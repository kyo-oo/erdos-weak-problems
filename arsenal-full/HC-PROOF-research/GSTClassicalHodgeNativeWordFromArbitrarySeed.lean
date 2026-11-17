import GSTClassicalHodgeGeometryFirstNativeWord
import GSTClassicalHodgeConcreteRankFreeGeneration
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — EVERY BASIS CYCLE FROM ONE ARBITRARY ALGEBRAIC HODGE SEED

The native GST matrix-unit word does not require the geometric seed itself to
be a basis vector.  Any nonzero algebraic Hodge class has a nonzero finite
basis coordinate.  Choose one live source coordinate `i`.  The concrete
rank-free GST matrix unit `E_{i,j}` sends the class to that nonzero coordinate
times the arbitrary target basis vector `j`.

Applying the corresponding *native* GST word to the seed cycle and dividing by
the live coefficient therefore produces a genuine native algebraic cycle for
every target Hodge basis vector.

This is the correct interface for the projective cut tower: geometry only has
to supply one nonzero Hodge cycle class in each weight.  It does not have to
hit a preselected Hodge basis direction.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeNativeWordFromArbitrarySeed

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeConcreteRankFreeGeneration
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeGeometryFirstNativeWord
open GSTClassicalHodgeRankFreeArsenalIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A native algebraic cycle whose actual class is a nonzero genuine rational
Hodge class. -/
structure NativeHodgeSeed where
  cycle : codimensionCycles V.X p
  class_is_hodge :
    H.cycleClass p cycle ∈ rationalHodgeSubspace (H.hodgeBigrading p)
  class_ne_zero : H.cycleClass p cycle ≠ 0

namespace NativeHodgeSeed

/-- The genuine Hodge vector carried by the seed. -/
noncomputable def hodgeClass
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) :
    ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p S.cycle, S.class_is_hodge⟩

/-- The seed Hodge vector is nonzero. -/
theorem hodgeClass_ne_zero
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) :
    S.hodgeClass ≠ 0 := by
  intro h
  apply S.class_ne_zero
  exact congrArg Subtype.val h

/-- Choose one genuinely live basis coordinate of the nonzero seed. -/
noncomputable def sourceIndex
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) :
    ClassicalHodgeBasisIndex V H p :=
  (chosenLiveSource S.hodgeClass S.hodgeClass_ne_zero).1

/-- Its source coefficient is nonzero. -/
noncomputable def sourceCoefficient
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) : ℚ :=
  (classicalHodgeBasis V H p).repr S.hodgeClass S.sourceIndex

 theorem sourceCoefficient_ne_zero
    (S : NativeHodgeSeed (V := V) (H := H) (p := p)) :
    S.sourceCoefficient ≠ 0 := by
  exact chosenLiveSource_coefficient_ne_zero
    S.hodgeClass S.hodgeClass_ne_zero

/-- Native GST word from the chosen live source coordinate to target `j`. -/
noncomputable def rawTargetCycle
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    codimensionCycles V.X p :=
  by
    classical
    exact if _ : S.sourceIndex = j then
      R.code.cycleOperator S.cycle
    else
      nativeWord R S.cycle

/-- The raw target cycle has class equal to the nonzero live source coefficient
times the arbitrary target Hodge basis vector. -/
theorem rawTargetCycle_spec
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    H.cycleClass p (S.rawTargetCycle j R) =
      S.sourceCoefficient • (classicalHodgeBasis V H p j).1 := by
  classical
  by_cases hij : S.sourceIndex = j
  · have hcode : H.cycleClass p (S.rawTargetCycle j R) =
        R.ambientCode S.hodgeClass.1 := by
      simp only [rawTargetCycle, dif_pos hij]
      change H.cycleClass p (R.code.cycleOperator S.cycle) =
        R.code.cohomologyOperator (H.cycleClass p S.cycle)
      exact R.code.cycleClass_natural S.cycle
    rw [hcode, R.ambientCode_on_hodge_of_eq hij S.hodgeClass]
    change (hodgeMatrixUnit S.sourceIndex j S.hodgeClass).1 = _
    rw [hodgeMatrixUnit_apply]
    rfl
  · have hword : H.cycleClass p (S.rawTargetCycle j R) =
        R.ambientWord S.hodgeClass.1 := by
      simp only [rawTargetCycle, dif_neg hij]
      exact cycleClass_nativeWord R S.cycle
    rw [hword, R.ambientWord_on_hodge hij S.hodgeClass]
    change (hodgeMatrixUnit S.sourceIndex j S.hodgeClass).1 = _
    rw [hodgeMatrixUnit_apply]
    rfl

/-- Normalize the target cycle by the nonzero live coefficient. -/
noncomputable def targetCycle
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    codimensionCycles V.X p :=
  S.sourceCoefficient⁻¹ • S.rawTargetCycle j R

/-- **ARBITRARY-SEED BASIS EXTRACTION.**
The normalized native GST word represents the arbitrary target basis vector
exactly. -/
theorem targetCycle_spec
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) S.sourceIndex j) :
    H.cycleClass p (S.targetCycle j R) =
      (classicalHodgeBasis V H p j).1 := by
  unfold targetCycle
  rw [LinearMap.map_smul, S.rawTargetCycle_spec j R]
  simp [S.sourceCoefficient_ne_zero]

/-- One arbitrary nonzero algebraic Hodge seed plus the genuine two-generator
GST/native realization to every target produces the complete basis-cycle
bridge. -/
noncomputable def basisCycleBridge
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j := S.targetCycle j (R j)
  basisCycle_spec j := S.targetCycle_spec j (R j)

/-- The entire genuine Hodge fiber is algebraic. -/
theorem hodge_weight
    (S : NativeHodgeSeed (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H (S.basisCycleBridge R) alpha halpha

end NativeHodgeSeed

/-- **ACTIVE-WEIGHT NATIVE GST SATURATION.**
Only weights with a genuinely nonzero rational Hodge fiber need a nonzero
native algebraic seed and the geometry-first two-generator transport.

For a zero fiber the cycle-class target holds with the zero native cycle,
without requiring an impossible nonzero seed or a distinguished source index.
This removes the all-natural-weights nonvanishing requirement from the
arbitrary-seed global theorem. The geometric native generators remain explicit
independent construction data in every live weight. -/
theorem bigradedBettiHodge_of_active_nativeHodgeSeeds
    (seed :
      ∀ (p : Nat),
        (∃ alpha : ClassicalHodgeFiber V H p, alpha ≠ 0) →
          NativeHodgeSeed (V := V) (H := H) (p := p))
    (R :
      ∀ (p : Nat)
        (hp : ∃ alpha : ClassicalHodgeFiber V H p, alpha ≠ 0),
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (seed p hp).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  classical
  intro p alpha halpha
  by_cases hp : ∃ beta : ClassicalHodgeFiber V H p, beta ≠ 0
  · exact (seed p hp).hodge_weight (R p hp) halpha
  · have halpha_zero : alpha = 0 := by
      by_contra hne
      apply hp
      refine ⟨⟨alpha, halpha⟩, ?_⟩
      intro h
      apply hne
      simpa using congrArg Subtype.val h
    exact ⟨0, by simp [halpha_zero]⟩

/-- **ONE ALGEBRAIC HODGE SEED PER WEIGHT + FULL LIMITLESS NATIVE GST ARSENAL
CLOSES STAGE 2G.** -/
theorem bigradedBettiHodge_of_nativeHodgeSeeds
    (seed : ∀ p : Nat, NativeHodgeSeed (V := V) (H := H) (p := p))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (seed p).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_active_nativeHodgeSeeds
    (fun p _ => seed p) (fun p _ => R p)

#check NativeHodgeSeed
#check NativeHodgeSeed.sourceIndex
#check NativeHodgeSeed.rawTargetCycle
#check NativeHodgeSeed.targetCycle
#check NativeHodgeSeed.targetCycle_spec
#check NativeHodgeSeed.basisCycleBridge
#check bigradedBettiHodge_of_active_nativeHodgeSeeds
#check bigradedBettiHodge_of_nativeHodgeSeeds

#print axioms NativeHodgeSeed.rawTargetCycle_spec
#print axioms NativeHodgeSeed.targetCycle_spec
#print axioms bigradedBettiHodge_of_active_nativeHodgeSeeds
#print axioms bigradedBettiHodge_of_nativeHodgeSeeds

end GSTClassicalHodgeNativeWordFromArbitrarySeed
