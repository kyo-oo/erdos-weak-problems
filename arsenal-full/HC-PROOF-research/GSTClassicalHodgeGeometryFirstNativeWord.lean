import GSTClassicalHodgeGeometryFirstTwoGenerator
import HodgeConjecture
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — THE FULL GST WORD AS AN ACTUAL NATIVE CYCLE OPERATOR

`GeometryFirstTwoGenerator` already externalizes the two noncommuting GST
primitives as genuine native algebraic-cycle operators:

* the two-slot code observable;
* the exact two-step Lefschetz transport.

The previous layer built the corresponding ambient cohomology word and proved
that, on the genuine Hodge fiber, it is exactly the rank-free matrix unit.
This file constructs the *same word directly on native cycles*.

Consequently, once one source Hodge basis vector has one genuine native cycle
representative, the complete projector/Lefschetz/Poincare word produces an
actual native cycle representative for every target Hodge basis direction.
The unrestricted Hodge fiber then follows by finite-support reconstruction.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeometryFirstNativeWord

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {i j : ClassicalHodgeBasisIndex V H p}

/-- Native source-sheet projector: identity minus the native code observable. -/
noncomputable def nativeSource
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    Module.End ℚ (codimensionCycles V.X p) :=
  LinearMap.id - R.code.cycleOperator

/-- **THE ACTUAL NATIVE GST MATRIX-UNIT WORD.**
This is the native-cycle counterpart of `GeometryFirstTwoGenerator.ambientWord`.
-/
noncomputable def nativeWord
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    Module.End ℚ (codimensionCycles V.X p) :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    (R.code.cycleOperator.comp
      (R.lefschetz.cycleOperator.comp (nativeSource R)))

/-- Cycle class of the native source projector equals the geometry-generated
ambient source projector. -/
theorem cycleClass_nativeSource
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeSource R Z) =
      R.ambientSource (H.cycleClass p Z) := by
  unfold nativeSource GeometryFirstTwoGenerator.ambientSource
  rw [LinearMap.sub_apply, LinearMap.map_sub]
  rw [R.code.cycleClass_natural Z]
  rfl

/-- **NATIVE/AMBIENT WORD COMMUTING SQUARE.**
The complete native GST word commutes with the actual cycle-class map and the
complete ambient GST word. -/
theorem cycleClass_nativeWord
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeWord R Z) =
      R.ambientWord (H.cycleClass p Z) := by
  unfold nativeWord GeometryFirstTwoGenerator.ambientWord
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [LinearMap.map_smul]
  rw [R.code.cycleClass_natural]
  rw [R.lefschetz.cycleClass_natural]
  rw [cycleClass_nativeSource R Z]
  rfl

/-- Applying the native word to a source-basis representative produces a
literal native representative of the target basis vector. -/
theorem nativeWord_cycleClass_of_source
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (hij : i ≠ j)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z = (classicalHodgeBasis V H p i).1) :
    H.cycleClass p (nativeWord R Z) =
      (classicalHodgeBasis V H p j).1 := by
  rw [cycleClass_nativeWord R Z, hZ]
  have hword := R.ambientWord_on_hodge hij
    (classicalHodgeBasis V H p i)
  rw [hword]
  simp [hodgeMatrixUnit_basis_source]

/-- One source cycle plus a geometry-first realization to every target gives
actual basis cycles explicitly, not merely membership in an algebraic span. -/
noncomputable def basisCycleBridgeOfNativeWords
    (source : ClassicalHodgeBasisIndex V H p)
    (Z0 : codimensionCycles V.X p)
    (hZ0 : H.cycleClass p Z0 = (classicalHodgeBasis V H p source).1)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) source j) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j := by
    classical
    exact if _ : source = j then Z0 else nativeWord (R j) Z0
  basisCycle_spec j := by
    classical
    by_cases hj : source = j
    · subst j
      simpa [HodgeConjecture.hodgeBasis, classicalHodgeBasis] using hZ0
    · simpa [hj, HodgeConjecture.hodgeBasis, classicalHodgeBasis] using
        nativeWord_cycleClass_of_source (R j) hj Z0 hZ0

/-- Every rational Hodge class in one weight therefore gets an explicit native
cycle from the same source cycle and the unrestricted GST native words. -/
theorem hodge_weight_of_one_source_and_native_words
    (source : ClassicalHodgeBasisIndex V H p)
    (Z0 : codimensionCycles V.X p)
    (hZ0 : H.cycleClass p Z0 = (classicalHodgeBasis V H p source).1)
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) source j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  let B := basisCycleBridgeOfNativeWords source Z0 hZ0 R
  intro alpha halpha
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H B alpha halpha

/-- **NATIVE-WORD GLOBAL HODGE CROWN.**
One source native representative in each nontrivial weight, together with the
actual geometry-first realization of the two GST primitives from that source
to every unrestricted Hodge basis sheet, closes the exact Stage-2G statement. -/
theorem bigradedBettiHodge_of_native_words
    (source : ∀ p : Nat, ClassicalHodgeBasisIndex V H p)
    (Z0 : ∀ p : Nat, codimensionCycles V.X p)
    (hZ0 : ∀ p : Nat,
      H.cycleClass p (Z0 p) =
        (classicalHodgeBasis V H p (source p)).1)
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (source p) j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_weight_of_one_source_and_native_words
    (source p) (Z0 p) (hZ0 p) (R p) halpha

#check nativeSource
#check nativeWord
#check cycleClass_nativeSource
#check cycleClass_nativeWord
#check nativeWord_cycleClass_of_source
#check basisCycleBridgeOfNativeWords
#check bigradedBettiHodge_of_native_words

#print axioms cycleClass_nativeSource
#print axioms cycleClass_nativeWord
#print axioms nativeWord_cycleClass_of_source
#print axioms bigradedBettiHodge_of_native_words

end GSTClassicalHodgeGeometryFirstNativeWord
