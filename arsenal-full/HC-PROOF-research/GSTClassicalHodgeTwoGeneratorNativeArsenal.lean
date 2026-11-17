import GSTClassicalHodgeUniversalTwoSlotNativeClosure
import GSTClassicalHodgeAtomicOperatorAlgebra

/-!
# GST CLASSICAL HODGE — TWO-GENERATOR NATIVE ARSENAL

The universal 2-slot GST machine does not require independent geometric
realizations of two spectral projectors.  On `Fin 2`, the invariant code
observable

    D = diag(0,1)

already generates both projectors by polynomial calculus:

    P_0 = I - D,    P_1 = D.

The only noncommuting primitive still needed is the actual two-step
Lefschetz operator.  Hence the complete rank-free Hodge arsenal externalizes
from exactly two ambient primitive operators:

* the two-slot code observable `D`;
* the two-step Lefschetz operator `L^2`.

Native point-lift naturality for those two primitives automatically gives
native naturality for both projectors, their normalized composition, every
rank-free matrix unit after recoordination, and therefore the whole universal
arsenal.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicOperatorAlgebra
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeFiberedCosmology

namespace GSTClassicalHodgeTwoGeneratorNativeArsenal

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Invariant two-slot code observable `diag(0,1)`. -/
def twoSlotCode : Module.End ℚ (RationalPureWindow 2) where
  toFun a := fun r => (r.1 : ℚ) * a r
  map_add' := by intro a b; funext r; simp [mul_add]
  map_smul' := by intro q a; funext r; simp [mul_left_comm]

@[simp]
theorem twoSlotCode_source
    (a : RationalPureWindow 2) :
    twoSlotCode a sourceSlot = 0 := by
  simp [twoSlotCode, sourceSlot]

@[simp]
theorem twoSlotCode_target
    (a : RationalPureWindow 2) :
    twoSlotCode a targetSlot = a targetSlot := by
  simp [twoSlotCode, targetSlot]

/-- Target projector is exactly the code observable. -/
theorem sheetProjectorQ_target_eq_code :
    sheetProjectorQ targetSlot = twoSlotCode := by
  apply LinearMap.ext
  intro a
  funext r
  fin_cases r <;> simp [sheetProjectorQ, rationalPureBasis,
    twoSlotCode, sourceSlot, targetSlot]

/-- Source projector is identity minus the code observable. -/
theorem sheetProjectorQ_source_eq_id_sub_code :
    sheetProjectorQ sourceSlot = (LinearMap.id - twoSlotCode) := by
  apply LinearMap.ext
  intro a
  funext r
  fin_cases r <;> simp [sheetProjectorQ, rationalPureBasis,
    twoSlotCode, sourceSlot, targetSlot]

/-- Hodge-fiber lift of the two-slot code observable for an ordered basis pair. -/
noncomputable def twoSlotCodeHodge
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  twoSlotHodgeOperator i j twoSlotCode

/-- Ambient extension of the code observable. -/
noncomputable def ambientTwoSlotCode
    (i j : ClassicalHodgeBasisIndex V H p) :=
  extendHodgeEndomorphism (V:=V) (H:=H) (twoSlotCodeHodge i j)

/-- The target projector ambient action agrees with the ambient code observable
on the genuine Hodge fiber. -/
theorem ambientTargetProjector_on_hodge_eq_code
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ambientTargetProjector i j alpha.1 =
      ambientTwoSlotCode i j alpha.1 := by
  unfold ambientTargetProjector ambientTwoSlotCode twoSlotCodeHodge
  rw [sheetProjectorQ_target_eq_code]

/-- The source projector ambient action agrees with identity minus the code
observable on Hodge classes supported in the two selected basis sheets. -/
theorem ambientSourceProjector_on_hodge_eq_id_sub_code
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p)
    (hspan : alpha =
        (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeCoordinate i alpha) •
          classicalHodgeBasis V H p i
      + (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeCoordinate j alpha) •
          classicalHodgeBasis V H p j) :
    ambientSourceProjector i j alpha.1 =
      alpha.1 - ambientTwoSlotCode i j alpha.1 := by
  have hround : finiteHodgeWrite (pairBasisIndex i j)
      (finiteHodgeRead (pairBasisIndex i j) alpha) = alpha := by
    have h1 : finiteHodgeWrite (pairBasisIndex i j)
        (finiteHodgeRead (pairBasisIndex i j) alpha) =
        (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeCoordinate i alpha) •
          classicalHodgeBasis V H p i
      + (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeCoordinate j alpha) •
          classicalHodgeBasis V H p j := by
      simp [finiteHodgeWrite, finiteHodgeRead, pairBasisIndex,
        sourceSlot, targetSlot]
    rw [h1]
    exact hspan.symm
  unfold ambientSourceProjector ambientTwoSlotCode twoSlotCodeHodge
  rw [extendHodgeEndomorphism_on_hodge (twoSlotHodgeOperator i j
      (sheetProjectorQ sourceSlot)) alpha,
    extendHodgeEndomorphism_on_hodge (twoSlotHodgeOperator i j twoSlotCode)
      alpha,
    sheetProjectorQ_source_eq_id_sub_code]
  have hkey : twoSlotHodgeOperator i j (LinearMap.id - twoSlotCode) alpha
      + twoSlotHodgeOperator i j twoSlotCode alpha = alpha := by
    show (finiteHodgeWrite (pairBasisIndex i j))
        (finiteHodgeRead (pairBasisIndex i j) alpha
          - twoSlotCode (finiteHodgeRead (pairBasisIndex i j) alpha))
      + (finiteHodgeWrite (pairBasisIndex i j))
        (twoSlotCode (finiteHodgeRead (pairBasisIndex i j) alpha)) = alpha
    rw [← LinearMap.map_add (finiteHodgeWrite (pairBasisIndex i j)),
      sub_add_cancel]
    exact hround
  have hval : (twoSlotHodgeOperator i j (LinearMap.id - twoSlotCode) alpha).1
      + (twoSlotHodgeOperator i j twoSlotCode alpha).1 = alpha.1 :=
    congrArg Subtype.val hkey
  rw [← hval]
  simp

/-- Native point-lift realization of the two minimal noncommuting primitives. -/
structure TwoGeneratorNative
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientTwoSlotCode i j)
  lefschetz : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientTwoStepLefschetz i j)

namespace TwoGeneratorNative

/-- Identity-minus-code is native-natural. -/
theorem idSubCode_nativePointLifts
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : TwoGeneratorNative (V:=V) (H:=H) i j) :
    HasNativePointLifts (p:=p) (cl:=H.cycleClass p)
      (LinearMap.id - ambientTwoSlotCode i j) := by
  rw [← smoothProjective_atomicStable_iff_nativePointLifts]
  exact atomicSpanStable_sub atomicSpanStable_id
    ((smoothProjective_atomicStable_iff_nativePointLifts
      (ambientTwoSlotCode i j)).2 R.code)

/-- The code observable itself gives the target projector naturality. -/
theorem targetProjector_nativePointLifts_on_hodge
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : TwoGeneratorNative (V:=V) (H:=H) i j) :
    HasNativePointLifts (p:=p) (cl:=H.cycleClass p)
      (ambientTwoSlotCode i j) :=
  R.code

/-- The two-generator data supply native naturality for the algebraic word
`D ∘ L² ∘ (I-D)`, the universal rank-one transfer on the Hodge fiber. -/
theorem codeLefschetzCodeWord_nativePointLifts
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : TwoGeneratorNative (V:=V) (H:=H) i j) :
    HasNativePointLifts (p:=p) (cl:=H.cycleClass p)
      ((ambientTwoSlotCode i j).comp
        ((ambientTwoStepLefschetz i j).comp
          (LinearMap.id - ambientTwoSlotCode i j))) := by
  exact nativePointLifts_comp R.code
    (nativePointLifts_comp R.lefschetz R.idSubCode_nativePointLifts)

/-- Rational normalization preserves native point lifts, giving the complete
normalized universal transfer word. -/
theorem normalizedWord_nativePointLifts
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : TwoGeneratorNative (V:=V) (H:=H) i j) :
    HasNativePointLifts (p:=p) (cl:=H.cycleClass p)
      ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
        ((ambientTwoSlotCode i j).comp
          ((ambientTwoStepLefschetz i j).comp
            (LinearMap.id - ambientTwoSlotCode i j)))) := by
  exact GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts.smul
    ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹)
    R.codeLefschetzCodeWord_nativePointLifts

end TwoGeneratorNative

#check twoSlotCode
#check sheetProjectorQ_target_eq_code
#check sheetProjectorQ_source_eq_id_sub_code
#check twoSlotCodeHodge
#check ambientTwoSlotCode
#check TwoGeneratorNative
#check TwoGeneratorNative.idSubCode_nativePointLifts
#check TwoGeneratorNative.codeLefschetzCodeWord_nativePointLifts
#check TwoGeneratorNative.normalizedWord_nativePointLifts

#print axioms sheetProjectorQ_target_eq_code
#print axioms sheetProjectorQ_source_eq_id_sub_code
#print axioms TwoGeneratorNative.codeLefschetzCodeWord_nativePointLifts
#print axioms TwoGeneratorNative.normalizedWord_nativePointLifts

end GSTClassicalHodgeTwoGeneratorNativeArsenal
