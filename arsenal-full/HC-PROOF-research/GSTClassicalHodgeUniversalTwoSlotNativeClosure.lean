import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeUniversalTwoSlotSaturation
import GSTClassicalHodgeAtomicOperatorAlgebra
import GSTClassicalHodgeCanonicalAmbientArsenal
import GSTClassicalHodgeExplicitArsenalGeneration

/-!
# GST CLASSICAL HODGE — UNIVERSAL TWO-SLOT NATIVE CLOSURE

Every rank-free Hodge matrix unit is the lift of the same finite two-slot GST
word.  This module pushes that compression through the native point-cycle
naturality calculus.

For an ordered pair `(i,j)` of genuine Hodge basis directions, the selected
2-slot Hodge fiber carries three primitive finite operators:

* source projector `P_0`;
* the actual rationalized GST Lefschetz step `L^2`;
* target projector `P_1`.

Their normalized composition is `forwardArsenalWord 0 1`, hence exactly the
rank-free matrix unit `E_{i,j}` after finite read/write conjugation.

Each primitive is extended linearly from the Hodge subspace to ambient
cohomology.  If the three ambient primitives admit native point lifts, the
existing atomic-operator algebra closes the property under composition and
rational scaling, yielding native naturality for the entire universal word.
Thus the unrestricted arsenal externalization reduces to three primitive
geometric point-transition laws in one universal 2-slot chart.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicOperatorAlgebra
open GSTClassicalHodgeNativeGeneratorNaturality

namespace GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh (H : HodgeBigradedBettiData V) (p : Nat) : Type _ :=
  RationalSingularCohomology H.analytification (2 * p)
abbrev HFiber (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) : Type _ :=
  ClassicalHodgeFiber V H p

/-- Extend an arbitrary endomorphism of the genuine Hodge fiber to ambient
rational cohomology. -/
noncomputable def extendHodgeEndomorphism
    (T : Module.End ℚ (HFiber V H p)) :
    Coh H p →ₗ[ℚ] Coh H p :=
  Classical.choose
    (LinearMap.exists_extend
      ((rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp T))

/-- Exact restriction law of the ambient extension. -/
theorem extendHodgeEndomorphism_on_hodge
    (T : Module.End ℚ (HFiber V H p))
    (alpha : HFiber V H p) :
    extendHodgeEndomorphism (V:=V) (H:=H) T alpha.1 = (T alpha).1 := by
  have h := Classical.choose_spec
    (LinearMap.exists_extend
      ((rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp T))
  exact LinearMap.congr_fun h alpha

/-- Lift one finite 2-slot GST operator to the genuine Hodge fiber for the
ordered basis pair `(i,j)`. -/
noncomputable def twoSlotHodgeOperator
    (i j : ClassicalHodgeBasisIndex V H p)
    (T : Module.End ℚ (RationalPureWindow 2)) :
    Module.End ℚ (HFiber V H p) :=
  liftFiniteHodgeOperator (pairBasisIndex i j) T

/-- Ambient source projector. -/
noncomputable def ambientSourceProjector
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  extendHodgeEndomorphism (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot))

/-- Ambient two-step GST Lefschetz primitive. -/
noncomputable def ambientTwoStepLefschetz
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  extendHodgeEndomorphism (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))

/-- Ambient target projector. -/
noncomputable def ambientTargetProjector
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  extendHodgeEndomorphism (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))

/-- Ambient normalized universal 2-slot word, assembled from the three
primitive ambient operators. -/
noncomputable def ambientUniversalTwoSlotWord
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    ((ambientTargetProjector i j).comp
      ((ambientTwoStepLefschetz i j).comp
        (ambientSourceProjector i j)))

/-- On the genuine Hodge fiber, the ambient universal word is exactly the
rank-free matrix unit. -/
theorem ambientUniversalTwoSlotWord_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p) (hij : i ≠ j)
    (alpha : HFiber V H p) :
    ambientUniversalTwoSlotWord i j alpha.1 =
      (hodgeMatrixUnit i j alpha).1 := by
  have hword :
      forwardArsenalWord sourceSlot targetSlot =
        pureMatrixUnit sourceSlot targetSlot :=
    forwardArsenalWord_eq_matrixUnit sourceSlot targetSlot (by decide)
  have hlift :
      liftFiniteHodgeOperator (pairBasisIndex i j)
          (forwardArsenalWord sourceSlot targetSlot) =
        hodgeMatrixUnit i j := by
    exact rankFreeMatrixUnit_eq_lifted_GST_word i j |>.symm
  have hsrc := extendHodgeEndomorphism_on_hodge
    (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha
  have hL := extendHodgeEndomorphism_on_hodge
    (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
    ((twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha)
  have htgt := extendHodgeEndomorphism_on_hodge
    (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))
    ((twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
      ((twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha))
  change _ = _
  rw [ambientUniversalTwoSlotWord]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply,
    ambientSourceProjector, ambientTwoStepLefschetz, ambientTargetProjector]
  rw [hsrc, hL, htgt]
  change
    ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
      (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))
        ((twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
          ((twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha))).1 = _
  have h01 : hodgeCoordinate i (classicalHodgeBasis V H p j) = 0 :=
    hodgeCoordinate_basis_other i j hij
  have h10 : hodgeCoordinate j (classicalHodgeBasis V H p i) = 0 :=
    hodgeCoordinate_basis_other j i (Ne.symm hij)
  have hrw : ∀ w : RationalPureWindow 2,
      finiteHodgeRead (pairBasisIndex i j)
        (finiteHodgeWrite (pairBasisIndex i j) w) = w := by
    intro w
    funext r
    fin_cases r
    · simp [finiteHodgeRead, finiteHodgeWrite, sourceSlot, targetSlot,
        pairBasisIndex, h01]
    · simp [finiteHodgeRead, finiteHodgeWrite, sourceSlot, targetSlot,
        pairBasisIndex, h10]
  have hfinite :
      ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
        ((sheetProjectorQ targetSlot).comp
          ((diagonalLefschetzQ 2 2).comp
            (sheetProjectorQ sourceSlot)))) =
      forwardArsenalWord sourceSlot targetSlot := by
    rfl
  have hLval : (GSTTruncatedWorldCohomologyRing.worldAct 2 2
      ((GSTTruncatedWorldCohomologyRing.L 2 2) ^ 2)
      (GSTWorldPoincareDuality.worldBasis
        (GSTGlobalPureHodgeCosmology.pureDiagonalState (0 : Fin 2)))
      (GSTGlobalPureHodgeCosmology.pureDiagonalState (1 : Fin 2))) =
      (2 : ℤ) :=
    gst_forward_scalar_receipt (N := 2) (p := sourceSlot) (q := targetSlot) (by decide)
  have hfs : (forwardScalar (N := 2) (0 : Fin 2) (1 : Fin 2) : ℚ) = 2 := by
    exact_mod_cast (show forwardScalar (N := 2) (0 : Fin 2) (1 : Fin 2) = 2 from by decide)
  simp [twoSlotHodgeOperator, liftFiniteHodgeOperator, finiteHodgeRead,
    finiteHodgeWrite, hfinite, hlift, pureMatrixUnit, rationalPureBasis,
    diagonalLefschetzQ, sheetProjectorQ, hodgeMatrixUnit_apply,
    sourceSlot, targetSlot, hrw, pairBasisIndex, h01, h10,
    hodgeCoordinate_basis_self, hLval,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply]
  rw [hfs]
  norm_num
  rw [one_div, smul_smul, mul_comm _ 2,
    inv_mul_cancel_left₀ (by norm_num : ((2:ℚ) ≠ 0))]

/-- Primitive native-natural data for the universal two-slot machine. -/
structure PrimitiveNativeTwoSlot
    (i j : ClassicalHodgeBasisIndex V H p) where
  source : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientSourceProjector i j)
  lefschetz : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientTwoStepLefschetz i j)
  target : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientTargetProjector i j)

namespace PrimitiveNativeTwoSlot

/-- Native point-lift naturality of the complete universal word follows from
the three primitive point-lift laws. -/
theorem universalWord_nativePointLifts
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : PrimitiveNativeTwoSlot (V:=V) (H:=H) i j) :
    HasNativePointLifts (p:=p) (cl:=H.cycleClass p)
      (ambientUniversalTwoSlotWord i j) := by
  unfold ambientUniversalTwoSlotWord
  apply GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts.smul
  apply nativePointLifts_comp R.target
  exact nativePointLifts_comp R.lefschetz R.source

/-- The full universal two-slot word therefore preserves the entire atomic
cycle-class span. -/
theorem universalWord_atomicStable
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : PrimitiveNativeTwoSlot (V:=V) (H:=H) i j) :
    AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      (ambientUniversalTwoSlotWord i j) := by
  rw [smoothProjective_atomicStable_iff_nativePointLifts]
  exact R.universalWord_nativePointLifts

end PrimitiveNativeTwoSlot

#check extendHodgeEndomorphism
#check extendHodgeEndomorphism_on_hodge
#check twoSlotHodgeOperator
#check ambientSourceProjector
#check ambientTwoStepLefschetz
#check ambientTargetProjector
#check ambientUniversalTwoSlotWord
#check ambientUniversalTwoSlotWord_on_hodge
#check PrimitiveNativeTwoSlot
#check PrimitiveNativeTwoSlot.universalWord_nativePointLifts
#check PrimitiveNativeTwoSlot.universalWord_atomicStable

#print axioms extendHodgeEndomorphism_on_hodge
#print axioms ambientUniversalTwoSlotWord_on_hodge
#print axioms PrimitiveNativeTwoSlot.universalWord_nativePointLifts
#print axioms PrimitiveNativeTwoSlot.universalWord_atomicStable

end GSTClassicalHodgeUniversalTwoSlotNativeClosure
