import GSTClassicalHodgeTotalSheetMatrixUnit
import GSTClassicalHodgeSupportCardinalityBridge
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — CONCRETE ARSENAL CONJUGATION

The rank-free classical Hodge matrix units are now identified with actual GST
operator words.

For one genuine Hodge class `alpha`:

* `integralHodgeSquare alpha` clears denominators and embeds the exact live
  classical basis coefficients on the diagonal of one finite integral square;
* `squareSheetOfLiveSlot` identifies every rank-free live basis slot with its
  exact integral-square sheet;
* `totalSheetMatrixUnit` is the concrete projector/Lefschetz/Poincare word
  sending one source sheet to one target sheet;
* reading the rationalized result back through the genuine classical basis
  and dividing by the denominator-clearing scale yields exactly the abstract
  `hodgeMatrixUnit` action.

Thus the complete local matrix-unit pattern is not postulated: it is the
coordinate conjugate of the existing GST operator arsenal.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeIntegralSquareLocalization
open GSTClassicalHodgeSupportCardinalityBridge
open GSTClassicalHodgeLiveSheetIntertwining
open GSTClassicalHodgeSupportCardinalityBridge
open GSTClassicalHodgeTotalSheetMatrixUnit
open GSTClassicalHodgeRankFreeArsenalIrreducibility

namespace GSTClassicalHodgeConcreteArsenalConjugation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Distinct rank-free live slots determine distinct integral-square sheets. -/
theorem squareSheetOfLiveSlot_injective
    (alpha : ClassicalHodgeFiber V H p) :
    Function.Injective (squareSheetOfLiveSlot alpha) := by
  intro r s hrs
  unfold squareSheetOfLiveSlot at hrs
  have haddr :=
    (fiberedSupportEquivFin (fiberedWeightCoordinates V H p alpha)).injective hrs
  have hsupp :
      ((liveEquivFin alpha).symm r : HodgeSupportIndex alpha) =
        (liveEquivFin alpha).symm s := by
    apply Subtype.ext
    have hpair : (liveFiberedAddress alpha ((liveEquivFin alpha).symm r)).1 =
        (liveFiberedAddress alpha ((liveEquivFin alpha).symm s)).1 :=
      congrArg (fun x => x.1) haddr
    show ((liveEquivFin alpha).symm r : HodgeSupportIndex alpha).1 =
      ((liveEquivFin alpha).symm s : HodgeSupportIndex alpha).1
    have hr1 : ((liveEquivFin alpha).symm r : HodgeSupportIndex alpha).1 =
        (liveFiberedAddress alpha ((liveEquivFin alpha).symm r)).1.2 := rfl
    have hs1 : ((liveEquivFin alpha).symm s : HodgeSupportIndex alpha).1 =
        (liveFiberedAddress alpha ((liveEquivFin alpha).symm s)).1.2 := rfl
    rw [hr1, hs1]
    congr 1
  exact (liveEquivFin alpha).symm.injective hsupp

/-- Read a rational square state back into the genuine live Hodge-basis
coordinates of `alpha`. -/
noncomputable def readLiveSquare
    (alpha : ClassicalHodgeFiber V H p)
    (g : GSTClassicalHodgeConcreteSheetMatrixUnit.RationalSquareCoef
      (fiberedSupportSize (fiberedWeightCoordinates V H p alpha))) :
    ClassicalHodgeFiber V H p :=
  ∑ r : Fin (liveRank alpha),
    g (squareSheetOfLiveSlot alpha r, squareSheetOfLiveSlot alpha r) •
      liveBasisVector alpha r

/-- Reading one exact target sheet returns precisely its scalar multiple of the
corresponding genuine Hodge basis vector. -/
theorem readLiveSquare_single_target
    (alpha : ClassicalHodgeFiber V H p)
    (s : Fin (liveRank alpha))
    (q : ℚ) :
    readLiveSquare alpha
      (fun x => if x =
          (squareSheetOfLiveSlot alpha s, squareSheetOfLiveSlot alpha s)
        then q else 0) =
      q • liveBasisVector alpha s := by
  classical
  have key : ∀ r : Fin (liveRank alpha),
      (if (squareSheetOfLiveSlot alpha r, squareSheetOfLiveSlot alpha r) =
          (squareSheetOfLiveSlot alpha s, squareSheetOfLiveSlot alpha s)
        then q else 0) • liveBasisVector alpha r =
      (if r = s then q else 0) • liveBasisVector alpha r := by
    intro r
    by_cases h : r = s
    · subst h
      simp
    · have hsheet : squareSheetOfLiveSlot alpha r ≠
        squareSheetOfLiveSlot alpha s := by
        intro hsheeteq
        exact h (squareSheetOfLiveSlot_injective alpha hsheeteq)
      simp [hsheet, h]
  unfold readLiveSquare
  simp only [key]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [hts]
  · simp

/-- Concrete GST matrix-unit output read back through the genuine basis. -/
theorem readLiveSquare_totalMatrixUnit
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) :
    readLiveSquare alpha
      (totalSheetMatrixUnit
        (squareSheetOfLiveSlot alpha r)
        (squareSheetOfLiveSlot alpha s)
        (integralHodgeSquare alpha).world) =
      ((integralHodgeSquare alpha).world
        (squareSheetOfLiveSlot alpha r,
         squareSheetOfLiveSlot alpha r) : ℚ) •
        liveBasisVector alpha s := by
  rw [totalSheetMatrixUnit_exact
    (squareSheetOfLiveSlot alpha r)
    (squareSheetOfLiveSlot alpha s)
    (integralHodgeSquare alpha).world
    (integralHodgeSquare alpha).world_pure]
  exact readLiveSquare_single_target alpha s _

/-- Denominator clearing on the source square sheet is exactly the global
integral scale times the genuine source basis coefficient. -/
theorem integralSquare_source_coefficient
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    ((integralHodgeSquare alpha).world
        (squareSheetOfLiveSlot alpha r,
         squareSheetOfLiveSlot alpha r) : ℚ) =
      ((integralHodgeSquare alpha).scale : ℚ) *
        ((classicalHodgeBasis V H p).repr alpha (liveBasisIndex alpha r)) := by
  have hs := (integralHodgeSquare alpha).scaled_eq
    (squareSheetOfLiveSlot alpha r, squareSheetOfLiveSlot alpha r)
  rw [supportDiagonalWorld_squareSheetOfLiveSlot alpha r] at hs
  exact hs.symm

/-- The integral-square scaling factor is nonzero over `Q`. -/
theorem integralHodgeSquare_scale_ne_zero
    (alpha : ClassicalHodgeFiber V H p) :
    ((integralHodgeSquare alpha).scale : ℚ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt (integralHodgeSquare alpha).scale_pos

/-- Normalize the concrete GST matrix-unit output and read it back into the
genuine Hodge fiber. -/
noncomputable def concreteHodgeMatrixUnit
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) :
    ClassicalHodgeFiber V H p :=
  ((integralHodgeSquare alpha).scale : ℚ)⁻¹ •
    readLiveSquare alpha
      (totalSheetMatrixUnit
        (squareSheetOfLiveSlot alpha r)
        (squareSheetOfLiveSlot alpha s)
        (integralHodgeSquare alpha).world)

/-- **CONCRETE GST = RANK-FREE MATRIX UNIT.**  On every live source/target pair,
the normalized projector/Lefschetz/Poincare word is exactly the genuine
rank-free Hodge matrix unit applied to the original class. -/
theorem concreteHodgeMatrixUnit_eq
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha)) :
    concreteHodgeMatrixUnit alpha r s =
      hodgeMatrixUnit (liveBasisIndex alpha r) (liveBasisIndex alpha s) alpha := by
  unfold concreteHodgeMatrixUnit
  rw [readLiveSquare_totalMatrixUnit]
  rw [integralSquare_source_coefficient]
  have hscale := integralHodgeSquare_scale_ne_zero alpha
  rw [smul_smul]
  simp [hscale]
  unfold hodgeCoordinate liveBasisVector
  simp [liveBasisIndex]

/-- Every live GST matrix-unit calculation is therefore a concrete realization
of the corresponding rank-free classical matrix-unit value. -/
theorem concrete_full_arsenal_receipt
    (alpha : ClassicalHodgeFiber V H p) :
    ∀ r s : Fin (liveRank alpha),
      concreteHodgeMatrixUnit alpha r s =
        hodgeMatrixUnit (liveBasisIndex alpha r) (liveBasisIndex alpha s) alpha :=
  concreteHodgeMatrixUnit_eq alpha

#check squareSheetOfLiveSlot_injective
#check readLiveSquare
#check readLiveSquare_single_target
#check readLiveSquare_totalMatrixUnit
#check integralSquare_source_coefficient
#check concreteHodgeMatrixUnit
#check concreteHodgeMatrixUnit_eq
#check concrete_full_arsenal_receipt

#print axioms readLiveSquare_totalMatrixUnit
#print axioms integralSquare_source_coefficient
#print axioms concreteHodgeMatrixUnit_eq
#print axioms concrete_full_arsenal_receipt

end GSTClassicalHodgeConcreteArsenalConjugation
