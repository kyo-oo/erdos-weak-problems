import GSTClassicalHodgeConcreteArsenalConjugation
import GSTClassicalHodgeIntegralSquareLocalization
import GSTClassicalHodgeTotalSheetMatrixUnit

/-!
# GST CLASSICAL HODGE — AUGMENTED TARGET WINDOWS

A genuine Hodge class has finite basis support, but the rank-free limitless
arsenal must be able to send one live source coordinate to an arbitrary basis
direction which need not already occur in that support.

The correct finite observation is therefore not merely the live support.  For
one requested target basis index `j`, adjoin `j` to the finite support and use
that finite union as the observation window.  The source coefficients are the
actual basis coordinates of the original class; the newly adjoined target may
initially carry coefficient zero.  Denominator clearing embeds the resulting
finite rational vector on the diagonal of an integral GST square.

The existing total sheet matrix unit can then move a nonzero live source into
the arbitrary target slot.  This is the finite-observation mechanism needed
to upgrade local live-support generation to unrestricted rank-free
generation.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeIntegralSquareLocalization
open GSTClassicalHodgeTotalSheetMatrixUnit
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeSquareStrandLocalization

namespace GSTClassicalHodgeAugmentedTargetWindow

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Finite support of `alpha` with one arbitrary target basis direction
adjoined, whether or not it is already live. -/
def augmentedSupport
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    Finset (ClassicalHodgeBasisIndex V H p) :=
  insert j ((classicalHodgeBasis V H p).repr alpha).support

/-- Finite index type of the augmented observation window. -/
abbrev AugmentedIndex
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :=
  {i : ClassicalHodgeBasisIndex V H p // i ∈ augmentedSupport alpha j}

/-- Size of the augmented finite observation. -/
def augmentedRank
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) : Nat :=
  Fintype.card (AugmentedIndex alpha j)

/-- Canonical enumeration of the augmented observation by `Fin N`. -/
noncomputable def augmentedEquivFin
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    AugmentedIndex alpha j ≃ Fin (augmentedRank alpha j) :=
  Fintype.equivFin (AugmentedIndex alpha j)

/-- Global Hodge-basis index at one augmented finite slot. -/
noncomputable def augmentedBasisIndex
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (r : Fin (augmentedRank alpha j)) :
    ClassicalHodgeBasisIndex V H p :=
  ((augmentedEquivFin alpha j).symm r).1

/-- The requested arbitrary target is always a member of the augmented
window. -/
def targetAugmentedIndex
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    AugmentedIndex alpha j :=
  ⟨j, by simp [augmentedSupport]⟩

/-- Finite slot occupied by the arbitrary requested target. -/
noncomputable def targetSlot
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    Fin (augmentedRank alpha j) :=
  augmentedEquivFin alpha j (targetAugmentedIndex alpha j)

@[simp]
theorem augmentedBasisIndex_targetSlot
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    augmentedBasisIndex alpha j (targetSlot alpha j) = j := by
  simp [augmentedBasisIndex, targetSlot, targetAugmentedIndex]

/-- Every actually live support index embeds in the augmented observation. -/
def liveToAugmented
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    AugmentedIndex alpha j :=
  ⟨i.1, by
    simp only [augmentedSupport, Finset.mem_insert]
    exact Or.inr i.2⟩

/-- Finite slot of one genuinely live source direction in the augmented
window. -/
noncomputable def liveSourceSlot
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    Fin (augmentedRank alpha j) :=
  augmentedEquivFin alpha j (liveToAugmented alpha j i)

@[simp]
theorem augmentedBasisIndex_liveSourceSlot
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    augmentedBasisIndex alpha j (liveSourceSlot alpha j i) = i.1 := by
  simp [augmentedBasisIndex, liveSourceSlot, liveToAugmented]

/-- Rational coefficient vector on the augmented finite observation.  Existing
support coordinates retain their exact values; the adjoined target receives
its genuine current coefficient, which may be zero. -/
noncomputable def augmentedCoordinateVector
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    Fin (augmentedRank alpha j) → ℚ :=
  fun r => (classicalHodgeBasis V H p).repr alpha
    (augmentedBasisIndex alpha j r)

/-- A live source keeps its original nonzero coefficient in the augmented
window. -/
theorem augmentedCoordinate_liveSource
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    augmentedCoordinateVector alpha j (liveSourceSlot alpha j i) =
      (classicalHodgeBasis V H p).repr alpha i.1 := by
  simp [augmentedCoordinateVector]

/-- In particular every embedded live source is nonzero. -/
theorem augmentedCoordinate_liveSource_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    augmentedCoordinateVector alpha j (liveSourceSlot alpha j i) ≠ 0 := by
  rw [augmentedCoordinate_liveSource]
  exact support_coefficient_ne_zero alpha i

/-- Pure rational square carrying the augmented coordinate vector on its
diagonal. -/
def augmentedRationalSquare
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    RationalWorldCoef (augmentedRank alpha j) :=
  fun x => if x.1 = x.2 then augmentedCoordinateVector alpha j x.1 else 0

/-- The augmented rational square is pure Hodge. -/
theorem augmentedRationalSquare_isPure
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :
    IsRationalPureHodge (augmentedRationalSquare alpha j) := by
  intro x hx
  have hne : x.1 ≠ x.2 := by
    intro h
    exact hx (congrArg Fin.val h)
  simp [augmentedRationalSquare, hne]

/-- Canonical integral GST square of the augmented observation. -/
noncomputable def augmentedIntegralSquare
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p) :=
  canonicalIntegralPureSquareModel
    (augmentedRationalSquare alpha j)
    (augmentedRationalSquare_isPure alpha j)

/-- Exact denominator-clearing formula on every augmented diagonal slot. -/
theorem augmentedIntegralSquare_diagonal
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (r : Fin (augmentedRank alpha j)) :
    ((augmentedIntegralSquare alpha j).world (r,r) : ℚ) =
      ((augmentedIntegralSquare alpha j).scale : ℚ) *
        augmentedCoordinateVector alpha j r := by
  have h := (augmentedIntegralSquare alpha j).scaled_eq (r,r)
  refine h.symm.trans ?_
  simp [augmentedRationalSquare]

/-- A genuinely live source remains nonzero in the augmented integral square. -/
theorem augmentedIntegralSquare_liveSource_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex alpha) :
    (augmentedIntegralSquare alpha j).world
      (liveSourceSlot alpha j i, liveSourceSlot alpha j i) ≠ 0 := by
  intro hz
  have hdiag := augmentedIntegralSquare_diagonal alpha j
    (liveSourceSlot alpha j i)
  rw [hz] at hdiag
  simp at hdiag
  have hscale : (augmentedIntegralSquare alpha j).scale ≠ 0 :=
    Nat.ne_of_gt (augmentedIntegralSquare alpha j).scale_pos
  exact (augmentedCoordinate_liveSource_ne_zero alpha j i)
    (hdiag.resolve_left hscale)

/-- Read a rational augmented square back into the corresponding genuine Hodge
basis directions. -/
noncomputable def readAugmentedSquare
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (g : GSTClassicalHodgeConcreteSheetMatrixUnit.RationalSquareCoef
      (augmentedRank alpha j)) :
    ClassicalHodgeFiber V H p :=
  ∑ r : Fin (augmentedRank alpha j),
    g (r,r) • classicalHodgeBasis V H p (augmentedBasisIndex alpha j r)

/-- Exact readback of a single augmented target sheet. -/
theorem readAugmentedSquare_target
    (alpha : ClassicalHodgeFiber V H p)
    (j : ClassicalHodgeBasisIndex V H p)
    (q : ℚ) :
    readAugmentedSquare alpha j
      (fun x => if x = (targetSlot alpha j, targetSlot alpha j)
        then q else 0) =
      q • classicalHodgeBasis V H p j := by
  classical
  unfold readAugmentedSquare
  rw [Finset.sum_eq_single (targetSlot alpha j)]
  · simp
  · intro r hr hrne
    have hpair : (r,r) ≠ (targetSlot alpha j, targetSlot alpha j) := by
      intro h
      exact hrne (congrArg Prod.fst h)
    simp [hpair]
  · simp

#check augmentedSupport
#check AugmentedIndex
#check augmentedRank
#check augmentedEquivFin
#check augmentedBasisIndex
#check targetSlot
#check liveSourceSlot
#check augmentedCoordinateVector
#check augmentedRationalSquare
#check augmentedIntegralSquare
#check augmentedIntegralSquare_liveSource_ne_zero
#check readAugmentedSquare
#check readAugmentedSquare_target

#print axioms augmentedBasisIndex_targetSlot
#print axioms augmentedCoordinate_liveSource_ne_zero
#print axioms augmentedIntegralSquare_diagonal
#print axioms augmentedIntegralSquare_liveSource_ne_zero
#print axioms readAugmentedSquare_target

end GSTClassicalHodgeAugmentedTargetWindow
