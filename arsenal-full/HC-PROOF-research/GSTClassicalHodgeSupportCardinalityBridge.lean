import GSTClassicalHodgeLiveSheetIntertwining
import GSTClassicalHodgeFiniteSupportArsenalConjugation
import GSTClassicalHodgeFiberedCosmology

/-!
# GST CLASSICAL HODGE — SUPPORT CARDINALITY BRIDGE

The classical finite-support machinery historically introduced two live-index
types:

* `HodgeSupportIndex alpha`, the support of the chosen basis coordinates of a
  genuine weight-p Hodge class;
* `LiveFiberedAddress (fiberedWeightCoordinates ... alpha)`, the support after
  embedding those coordinates into the total limitless fibered address space.

They are the same finite set with a weight label attached.  This module gives
the explicit equivalence, proves equality of their cardinalities, and aligns
the two canonical `Fin N` enumerations.  Consequently the integral pure-square
sheet index and the rank-free classical live-basis index refer to the same
multiplicity direction.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeLiveSheetIntertwining
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeSquareStrandLocalization

namespace GSTClassicalHodgeSupportCardinalityBridge

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Attach the fixed Hodge weight to one live classical basis index. -/
noncomputable def toLiveFibered
    (alpha : ClassicalHodgeFiber V H p) :
    HodgeSupportIndex alpha →
      LiveFiberedAddress (fiberedWeightCoordinates V H p alpha) :=
  liveFiberedAddress alpha

/-- Every live fibered address carries a genuine classical basis index whose
embedded address is exactly it. -/
theorem liveFiberedAddress_witness
    (alpha : ClassicalHodgeFiber V H p)
    (s : LiveFiberedAddress (fiberedWeightCoordinates V H p alpha)) :
    ∃ idx : ClassicalHodgeBasisIndex V H p,
      idx ∈ ((classicalHodgeBasis V H p).repr alpha).support ∧
        (⟨p, idx⟩ : FiberedHodgeIndex V H) = s.1 := by
  rcases s with ⟨⟨q, i⟩, hs⟩
  have hsup : fiberedWeightCoordinates V H p alpha
      (⟨q, i⟩ : FiberedHodgeIndex V H) ≠ 0 :=
    Finsupp.mem_support_iff.mp hs
  by_cases hqp : q = p
  · subst q
    have hval : fiberedWeightCoordinates V H p alpha
        (⟨p, i⟩ : FiberedHodgeIndex V H)
        = (classicalHodgeBasis V H p).repr alpha i :=
      Finsupp.embDomain_apply_self (weightFiberEmbedding V H p)
        ((classicalHodgeBasis V H p).repr alpha) i
    rw [hval] at hsup
    exact ⟨i, Finsupp.mem_support_iff.mpr hsup, rfl⟩
  · exfalso
    apply hsup
    simp only [fiberedWeightCoordinates, weightFiberEmbedding]
    apply Finsupp.embDomain_of_notMem_range
    intro hm
    rcases hm with ⟨a, ha⟩
    have ha' : (⟨p, a⟩ : FiberedHodgeIndex V H) = ⟨q, i⟩ := ha
    injection ha' with hp _
    exact hqp hp.symm

/-- Remove the fixed weight label from one live fibered address. -/
noncomputable def fromLiveFibered
    (alpha : ClassicalHodgeFiber V H p) :
    LiveFiberedAddress (fiberedWeightCoordinates V H p alpha) →
      HodgeSupportIndex alpha :=
  fun s =>
    ⟨Classical.choose (liveFiberedAddress_witness alpha s),
     (Classical.choose_spec (liveFiberedAddress_witness alpha s)).1⟩

/-- The classical witness of a live fibered address embeds back to it. -/
theorem fromLiveFibered_apply
    (alpha : ClassicalHodgeFiber V H p)
    (s : LiveFiberedAddress (fiberedWeightCoordinates V H p alpha)) :
    (⟨p, (fromLiveFibered alpha s).1⟩ : FiberedHodgeIndex V H) = s.1 :=
  (Classical.choose_spec (liveFiberedAddress_witness alpha s)).2

theorem fromLiveFibered_toLiveFibered
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    fromLiveFibered alpha (toLiveFibered alpha i) = i := by
  apply Subtype.ext
  have h1 := fromLiveFibered_apply alpha (toLiveFibered alpha i)
  have h2 : (toLiveFibered alpha i).1
      = (⟨p, i.1⟩ : FiberedHodgeIndex V H) := rfl
  rw [h2] at h1
  injection h1 with _ heq

theorem toLiveFibered_fromLiveFibered
    (alpha : ClassicalHodgeFiber V H p)
    (s : LiveFiberedAddress (fiberedWeightCoordinates V H p alpha)) :
    toLiveFibered alpha (fromLiveFibered alpha s) = s := by
  apply Subtype.ext
  have h3 : (toLiveFibered alpha (fromLiveFibered alpha s)).1
      = (⟨p, (fromLiveFibered alpha s).1⟩ : FiberedHodgeIndex V H) := rfl
  rw [h3, fromLiveFibered_apply alpha s]

/-- The two live-support types are canonically equivalent. -/
noncomputable def hodgeSupportEquivFibered
    (alpha : ClassicalHodgeFiber V H p) :
    HodgeSupportIndex alpha ≃
      LiveFiberedAddress (fiberedWeightCoordinates V H p alpha) where
  toFun := toLiveFibered alpha
  invFun := fromLiveFibered alpha
  left_inv := fromLiveFibered_toLiveFibered alpha
  right_inv := toLiveFibered_fromLiveFibered alpha

/-- The classical live rank and fibered support size are exactly equal. -/
theorem liveRank_eq_fiberedSupportSize
    (alpha : ClassicalHodgeFiber V H p) :
    liveRank alpha =
      fiberedSupportSize (fiberedWeightCoordinates V H p alpha) := by
  unfold liveRank fiberedSupportSize
  exact Fintype.card_congr (hodgeSupportEquivFibered alpha)

/-- Canonical reindexing between the two `Fin` presentations. -/
noncomputable def liveFinEquivFiberedFin
    (alpha : ClassicalHodgeFiber V H p) :
    Fin (liveRank alpha) ≃
      Fin (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)) :=
  finCongr (liveRank_eq_fiberedSupportSize alpha)

/-- A classical live slot and its corresponding fibered slot select the same
underlying genuine Hodge basis index. -/
theorem liveBasisIndex_fibered
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    let i := (liveEquivFin alpha).symm r
    liveSheetIndex alpha i =
      fiberedSupportEquivFin (fiberedWeightCoordinates V H p alpha)
        (hodgeSupportEquivFibered alpha i) := by
  rfl

/-- Every classical live slot therefore has a unique integral-square sheet. -/
noncomputable def squareSheetOfLiveSlot
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    Fin (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)) :=
  liveSheetIndex alpha ((liveEquivFin alpha).symm r)

/-- The integral-square coefficient at the corresponding sheet is the genuine
classical basis coefficient selected by the rank-free live slot. -/
theorem supportDiagonalWorld_squareSheetOfLiveSlot
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    supportDiagonalWorld (fiberedWeightCoordinates V H p alpha)
        (squareSheetOfLiveSlot alpha r, squareSheetOfLiveSlot alpha r) =
      (classicalHodgeBasis V H p).repr alpha (liveBasisIndex alpha r) := by
  unfold squareSheetOfLiveSlot liveBasisIndex
  exact supportDiagonalWorld_liveSheet alpha ((liveEquivFin alpha).symm r)

/-- After denominator clearing the same corresponding square sheet remains
nonzero. -/
theorem integralHodgeSquare_squareSheet_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    (integralHodgeSquare alpha).world
      (squareSheetOfLiveSlot alpha r, squareSheetOfLiveSlot alpha r) ≠ 0 := by
  unfold squareSheetOfLiveSlot
  exact integralHodgeSquare_liveSheet_ne_zero alpha
    ((liveEquivFin alpha).symm r)

#check toLiveFibered
#check fromLiveFibered
#check hodgeSupportEquivFibered
#check liveRank_eq_fiberedSupportSize
#check liveFinEquivFiberedFin
#check squareSheetOfLiveSlot
#check supportDiagonalWorld_squareSheetOfLiveSlot
#check integralHodgeSquare_squareSheet_ne_zero

#print axioms hodgeSupportEquivFibered
#print axioms liveRank_eq_fiberedSupportSize
#print axioms supportDiagonalWorld_squareSheetOfLiveSlot
#print axioms integralHodgeSquare_squareSheet_ne_zero

end GSTClassicalHodgeSupportCardinalityBridge
