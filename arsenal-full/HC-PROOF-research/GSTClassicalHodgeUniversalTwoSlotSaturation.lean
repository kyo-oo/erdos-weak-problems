import GSTClassicalHodgeRankFreePrimitiveGeneration
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — UNIVERSAL TWO-SLOT SATURATION

Every rank-free Hodge matrix unit is the recoordination lift of the same
2x2 GST operator word.  Consequently the full irreducibility hypothesis can
be compressed to stability under this *single universal local machine* for
every ordered pair of classical Hodge-basis directions.

This is substantially stronger than assuming invariance under arbitrary
matrix units: the only operator whose geometric externalization remains is

  forwardArsenalWord 0 1

which is already explicitly the normalized word `P_1 L^2 P_0` in the native
finite GST arsenal.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration

namespace GSTClassicalHodgeUniversalTwoSlotSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Stability under the single universal 2x2 GST transfer word after arbitrary
recoordination of two genuine Hodge-basis directions into source/target slots. -/
def UniversalTwoSlotInvariant
    (S : Submodule ℚ (ClassicalHodgeFiber V H p)) : Prop :=
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∀ alpha ∈ S,
      liftFiniteHodgeOperator (pairBasisIndex i j)
          (forwardArsenalWord sourceSlot targetSlot) alpha ∈ S

/-- **ONE UNIVERSAL GST WORD GENERATES FULL RANK-FREE INVARIANCE.** -/
theorem universalTwoSlotInvariant_rankFree
    (S : Submodule ℚ (ClassicalHodgeFiber V H p))
    (h : UniversalTwoSlotInvariant S) :
    RankFreeArsenalInvariant S := by
  intro i j alpha halpha
  rw [rankFreeMatrixUnit_eq_lifted_GST_word i j]
  exact h i j alpha halpha

/-- Any nonzero Hodge submodule stable under the universal two-slot machine is
the whole unrestricted Hodge fiber. -/
theorem universalTwoSlotInvariant_eq_top
    (S : Submodule ℚ (ClassicalHodgeFiber V H p))
    (h : UniversalTwoSlotInvariant S)
    (hne : S ≠ ⊥) :
    S = ⊤ :=
  rankFreeArsenalInvariant_eq_top S
    (universalTwoSlotInvariant_rankFree S h) hne

/-- Apply the universal two-slot saturation directly to the actual algebraic
Hodge subspace. -/
theorem algebraicHodgeSubspace_eq_top_of_twoSlot
    (htransport : UniversalTwoSlotInvariant
      (AlgebraicHodgeSubspace V H p))
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    AlgebraicHodgeSubspace V H p = ⊤ :=
  universalTwoSlotInvariant_eq_top
    (AlgebraicHodgeSubspace V H p) htransport hseed

/-- Under universal two-slot transport plus one nonzero algebraic seed, the
atomic defect in one weight vanishes. -/
theorem atomicDefect_eq_zero_of_twoSlot
    (htransport : UniversalTwoSlotInvariant
      (AlgebraicHodgeSubspace V H p))
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p = 0 := by
  apply GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap_eq_zero_iff V H p |>.2
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have htop := algebraicHodgeSubspace_eq_top_of_twoSlot
    (V := V) (H := H) (p := p) htransport hseed
  have ha : alphaH ∈ AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  exact ha

/-- Family crown in universal-machine form. -/
theorem bigradedBettiHodge_of_universalTwoSlot
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (htransport : ∀ p : Nat,
      UniversalTwoSlotInvariant (AlgebraicHodgeSubspace V H p))
    (hseed : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
      AlgebraicHodgeSubspace V H p ≠ ⊥) :
    BigradedBettiHodgeStatement V H := by
  apply GSTClassicalHodgeAtomicDefectDuality.bigradedBettiHodgeStatement_iff_atomicDefect_zero V H |>.2
  intro p
  by_cases hH : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · apply LinearMap.ext
    intro alpha
    have ha : alpha = 0 := by
      apply Subtype.ext
      have : alpha.1 ∈ (⊥ : Submodule ℚ
        (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hH] using alpha.2
      simpa using this
    subst alpha
    simp
  · exact atomicDefect_eq_zero_of_twoSlot
      (V := V) (H := H) (p := p)
      (htransport p) (hseed p hH)

/-- Universal two-slot compression receipt. -/
theorem universal_two_slot_saturation_crown :
    ∀ (S : Submodule ℚ (ClassicalHodgeFiber V H p)),
      UniversalTwoSlotInvariant S → S ≠ ⊥ → S = ⊤ :=
  universalTwoSlotInvariant_eq_top

#check UniversalTwoSlotInvariant
#check universalTwoSlotInvariant_rankFree
#check universalTwoSlotInvariant_eq_top
#check algebraicHodgeSubspace_eq_top_of_twoSlot
#check bigradedBettiHodge_of_universalTwoSlot
#check universal_two_slot_saturation_crown

#print axioms universalTwoSlotInvariant_rankFree
#print axioms universalTwoSlotInvariant_eq_top
#print axioms algebraicHodgeSubspace_eq_top_of_twoSlot
#print axioms bigradedBettiHodge_of_universalTwoSlot

end GSTClassicalHodgeUniversalTwoSlotSaturation
