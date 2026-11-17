import GSTClassicalHodgeArsenalNonCircularity
import GSTClassicalHodgeRankFreePrimitiveGeneration

/-!
# GST CLASSICAL HODGE — CONCRETE FAILURE DICHOTOMY

The internal limitless arsenal has now been reduced all the way to one fixed
2-slot GST word.  This module turns failure of algebraic saturation into a
concrete alternative rather than another abstract realization package.

For one weight p, write A_p for the actual Hodge classes already lying in the
native point-cycle class span.  If A_p is not the whole Hodge fiber, then:

* either A_p is zero (there is no nonzero algebraic Hodge seed in that weight),
* or the fixed 2-slot GST projector/Lefschetz word has an explicit algebraic
  input whose output leaves A_p.

The second branch is expressed with the *actual* `forwardArsenalWord` and the
rank-free finite read/write conjugation.  Hence closing the classical theorem
no longer requires reasoning about arbitrary basis endomorphisms: projective
geometry only has to rule out these two explicit failure modes.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeArsenalNonCircularity
open GSTClassicalHodgeExplicitArsenalGeneration

namespace GSTClassicalHodgeConcreteFailureDichotomy

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev AlgebraicFiber :=
  AlgebraicHodgeSubspace V H p

/-- A fully concrete witness that the universal two-slot GST word fails to
preserve the actual algebraic Hodge subspace. -/
structure TwoSlotEscape where
  source : ClassicalHodgeBasisIndex V H p
  target : ClassicalHodgeBasisIndex V H p
  alpha : ClassicalHodgeFiber V H p
  alpha_algebraic : alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p)
  escapes :
    liftFiniteHodgeOperator (pairBasisIndex source target)
        (forwardArsenalWord sourceSlot targetSlot) alpha ∉
      AlgebraicFiber (V := V) (H := H) (p := p)

/-- The concrete two-slot word is exactly the corresponding rank-free matrix
unit, pointwise. -/
theorem twoSlotWord_apply_eq_matrixUnit
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    liftFiniteHodgeOperator (pairBasisIndex i j)
        (forwardArsenalWord sourceSlot targetSlot) alpha =
      hodgeMatrixUnit i j alpha := by
  have h := rankFreeMatrixUnit_eq_lifted_GST_word
    (V := V) (H := H) (p := p) i j
  exact LinearMap.congr_fun h.symm alpha

/-- If the concrete 2-slot GST word preserves the algebraic Hodge subspace for
every recoordination, then the full rank-free arsenal preserves it. -/
theorem rankFreeInvariant_of_twoSlotStable
    (hstable :
      ∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p),
        liftFiniteHodgeOperator (pairBasisIndex i j)
            (forwardArsenalWord sourceSlot targetSlot) alpha ∈
          AlgebraicFiber (V := V) (H := H) (p := p)) :
    RankFreeArsenalInvariant
      (AlgebraicFiber (V := V) (H := H) (p := p)) := by
  intro i j alpha halpha
  rw [← twoSlotWord_apply_eq_matrixUnit (V := V) (H := H) (p := p)
    i j alpha]
  exact hstable i j alpha halpha

/-- Conversely, rank-free invariance forces stability under the actual fixed
GST word after every two-slot recoordination. -/
theorem twoSlotStable_of_rankFreeInvariant
    (hstable : RankFreeArsenalInvariant
      (AlgebraicFiber (V := V) (H := H) (p := p))) :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∀ alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p),
      liftFiniteHodgeOperator (pairBasisIndex i j)
          (forwardArsenalWord sourceSlot targetSlot) alpha ∈
        AlgebraicFiber (V := V) (H := H) (p := p) := by
  intro i j alpha halpha
  rw [twoSlotWord_apply_eq_matrixUnit (V := V) (H := H) (p := p)
    i j alpha]
  exact hstable i j alpha halpha

/-- Exact equivalence between abstract full-arsenal invariance and stability
of the one concrete 2-slot GST word under arbitrary recoordination. -/
theorem twoSlotStable_iff_rankFreeInvariant :
    (∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p),
        liftFiniteHodgeOperator (pairBasisIndex i j)
            (forwardArsenalWord sourceSlot targetSlot) alpha ∈
          AlgebraicFiber (V := V) (H := H) (p := p)) ↔
      RankFreeArsenalInvariant
        (AlgebraicFiber (V := V) (H := H) (p := p)) := by
  constructor
  · exact rankFreeInvariant_of_twoSlotStable
  · exact twoSlotStable_of_rankFreeInvariant

/-- **CONCRETE FAILURE DICHOTOMY.** If the actual algebraic Hodge subspace is
proper, then either it is zero or the one fixed GST 2-slot word has a concrete
algebraic input which it ejects from the cycle-class range. -/
theorem proper_algebraicFiber_zero_or_twoSlotEscape
    (hproper : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊤) :
    AlgebraicFiber (V := V) (H := H) (p := p) = ⊥ ∨
      Nonempty (TwoSlotEscape (V := V) (H := H) (p := p)) := by
  classical
  by_cases hzero : AlgebraicFiber (V := V) (H := H) (p := p) = ⊥
  · exact Or.inl hzero
  · right
    have hnotInv : ¬ RankFreeArsenalInvariant
        (AlgebraicFiber (V := V) (H := H) (p := p)) := by
      intro hInv
      exact hproper
        (rankFreeArsenalInvariant_eq_top
          (AlgebraicFiber (V := V) (H := H) (p := p)) hInv hzero)
    have hnotStable : ¬ (∀ i j : ClassicalHodgeBasisIndex V H p,
        ∀ alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p),
          liftFiniteHodgeOperator (pairBasisIndex i j)
              (forwardArsenalWord sourceSlot targetSlot) alpha ∈
            AlgebraicFiber (V := V) (H := H) (p := p)) := by
      intro hs
      exact hnotInv (rankFreeInvariant_of_twoSlotStable hs)
    push_neg at hnotStable
    obtain ⟨i, j, alpha, halpha, hescape⟩ := hnotStable
    exact ⟨{
      source := i
      target := j
      alpha := alpha
      alpha_algebraic := halpha
      escapes := hescape
    }⟩

/-- Eliminating the two concrete failure modes forces algebraic saturation in
one weight. -/
theorem algebraicFiber_eq_top_of_seed_and_twoSlotStable
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥)
    (hstable :
      ∀ i j : ClassicalHodgeBasisIndex V H p,
      ∀ alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p),
        liftFiniteHodgeOperator (pairBasisIndex i j)
            (forwardArsenalWord sourceSlot targetSlot) alpha ∈
          AlgebraicFiber (V := V) (H := H) (p := p)) :
    AlgebraicFiber (V := V) (H := H) (p := p) = ⊤ := by
  exact rankFreeArsenalInvariant_eq_top
    (AlgebraicFiber (V := V) (H := H) (p := p))
    (rankFreeInvariant_of_twoSlotStable hstable) hseed

#check TwoSlotEscape
#check twoSlotWord_apply_eq_matrixUnit
#check twoSlotStable_iff_rankFreeInvariant
#check proper_algebraicFiber_zero_or_twoSlotEscape
#check algebraicFiber_eq_top_of_seed_and_twoSlotStable

#print axioms twoSlotWord_apply_eq_matrixUnit
#print axioms twoSlotStable_iff_rankFreeInvariant
#print axioms proper_algebraicFiber_zero_or_twoSlotEscape
#print axioms algebraicFiber_eq_top_of_seed_and_twoSlotStable

end GSTClassicalHodgeConcreteFailureDichotomy
