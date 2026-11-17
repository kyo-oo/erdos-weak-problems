import GSTClassicalHodgeUniversalTwoSlotSaturation
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — ARSENAL NON-CIRCULARITY AUDIT

The full/rank-free arsenal is an extremely strong irreducibility machine.
This module records the exact logical firewall needed for the classical
landing: after one nonzero algebraic seed is present, invariance of the
algebraic Hodge subspace under *all* abstract basis matrix units already
forces that subspace to be the whole Hodge fiber.

Consequently an external proof must not simply assume matrix-unit naturality
or arbitrary basis-localization naturality.  Those operators must be derived
from independently constructed geometric transports.  This audit prevents a
coordinate reformulation of the desired conclusion from being mistaken for
its geometric proof.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeUniversalTwoSlotSaturation

namespace GSTClassicalHodgeArsenalNonCircularity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- If the algebraic Hodge subspace is already top, it is automatically
stable under every abstract matrix unit. -/
theorem rankFreeInvariant_of_eq_top
    (hTop : AlgebraicHodgeSubspace V H p = ⊤) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  rw [hTop]
  trivial

/-- Likewise the universal two-slot coordinate-localization condition follows
trivially after algebraic saturation. -/
theorem universalTwoSlotInvariant_of_eq_top
    (hTop : AlgebraicHodgeSubspace V H p = ⊤) :
    UniversalTwoSlotInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  rw [hTop]
  trivial

/-- With a nonzero algebraic seed present, abstract rank-free matrix-unit
invariance is equivalent to complete algebraic saturation. -/
theorem rankFreeInvariant_iff_eq_top_of_seed
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) ↔
      AlgebraicHodgeSubspace V H p = ⊤ := by
  constructor
  · intro h
    exact rankFreeArsenalInvariant_eq_top
      (AlgebraicHodgeSubspace V H p) h hseed
  · exact rankFreeInvariant_of_eq_top

/-- Same audit for the compressed universal two-slot condition. -/
theorem universalTwoSlotInvariant_iff_eq_top_of_seed
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    UniversalTwoSlotInvariant (AlgebraicHodgeSubspace V H p) ↔
      AlgebraicHodgeSubspace V H p = ⊤ := by
  constructor
  · intro h
    exact universalTwoSlotInvariant_eq_top
      (AlgebraicHodgeSubspace V H p) h hseed
  · exact universalTwoSlotInvariant_of_eq_top

/-- Full saturation of the algebraic Hodge subspace is exactly the statement
that every genuine Hodge class in this weight lies in the point-cycle span. -/
theorem algebraicHodgeSubspace_eq_top_iff
    : AlgebraicHodgeSubspace V H p = ⊤ ↔
      ∀ alpha : ClassicalHodgeFiber V H p,
        alpha.1 ∈ GSTClassicalHodgeAtomicSpan.pointCycleClassSpan
          p (H.cycleClass p) := by
  constructor
  · intro h alpha
    have : alpha ∈ AlgebraicHodgeSubspace V H p := by
      rw [h]
      trivial
    exact this
  · intro h
    apply top_unique
    intro alpha _
    exact h alpha

/-- **NON-CIRCULARITY CROWN.**  Once a seed is known, importing arbitrary
basis-matrix-unit stability is logically as strong as saturating the whole
Hodge fiber.  Therefore the remaining externalization must proceed through
independently constructed projective/cycle operations. -/
theorem arsenal_noncircularity_crown
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    (RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) ↔
      AlgebraicHodgeSubspace V H p = ⊤)
    ∧ (UniversalTwoSlotInvariant (AlgebraicHodgeSubspace V H p) ↔
      AlgebraicHodgeSubspace V H p = ⊤) := by
  exact ⟨rankFreeInvariant_iff_eq_top_of_seed hseed,
    universalTwoSlotInvariant_iff_eq_top_of_seed hseed⟩

#check rankFreeInvariant_iff_eq_top_of_seed
#check universalTwoSlotInvariant_iff_eq_top_of_seed
#check algebraicHodgeSubspace_eq_top_iff
#check arsenal_noncircularity_crown

#print axioms rankFreeInvariant_iff_eq_top_of_seed
#print axioms universalTwoSlotInvariant_iff_eq_top_of_seed
#print axioms algebraicHodgeSubspace_eq_top_iff
#print axioms arsenal_noncircularity_crown

end GSTClassicalHodgeArsenalNonCircularity
