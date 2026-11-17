import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — GENERIC GHOST-INDEXED CIRCULARITY BARRIER

Any proposed closure law whose only domain is the type of hypothetical Hodge
failure ghosts is vacuous once Hodge holds. Therefore, if such a law is also
strong enough to imply Hodge, it is automatically equivalent to Hodge.

This generic theorem prevents future work from repeatedly renaming the
conclusion as a ghost survival, fan, closure, plane, materialization or
collision package.
-/

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGhostIndexedCriterionCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every proposition attached only to an omniversal separator ghost holds
vacuously after the Hodge conclusion, because there are no ghosts left. -/
theorem ghostIndexedCriterion_of_hodge
    (G : GeometricCycleClassSpine V H)
    (C : OmniversalSeparatorGhost G → Prop)
    (hHodge : BigradedBettiHodgeStatement V H) :
    ∀ E : OmniversalSeparatorGhost G, C E := by
  have hempty : IsEmpty (OmniversalSeparatorGhost G) :=
    (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
  intro E
  exact isEmptyElim E

/-- GENERIC CIRCULARITY BARRIER.
If a ghost-indexed criterion implies Hodge, then the universally quantified
criterion is exactly equivalent to Hodge. It cannot be used as a logically
weaker foundation for a noncircular proof. -/
theorem ghostIndexedCriterion_iff_hodge
    (G : GeometricCycleClassSpine V H)
    (C : OmniversalSeparatorGhost G → Prop)
    (hkill : (∀ E : OmniversalSeparatorGhost G, C E) →
      BigradedBettiHodgeStatement V H) :
    (∀ E : OmniversalSeparatorGhost G, C E) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · exact hkill
  · exact ghostIndexedCriterion_of_hodge G C

/-- Existential-data version. Any family of witnesses requested only for
hypothetical ghosts is likewise conclusion-equivalent as soon as existence of
those witnesses kills all ghosts. -/
theorem ghostIndexedWitnesses_iff_hodge
    (G : GeometricCycleClassSpine V H)
    (W : OmniversalSeparatorGhost G → Type*)
    (hkill : (∀ E : OmniversalSeparatorGhost G, Nonempty (W E)) →
      BigradedBettiHodgeStatement V H) :
    (∀ E : OmniversalSeparatorGhost G, Nonempty (W E)) ↔
      BigradedBettiHodgeStatement V H :=
  ghostIndexedCriterion_iff_hodge G (fun E => Nonempty (W E)) hkill

/-- The same barrier applies to any ghost-indexed relation between the ghost
and auxiliary geometric data. -/
theorem ghostIndexedRelation_iff_hodge
    (G : GeometricCycleClassSpine V H)
    (A : Type*)
    (R : OmniversalSeparatorGhost G → A → Prop)
    (hkill : (∀ E : OmniversalSeparatorGhost G, ∃ a : A, R E a) →
      BigradedBettiHodgeStatement V H) :
    (∀ E : OmniversalSeparatorGhost G, ∃ a : A, R E a) ↔
      BigradedBettiHodgeStatement V H := by
  apply ghostIndexedCriterion_iff_hodge G
    (fun E => ∃ a : A, R E a)
  exact hkill

#check ghostIndexedCriterion_of_hodge
#check ghostIndexedCriterion_iff_hodge
#check ghostIndexedWitnesses_iff_hodge
#check ghostIndexedRelation_iff_hodge

#print axioms ghostIndexedCriterion_iff_hodge
#print axioms ghostIndexedWitnesses_iff_hodge
#print axioms ghostIndexedRelation_iff_hodge

end GSTClassicalHodgeGhostIndexedCriterionCircularity
