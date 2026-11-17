import GSTClassicalHodgePlaneCompletenessTheorem
import GSTClassicalHodgeOmniversalGhostPlaneStrike

/-!
# GST CLASSICAL HODGE — STRICT-PLANE CIRCULARITY AUDIT

The ghost-adaptive strict-plane predicate is indexed by hypothetical Hodge
counterexamples themselves.  Its logical status must therefore be made
explicit before it is allowed anywhere near a foundational proof.

For each ghost `E`, a `GhostStrictPlaneStrike G E` already derives `False`.
Hence the strike type is empty.  Asking every ghost to carry a nonempty strike
is exactly asking that there be no ghosts at all.  Through the repository's
established separator equivalence, that is exactly the Hodge conclusion.

So the strict ghost-plane predicate is a downstream consequence-normal form,
not a lower geometric axiom.  This complements the common-class and
survival/closure circularity certificates in
`GSTClassicalHodgePlaneCompletenessTheorem`.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeStrictPlaneCircularityAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniversalGhostPlaneStrike
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgePlaneCompletenessTheorem

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- For a fixed hypothetical ghost, the strict-plane strike type is empty:
any inhabitant already carries the contradiction that kills the ghost. -/
theorem ghostStrictPlaneStrike_isEmpty
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty (GhostStrictPlaneStrike G E) := by
  exact ⟨fun P => P.contradiction⟩

/-- **EXACT NO-GHOST STATUS OF STRICT PLANE COMPLETENESS.** -/
theorem ghostAdaptiveStrictPlanes_iff_noGhost
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveStrictPlaneCompleteness G ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · exact no_omniversalSeparatorGhost_of_ghostAdaptiveStrictPlanes G
  · intro hEmpty E
    exact isEmptyElim E

/-- **STRICT-PLANE CIRCULARITY CERTIFICATE.**
The ghost-adaptive strict-plane condition is exactly equivalent to the Stage-2G
Hodge conclusion.  It is therefore forbidden as a foundational premise in a
noncircular proof. -/
theorem ghostAdaptiveStrictPlanes_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveStrictPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H :=
  (ghostAdaptiveStrictPlanes_iff_noGhost G).trans
    (hodge_iff_no_omniversalSeparatorGhost G).symm

/-- Hodge makes the strict ghost-plane completeness package a theorem, solely
because no ghost remains to index a strike.  No geometric construction should
be inferred from this vacuous direction. -/
theorem ghostAdaptiveStrictPlanes_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    GhostAdaptiveStrictPlaneCompleteness G :=
  (ghostAdaptiveStrictPlanes_iff_hodge G).2 hHodge

/-- Both historical ghost-adaptive plane formulations have the same exact
logical status: each is equivalent to Hodge and hence neither is a lower
completeness axiom. -/
theorem all_ghostAdaptive_plane_packages_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    (GhostAdaptiveStrictPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H)
    ∧ (GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H) := by
  exact ⟨ghostAdaptiveStrictPlanes_iff_hodge G,
    ghostAdaptiveCommonClassPlanes_iff_hodge G⟩

#check ghostStrictPlaneStrike_isEmpty
#check ghostAdaptiveStrictPlanes_iff_noGhost
#check ghostAdaptiveStrictPlanes_iff_hodge
#check ghostAdaptiveStrictPlanes_of_hodge
#check all_ghostAdaptive_plane_packages_iff_hodge

#print axioms ghostStrictPlaneStrike_isEmpty
#print axioms ghostAdaptiveStrictPlanes_iff_noGhost
#print axioms ghostAdaptiveStrictPlanes_iff_hodge
#print axioms all_ghostAdaptive_plane_packages_iff_hodge

end GSTClassicalHodgeStrictPlaneCircularityAudit
