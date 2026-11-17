import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeAtomicSpan

/-!
# GST actual-geometric irreducibility: a different universal proof route

The existing unlimited internal GST matrix-unit arsenal is irreducible as an
ABSTRACT Hodge-fiber endomorphism algebra. To obtain algebraic cycles one
must instead act using genuine realized closed correspondences, for which the
native/cycle-class square has been proved.

A substantive, separate proof route is possible: the actual algebraic Hodge
subspace is invariant under every genuinely realized Hodge-compatible closed
correspondence. If these actual geometric actions have NO nonzero proper
invariant Hodge subspace, then a single nonzero genuinely algebraic Hodge
seed saturates the entire Hodge fiber.

This proves the *logical route*, but does NOT silently identify the abstract
GST matrix units with finite-closed correspondence geometries. Global
irreducibility must still be derived from actual geometry; arbitrary smooth
projective varieties do not automatically provide it from the current record.
-/

set_option maxHeartbeats 15000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeActualGeometricIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A subspace invariant under *genuine* finite closed correspondences that
are separately certified to preserve Hodge type. Unlike an abstract GST
matrix unit, every operator here has an actual native geometric action. -/
def InvariantUnderActualHodgeCorrespondences
    (S : Submodule ℚ (ClassicalHodgeFiber V H p)) : Prop :=
  ∀ (R : RealizedFiniteClosedCorrespondence V H p)
    (hR : R.HodgeCompatible)
    (alpha : ClassicalHodgeFiber V H p),
      alpha ∈ S → R.hodgeOperator hR alpha ∈ S

/-- Genuine geometric irreducibility means the only Hodge subspaces
invariant under all these actual correspondences are zero and the whole
Hodge fiber. The statement itself is a condition to be proved from
geometry, NOT assumed automatically by the abstract GST arsenal. -/
def ActualHodgeCorrespondenceIrreducible : Prop :=
  ∀ S : Submodule ℚ (ClassicalHodgeFiber V H p),
    InvariantUnderActualHodgeCorrespondences S →
      S = ⊥ ∨ S = ⊤

/-- Each actual finite closed Hodge-compatible geometric correspondence
preserves the subspace of genuine native algebraic Hodge cycle classes.
No Hodge-surjectivity assumption or per-target native lift is used. -/
theorem algebraicHodgeSubspace_actual_correspondence_invariant :
    InvariantUnderActualHodgeCorrespondences
      (AlgebraicHodgeSubspace V H p) := by
  intro R hR alpha halpha
  exact R.maps_algebraicHodgeSubspace hR alpha halpha

/-- One nonzero genuine native projective spine + irreducibility of *actual
geometric* correspondences produces native algebraic cycles for EVERY
rational Hodge class at that weight. The only nontrivial geometric inputs
are explicitly visible in the statement. -/
theorem all_hodge_classes_of_actual_geometric_irreducibility
    (G : GeometricCycleClassSpine V H)
    (hseed : spineHodgeSeed G p ≠ 0)
    (hirred : ActualHodgeCorrespondenceIrreducible
      (V := V) (H := H) (p := p))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  have hstable :
      InvariantUnderActualHodgeCorrespondences
        (AlgebraicHodgeSubspace V H p) :=
    algebraicHodgeSubspace_actual_correspondence_invariant
  have hnonzero : AlgebraicHodgeSubspace V H p ≠ ⊥ :=
    algebraicHodgeSubspace_ne_bot_of_spineSeed G p hseed
  have htop : AlgebraicHodgeSubspace V H p = ⊤ := by
    rcases hirred (AlgebraicHodgeSubspace V H p) hstable with hbot | htop
    · exact False.elim (hnonzero hbot)
    · exact htop
  have htarget :
      (⟨alpha, halpha⟩ : ClassicalHodgeFiber V H p) ∈
        AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  change alpha ∈ pointCycleClassSpan p (H.cycleClass p) at htarget
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at htarget
  exact htarget

/-- If zero Hodge fibers are treated separately, one genuine geometric
irreducibility certificate and one nonzero native algebraic spine in each
active weight suffice for the full Stage-2G rational Hodge target.
This is an independent operator-irreducibility route, not the determinant
route and not an unconditional proof of the geometric hypotheses. -/
theorem full_hodge_of_actual_geometric_irreducibility
    (G : GeometricCycleClassSpine V H)
    (hirred : ∀ q : Nat,
      ActualHodgeCorrespondenceIrreducible
        (V := V) (H := H) (p := q))
    (hseed : ∀ q : Nat,
      (∃ a : ClassicalHodgeFiber V H q, a ≠ 0) →
        spineHodgeSeed G q ≠ 0) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  by_cases hactive :
      ∃ a : ClassicalHodgeFiber V H q, a ≠ 0
  · exact all_hodge_classes_of_actual_geometric_irreducibility
      G (hseed q hactive) (hirred q) alpha halpha
  · have ha0 : alpha = 0 := by
      by_contra hne
      apply hactive
      refine ⟨⟨alpha, halpha⟩, ?_⟩
      intro hz
      apply hne
      simpa using congrArg Subtype.val hz
    exact ⟨0, by simp [ha0]⟩

#check InvariantUnderActualHodgeCorrespondences
#check ActualHodgeCorrespondenceIrreducible
#check algebraicHodgeSubspace_actual_correspondence_invariant
#check all_hodge_classes_of_actual_geometric_irreducibility
#check full_hodge_of_actual_geometric_irreducibility

#print axioms algebraicHodgeSubspace_actual_correspondence_invariant
#print axioms all_hodge_classes_of_actual_geometric_irreducibility
#print axioms full_hodge_of_actual_geometric_irreducibility

end GSTClassicalHodgeActualGeometricIrreducibility
