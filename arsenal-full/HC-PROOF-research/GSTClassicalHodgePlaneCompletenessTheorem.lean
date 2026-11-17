import GSTClassicalHodgeCommonClassPlaneRealization
import GSTClassicalHodgeStage2GSemanticRigidity

/-!
# GST CLASSICAL HODGE — PLANE COMPLETENESS AS A THEOREM

This file separates two statements that must not be conflated.

The first is the intrinsic GST/omniverse plane statement.  It is unconditional:
from one live coordinate of a nonzero Hodge state, the already-constructed
augmented GST matrix unit fires to every requested basis sheet.  The SAME live
source works for every target, and the original state is recovered exactly by
a finite rational collapse of those branches.  No plane-completeness axiom is
needed for this statement.

The second is the historical geometric/ghost plane package.  A common-class
plane packet contains genuine scheme-correspondence geometry, so it cannot be
manufactured from the bare Stage-2G semantic record.  More strongly, the
existing ghost-indexed versions of plane completeness are consequence-normal
forms: because their domain is the type of Hodge counterexamples, they are
logically equivalent to ghost extinction, hence to the Hodge target itself.
They are therefore proved here as downstream theorems and are forbidden as
foundational assumptions in a noncircular route.

Everything below uses only the repository's own GST/omniverse mathematics.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneCompletenessTheorem

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAugmentedTargetMatrixUnit
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniversalGhostBranchClosure
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## I. Unconditional GST plane completeness -/

/-- Every support coordinate is genuinely live. -/
theorem liveSource_coordinate_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    hodgeCoordinate i.1 alpha ≠ 0 := by
  have hi :
      i.1 ∈ ((classicalHodgeBasis V H p).repr alpha).support := i.2
  exact Finsupp.mem_support_iff.mp hi

/-- **FIXED-SOURCE GST PLANE FIRING.**

The source does not depend on the target.  Any one live support coordinate of
`alpha` fires, by the already-proved augmented GST word, to every requested
basis sheet and to every omniversal sector. -/
theorem fixedSource_event_to_every_target
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchEvent
      (⟨Sector.gstPlus, alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
      (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p)) := by
  refine ⟨j, i, ?_⟩
  exact (augmentedConcreteHodgeMatrixUnit_eq alpha j i).symm

/-- The fixed-source plane firing is an actual path in the omniversal causal
closure. -/
theorem fixedSource_reachable_every_target
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p))
      (⟨Sector.gstPlus, alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
      (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p)) := by
  exact OmniversalGraph.reachable_of_event
    (hodgeBranchGraph (V := V) (H := H) (p := p))
    (fixedSource_event_to_every_target alpha i s j)

/-- **FIXED-SOURCE BRANCH COLLAPSE.**

The previous branch-collapse theorem chose a live source existentially.  The
stronger fact is that EVERY live source gives the same exact reconstruction.
Thus plane completeness does not require target-dependent source choices. -/
theorem fixedSource_branch_collapse
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        (((classicalHodgeBasis V H p).repr alpha j) *
            (hodgeCoordinate i.1 alpha)⁻¹) •
          hodgeMatrixUnit i.1 j alpha := by
  have hi : hodgeCoordinate i.1 alpha ≠ 0 :=
    liveSource_coordinate_ne_zero alpha i
  have hsum :
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          ((classicalHodgeBasis V H p).repr alpha j) •
            classicalHodgeBasis V H p j :=
    (classicalHodgeBasis V H p).sum_repr alpha
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hodgeMatrixUnit_apply]
  simp only [smul_smul]
  simp [hi, mul_assoc, hodgeCoordinate]

/-- **UNCONDITIONAL GST PLANE COMPLETENESS CROWN.**

For every nonzero genuine Hodge state there is one fixed live source such that
all target sheets in all sectors are primitive GST events, are causally
reachable, and their finite rational collapse is exactly the original state.
There is no plane-completeness premise anywhere in this theorem. -/
theorem gst_plane_completeness
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0
      ∧ (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
          HodgeBranchEvent
            (⟨Sector.gstPlus, alpha⟩ :
              HodgeBranchNode (V := V) (H := H) (p := p))
            (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
              HodgeBranchNode (V := V) (H := H) (p := p)))
      ∧ (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
          OmniversalGraph.Reachable
            (hodgeBranchGraph (V := V) (H := H) (p := p))
            (⟨Sector.gstPlus, alpha⟩ :
              HodgeBranchNode (V := V) (H := H) (p := p))
            (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
              HodgeBranchNode (V := V) (H := H) (p := p)))
      ∧ alpha =
          ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
            (((classicalHodgeBasis V H p).repr alpha j) *
                (hodgeCoordinate i.1 alpha)⁻¹) •
              hodgeMatrixUnit i.1 j alpha := by
  obtain ⟨k, hk⟩ := exists_nonzero_hodgeCoordinate halpha
  have hmem :
      k ∈ ((classicalHodgeBasis V H p).repr alpha).support := by
    apply Finsupp.mem_support_iff.mpr
    simpa [hodgeCoordinate] using hk
  let i : HodgeSupportIndex alpha := ⟨k, hmem⟩
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · exact liveSource_coordinate_ne_zero alpha i
  · intro s j
    exact fixedSource_event_to_every_target alpha i s j
  · intro s j
    exact fixedSource_reachable_every_target alpha i s j
  · exact fixedSource_branch_collapse alpha i

/-! ## II. Circularity elimination for the historical ghost plane packages -/

/-- The historical ghost-adaptive common-class plane condition has exactly the
same truth value as extinction of the ghost domain.  Reverse implication is
not a geometric construction: when there are no ghosts, the ghost-indexed
requirement is empty.  This theorem makes that logical status explicit. -/
theorem ghostAdaptiveCommonClassPlanes_iff_noGhost
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveCommonClassPlaneCompleteness G ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · exact no_omniversalSeparatorGhost_of_commonClassPlanes G
  · intro hEmpty E
    exact isEmptyElim E

/-- **CIRCULARITY CERTIFICATE.**
The historical ghost-adaptive common-class plane condition is equivalent to
the exact Stage-2G Hodge target.  Therefore it may be used only downstream as
a consequence of an unconditional proof, never as a foundational axiom for
that proof. -/
theorem ghostAdaptiveCommonClassPlanes_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H :=
  (ghostAdaptiveCommonClassPlanes_iff_noGhost G).trans
    (hodge_iff_no_omniversalSeparatorGhost G).symm

/-- Hodge itself makes the historical ghost-weight source-survival package a
theorem, because there is no ghost weight left to supply. -/
theorem ghostWeightNativeSeedSurvival_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    GhostWeightNativeSeedSurvival G := by
  have hEmpty := (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
  intro E
  exact isEmptyElim E

/-- Hodge likewise makes the historical ghost-weight strict-branch closure a
theorem. -/
theorem ghostWeightPrimitiveStrictClosure_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    GhostWeightPrimitiveStrictClosure G := by
  have hEmpty := (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
  intro E
  exact isEmptyElim E

/-- Hodge likewise makes the historical ghost-weight common-class plane closure
a theorem. -/
theorem ghostWeightPrimitiveCommonClassClosure_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    GhostWeightPrimitiveCommonClassClosure G := by
  have hEmpty := (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
  intro E
  exact isEmptyElim E

/-- **STRICT-GHOST PACKAGE EXACT STATUS.**
Source survival plus strict branch closure is not a weaker foundation: as a
combined ghost-indexed package it is equivalent to Hodge itself. -/
theorem survival_and_strictClosure_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    (GhostWeightNativeSeedSurvival G ∧ GhostWeightPrimitiveStrictClosure G) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · rintro ⟨hsurvive, hstrict⟩
    exact hodge_of_survival_and_strictBranchClosure G hsurvive hstrict
  · intro hHodge
    exact ⟨ghostWeightNativeSeedSurvival_of_hodge G hHodge,
      ghostWeightPrimitiveStrictClosure_of_hodge G hHodge⟩

/-- **COMMON-CLASS GHOST PACKAGE EXACT STATUS.**
Source survival plus common-class plane closure is likewise equivalent to the
Hodge target, so it cannot be an independent noncircular starting point. -/
theorem survival_and_commonClassClosure_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    (GhostWeightNativeSeedSurvival G ∧
      GhostWeightPrimitiveCommonClassClosure G) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · rintro ⟨hsurvive, hplanes⟩
    exact hodge_of_survival_and_commonClassPlaneClosure G hsurvive hplanes
  · intro hHodge
    exact ⟨ghostWeightNativeSeedSurvival_of_hodge G hHodge,
      ghostWeightPrimitiveCommonClassClosure_of_hodge G hHodge⟩

/-- One crown recording the logical status of every historical ghost-plane
foundation used by this branch.  All three are conclusion-equivalent packages,
not lower axioms. -/
theorem ghost_plane_circularity_crown
    (G : GeometricCycleClassSpine V H) :
    (GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H)
    ∧ ((GhostWeightNativeSeedSurvival G ∧
          GhostWeightPrimitiveStrictClosure G) ↔
        BigradedBettiHodgeStatement V H)
    ∧ ((GhostWeightNativeSeedSurvival G ∧
          GhostWeightPrimitiveCommonClassClosure G) ↔
        BigradedBettiHodgeStatement V H) := by
  exact ⟨ghostAdaptiveCommonClassPlanes_iff_hodge G,
    survival_and_strictClosure_iff_hodge G,
    survival_and_commonClassClosure_iff_hodge G⟩

/-! ## III. Why genuine geometric semantics cannot be skipped -/

/-- The repository's own zero-cycle-class model proves that no theorem over the
bare unconstrained Stage-2G record can turn intrinsic GST plane completeness
into the classical geometric landing.  A genuine cycle-class semantic layer
must occur somewhere in any unconditional proof. -/
theorem bareStage2G_cannot_be_unconditional_geometric_landing
    (H0 : HodgeBigradedBettiData V)
    (q : Nat)
    (hlive : rationalHodgeSubspace (H0.hodgeBigrading q) ≠ ⊥) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      BigradedBettiHodgeStatement V H') := by
  exact
    GSTClassicalHodgeStage2GSemanticRigidity.arbitrary_cycleClass_semantics_cannot_be_final_target
      H0 q hlive

/-- **PLANE-COMPLETENESS / GEOMETRIC-SEMANTICS SEPARATION CROWN.**
Intrinsic GST plane completeness is theorem-level, while the bare semantic
record is formally too weak to imply geometric Hodge landing.  This is the
noncircular boundary any later unconditional geometric proof must respect. -/
theorem gstPlane_complete_but_bareStage2G_not_geometrically_complete
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (q : Nat)
    (hlive : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥) :
    (∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0
      ∧ (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
          HodgeBranchEvent
            (⟨Sector.gstPlus, alpha⟩ :
              HodgeBranchNode (V := V) (H := H) (p := p))
            (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
              HodgeBranchNode (V := V) (H := H) (p := p))))
    ∧ ¬ (∀ H' : HodgeBigradedBettiData V,
      BigradedBettiHodgeStatement V H') := by
  constructor
  · obtain ⟨i, hi, hevent, _hreach, _hcollapse⟩ :=
      gst_plane_completeness alpha halpha
    exact ⟨i, hi, hevent⟩
  · exact bareStage2G_cannot_be_unconditional_geometric_landing H q hlive

#check liveSource_coordinate_ne_zero
#check fixedSource_event_to_every_target
#check fixedSource_reachable_every_target
#check fixedSource_branch_collapse
/-- Explicitly named alias for the theorem above.  New callers should use this
name when they mean coordinate/causal plane completeness rather than native
algebraic plane completeness. -/
theorem intrinsic_gst_plane_completeness
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      hodgeCoordinate i alpha ≠ 0 ∧
      (∀ sigma : Sector,
       ∀ j : ClassicalHodgeBasisIndex V H p,
         HodgeBranchEvent
           (⟨gstPlus, alpha.1⟩ : HodgeBranchNode V H p)
           (⟨sigma, augmentedConcreteHodgeMatrixUnit alpha j i⟩ :
             HodgeBranchNode V H p)
         ∧ OmniversalGraph.Reachable (hodgeBranchGraph V H p)
           (⟨gstPlus, alpha.1⟩ : HodgeBranchNode V H p)
           (⟨sigma, augmentedConcreteHodgeMatrixUnit alpha j i⟩ :
             HodgeBranchNode V H p)) ∧
      (∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          hodgeCoordinate j alpha •
            augmentedConcreteHodgeMatrixUnit alpha j i) = alpha.1 :=
  gst_plane_completeness alpha halpha

#check gst_plane_completeness
#check intrinsic_gst_plane_completeness
#check ghostAdaptiveCommonClassPlanes_iff_noGhost
#check ghostAdaptiveCommonClassPlanes_iff_hodge
#check ghostWeightNativeSeedSurvival_of_hodge
#check ghostWeightPrimitiveStrictClosure_of_hodge
#check ghostWeightPrimitiveCommonClassClosure_of_hodge
#check survival_and_strictClosure_iff_hodge
#check survival_and_commonClassClosure_iff_hodge
#check ghost_plane_circularity_crown
#check bareStage2G_cannot_be_unconditional_geometric_landing
#check gstPlane_complete_but_bareStage2G_not_geometrically_complete

#print axioms fixedSource_event_to_every_target
#print axioms fixedSource_branch_collapse
#print axioms gst_plane_completeness
#print axioms intrinsic_gst_plane_completeness
#print axioms ghostAdaptiveCommonClassPlanes_iff_hodge
#print axioms survival_and_strictClosure_iff_hodge
#print axioms survival_and_commonClassClosure_iff_hodge
#print axioms ghost_plane_circularity_crown
#print axioms bareStage2G_cannot_be_unconditional_geometric_landing

end GSTClassicalHodgePlaneCompletenessTheorem
