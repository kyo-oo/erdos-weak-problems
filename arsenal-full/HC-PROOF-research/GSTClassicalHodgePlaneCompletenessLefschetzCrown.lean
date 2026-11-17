import GSTClassicalHodgePlaneCompletenessTheorem
import GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch

/-!
# GST CLASSICAL HODGE — PLANE COMPLETENESS LEFSCHETZ CROWN

The intrinsic plane-completeness theorem still names the rank-free matrix unit
at its target face.  That notation is not primitive mathematics: the existing
universal two-slot theorem proves that every such matrix unit is exactly the
same normalized localized bare `L^2` firing.

This file substitutes that identity into the strengthened fixed-source plane
completeness theorem.  The result is a completely theorem-generated GST plane:

* choose one live source coordinate once;
* use the same universal two-slot `L^2` law for every target sheet;
* every resulting target is a primitive omniverse event and a causal path;
* the finite rational collapse of those `L^2` firings is the original state.

No matrix-unit realization axiom, plane axiom, source-per-target choice, or
geometric correspondence premise occurs in this intrinsic theorem.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneCompletenessLefschetzCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgePlaneCompletenessTheorem
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The target reached from a fixed live source is literally one normalized
localized bare two-step Lefschetz firing. -/
theorem fixedSource_target_is_normalized_L2
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha)
    (j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i.1 j alpha =
      (twoSlotScalar)⁻¹ •
        GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
          (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
          (diagonalLefschetzQ 2 2) alpha := by
  exact matrixUnit_apply_eq_normalized_localized_L2
    (V := V) (H := H) (p := p) i.1 j alpha

/-- Every target of the fixed-source plane is simultaneously a certified GST
primitive event and the normalized localized `L^2` output. -/
theorem fixedSource_event_and_L2_target
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchEvent
      (⟨Sector.gstPlus, alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
      (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
    ∧ hodgeMatrixUnit i.1 j alpha =
      (twoSlotScalar)⁻¹ •
        GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
          (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
          (diagonalLefschetzQ 2 2) alpha := by
  exact ⟨fixedSource_event_to_every_target alpha i s j,
    fixedSource_target_is_normalized_L2 alpha i j⟩

/-- **FIXED-SOURCE LEFSCHETZ COLLAPSE.**
The entire Hodge state is reconstructed from normalized bare `L^2` firings out
of any chosen live source coordinate. -/
theorem fixedSource_branch_collapse_via_L2
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha) :
    alpha =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
        (((classicalHodgeBasis V H p).repr alpha j) *
            (hodgeCoordinate i.1 alpha)⁻¹) •
          ((twoSlotScalar)⁻¹ •
            GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
              (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
              (diagonalLefschetzQ 2 2) alpha) := by
  rw [fixedSource_branch_collapse alpha i]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fixedSource_target_is_normalized_L2 alpha i j]

/-- **LEFSCHETZ-ONLY GST PLANE COMPLETENESS CROWN.**

For every nonzero Hodge state, one fixed live source drives the complete plane.
Every target is an omniverse event and reachable path, every target is exactly
the normalized local `L^2` firing, and the finite collapse of those firings is
the original state.  This is the intrinsic GST plane-completeness theorem with
all auxiliary operator primitives eliminated. -/
theorem gst_plane_completeness_via_universal_L2
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
      ∧ (∀ j : ClassicalHodgeBasisIndex V H p,
          hodgeMatrixUnit i.1 j alpha =
            (twoSlotScalar)⁻¹ •
              GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
                (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
                (diagonalLefschetzQ 2 2) alpha)
      ∧ alpha =
          ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
            (((classicalHodgeBasis V H p).repr alpha j) *
                (hodgeCoordinate i.1 alpha)⁻¹) •
              ((twoSlotScalar)⁻¹ •
                GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
                  (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
                  (diagonalLefschetzQ 2 2) alpha) := by
  obtain ⟨i, hi, hevent, hreach, _hcollapse⟩ :=
    gst_plane_completeness alpha halpha
  refine ⟨i, hi, hevent, hreach, ?_, ?_⟩
  · intro j
    exact fixedSource_target_is_normalized_L2 alpha i j
  · exact fixedSource_branch_collapse_via_L2 alpha i

/-- The earlier existential-source `branch_collapse_via_localized_L2` is a
strict corollary of the stronger fixed-source theorem above. -/
theorem branch_collapse_via_localized_L2_from_fixedSource
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            ((twoSlotScalar)⁻¹ •
              GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
                (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
                (diagonalLefschetzQ 2 2) alpha := by
  obtain ⟨i, hi, _hevent, _hreach, _hL2, hcollapse⟩ :=
    gst_plane_completeness_via_universal_L2 alpha halpha
  exact ⟨i, hi, hcollapse⟩

#check fixedSource_target_is_normalized_L2
#check fixedSource_event_and_L2_target
#check fixedSource_branch_collapse_via_L2
#check gst_plane_completeness_via_universal_L2
#check branch_collapse_via_localized_L2_from_fixedSource

#print axioms fixedSource_target_is_normalized_L2
#print axioms fixedSource_branch_collapse_via_L2
#print axioms gst_plane_completeness_via_universal_L2
#print axioms branch_collapse_via_localized_L2_from_fixedSource

end GSTClassicalHodgePlaneCompletenessLefschetzCrown
