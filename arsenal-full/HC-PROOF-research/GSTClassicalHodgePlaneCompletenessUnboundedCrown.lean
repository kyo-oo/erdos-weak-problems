import GSTClassicalHodgePlaneCompletenessLefschetzCrown
import GSTClassicalHodgePiUnboundedOmniverseCrown

/-!
# GST CLASSICAL HODGE — UNBOUNDED PLANE COMPLETENESS CROWN

The fixed-source plane theorem already proves every target branch exists and is
reachable, and the Lefschetz crown identifies every such branch with the same
normalized localized bare `L^2` primitive.

The GST higher-causal cosmos contains every branch world unchanged at every
finite causal dimension.  Therefore plane completeness is stronger than unary
graph reachability: the complete fixed-source target family persists through an
unbounded tower of higher causal cells.

No correspondence materialization, cycle-class surjectivity, ghost closure, or
plane-completeness hypothesis is used below.  This is a purely intrinsic
omniverse theorem.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneCompletenessUnboundedCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgePlaneCompletenessTheorem
open GSTClassicalHodgePlaneCompletenessLefschetzCrown
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Every fixed-source target branch persists as the identical projective/Hodge
world at every finite level of the unbounded higher-causal cosmos. -/
theorem fixedSource_target_has_unbounded_higher_tower
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∀ n : Nat,
      ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
        c =
          (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p)) := by
  exact branchWorld_has_unbounded_higher_tower
    (V := V) (H := H) (p := p)
    (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
      HodgeBranchNode (V := V) (H := H) (p := p))

/-- The same target simultaneously has primitive-event, graph-reachability,
normalized-local-`L^2`, and unbounded-higher-causal certificates. -/
theorem fixedSource_target_full_omniverse_certificate
    (alpha : ClassicalHodgeFiber V H p)
    (i : HodgeSupportIndex alpha)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    HodgeBranchEvent
      (⟨Sector.gstPlus, alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
      (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
    ∧ OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p))
      (⟨Sector.gstPlus, alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
      (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
    ∧ hodgeMatrixUnit i.1 j alpha =
      (twoSlotScalar)⁻¹ •
        GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
          (GSTClassicalHodgeRankFreePrimitiveGeneration.pairBasisIndex i.1 j)
          (diagonalLefschetzQ 2 2) alpha
    ∧ (∀ n : Nat,
      ∃ c : (hodgeHigherCausalCosmos (V := V) (H := H) (p := p)).Cell n,
        c =
          (⟨s, hodgeMatrixUnit i.1 j alpha⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p))) := by
  exact ⟨fixedSource_event_to_every_target alpha i s j,
    fixedSource_reachable_every_target alpha i s j,
    fixedSource_target_is_normalized_L2 alpha i j,
    fixedSource_target_has_unbounded_higher_tower alpha i s j⟩

/-- **UNBOUNDED FIXED-SOURCE GST PLANE COMPLETENESS.**

One live coordinate of any nonzero Hodge state drives the entire omniversal
plane.  Every target in every historical sector is:

* a primitive GST event;
* graph-reachable from the common source;
* exactly one normalized local bare `L^2` firing;
* present at every finite higher-causal dimension;

and the finite rational collapse of these same `L^2` firings reconstructs the
original Hodge state exactly.
-/
theorem gst_plane_completeness_unbounded_via_universal_L2
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
      ∧ (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
          ∀ n : Nat,
            ∃ c : (hodgeHigherCausalCosmos
              (V := V) (H := H) (p := p)).Cell n,
              c =
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
  obtain ⟨i, hi, hevent, hreach, hL2, hcollapse⟩ :=
    gst_plane_completeness_via_universal_L2 alpha halpha
  refine ⟨i, hi, hevent, hreach, ?_, hL2, hcollapse⟩
  intro s j n
  exact fixedSource_target_has_unbounded_higher_tower alpha i s j n

#check fixedSource_target_has_unbounded_higher_tower
#check fixedSource_target_full_omniverse_certificate
#check gst_plane_completeness_unbounded_via_universal_L2

#print axioms fixedSource_target_has_unbounded_higher_tower
#print axioms fixedSource_target_full_omniverse_certificate
#print axioms gst_plane_completeness_unbounded_via_universal_L2

end GSTClassicalHodgePlaneCompletenessUnboundedCrown
