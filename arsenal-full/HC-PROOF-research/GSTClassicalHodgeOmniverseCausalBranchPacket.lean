import GSTClassicalHodgeTransferSeedUniverse
import GSTClassicalHodgeLiveSheetIntertwining
import GSTClassicalHodgeAugmentedTargetMatrixUnit
import GSTGraphV2OmniversalCore
import GSTGraphV2OmniversalHyperEvents
import GSTMultiChannelHodgeCosmology
import waves.GSTNCohomology
import HodgeDeRhamBridge

/-!
# GST CLASSICAL HODGE — OMNIVERSE CAUSAL BRANCH PACKET

This file formalizes the handwritten omniverse construction at the Hodge-state
level without inserting any algebraicity premise.

A nonzero rational Hodge state `alpha` is first tethered to its canonical GST
transfer seed.  Its finite live support is then viewed inside an unbounded
three-sector event graph.  A primitive event is not an abstract matrix unit:
it is the already-proved augmented support-plus-target GST computation.  From
one live source coordinate, there is therefore a certified causal branch to
an arbitrary Hodge-basis target.

The resulting family is unbounded in the ambient basis/sector universe while
any one requested class still has finite active support.  The original class is
recovered exactly by rescaling and summing the causal target branches:

  alpha = sum_{j in supp(alpha)} (alpha_j / c) E_{ij}(alpha),

where `c` is one fixed nonzero live source coefficient.

The same finite live packet is also exposed as an `NShape`, so the already
proved N-cohomology channel-separation machinery applies to the packet.  The
three-sector event graph has a canonical General-Space realization, and a
higher-event system is supplied for finite rational synthesis of previously
generated branches.

This is the purely GST/omniverse half of the Hodge attack.  It deliberately
contains no assertion that the causal branch events are algebraic
correspondences; that geometric materialization is handled downstream by the
strict graded Betti/correspondence layer.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseCausalBranchPacket

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeLiveSheetIntertwining
open GSTClassicalHodgeTransferSeedUniverse
open GSTClassicalHodgeAugmentedTargetMatrixUnit
open GSTGraphV2OmniversalCore
open GSTGraphV2OmniversalHyperEvents

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One node of the Hodge omniverse: a genuine rational Hodge state together
with one of the three historical GST sectors. -/
structure HodgeBranchNode where
  sector : Sector
  state : ClassicalHodgeFiber V H p

/-- Primitive causal branch event.  The state transition is exactly the
finite augmented-support GST matrix-unit computation already proved in
`GSTClassicalHodgeAugmentedTargetMatrixUnit`.  The target sector is free: the
same certified state can be observed in any of the three omniversal sectors. -/
def HodgeBranchEvent
    (x y : HodgeBranchNode (V := V) (H := H) (p := p)) : Prop :=
  ∃ j : ClassicalHodgeBasisIndex V H p,
    ∃ i : HodgeSupportIndex x.state,
      y.state = augmentedConcreteHodgeMatrixUnit x.state j i

/-- Three-sector omniversal graph carried by the genuine Hodge fiber. -/
def hodgeBranchGraph : OmniversalGraph where
  Node := HodgeBranchNode (V := V) (H := H) (p := p)
  sector := HodgeBranchNode.sector
  Event := HodgeBranchEvent

/-- The branch graph itself is therefore a General Space: paths are exactly
finite causal histories of certified augmented GST transports. -/
def hodgeBranchGeneralSpace :=
  (hodgeBranchGraph (V := V) (H := H) (p := p)).toGeneralSpace

/-- Every nonzero Hodge state has an exact fibered GST sheet which forgets to
the canonical limitless transfer seed.  This is the formal
Hodge -> unbounded-GST entry map used by the branch construction. -/
theorem nonzero_state_has_exact_transfer_seed
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p).repr alpha i ≠ 0
      ∧ fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i) =
          GSTClassicalHodgeFiberedTransferCompletion.fiberedSheetGenerator
            V H ⟨p, i⟩
      ∧ forgetMultiplicityToGST
          (GSTClassicalHodgeFiberedTransferCompletion.fiberedSheetGenerator
            V H ⟨p, i⟩) = cosmicTransferSeed p :=
  nonzero_hodge_has_exact_fibered_transfer_sheet alpha halpha

/-- From one nonzero Hodge state there is a certified primitive GST event to
an arbitrary requested basis direction, in any of the three omniversal
sectors. -/
theorem event_to_arbitrary_target
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
        ⟨Sector.gstPlus, alpha⟩
        ⟨s, hodgeMatrixUnit i.1 j alpha⟩
      ∧ hodgeCoordinate i.1 alpha ≠ 0 := by
  obtain ⟨i, hiEq, hi⟩ :=
    exists_nonzero_augmented_target_transport alpha halpha j
  refine ⟨i, ?_, hi⟩
  exact ⟨j, i, hiEq.symm⟩

/-- The preceding primitive event is an actual path in the omniversal causal
closure.  Thus one live Hodge state branches to every target multiplicity
sheet, with no global finite-rank assumption. -/
theorem reachable_arbitrary_target
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (s : Sector)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ i : HodgeSupportIndex alpha,
      OmniversalGraph.Reachable
        (hodgeBranchGraph (V := V) (H := H) (p := p))
        ⟨Sector.gstPlus, alpha⟩
        ⟨s, hodgeMatrixUnit i.1 j alpha⟩
      ∧ hodgeCoordinate i.1 alpha ≠ 0 := by
  obtain ⟨i, he, hi⟩ := event_to_arbitrary_target alpha halpha s j
  exact ⟨i,
    OmniversalGraph.reachable_of_event
      (hodgeBranchGraph (V := V) (H := H) (p := p)) he,
    hi⟩

/-- **OMNIVERSE BRANCH-COLLAPSE IDENTITY.**
Choose one live source coefficient `c`.  Every support direction is reachable
by the exact augmented GST matrix-unit branch, and the original Hodge state is
precisely the finite rational collapse of those branches.

This is the formal version of the handwritten sum over causal sub-branches. -/
theorem branch_collapse_identity
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ i : HodgeSupportIndex alpha,
      hodgeCoordinate i.1 alpha ≠ 0 ∧
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          (((classicalHodgeBasis V H p).repr alpha j) *
              (hodgeCoordinate i.1 alpha)⁻¹) •
            hodgeMatrixUnit i.1 j alpha := by
  obtain ⟨k, hk⟩ := exists_nonzero_hodgeCoordinate halpha
  have hkSupport :
      k ∈ ((classicalHodgeBasis V H p).repr alpha).support := by
    apply Finsupp.mem_support_iff.mpr
    simpa [hodgeCoordinate] using hk
  let i : HodgeSupportIndex alpha := ⟨k, hkSupport⟩
  have hi : hodgeCoordinate i.1 alpha ≠ 0 := by
    simpa [i] using hk
  refine ⟨i, hi, ?_⟩
  have hsum :
      alpha =
        ∑ j ∈ ((classicalHodgeBasis V H p).repr alpha).support,
          ((classicalHodgeBasis V H p).repr alpha j) •
            classicalHodgeBasis V H p j := by
    have h0 := (classicalHodgeBasis V H p).linearCombination_repr alpha
    rw [Finsupp.linearCombination_apply] at h0
    exact h0.symm
  conv_lhs => rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hodgeMatrixUnit_apply]
  simp only [smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hi, mul_one]

/-- Finite active branch packet underlying one Hodge state.  The ambient
omniverse remains unbounded; `holes` counts only the live coordinates of the
particular compact state being observed. -/
def liveSupportNShape
    (alpha : ClassicalHodgeFiber V H p) : GSTNCohomology.NShape where
  holes := Fintype.card (HodgeSupportIndex alpha)
  channel := fun i => i.1
  distinct := by
    intro i j hij hchan
    apply hij
    exact Fin.ext hchan

/-- The live packet has an honest N-cohomology readout family.  At depth one
all channels are nonempty, and their indices are distinct by construction. -/
theorem liveSupport_ncohomology_rank
    (R : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ basis : Fin (liveSupportNShape alpha).holes →
        GSTNCohomology.nCohoClasses R (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveSupportNShape alpha).holes,
        (basis i).1 i =
          GSTNCohomology.towerWindow R
            ((liveSupportNShape alpha).channel i) 1 := by
  apply GSTNCohomology.ncoho_rank
  intro i
  exact GSTNCohomology.towerWindow_pos R
    ((liveSupportNShape alpha).channel i) (by omega)

/-- Finite rational linear synthesis is a genuine higher-arity event in the
Hodge omniverse.  This is the formal collapse mechanism after causal branch
selection. -/
structure BranchLinearRule where
  sector : Sector
  rank : Nat
  input : Fin rank → HodgeBranchNode (V := V) (H := H) (p := p)
  coeff : Fin rank → ℚ

/-- State produced by one finite branch-synthesis rule. -/
def BranchLinearRule.outputState
    (r : BranchLinearRule (V := V) (H := H) (p := p)) :
    ClassicalHodgeFiber V H p :=
  ∑ i : Fin r.rank, r.coeff i • (r.input i).state

/-- Higher-event system whose hyper-events are finite rational syntheses of
already-generated Hodge branches. -/
def hodgeBranchHyperEvents :
    HyperEventSystem (hodgeBranchGraph (V := V) (H := H) (p := p)) where
  Rule := BranchLinearRule (V := V) (H := H) (p := p)
  Premise := fun r => Fin r.rank
  input := fun r i => r.input i
  output := fun r => ⟨r.sector, r.outputState⟩

/-- Once all inputs of a finite synthesis have entered the omniversal closure,
their rational collapse is generated as one higher event. -/
theorem linear_synthesis_generated
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (r : BranchLinearRule (V := V) (H := H) (p := p))
    (h : ∀ i : Fin r.rank,
      HyperEventSystem.Generated
        (hodgeBranchHyperEvents (V := V) (H := H) (p := p))
        Seed (r.input i)) :
    HyperEventSystem.Generated
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p))
      Seed ⟨r.sector, r.outputState⟩ := by
  exact HyperEventSystem.hyper_generated
    (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed r h

#check hodgeBranchGraph
#check hodgeBranchGeneralSpace
#check nonzero_state_has_exact_transfer_seed
#check event_to_arbitrary_target
#check reachable_arbitrary_target
#check branch_collapse_identity
#check liveSupportNShape
#check liveSupport_ncohomology_rank
#check hodgeBranchHyperEvents
#check linear_synthesis_generated
#check HodgeDeRhamBridge.deRham_betti_comparison_finite
#check HodgeDeRhamBridge.mixed_period_exact

#print axioms nonzero_state_has_exact_transfer_seed
#print axioms event_to_arbitrary_target
#print axioms reachable_arbitrary_target
#print axioms branch_collapse_identity
#print axioms liveSupport_ncohomology_rank
#print axioms linear_synthesis_generated

end GSTClassicalHodgeOmniverseCausalBranchPacket
