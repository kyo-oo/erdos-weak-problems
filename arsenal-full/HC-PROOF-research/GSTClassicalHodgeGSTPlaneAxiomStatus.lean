import GSTClassicalHodgePlaneCompletenessTheorem
import GSTClassicalHodgeCommonClassPlaneReduction
import GSTClassicalHodgePlaneSemanticIndependence
import GSTClassicalHodgeCoherentNativeGhostObstruction
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — GST PLANE AXIOM STATUS AND NONCIRCULARITY

This module records the strongest conclusion justified by the present
GST/omniverse mathematics without smuggling the classical Hodge target back
into the plane-realization interface.

The central distinction is:

* intrinsic GST plane completeness is an unconditional theorem;
* common-class planes and raw strict-relation packets are extensionally the
  same existence datum;
* once native seed survival is fixed, the minimal ghost-target strict closure
  is equivalent to extinction of the omniversal separator ghost;
* a hypothetical ghost makes the corresponding strict target packet empty;
* consequently the remaining branch-packet geometric construction is not a
  bookkeeping theorem. It is exactly the independent geometric content whose
  proof would close the Hodge target.

The semantic countermodel in which the cycle-class map is erased is used only
as a soundness firewall: it preserves the whole intrinsic GST plane while
destroying geometric Hodge landing. Thus no theorem can derive the geometric
plane from intrinsic GST data alone.

Everything below is internal to the repository's GST/omniverse formalism.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeGSTPlaneAxiomStatus

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
open GSTClassicalHodgeCommonClassPlaneReduction
open GSTClassicalHodgePlaneCompletenessTheorem
open GSTClassicalHodgePlaneSemanticIndependence
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeCoherentNativeGhostObstruction
open GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **FULL INTRINSIC GST PLANE COMPLETENESS.**

This is the exact coordinate/causal statement proved by the GST matrix-unit
construction: one live source works simultaneously for every sector and target,
every target is causally reachable, and the finite rational collapse reconstructs
the original Hodge state.

No geometric cycle-class realization is mentioned in this predicate.
-/
def IntrinsicGSTPlaneCompleteness
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q, alpha ≠ 0 →
    ∃ i : ClassicalHodgeBasisIndex V H q,
      hodgeCoordinate i alpha ≠ 0 ∧
      (∀ sigma : Sector,
       ∀ j : ClassicalHodgeBasisIndex V H q,
         HodgeBranchEvent
           (⟨gstPlus, alpha.1⟩ : HodgeBranchNode V H q)
           (⟨sigma, augmentedConcreteHodgeMatrixUnit alpha j i⟩ :
             HodgeBranchNode V H q)
         ∧
         OmniversalGraph.Reachable
           (hodgeBranchGraph V H q)
           (⟨gstPlus, alpha.1⟩ : HodgeBranchNode V H q)
           (⟨sigma, augmentedConcreteHodgeMatrixUnit alpha j i⟩ :
             HodgeBranchNode V H q)) ∧
      (∑ j ∈ ((classicalHodgeBasis V H q).repr alpha).support,
          hodgeCoordinate j alpha •
            augmentedConcreteHodgeMatrixUnit alpha j i) = alpha.1

/-- **A IS A THEOREM.** The intrinsic GST plane is unconditionally complete. -/
theorem intrinsicGSTPlaneCompleteness
    (H : HodgeBigradedBettiData V) :
    IntrinsicGSTPlaneCompleteness (V := V) H := by
  intro q alpha halpha
  exact intrinsic_gst_plane_completeness alpha halpha

/-- The same theorem remains true after erasing cycle-class semantics. This is
the key semantic-independence witness: all intrinsic GST/omniverse firing data
remain intact. -/
theorem zeroCycleClass_intrinsicGSTPlaneCompleteness
    (H : HodgeBigradedBettiData V) :
    IntrinsicGSTPlaneCompleteness
      (V := V) (zeroCycleClassData H) := by
  intro q alpha halpha
  exact intrinsic_gst_plane_completeness alpha halpha

/-- **INTRINSIC PLANE CANNOT IMPLY GEOMETRIC HODGE.**

There is no universal theorem over the present unconstrained Stage-2G semantic
record saying that intrinsic GST plane completeness by itself implies the
geometric Hodge statement. The zero-cycle-class model satisfies the intrinsic
plane theorem while its cycle-class map is identically zero.
-/
theorem no_intrinsicGSTPlane_to_hodge_unconditionally
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      IntrinsicGSTPlaneCompleteness (V := V) H' →
        BigradedBettiHodgeStatement V H') := by
  intro h
  have hHodge :
      BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
    h (zeroCycleClassData H)
      (zeroCycleClass_intrinsicGSTPlaneCompleteness H)
  exact
    GSTClassicalHodgeStage2GSemanticRigidity.not_bigradedBettiHodge_zeroCycleClass
      H p alpha.1 alpha.2 (by
        intro hzero
        apply halpha
        apply Subtype.ext
        exact hzero) hHodge

/-- **INTRINSIC PLANE CANNOT IMPLY FULL GEOMETRIC PLANE.**

The same semantic countermodel blocks any universal upgrade from intrinsic GST
plane completeness to executable full-correspondence plane completeness.
-/
theorem no_intrinsicGSTPlane_to_fullCorrespondencePlane_unconditionally
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      IntrinsicGSTPlaneCompleteness (V := V) H' →
        FullCorrespondenceGSTPlaneCompleteness (V := V)
          (zeroCycleClassSpine H')) := by
  intro h
  have hplane :
      FullCorrespondenceGSTPlaneCompleteness
        (V := V) (zeroCycleClassSpine H) :=
    h (zeroCycleClassData H)
      (zeroCycleClass_intrinsicGSTPlaneCompleteness H)
  have hHodge :
      BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
    hodge_of_fullCorrespondenceGSTPlane
      (zeroCycleClassSpine H) hplane
  exact
    GSTClassicalHodgeStage2GSemanticRigidity.not_bigradedBettiHodge_zeroCycleClass
      H p alpha.1 alpha.2 (by
        intro hzero
        apply halpha
        apply Subtype.ext
        exact hzero) hHodge

/-- **ANY HODGE-SUFFICIENT EXTRA PREMISE MUST ADD NON-INTRINSIC CONTENT.**

Abstractly package any proposed additional semantic premise P. If P
unconditionally implied the Hodge target, then P must fail in the zero-cycle
semantic copy whenever that copy contains a nonzero Hodge state.

This is the general soundness principle behind the plane audit: an
unconditional proof must contain information that is genuinely sensitive to
the native cycle-class geometry.
-/
theorem any_hodge_sufficient_premise_fails_zeroCycleWorld
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (P : HodgeBigradedBettiData V → Prop)
    (hP :
      ∀ H' : HodgeBigradedBettiData V,
        P H' → BigradedBettiHodgeStatement V H') :
    ¬ P (zeroCycleClassData H) := by
  intro hP0
  have hHodge :
      BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
    hP (zeroCycleClassData H) hP0
  exact
    GSTClassicalHodgeStage2GSemanticRigidity.not_bigradedBettiHodge_zeroCycleClass
      H p alpha.1 alpha.2 (by
        intro hzero
        apply halpha
        apply Subtype.ext
        exact hzero) hHodge

/-- **B/C ARE ONE EXISTENCE LAW.**

For a fixed branch, common-class plane existence is exactly strict geometric
relation-packet existence. The common carrier class is a canonical repackaging
of the strict relation, so it is not an independent geometric axiom.
-/
theorem commonClassPlane_exists_iff_strictRelationPacket
    {p : Nat}
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)} :
    Nonempty (CommonClassPlanePacket u v) ↔
      Nonempty (StrictRelationEdgePacket u v) :=
  CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket

/-- **D IS EXACTLY THE MINIMAL GHOST-TARGET CLOSURE.**

Once the genuine native seed survives at each hypothetical ghost weight, the
one source-to-detected-sheet strict packet is equivalent to extinction of the
omniversal separator ghost.

Thus the missing geometric theorem is not an auxiliary compiler theorem.
It is exactly the ghost-eliminating content of the proof.
-/
theorem targetStrictClosure_iff_noGhost
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G) :
    GhostSeedTargetStrictClosure G ↔
      IsEmpty (OmniversalSeparatorGhost G) :=
  targetStrictClosure_iff_noGhost_of_survival G hsurvive

/-- **A GHOST MAKES THE D-PACKET EMPTY.**

The intrinsic GST branch still exists, but a strict geometric packet targeting
the ghost's detected matrix unit cannot coexist with that ghost.
-/
theorem branch_exists_but_D_packet_empty
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)) :
    HodgeBranchEvent
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
        (⟨Sector.gstPlus,
          hodgeMatrixUnit S.sourceIndex E.sheet S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
      ∧
      IsEmpty
        (StrictRelationEdgePacket
          (⟨Sector.gstPlus, S.hodge⟩ :
            HodgeBranchNode (V := V) (H := H) (p := E.weight))
          (⟨Sector.gstPlus,
            hodgeMatrixUnit S.sourceIndex E.sheet S.hodge⟩ :
            HodgeBranchNode (V := V) (H := H) (p := E.weight))) :=
  ghostBranchEvent_exists_but_strictPacket_empty G E S

/-- **NATIVE COHERENCE DOES NOT HIDE D.**

Any labelled native operator satisfying the exact column-coherence and
cycle-class-kernel stability tests still misses the ghost-selected GST target
by a detector-nonzero amount. Therefore routing, native lift ambiguity, and
finite tensor cancellation do not manufacture the missing strict packet.
-/
theorem coherentNativeLayer_misses_ghost_target
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i0 : ClassicalHodgeBasisIndex V H E.weight)
    (U : Module.End ℚ (FiberedNativeAddress V H E.weight))
    (hcolumns :
      ∀ i : ClassicalHodgeBasisIndex V H E.weight,
        (H.cycleClass E.weight).comp (nativeColumn i U) =
          (H.cycleClass E.weight).comp (nativeColumn i0 U))
    (hkernel :
      NativeClassKernelStable
        (H.cycleClass E.weight) (nativeColumn i0 U)) :
    nativeAmbientAction
        (H.cycleClass E.weight)
        (nativeColumn i0 U)
        hkernel
        S.hodge.1 ≠
      (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1 := by
  exact
    ghostSeedTarget_coherentNativeAction_mismatch_ne_zero
      G E S i0 U hcolumns hkernel

/-- **SOURCE SURVIVAL FROM A CONSERVED NATIVE CHARGE.**

The ghost-weight native seed is not an independent axiom once the branch's
conserved geometric charge has been independently constructed.  The canonical
spine tower supplies both the native cycle and its Hodge state; charge
conservation proves the Hodge state is nonzero, while the spine naturality
theorem identifies its cycle class with the state.

Thus source survival reduces to one explicit native conserved-charge law.
-/
theorem ghostWeightNativeSeedSurvival_of_conservedCharge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge (V := V) (H := H) G) :
    GhostWeightNativeSeedSurvival G := by
  intro E
  let Z : codimensionCycles V.X E.weight :=
    spineNativeTower G E.weight
  let a : ClassicalHodgeFiber V H E.weight :=
    spineHodgeSeed G E.weight
  have ha : a ≠ 0 := D.spineHodgeSeed_ne_zero E.weight
  have hclass :
      H.cycleClass E.weight Z = a.1 :=
    spineNativeTower_cycleClass G E.weight
  exact ⟨{
    cycle := Z
    hodge := a
    hodge_ne_zero := ha
    class_eq := hclass
  }⟩

/-- A native-mass bridge is enough to manufacture the same source survival:
its three mass laws build a conserved charge, and the conserved charge builds
the seed at every ghost weight.
-/
theorem ghostWeightNativeSeedSurvival_of_nativeMassBridge
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge (V := V) (H := H)) :
    GhostWeightNativeSeedSurvival G :=
  ghostWeightNativeSeedSurvival_of_conservedCharge G
    (NativeMassCycleClassBridge.toConservedCharge M G)

/-- A hypothetical ghost rules out simultaneous source survival and the
ghost-target strict closure.  This is the direct two-obstruction form of the
plane proof: in a ghost world, at least one of the two genuinely geometric
bridges must fail.
-/
theorem ghost_forces_source_or_D_failure
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) :
    ¬ (GhostWeightNativeSeedSurvival G ∧
      GhostSeedTargetStrictClosure G) := by
  intro h
  have hnone :
      IsEmpty (OmniversalSeparatorGhost G) :=
    (targetStrictClosure_iff_noGhost G h.1).1 h.2
  exact isEmpty_iff.mp hnone E

/-- With the native conserved-charge bridge in hand, source survival is no
longer an independent premise, so the GST route reduces exactly to the target
strict closure D.
-/
theorem hodge_of_nativeMassBridge_and_D
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge (V := V) (H := H))
    (hD : GhostSeedTargetStrictClosure G) :
    BigradedBettiHodgeStatement V H :=
  hodge_of_independent_D G
    (ghostWeightNativeSeedSurvival_of_nativeMassBridge G M)
    hD

/-- **MASTER GST PLANE AXIOM-STATUS CROWN.**

The branch's requested axioms therefore have the following exact status:

* intrinsic plane completeness: proved unconditionally;
* common-class plane vs. strict packet: same existence datum;
* minimal target closure D: equivalent to no-ghost once source survival is
  fixed, and impossible in the presence of a ghost;
* coherent native operators: strictly insufficient to supply D;
* any Hodge-sufficient extra premise: necessarily breaks the zero-cycle model.

This is the strongest noncircular theorem ledger available from the current
semantic interface. It does not relabel the Hodge target as a theorem.
-/
theorem gstPlane_axiom_status_crown
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G) :
    IntrinsicGSTPlaneCompleteness (V := V) H
    ∧
    (∀ {p : Nat}
      {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
      Nonempty (CommonClassPlanePacket u v) ↔
        Nonempty (StrictRelationEdgePacket u v))
    ∧
    (GhostSeedTargetStrictClosure G ↔
      IsEmpty (OmniversalSeparatorGhost G)) := by
  refine ⟨intrinsicGSTPlaneCompleteness H, ?_, ?_⟩
  · intro p u v
    exact commonClassPlane_exists_iff_strictRelationPacket
  · exact targetStrictClosure_iff_noGhost G hsurvive

/-- A compact downstream form: if source survival and the minimal D closure are
actually supplied by an independent construction, Hodge follows. No
ghost-indexed plane axiom is inserted inside this theorem.
-/
theorem hodge_of_independent_D
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hD : GhostSeedTargetStrictClosure G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    ((targetStrictClosure_iff_noGhost G hsurvive).1 hD)

#check IntrinsicGSTPlaneCompleteness
#check intrinsicGSTPlaneCompleteness
#check zeroCycleClass_intrinsicGSTPlaneCompleteness
#check no_intrinsicGSTPlane_to_hodge_unconditionally
#check no_intrinsicGSTPlane_to_fullCorrespondencePlane_unconditionally
#check any_hodge_sufficient_premise_fails_zeroCycleWorld
#check commonClassPlane_exists_iff_strictRelationPacket
#check targetStrictClosure_iff_noGhost
#check branch_exists_but_D_packet_empty
#check coherentNativeLayer_misses_ghost_target
#check gstPlane_axiom_status_crown

#check ghostWeightNativeSeedSurvival_of_conservedCharge
#check ghostWeightNativeSeedSurvival_of_nativeMassBridge
#check ghost_forces_source_or_D_failure
#check hodge_of_nativeMassBridge_and_D

#check hodge_of_independent_D

#print axioms intrinsicGSTPlaneCompleteness
#print axioms zeroCycleClass_intrinsicGSTPlaneCompleteness
#print axioms no_intrinsicGSTPlane_to_hodge_unconditionally
#print axioms no_intrinsicGSTPlane_to_fullCorrespondencePlane_unconditionally
#print axioms any_hodge_sufficient_premise_fails_zeroCycleWorld
#print axioms commonClassPlane_exists_iff_strictRelationPacket
#print axioms targetStrictClosure_iff_noGhost
#print axioms branch_exists_but_D_packet_empty
#print axioms coherentNativeLayer_misses_ghost_target
#print axioms gstPlane_axiom_status_crown

#print axioms ghostWeightNativeSeedSurvival_of_conservedCharge
#print axioms ghostWeightNativeSeedSurvival_of_nativeMassBridge
#print axioms ghost_forces_source_or_D_failure
#print axioms hodge_of_nativeMassBridge_and_D

#print axioms hodge_of_independent_D

end GSTClassicalHodgeGSTPlaneAxiomStatus
