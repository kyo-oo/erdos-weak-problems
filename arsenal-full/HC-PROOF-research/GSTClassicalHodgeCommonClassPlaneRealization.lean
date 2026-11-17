import GSTClassicalHodgeOmniversalGhostBranchClosure
import GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

/-!
# GST CLASSICAL HODGE — COMMON-CLASS PLANE REALIZATION LAW

This file is the Lean translation of `docs/GST_HODGE_PLANE_REALIZATION_LAW.tex`.

A GST plane is not treated as an intrinsic Euclidean plane or as a finite-rank
replacement for the limitless Hodge universe.  It is only a finite observation
of one causal branch.  The geometric datum extracted from such an observation
is therefore not a coordinate chart equation but a single class on the
intrinsic analytic carrier of a genuine strict correspondence.

For a branch `u -> v`, a `CommonClassPlanePacket u v` stores

* a genuine scheme-bi-finite correspondence `K`;
* a finite right Betti trace;
* point-cycle compatibility;
* one class `omega` in the rational singular cohomology of the intrinsic
  analytic carrier of `K`;
* a source-face theorem `l^*(u) = omega`;
* a target-face theorem `r^*(v) = omega`.

The desired strict Betti relation

    l^*(u) = r^*(v)

is then DERIVED by transitivity through `omega`; it is not an action equation
stored in the packet.  The existing strict-relation compiler converts that
relation into the genuine correspondence expression and native/cohomological
commuting square.

For a hypothetical omniversal separator ghost, it is enough to construct one
such common-class plane packet from one surviving native seed to the single
scaled matrix-unit branch aimed at the sheet detected by the ghost.  The
existing normalized branch target theorem then constructs the exact detected
basis sheet as a native cycle, and the identity graded program gives the
separator contradiction.

No finite global rank, 4x3 chart, twelve-sheet bound, all-target fan, cycle
representative for the target sheet, or supplied ambient operator equation is
used here.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCommonClassPlaneRealization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeOmniversalGhostPlaneStrike
open GSTClassicalHodgeOmniversalGhostBranchClosure
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **COMMON-CLASS GST PLANE PACKET.**

`planeClass` is the branch itself seen on the intrinsic analytic carrier.
The source and target are two faces of this one carrier state.  In particular
we do not store `BettiRelated` as a field: it is derived from these two face
identifications. -/
structure CommonClassPlanePacket
    (u v : HodgeBranchNode (V := V) (H := H) (p := p)) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  trace : RightFiniteBettiTrace H.analytification correspondence (2 * p)
  pointCompatibility :
    PointCycleCompatibility (n := p) correspondence trace
  planeClass :
    CarrierCohomology H.analytification correspondence (2 * p)
  source_face :
    leftCohomologyPullback H.analytification correspondence (2 * p)
        u.state.1 = planeClass
  target_face :
    rightCohomologyPullback H.analytification correspondence (2 * p)
        v.state.1 = planeClass

namespace CommonClassPlanePacket

variable
  {u v : HodgeBranchNode (V := V) (H := H) (p := p)}

/-- **GST PLANE REALIZATION LAW.**
Two faces of the same intrinsic carrier class determine the strict Betti
relation.  This is the paper equation

    l^*(source) = omega = r^*(target).
-/
theorem plane_realization_law
    (P : CommonClassPlanePacket u v) :
    BettiRelated H.analytification P.correspondence (2 * p)
      u.state.1 v.state.1 := by
  unfold BettiRelated
  exact P.source_face.trans P.target_face.symm

/-- Convert the common-class observation plane into the canonical raw strict
relation packet already consumed by the correspondence compiler. -/
noncomputable def toStrictRelationEdgePacket
    (P : CommonClassPlanePacket u v) :
    StrictRelationEdgePacket u v where
  correspondence := P.correspondence
  trace := P.trace
  pointCompatibility := P.pointCompatibility
  related := P.plane_realization_law

/-- The common-carrier law therefore derives the whole-Betti push-pull target
through the existing finite-trace uniqueness theorem.  No source-action field
occurs in `CommonClassPlanePacket`. -/
theorem pushPull_source_eq_target
    (P : CommonClassPlanePacket u v) :
    P.trace.pushPull u.state.1 = v.state.1 := by
  exact P.toStrictRelationEdgePacket.pushPull_source_eq_target

end CommonClassPlanePacket

/-! ## Ghost-adaptive one-plane strike -/

/-- One plane packet aimed only at the sheet selected by one hypothetical
omniversal separator ghost.

The target is the actual GST matrix-unit branch from a live source coordinate
of a genuine synchronized native seed.  It is generally a nonzero scalar
multiple of the detected basis sheet; the branch-closure normalization theorem
removes that scalar on the native side. -/
structure GhostCommonClassPlaneStrike
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) where
  seed : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)
  source : HodgeSupportIndex seed.hodge
  plane : CommonClassPlanePacket
    (⟨Sector.gstPlus, seed.hodge⟩ :
      HodgeBranchNode (V := V) (H := H) (p := E.weight))
    (⟨Sector.gstPlus,
      hodgeMatrixUnit source.1 E.sheet seed.hodge⟩ :
      HodgeBranchNode (V := V) (H := H) (p := E.weight))

namespace GhostCommonClassPlaneStrike

variable
  {G : GeometricCycleClassSpine V H}
  {E : OmniversalSeparatorGhost G}

/-- A support index is live, hence the scalar multiplying the target sheet is
nonzero. -/
theorem sourceCoefficient_ne_zero
    (P : GhostCommonClassPlaneStrike G E) :
    hodgeCoordinate P.source.1 P.seed.hodge ≠ 0 := by
  have hsupp :
      P.source.1 ∈
        ((classicalHodgeBasis V H E.weight).repr P.seed.hodge).support :=
    P.source.2
  exact Finsupp.mem_support_iff.mp hsupp

/-- Raw strict relation derived from the common plane class. -/
noncomputable def strictRelation
    (P : GhostCommonClassPlaneStrike G E) :
    StrictRelationEdgePacket
      (⟨Sector.gstPlus, P.seed.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus,
        hodgeMatrixUnit P.source.1 E.sheet P.seed.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight)) :=
  P.plane.toStrictRelationEdgePacket

/-- Normalize the genuine native image of the branch by its nonzero live
source coefficient. -/
noncomputable def targetCycle
    (P : GhostCommonClassPlaneStrike G E) :
    codimensionCycles V.X E.weight :=
  normalizedStrictBranchTargetCycle P.seed P.source P.strictRelation

/-- **COMMON-CLASS PLANE -> EXACT NATIVE TARGET SHEET.** -/
theorem targetCycle_spec
    (P : GhostCommonClassPlaneStrike G E) :
    H.cycleClass E.weight P.targetCycle =
      (classicalHodgeBasis V H E.weight E.sheet).1 := by
  exact normalizedStrictBranchTargetCycle_spec
    P.seed P.source P.sourceCoefficient_ne_zero P.strictRelation

/-- **ONE COMMON-CLASS GST PLANE STRIKE KILLS THE GHOST.**
The resulting cycle is genuine native geometry, so the omniversal separator
kills it under the identity graded program.  But its cycle class is exactly
the sheet detected nontrivially by the same separator. -/
theorem contradiction
    (P : GhostCommonClassPlaneStrike G E) : False := by
  have hkill :=
    E.kills_all_native_programs E.weight
      (GradedGeometricProgram.id E.weight) P.targetCycle
  have hkill' :
      E.separator.detector
        (H.cycleClass E.weight P.targetCycle) = 0 := by
    simpa [GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair,
      GradedCycleClassOperatorPair.idPair] using hkill
  rw [P.targetCycle_spec] at hkill'
  exact E.separator.detects_basis hkill'

end GhostCommonClassPlaneStrike

/-- **GHOST-ADAPTIVE COMMON-CLASS PLANE COMPLETENESS.**
Every hypothetical ghost has one surviving native source and one common-class
strict plane realization aimed at the exact sheet it detects. -/
def GhostAdaptiveCommonClassPlaneCompleteness
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ E : OmniversalSeparatorGhost G,
    Nonempty (GhostCommonClassPlaneStrike G E)

/-- Common-class plane completeness eliminates every omniversal separator
ghost. -/
theorem no_omniversalSeparatorGhost_of_commonClassPlanes
    (G : GeometricCycleClassSpine V H)
    (hplane : GhostAdaptiveCommonClassPlaneCompleteness G) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  exact (Classical.choice (hplane E)).contradiction

/-- **COMMON-CLASS GST PLANE NO-GHOST FINALE.** -/
theorem hodge_of_commonClassPlanes
    (G : GeometricCycleClassSpine V H)
    (hplane : GhostAdaptiveCommonClassPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (no_omniversalSeparatorGhost_of_commonClassPlanes G hplane)

/-! ## Branch-level compiler form

The pointwise ghost-adaptive theorem above is the weakest useful form.  For
compatibility with the existing branch-closure machinery we also package the
stronger statement that every primitive event at a weight has a common-class
plane realization. -/

/-- Every primitive causal branch at weight `p` is realized by a common carrier
class. -/
def PrimitiveCommonClassPlaneCompiler : Prop :=
  ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
    HodgeBranchEvent u v → Nonempty (CommonClassPlanePacket u v)

/-- Common-class plane realization derives the existing primitive strict
relation compiler; the strict relation is not an additional hypothesis. -/
noncomputable def primitiveStrictRelationCompiler_of_commonClassPlanes
    (C : PrimitiveCommonClassPlaneCompiler (V := V) (H := H) (p := p)) :
    PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p) := by
  intro u v huv
  obtain ⟨P⟩ := C huv
  exact ⟨P.toStrictRelationEdgePacket⟩

/-- Common-class closure needed only at weights selected by hypothetical ghosts. -/
def GhostWeightPrimitiveCommonClassClosure
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ E : OmniversalSeparatorGhost G,
    PrimitiveCommonClassPlaneCompiler
      (V := V) (H := H) (p := E.weight)

/-- **SURVIVAL + COMMON-CLASS PLANE CLOSURE -> HODGE.**
This is the branch-level translation of the paper derivation.  The existing
branch theorem supplies the live matrix-unit event; common-class realization
derives its strict relation; the already-proved branch normalization and
no-ghost collision finish the proof. -/
theorem hodge_of_survival_and_commonClassPlaneClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hplanes : GhostWeightPrimitiveCommonClassClosure G) :
    BigradedBettiHodgeStatement V H := by
  apply hodge_of_survival_and_strictBranchClosure G hsurvive
  intro E
  exact primitiveStrictRelationCompiler_of_commonClassPlanes (hplanes E)

#check CommonClassPlanePacket
#check CommonClassPlanePacket.plane_realization_law
#check CommonClassPlanePacket.toStrictRelationEdgePacket
#check CommonClassPlanePacket.pushPull_source_eq_target
#check GhostCommonClassPlaneStrike
#check GhostCommonClassPlaneStrike.sourceCoefficient_ne_zero
#check GhostCommonClassPlaneStrike.targetCycle
#check GhostCommonClassPlaneStrike.targetCycle_spec
#check GhostCommonClassPlaneStrike.contradiction
#check GhostAdaptiveCommonClassPlaneCompleteness
#check no_omniversalSeparatorGhost_of_commonClassPlanes
#check hodge_of_commonClassPlanes
#check PrimitiveCommonClassPlaneCompiler
#check primitiveStrictRelationCompiler_of_commonClassPlanes
#check GhostWeightPrimitiveCommonClassClosure
#check hodge_of_survival_and_commonClassPlaneClosure

#print axioms CommonClassPlanePacket.plane_realization_law
#print axioms CommonClassPlanePacket.pushPull_source_eq_target
#print axioms GhostCommonClassPlaneStrike.targetCycle_spec
#print axioms GhostCommonClassPlaneStrike.contradiction
#print axioms no_omniversalSeparatorGhost_of_commonClassPlanes
#print axioms hodge_of_commonClassPlanes
#print axioms hodge_of_survival_and_commonClassPlaneClosure

end GSTClassicalHodgeCommonClassPlaneRealization
