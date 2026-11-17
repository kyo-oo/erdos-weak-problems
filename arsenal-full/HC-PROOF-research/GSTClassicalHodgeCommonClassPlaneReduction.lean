import GSTClassicalHodgeCommonClassPlaneRealization
import GSTClassicalHodgeNativePointSeedDegreeUpgrade
import GSTClassicalHodgeCodimensionPointTower

/-!
# GST CLASSICAL HODGE — COMMON-CLASS PLANE REDUCTION

This module removes bookkeeping from the logical burden of GST plane
completeness.

A `CommonClassPlanePacket u v` does not contain geometric information beyond a
`StrictRelationEdgePacket u v`: from a strict relation packet, choose the
common carrier class to be the left pullback of the source itself.  The source
face is reflexive and the target face is exactly the symmetry of the strict
Betti relation.

Consequently the common-plane layer adds no new existence axiom beyond strict
relation geometry.  A nonzero synchronized seed already contains a canonical
live source coordinate.  We therefore do not need a compiler for every causal
event: one strict relation from that canonical source to the single ghost
sheet is sufficient.  Projective degree removes the Hodge/nonzero fields from
the seed packet as well.

The canonical codimension-zero apex plus a uniform native principal-cut
survival HYPOTHESIS recursively generates an actual codimension-p point at
every finite weight.  The tower does not prove that survival hypothesis.
`nativeCutSearch` now constructs a finite path or a certified stopped cut
without it.  The strict target packet and positive-degree semantics below
also remain explicit premises, not established existence theorems.
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
open GSTClassicalHodgeConcreteRankFreeGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeNativePointSeedSaturation
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeOmniversalGhostBranchClosure
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
open GSTClassicalHodgeCodimensionPointTower
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace CommonClassPlanePacket

variable
  {u v : HodgeBranchNode (V := V) (H := H) (p := p)}

/-- **STRICT RELATION -> COMMON-CLASS PLANE.**

The intrinsic common class can be chosen canonically as the left pullback of
the source.  Hence the two face equations are not extra geometric hypotheses
once the strict relation is known. -/
noncomputable def ofStrictRelationEdgePacket
    (R : StrictRelationEdgePacket u v) :
    CommonClassPlanePacket u v where
  correspondence := R.correspondence
  trace := R.trace
  pointCompatibility := R.pointCompatibility
  planeClass :=
    leftCohomologyPullback H.analytification R.correspondence (2 * p)
      u.state.1
  source_face := rfl
  target_face := by
    change
      rightCohomologyPullback H.analytification R.correspondence (2 * p)
          v.state.1 =
        leftCohomologyPullback H.analytification R.correspondence (2 * p)
          u.state.1
    exact R.related.symm

/-- Common-class plane existence is exactly equivalent to raw strict-relation
packet existence for a fixed branch. -/
theorem nonempty_iff_strictRelationEdgePacket :
    Nonempty (CommonClassPlanePacket u v) ↔
      Nonempty (StrictRelationEdgePacket u v) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toStrictRelationEdgePacket⟩
  · rintro ⟨R⟩
    exact ⟨ofStrictRelationEdgePacket R⟩

end CommonClassPlanePacket

/-- **ONE SEED + UNIVERSAL STRICT CLOSURE CONSTRUCTS A GHOST PLANE STRIKE.**

This compatibility theorem keeps the older all-event compiler available, but
it is intentionally no longer the minimal interface below. -/
noncomputable def ghostCommonClassPlaneStrike_of_seed_strictClosure
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (C : PrimitiveStrictRelationCompiler
      (V := V) (H := H) (p := E.weight)) :
    GhostCommonClassPlaneStrike G E := by
  obtain ⟨i, hevent, _hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H)
      S.hodge S.hodge_ne_zero Sector.gstPlus E.sheet
  let R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight)) :=
    Classical.choice (C hevent)
  exact {
    seed := S
    source := i
    plane := CommonClassPlanePacket.ofStrictRelationEdgePacket R
  }

/-- **MINIMAL GHOST-TARGET STRICT CLOSURE.**

For each hypothetical ghost and each nonzero synchronized seed at its weight,
require only the one strict relation packet from the seed's canonical live
source coordinate to the sheet selected by that ghost.  No all-event fan or
causal-branch compiler is quantified here. -/
def GhostSeedTargetStrictClosure
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)),
    Nonempty
      (StrictRelationEdgePacket
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
        (⟨Sector.gstPlus,
          hodgeMatrixUnit S.sourceIndex E.sheet S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight)))

/-- One canonical seed-target strict packet directly manufactures the entire
common-class plane strike.  The source support witness is already carried by
`chosenLiveSource`; no event search is needed. -/
noncomputable def ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (C : GhostSeedTargetStrictClosure G) :
    GhostCommonClassPlaneStrike G E := by
  let i : HodgeSupportIndex S.hodge :=
    chosenLiveSource S.hodge S.hodge_ne_zero
  let R0 := Classical.choice (C E S)
  let R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight)) := by
    simpa [i, NativeHodgeOrbitSeed.sourceIndex] using R0
  exact {
    seed := S
    source := i
    plane := CommonClassPlanePacket.ofStrictRelationEdgePacket R
  }

/-- Ghost-weight seed survival plus the minimal one-target closure is enough
for Plane Completeness. -/
theorem commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostSeedTargetStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  intro E
  let S := Classical.choice (hsurvive E)
  exact ⟨ghostCommonClassPlaneStrike_of_seed_targetStrictClosure G E S hclose⟩

/-- A ghost detector kills the trace image of any native cycle whenever the
trace is compatible with the actual point-incidence operator.  This proof is
local to the native cycle-class range: it needs no common plane, Hodge finale,
normalized target cycle, or assumed strict relation. -/
theorem ghost_tracePushPull_nativeCycle_eq_zero
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * E.weight))
    (C : PointCycleCompatibility (n := E.weight) K T)
    (Z : codimensionCycles V.X E.weight) :
    E.separator.detector (T.pushPull (H.cycleClass E.weight Z)) = 0 := by
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker E.weight
      (H.cycleClass E.weight) E.separator.detector).1 E.separator.annihilates_atoms
  rw [← C.cycleClass_natural Z]
  apply hker
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
  exact ⟨_, rfl⟩

/-- **EXPLICIT GST BRANCH MISMATCH ON EVERY COMPATIBLE STRICT CARRIER.**

For every actual carrier and compatible finite trace, the detected component
of the discrepancy with the requested branch is exactly minus the live source
coefficient times the separator's target reading.  The equation is proved
without assuming a relation packet or constructing a target representative.
It is stronger than the previous packet-emptiness statement: the obstruction
already appears at the prescribed trace action, even if carrier defects have
been eliminated by a geometric construction. -/
theorem ghostSeedTarget_traceMismatch_formula
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * E.weight))
    (C : PointCycleCompatibility (n := E.weight) K T) :
    E.separator.detector
        (T.pushPull S.hodge.1 -
          (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1) =
      -(hodgeCoordinate S.sourceIndex S.hodge *
        E.separator.detector (classicalHodgeBasis V H E.weight E.sheet).1) := by
  have hkill : E.separator.detector (T.pushPull S.hodge.1) = 0 := by
    rw [← S.class_eq]
    exact ghost_tracePushPull_nativeCycle_eq_zero G E K T C S.cycle
  have hbranch := congrArg Subtype.val
    (hodgeMatrixUnit_apply S.sourceIndex E.sheet S.hodge)
  rw [map_sub, hkill, hbranch, map_smul]
  simp only [zero_sub, smul_eq_mul]

/-- A hypothetical ghost forces a nonzero discrepancy for EVERY compatible
carrier, not only failure of a chosen plane packet. -/
theorem ghostSeedTarget_traceMismatch_ne_zero
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * E.weight))
    (C : PointCycleCompatibility (n := E.weight) K T) :
    E.separator.detector
      (T.pushPull S.hodge.1 -
        (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1) ≠ 0 := by
  rw [ghostSeedTarget_traceMismatch_formula G E S K T C]
  apply neg_ne_zero.mpr
  apply mul_ne_zero
  · exact S.sourceCoefficient_ne_zero
  · exact E.separator.detects_basis

/-- The prescribed target cannot equal any compatible carrier's trace image
while the hypothetical separator survives.  No common-plane wrapper or
Hodge-equivalent closure assumption is used. -/
theorem ghostSeedTarget_pushPull_ne_target
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * E.weight))
    (C : PointCycleCompatibility (n := E.weight) K T) :
    T.pushPull S.hodge.1 ≠
      (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1 := by
  intro heq
  have hnonzero := ghostSeedTarget_traceMismatch_ne_zero G E S K T C
  rw [heq, sub_self, map_zero] at hnonzero
  exact hnonzero rfl

/-- **A SURVIVING GHOST FORBIDS THE REQUESTED STRICT BRANCH PACKET.**

This is the exact negative face of the branch-packet plane realization law.
Fix a hypothetical omniversal ghost and an already genuine synchronized native
seed in the ghost's weight.  There cannot exist the strict relation packet from
the seed's canonical live GST source to the matrix-unit target detected by the
ghost: such a packet canonically gives a common-class plane strike, whose
normalized native target cycle is the detected basis sheet, contradicting the
ghost detector.

Thus the missing realization theorem is located at precisely the contradiction
point, with no intermediate Hodge-shaped wrapper.  The proof below now uses
the explicit trace mismatch directly; it no longer creates a common-plane
strike or a normalized target cycle to establish emptiness. -/
theorem ghostSeedTargetStrictPacket_isEmpty
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)) :
    IsEmpty
      (StrictRelationEdgePacket
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
        (⟨Sector.gstPlus,
          hodgeMatrixUnit S.sourceIndex E.sheet S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))) := by
  refine ⟨?_⟩
  intro R
  exact ghostSeedTarget_pushPull_ne_target G E S
    R.correspondence R.trace R.pointCompatibility R.pushPull_source_eq_target

/-- **ABSTRACT GST BRANCH EXISTS WHILE STRICT GEOMETRIC REALIZATION IS FORBIDDEN BY A GHOST.**

This pins down the exact logical gap in the branch-packet derivation.
For a hypothetical omniversal ghost and an already synchronized nonzero native
seed at its weight, the intrinsic GST causal branch from the seed's canonical
live source coordinate to the ghost-detected matrix-unit target exists
unconditionally.  Nevertheless the corresponding strict geometric relation
packet is empty: if such a packet existed, the common-carrier/finite-trace
machinery would construct the detected basis cycle and contradict the ghost.

Hence branch existence, sector choice, reachability and recoordination cannot
by themselves manufacture the required strict scheme correspondence.  Any
proof of the branch-packet plane realization law must add genuinely geometric
content that rules out the ghost, rather than merely repackage the intrinsic
GST event. -/
theorem ghostBranchEvent_exists_but_strictPacket_empty
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
          HodgeBranchNode (V := V) (H := H) (p := E.weight))) := by
  constructor
  · let i : HodgeSupportIndex S.hodge :=
      chosenLiveSource S.hodge S.hodge_ne_zero
    refine ⟨E.sheet, i, ?_⟩
    simpa [i, NativeHodgeOrbitSeed.sourceIndex] using
      (GSTClassicalHodgeAugmentedTargetMatrixUnit
        .augmentedConcreteHodgeMatrixUnit_eq
          S.hodge E.sheet i).symm
  · exact ghostSeedTargetStrictPacket_isEmpty G E S

/-- **BRANCH-PACKET REALIZATION = NO-GHOST, ONCE THE NATIVE SOURCE EXISTS.**

This is the exact logical form of the handwritten GST plane derivation.
With ghost-weight native seed survival fixed, the sole remaining statement
`GhostSeedTargetStrictClosure` is equivalent to extinction of every
omniversal separator ghost.

Forward: choose the genuine seed at a hypothetical ghost weight, realize the
single source-to-detected-sheet strict packet, convert it to a common-carrier
plane, and invoke the already-proved one-plane contradiction.
Backward: when no ghost exists, the ghost-indexed strict-closure statement is
vacuous.

No Hodge statement occurs in this equivalence. -/
theorem targetStrictClosure_iff_noGhost_of_survival
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G) :
    GhostSeedTargetStrictClosure G ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · intro hclose
    exact no_omniversalSeparatorGhost_of_commonClassPlanes G
      (commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
        G hsurvive hclose)
  · intro hnone E S
    exact False.elim (isEmpty_iff.mp hnone E)

/-- **EXACT STATUS OF THE MINIMAL BRANCH-PACKET REALIZATION LAW.**

Once the source side is the already-existing ghost-weight native-seed survival
law, the genuinely minimal target-side statement is exactly
`GhostSeedTargetStrictClosure`: for the one canonical live source and the one
sheet detected by a hypothetical ghost, construct the strict correspondence
packet whose carrier pullbacks identify the GST branch faces.

This theorem proves that this two-piece package is not merely another compiler
waiting to be wired.  It is equivalent to the Stage-2G Hodge conclusion.
The forward implication is the branch-packet derivation:
strict packet -> common carrier plane -> exact target cycle -> no ghost -> Hodge.
The reverse implication is vacuous because Hodge leaves no ghost to quantify
over.  Thus any unconditional proof of the requested branch-packet plane
realization law is precisely the new mathematical content that closes Hodge;
it cannot be recovered by rearranging the already-green downstream wrappers. -/
theorem survival_and_targetStrictClosure_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    (GhostWeightNativeSeedSurvival G ∧ GhostSeedTargetStrictClosure G) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · rintro ⟨hsurvive, hclose⟩
    exact hodge_of_commonClassPlanes G
      (commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
        G hsurvive hclose)
  · intro hHodge
    have hnone : IsEmpty (OmniversalSeparatorGhost G) :=
      (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
    constructor
    · intro E
      exact False.elim (isEmpty_iff.mp hnone E)
    · intro E S
      exact False.elim (isEmpty_iff.mp hnone E)

/-- Compatibility with the older, stronger all-event closure theorem. -/
theorem commonClassPlaneCompleteness_of_survival_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  intro E
  let S := Classical.choice (hsurvive E)
  exact ⟨ghostCommonClassPlaneStrike_of_seed_strictClosure G E S (hclose E)⟩

/-- **TWO-LAW REDUCTION WITH GHOST-INDEXED POINT EXISTENCE.**

Projective degree removes Hodge type and nonvanishing from the seed burden.
The universal primitive-event compiler is also removed.  This compatibility
form keeps the older point-existence interface. -/
theorem commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (GSTNativeCodimensionCyclePresentation.CodimensionPoint
        V.X E.weight))
    (hclose : GhostSeedTargetStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact commonClassPlaneCompleteness_of_survival_and_targetStrictClosure G
    (ghostWeightNativeSeedSurvival_of_codimensionPoints G D hpoint)
    hclose

/-- **CONDITIONAL UNIFORM-TOWER PLANE-COMPLETENESS REDUCTION.**

The ghost-indexed point-existence premise is replaced by a uniform survival
premise; it is not proved or eliminated.  The canonical codimension-zero apex
and this premise construct points at every finite weight.  This interface
requires:

* projective-degree trace semantics, used solely to certify nonvanishing of the
  genuine point-cycle seed;
* the uniform native principal-cut successor nonvanishing law;
* the one canonical source-to-ghost strict relation packet.

No ghost-indexed point-existence axiom, target cycle, target algebraicity,
all-event fan, common plane class, source-action equation, or Hodge conclusion
is supplied. -/
theorem commonClassPlaneCompleteness_of_nativePointTower_and_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V)
    (hclose : GhostSeedTargetStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  apply commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
    G D
  · exact ghostCodimensionPoints_of_nativePointSuccessorNonvanishing G hstep
  · exact hclose

/-- Older stronger closure retained as a corollary. -/
theorem commonClassPlaneCompleteness_of_codimensionPoints_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (GSTNativeCodimensionCyclePresentation.CodimensionPoint
        V.X E.weight))
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact commonClassPlaneCompleteness_of_survival_and_strictClosure G
    (ghostWeightNativeSeedSurvival_of_codimensionPoints G D hpoint)
    hclose

/-!
## Actual cut-to-seed extraction, without impossible all-weight survival

The native cut search already returns either a reached projective point or
the first certified stopped cut.  Combining that geometric search directly
with the degree-certified point-seed constructor produces a genuinely native
Hodge seed whenever the requested level is reached.  Otherwise the stopping
certificate proves the realized cohomological cut vanishes.

Unlike the old global native-mass bridge, this construction does not demand
two successors at every point of every weight.  It uses no hypothesized
target basis cycle, no Hodge conclusion, and no ghost-indexed packet supply.
-/

/-- **EXPLICIT PROJECTIVE NATIVE-SEED OR STOP CERTIFICATE.**
At the target weight, return the whole actual native cut history together
with the synchronized point-cycle seed, or a genuine stopped-cut certificate.
The left output proves its seed is literally the point cycle at the end of
the native cut path. -/
noncomputable def nativeCutSeedOrStop
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (target : Nat) :
    Sum
      (Σ R : NativeCutReached V target,
        {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := target) //
          S.cycle = codimensionPointCycle V.X target R.point})
      (NativeCutStop V target) := by
  classical
  cases nativeCutSearch V target with
  | inl R =>
      refine .inl ⟨R, ⟨nativeHodgeOrbitSeed_of_codimensionPoint G D R.point, ?_⟩⟩
      rfl
  | inr S =>
      exact .inr S

/-- **NONCIRCULAR GST GEOMETRIC CUT DICHOTOMY.**
Either the requested weight has an actual nonzero algebraic Hodge seed
constructed along a finite native cut history, or a concrete earlier cut
is zero already in native cohomology.  This is an actual construction,
not an assumed universal point tower. -/
theorem nativeCutSeedOrStop_hodge_certificate
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (target : Nat) :
    (∃ (R : NativeCutReached V target)
       (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := target)),
       S.cycle = codimensionPointCycle V.X target R.point)
    ∨
    (∃ T : NativeCutStop V target,
      (G.principalCutPair T.level).cohomologyOperator
        (H.cycleClass T.level
          (codimensionPointCycle V.X T.level T.reached.point)) = 0) := by
  classical
  cases nativeCutSeedOrStop G D target with
  | inl h =>
      exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
  | inr T =>
      exact Or.inr ⟨T, T.cohomological_cut_eq_zero G⟩

/-!
## Bounded geometric Hodge closure from actual native-cut histories

The preceding cut construction no longer requires an infinite supply of
codimension points.  At each target level it either provides an actual
degree-certified source point or a certified stopped cut.  A live level can
therefore use the existing geometry-first two-generator theorem immediately.
The exact global Hodge statement follows if all fibers beyond a finite
geometric horizon are zero, without imposing nonzero seeds beyond that bound.
-/

/-- Hodge algebraization at a certified live weight, directly from the
constructed projective cut history and the true geometry-first GST generators.
The input is not a Hodge class realization or a target cycle. -/
theorem hodgeWeight_of_unstoppedNativeCut
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (weight : Nat)
    (hstop : IsEmpty (NativeCutStop V weight))
    (R : ∀ i j : ClassicalHodgeBasisIndex V H weight,
      GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
        (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading weight) ≤
      LinearMap.range (H.cycleClass weight) := by
  classical
  cases nativeCutSeedOrStop G D weight with
  | inl w =>
      let P : NativePointHodgeSeed V H weight :=
        NativePointHodgeSeed.ofCodimensionPoint G D w.1.point
      exact P.hodge_weight_le_cycleClass_range R
  | inr T =>
      letI : IsEmpty (NativeCutStop V weight) := hstop
      exact isEmptyElim T

/-- One finite path-survival law and actual native GST generators give all
Hodge cycle classes in every certified finite codimension. -/
theorem hodgeThroughFiniteNativeHorizon
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (horizon : Nat)
    (hnoStop : ∀ (p : Nat), p ≤ horizon → IsEmpty (NativeCutStop V p))
    (R : ∀ (p : Nat), p ≤ horizon →
      ∀ i j : ClassicalHodgeBasisIndex V H p,
        GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
          (V := V) (H := H) i j) :
    ∀ (p : Nat), p ≤ horizon →
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p) := by
  intro p hp
  exact hodgeWeight_of_unstoppedNativeCut
    G D p (hnoStop p hp) (R p hp)

/-- **FINITE-GEOMETRY GST GLOBAL SATURATION.**
A genuinely bounded native-cut tower plus geometric two-generator
correspondences saturates all live Hodge weights.  Higher zero fibers are
settled by the zero native cycle rather than by impossible nonzero seeds.
No global native-mass bridge or all-weight point-survival axiom is used. -/
theorem bigradedHodge_of_boundedNativeCuts
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (horizon : Nat)
    (hnoStop : ∀ (p : Nat), p ≤ horizon → IsEmpty (NativeCutStop V p))
    (R : ∀ (p : Nat), p ≤ horizon →
      ∀ i j : ClassicalHodgeBasisIndex V H p,
        GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
          (V := V) (H := H) i j)
    (hzero : ∀ (p : Nat), horizon < p →
      ∀ alpha : ClassicalHodgeFiber V H p, alpha = 0) :
    BigradedBettiHodgeStatement V H := by
  classical
  intro p alpha halpha
  by_cases hp : p ≤ horizon
  · exact (hodgeThroughFiniteNativeHorizon G D horizon hnoStop R p hp)
      halpha
  · have hz : alpha = 0 := by
      have hval := congrArg Subtype.val
        (hzero p (Nat.lt_of_not_ge hp)
          (⟨alpha, halpha⟩ : ClassicalHodgeFiber V H p))
      simpa using hval
    exact ⟨0, by simp [hz]⟩

#check ghostBranchEvent_exists_but_strictPacket_empty
#check ghostSeedTarget_traceMismatch_formula
#check ghostSeedTarget_traceMismatch_ne_zero
#check ghostSeedTarget_pushPull_ne_target
#check targetStrictClosure_iff_noGhost_of_survival
#check ghostSeedTargetStrictPacket_isEmpty
#check survival_and_targetStrictClosure_iff_hodge
#check CommonClassPlanePacket.ofStrictRelationEdgePacket
#check CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#check GhostSeedTargetStrictClosure
#check ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
#check commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
#check commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
#check commonClassPlaneCompleteness_of_nativePointTower_and_targetStrictClosure
#check nativeCutSeedOrStop
#check nativeCutSeedOrStop_hodge_certificate
#check hodgeWeight_of_unstoppedNativeCut
#check hodgeThroughFiniteNativeHorizon
#check bigradedHodge_of_boundedNativeCuts

#print axioms ghostBranchEvent_exists_but_strictPacket_empty
#print axioms ghost_tracePushPull_nativeCycle_eq_zero
#print axioms ghostSeedTarget_traceMismatch_formula
#print axioms ghostSeedTarget_traceMismatch_ne_zero
#print axioms ghostSeedTarget_pushPull_ne_target
#print axioms targetStrictClosure_iff_noGhost_of_survival
#print axioms ghostSeedTargetStrictPacket_isEmpty
#print axioms survival_and_targetStrictClosure_iff_hodge
#print axioms CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#print axioms ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_nativePointTower_and_targetStrictClosure
#print axioms nativeCutSeedOrStop
#print axioms nativeCutSeedOrStop_hodge_certificate
#print axioms hodgeWeight_of_unstoppedNativeCut
#print axioms hodgeThroughFiniteNativeHorizon
#print axioms bigradedHodge_of_boundedNativeCuts

end GSTClassicalHodgeCommonClassPlaneRealization
