import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeOmniverseStrictRelationRayCompiler
import GSTClassicalHodgeSynchronizedDefectOrbit

/-!
# GST CLASSICAL HODGE — OMNIVERSAL GHOST PLANE STRIKE

This is the ghost-adaptive form of the limitless plane argument.

A hypothetical omniversal separator ghost chooses one weight and one exact
Hodge basis sheet.  To kill it, we do *not* need a global fan, every matrix
unit, a finite global rank, or a realization theorem for every Hodge class.
It suffices to exhibit one genuine native algebraic source in that weight and
one raw strict bi-finite correspondence relation from that source to the
single sheet detected by the ghost.

The existing strict-relation compiler turns the raw pullback relation into an
actual realized correspondence expression.  Executing the expression on the
source's native cycle therefore constructs a genuine native cycle whose class
is exactly the detected basis sheet.  The omniversal ghost annihilates that
cycle under the identity graded program, while its separator detects the same
sheet nontrivially.  Contradiction.

Thus the final geometric burden is pointwise and counterfactual: for each
hypothetical ghost, construct one strict plane edge to the sheet it detects.
The ambient Hodge/GST universe remains unrestricted and limitless.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalGhostPlaneStrike

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One ghost-adaptive limitless observation plane.

The source is a genuine synchronized native/Hodge seed in the ghost's weight.
The target is exactly the basis sheet detected by the ghost.  The only edge
input is the raw strict Betti relation packet; no operator-action equation is
stored here. -/
structure GhostStrictPlaneStrike
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) where
  seed : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)
  relation : StrictRelationEdgePacket
    (⟨Sector.gstPlus, seed.hodge⟩ :
      HodgeBranchNode (V := V) (H := H) (p := E.weight))
    (⟨Sector.gstPlus,
      classicalHodgeBasis V H E.weight E.sheet⟩ :
      HodgeBranchNode (V := V) (H := H) (p := E.weight))

namespace GhostStrictPlaneStrike

/-- Execute the compiled genuine correspondence expression on the actual
native source cycle. -/
noncomputable def targetCycle
    {G : GeometricCycleClassSpine V H}
    {E : OmniversalSeparatorGhost G}
    (P : GhostStrictPlaneStrike G E) :
    codimensionCycles V.X E.weight :=
  P.relation.expression.cycleOperator P.seed.cycle

/-- **STRICT PLANE EDGE CONSTRUCTS THE DETECTED SHEET NATIVELY.**
The equality is derived from the raw Betti relation by the strict-relation
compiler and the exact native/cohomological commuting square of the resulting
realized correspondence expression. -/
theorem targetCycle_spec
    {G : GeometricCycleClassSpine V H}
    {E : OmniversalSeparatorGhost G}
    (P : GhostStrictPlaneStrike G E) :
    H.cycleClass E.weight P.targetCycle =
      (classicalHodgeBasis V H E.weight E.sheet).1 := by
  have hnat := P.relation.expression.cycleClass_natural P.seed.cycle
  rw [P.seed.class_eq] at hnat
  have hmat := P.relation.expression_materializes
  unfold GSTClassicalHodgePiOmniverseBranchSynthesis.ExprMaterializesBranch at hmat
  exact hnat.trans hmat.symm

/-- **ONE STRICT PLANE EDGE KILLS THE GHOST.**
The target cycle is genuine native geometry, so the ghost must annihilate it
under the identity graded program.  But the same cycle class is exactly the
basis sheet the separator detects. -/
theorem contradiction
    {G : GeometricCycleClassSpine V H}
    {E : OmniversalSeparatorGhost G}
    (P : GhostStrictPlaneStrike G E) :
    False := by
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

end GhostStrictPlaneStrike

/-- **GHOST-ADAPTIVE STRICT PLANE COMPLETENESS.**
Every hypothetical ghost admits one genuine strict plane edge from an actual
native source to precisely the sheet it detects.  This is much weaker than a
fan or a realization family indexed by every basis direction independent of a
failure. -/
def GhostAdaptiveStrictPlaneCompleteness
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ E : OmniversalSeparatorGhost G,
    Nonempty (GhostStrictPlaneStrike G E)

/-- Ghost-adaptive strict plane completeness eliminates all omniversal ghosts. -/
theorem no_omniversalSeparatorGhost_of_ghostAdaptiveStrictPlanes
    (G : GeometricCycleClassSpine V H)
    (hplane : GhostAdaptiveStrictPlaneCompleteness G) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  exact (Classical.choice (hplane E)).contradiction

/-- **LIMITLESS PLANE NO-GHOST FINALE.**
Once every hypothetical ghost has its one strict geometric plane strike, the
exact Stage-2G Hodge statement follows through the established omniversal
separator equivalence. -/
theorem hodge_of_ghostAdaptiveStrictPlanes
    (G : GeometricCycleClassSpine V H)
    (hplane : GhostAdaptiveStrictPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (no_omniversalSeparatorGhost_of_ghostAdaptiveStrictPlanes G hplane)

#check GhostStrictPlaneStrike
#check GhostStrictPlaneStrike.targetCycle
#check GhostStrictPlaneStrike.targetCycle_spec
#check GhostStrictPlaneStrike.contradiction
#check GhostAdaptiveStrictPlaneCompleteness
#check no_omniversalSeparatorGhost_of_ghostAdaptiveStrictPlanes
#check hodge_of_ghostAdaptiveStrictPlanes

#print axioms GhostStrictPlaneStrike.targetCycle_spec
#print axioms GhostStrictPlaneStrike.contradiction
#print axioms no_omniversalSeparatorGhost_of_ghostAdaptiveStrictPlanes
#print axioms hodge_of_ghostAdaptiveStrictPlanes

end GSTClassicalHodgeOmniversalGhostPlaneStrike
