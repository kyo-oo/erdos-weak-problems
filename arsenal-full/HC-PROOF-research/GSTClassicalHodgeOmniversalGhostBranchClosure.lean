import GSTClassicalHodgeOmniversalGhostPlaneStrike
import GSTClassicalHodgeOmniverseCausalBranchPacket
import GSTClassicalHodgeOmniverseStrictRelationRayCompiler

/-!
# GST CLASSICAL HODGE — OMNIVERSAL GHOST BRANCH CLOSURE

This module derives the ghost plane strike from the actual limitless omniverse
branch architecture.

For a hypothetical ghost at weight `p` and detected sheet `j`, assume only:

* SURVIVAL: one genuine nonzero synchronized native/Hodge seed exists at `p`;
* STRICT CLOSURE: every primitive GST branch event at `p` admits its raw
  scheme-bi-finite strict-relation packet.

The already-proved omniverse branch theorem chooses a live source coordinate
`i` of the seed and gives a primitive event

  seed -> E_ij(seed) = c * basis_j,

with `c != 0`.  Strict closure materializes that one event from the raw Betti
relation.  Executing its realized correspondence expression on the genuine
native source cycle and rescaling by `c^{-1}` constructs an actual native cycle
whose class is exactly `basis_j`.

The omniversal separator must kill that native cycle under the identity graded
program, while by definition it detects `basis_j`.  Contradiction.

No finite global Hodge rank, no all-target correspondence fan, no origin-only
orbit condition and no supplied operator-action equation occur here.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalGhostBranchClosure

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
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Normalize the native image of one strict branch event to its exact target
basis sheet. -/
noncomputable def normalizedStrictBranchTargetCycle
    {G : GeometricCycleClassSpine V H}
    {E : OmniversalSeparatorGhost G}
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i : HodgeSupportIndex S.hodge)
    (R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))) :
    codimensionCycles V.X E.weight :=
  (hodgeCoordinate i.1 S.hodge)⁻¹ •
    R.expression.cycleOperator S.cycle

/-- The normalized native image of the strict branch is exactly the ghost's
detected basis sheet. -/
theorem normalizedStrictBranchTargetCycle_spec
    {G : GeometricCycleClassSpine V H}
    {E : OmniversalSeparatorGhost G}
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i : HodgeSupportIndex S.hodge)
    (hi : hodgeCoordinate i.1 S.hodge ≠ 0)
    (R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))) :
    H.cycleClass E.weight
        (normalizedStrictBranchTargetCycle S i R) =
      (classicalHodgeBasis V H E.weight E.sheet).1 := by
  have hnat := R.expression.cycleClass_natural S.cycle
  rw [S.class_eq] at hnat
  have hmat := R.expression_materializes
  unfold GSTClassicalHodgePiOmniverseBranchSynthesis.ExprMaterializesBranch at hmat
  have htarget :
      R.expression.cohomologyOperator S.hodge.1 =
        (hodgeCoordinate i.1 S.hodge) •
          (classicalHodgeBasis V H E.weight E.sheet).1 := by
    rw [← hmat]
    exact congrArg Subtype.val
      (hodgeMatrixUnit_apply i.1 E.sheet S.hodge)
  unfold normalizedStrictBranchTargetCycle
  rw [LinearMap.map_smul, hnat, htarget]
  simp [hi, smul_smul]

/-- **BRANCH + SURVIVAL + STRICT CLOSURE KILLS ONE GHOST.** -/
theorem false_of_omniversalGhost_nativeSeed_strictClosure
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (C : PrimitiveStrictRelationCompiler
      (V := V) (H := H) (p := E.weight)) :
    False := by
  obtain ⟨i, hevent, hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H)
      S.hodge S.hodge_ne_zero Sector.gstPlus E.sheet
  let R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight)) :=
    Classical.choice (C hevent)
  let Z : codimensionCycles V.X E.weight :=
    normalizedStrictBranchTargetCycle S i R
  have hZ :
      H.cycleClass E.weight Z =
        (classicalHodgeBasis V H E.weight E.sheet).1 := by
    simpa [Z] using normalizedStrictBranchTargetCycle_spec S i hi R
  have hkill :=
    E.kills_all_native_programs E.weight
      (GradedGeometricProgram.id E.weight) Z
  have hkill' :
      E.separator.detector (H.cycleClass E.weight Z) = 0 := by
    simpa [GradedGeometricProgram.cohomologyEval,
      GradedGeometricProgram.toPair,
      GradedCycleClassOperatorPair.idPair] using hkill
  rw [hZ] at hkill'
  exact E.separator.detects_basis hkill'

/-- Survival law needed only on a hypothetical ghost's own live weight. -/
def GhostWeightNativeSeedSurvival
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ E : OmniversalSeparatorGhost G,
    Nonempty
      (NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))

/-- Strict closure is likewise needed only at weights selected by hypothetical
ghosts. -/
def GhostWeightPrimitiveStrictClosure
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ E : OmniversalSeparatorGhost G,
    PrimitiveStrictRelationCompiler
      (V := V) (H := H) (p := E.weight)

/-- The two genuine structural laws manufacture the ghost-adaptive plane strike
and therefore eliminate every omniversal ghost. -/
theorem no_omniversalSeparatorGhost_of_survival_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  let S := Classical.choice (hsurvive E)
  exact false_of_omniversalGhost_nativeSeed_strictClosure E S (hclose E)

/-- **LIMITLESS BRANCH/SURVIVAL/CLOSURE NO-GHOST FINALE.** -/
theorem hodge_of_survival_and_strictBranchClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (no_omniversalSeparatorGhost_of_survival_and_strictClosure
      G hsurvive hclose)

#check normalizedStrictBranchTargetCycle
#check normalizedStrictBranchTargetCycle_spec
#check false_of_omniversalGhost_nativeSeed_strictClosure
#check GhostWeightNativeSeedSurvival
#check GhostWeightPrimitiveStrictClosure
#check no_omniversalSeparatorGhost_of_survival_and_strictClosure
#check hodge_of_survival_and_strictBranchClosure

#print axioms normalizedStrictBranchTargetCycle_spec
#print axioms false_of_omniversalGhost_nativeSeed_strictClosure
#print axioms no_omniversalSeparatorGhost_of_survival_and_strictClosure
#print axioms hodge_of_survival_and_strictBranchClosure

end GSTClassicalHodgeOmniversalGhostBranchClosure
