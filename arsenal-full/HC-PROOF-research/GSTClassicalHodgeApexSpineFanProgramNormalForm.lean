import GSTClassicalHodgeCanonicalCutProgramSpine
import GSTClassicalHodgeRootedStrictRelationFan
import GSTClassicalHodgeGradedOrbitSingleProgramCollapse

/-!
# GST CLASSICAL HODGE — APEX / SPINE / FAN PROGRAM NORMAL FORM

The upgraded GST Graph V2 picture has a literal executable normal form.

* APEX: the codimension-zero geometric origin.
* SPINE: the canonical principal-cut program

      cut 0 ; cut 1 ; ... ; cut (p-1).

* FAN: one locally materialized strict-relation ray inside weight `p`.

A strict-relation ray was previously used only semantically: algebraicity was
propagated edge by edge.  But every raw strict-relation packet already compiles
to a genuine `RealizedCorrespondenceExpr`, and the graded correspondence
language already supports same-weight correspondence instructions and ordered
composition.  Hence the entire ray itself is ONE same-weight graded program.

Composing that horizontal program after the canonical cut spine gives one
root-to-node program from weight zero.  Normalizing by the single live source
coordinate gives one root-to-basis program.  Since the full-program orbit is
already a rational submodule, finite Hodge basis expansion then compiles every
rational Hodge class into ONE graded correspondence program from the geometric
origin.

This removes the arbitrary `SeedPropagationFamily` from the graph-shaped route:
the vertical path is fixed to the actual canonical principal-cut spine.  The
remaining geometric burdens are exactly visible:

1. the concrete canonical projective-cut tower class is nonzero in each weight;
2. one finite strict-relation ray from that canonical live node to each target
   basis direction is geometrically materialized.

No global omniverse compiler, arbitrary higher-weight seed family, direct giant
apex-to-target correspondence, or external span of unrelated causal histories
is used.
-/

set_option maxHeartbeats 160000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeApexSpineFanProgramNormalForm

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeRootedStrictRelationFan
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeGradedOrbitSingleProgramCollapse
open GSTClassicalHodgeCanonicalCutProgramSpine
open GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Compile one locally materialized horizontal GST ray into ONE genuine
same-weight graded correspondence program. -/
noncomputable def strictRayProgram
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)} :
    StrictRelationRay u v -> GradedCorrespondenceProgram V H p p
  | .nil _ => .id p
  | .cons _ relation tail =>
      .comp (.correspondence relation.expression) (strictRayProgram tail)

/-- **RAY PROGRAM ENDPOINT EQUATION.**
Executing the compiled program on the source state lands exactly at the target
state of the ray.  This upgrades path-local algebraicity propagation to an
actual executable correspondence-program identity. -/
theorem strictRayProgram_eval
    (G : GeometricCycleClassSpine V H)
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (r : StrictRelationRay u v) :
    (strictRayProgram r).cohomologyEval G u.state.1 = v.state.1 := by
  induction r with
  | nil u =>
      rfl
  | @cons u v w event relation tail ih =>
      change
        (strictRayProgram tail).cohomologyEval G
          (relation.expression.cohomologyOperator u.state.1) = w.state.1
      rw [<- relation.expression_materializes]
      exact ih

/-- One spoke of a rooted fan, now viewed as ONE executable same-weight
correspondence program rather than merely a path carrying semantic stability. -/
noncomputable def rootedFanProgram
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (F : RootedStrictRelationFan S)
    (j : ClassicalHodgeBasisIndex V H p) :
    GradedCorrespondenceProgram V H p p :=
  strictRayProgram (F.ray j)

/-- Exact action of the compiled fan spoke on its common apex. -/
theorem rootedFanProgram_eval
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (F : RootedStrictRelationFan S)
    (j : ClassicalHodgeBasisIndex V H p) :
    (rootedFanProgram S F j).cohomologyEval G S.hodge.1 =
      (rootedFanTarget S j).state.1 := by
  simpa [rootedFanProgram, rootedFanApex] using
    strictRayProgram_eval G (F.ray j)

/-- Compose the fixed vertical principal-cut spine with one horizontal fan ray.
This is the literal root-to-node path suggested by the GST Graph V2 picture. -/
noncomputable def canonicalRootToTargetProgram
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne))
    (j : ClassicalHodgeBasisIndex V H p) :
    GradedCorrespondenceProgram V H 0 p :=
  .comp
    (canonicalCutProgram (V := V) (H := H) p)
    (rootedFanProgram (canonicalCutOrbitSeed G p hne) F j)

/-- **APEX -> SPINE -> FAN ENDPOINT.**
The composed root-to-node program sends the actual geometric origin exactly to
the selected rooted-fan target. -/
theorem canonicalRootToTargetProgram_origin_action
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne))
    (j : ClassicalHodgeBasisIndex V H p) :
    (canonicalRootToTargetProgram G p hne F j).cohomologyEval G
        (correspondenceGeometricOriginClass V H) =
      (rootedFanTarget (canonicalCutOrbitSeed G p hne) j).state.1 := by
  change
    (rootedFanProgram (canonicalCutOrbitSeed G p hne) F j).cohomologyEval G
      ((canonicalCutProgram (V := V) (H := H) p).cohomologyEval G
        (correspondenceGeometricOriginClass V H)) = _
  have hseed :
      (canonicalCutProgram (V := V) (H := H) p).cohomologyEval G
          (correspondenceGeometricOriginClass V H) =
        (canonicalCutOrbitSeed G p hne).hodge.1 := by
    rfl
  rw [hseed]
  exact rootedFanProgram_eval G (canonicalCutOrbitSeed G p hne) F j

/-- Normalize the root-to-target program by the one nonzero live source
coordinate.  Its output is the genuine target basis vector, not merely the
scaled fan endpoint. -/
noncomputable def canonicalRootToBasisProgram
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne))
    (j : ClassicalHodgeBasisIndex V H p) :
    GradedCorrespondenceProgram V H 0 p :=
  let S := canonicalCutOrbitSeed G p hne
  .smul (hodgeCoordinate S.sourceIndex S.hodge)⁻¹
    (canonicalRootToTargetProgram G p hne F j)

/-- **ONE ROOT-TO-BASIS PROGRAM.**
Each Hodge basis direction is exactly the output of one apex/spine/fan program
from the canonical geometric origin. -/
theorem canonicalRootToBasisProgram_origin_action
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne))
    (j : ClassicalHodgeBasisIndex V H p) :
    (canonicalRootToBasisProgram G p hne F j).cohomologyEval G
        (correspondenceGeometricOriginClass V H) =
      (classicalHodgeBasis V H p j).1 := by
  let S := canonicalCutOrbitSeed G p hne
  have hc : hodgeCoordinate S.sourceIndex S.hodge != 0 := by
    simpa [hodgeCoordinate] using S.sourceCoefficient_ne_zero
  rw [canonicalRootToBasisProgram, cohomologyEval_smul]
  rw [canonicalRootToTargetProgram_origin_action G p hne F j]
  simp [rootedFanTarget, hodgeMatrixUnit_apply, S, hc, smul_smul]

/-- Every basis sheet belongs to the orbit ITSELF (not merely its external
span), because its witness is the explicit root-to-basis program above. -/
theorem basis_mem_fullCorrespondenceOrbitModule_of_apexSpineFan
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne))
    (j : ClassicalHodgeBasisIndex V H p) :
    (classicalHodgeBasis V H p j).1 ∈
      fullCorrespondenceOrbitModule G p := by
  refine ⟨canonicalRootToBasisProgram G p hne F j, ?_⟩
  exact (canonicalRootToBasisProgram_origin_action G p hne F j).symm

/-- **GRAPH NORMAL FORM FOR AN ARBITRARY HODGE CLASS.**
The finite basis expansion lives in the already-closed full-program orbit, so
it is itself the output of ONE graded program.  Thus an arbitrary rational
Hodge class admits one executable causal history of the form

  origin apex -> canonical cut spine -> compiled horizontal fan synthesis.
-/
theorem exists_singleProgram_of_canonicalCut_rootedFan
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : H.cycleClass p (projectiveCutTower V p) != 0)
    (F : RootedStrictRelationFan (canonicalCutOrbitSeed G p hne))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ P : GradedCorrespondenceProgram V H 0 p,
      alpha = P.cohomologyEval G
        (correspondenceGeometricOriginClass V H) := by
  apply (mem_fullCorrespondenceOrbitSubspace_iff_singleProgram G p alpha).1
  rw [fullCorrespondenceOrbitSubspace_eq_module]
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  rw [show alphaH =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alphaH).support,
        ((classicalHodgeBasis V H p).repr alphaH j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr alphaH]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (fullCorrespondenceOrbitModule G p).smul_mem
    ((classicalHodgeBasis V H p).repr alphaH j)
    (basis_mem_fullCorrespondenceOrbitModule_of_apexSpineFan G p hne F j)

/-- **APEX/SPINE/FAN EXACT HODGE REDUCTION.**
With the vertical route fixed to the genuine canonical cut spine, concrete
nonvanishing of that spine and one locally materialized strict-relation ray per
target basis node suffice for the literal rational Hodge statement. -/
theorem exactHodge_of_canonicalCut_rootedFans
    (G : GeometricCycleClassSpine V H)
    (hne : ∀ p : Nat, H.cycleClass p (projectiveCutTower V p) != 0)
    (fan : ∀ p : Nat,
      RootedStrictRelationFan (canonicalCutOrbitSeed G p (hne p))) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply exactHodge_of_singleProgramGeneration G
  intro p alpha halpha
  exact exists_singleProgram_of_canonicalCut_rootedFan
    G p (hne p) (fan p) alpha halpha

#check strictRayProgram
#check strictRayProgram_eval
#check rootedFanProgram
#check rootedFanProgram_eval
#check canonicalRootToTargetProgram
#check canonicalRootToTargetProgram_origin_action
#check canonicalRootToBasisProgram
#check canonicalRootToBasisProgram_origin_action
#check basis_mem_fullCorrespondenceOrbitModule_of_apexSpineFan
#check exists_singleProgram_of_canonicalCut_rootedFan
#check exactHodge_of_canonicalCut_rootedFans

#print axioms strictRayProgram_eval
#print axioms canonicalRootToTargetProgram_origin_action
#print axioms canonicalRootToBasisProgram_origin_action
#print axioms exists_singleProgram_of_canonicalCut_rootedFan
#print axioms exactHodge_of_canonicalCut_rootedFans

end GSTClassicalHodgeApexSpineFanProgramNormalForm
