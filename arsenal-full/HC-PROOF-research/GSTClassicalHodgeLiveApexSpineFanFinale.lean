import GSTClassicalHodgeApexSpineFanProgramNormalForm

/-!
# GST CLASSICAL HODGE — LIVE APEX / SPINE / FAN FINALE

The apex/spine/fan program normal form fixed the vertical route to the genuine
canonical principal-cut program and compiled every horizontal strict-relation
ray into one same-weight correspondence program.

Its first global finale asked the canonical cut tower to have nonzero cycle
class in EVERY natural weight.  That is stronger than the actual Hodge target
requires: a weight whose rational `(p,p)` Hodge subspace is zero has no live
node to generate at all.  In such a weight the exact Hodge statement is
trivial and the explicit zero-output graded program is already available.

This file therefore makes the ontological graph sparse in exactly the right
sense.  Only LIVE sheets require a vertical live node and outgoing fan rays.
Dead sheets are discharged by the zero program.

The remaining geometric burden is consequently:

* for every weight with nonzero rational Hodge sector, the canonical projective
  cut tower has nonzero genuine cycle class;
* for every such live weight, one locally materialized strict-relation ray from
  the canonical cut node reaches each target basis direction.

No nonvanishing assertion is demanded beyond the live Hodge range.
-/

set_option maxHeartbeats 160000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLiveApexSpineFanFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRootedStrictRelationFan
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedOrbitSingleProgramCollapse
open GSTClassicalHodgeCanonicalCutProgramSpine
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeApexSpineFanProgramNormalForm
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A Hodge weight is live exactly when its rational `(p,p)` subspace is not
bottom. -/
def HodgeWeightLive (H : HodgeBigradedBettiData V) (p : Nat) : Prop :=
  rationalHodgeSubspace (H.hodgeBigrading p) != ⊥

/-- **LIVE-WEIGHT SINGLE-PROGRAM GENERATION.**
Dead sheets are represented by the explicit zero-output program.  A live sheet
uses the canonical cut spine and its rooted strict-relation fan. -/
theorem singleProgramGeneration_of_live_apexSpineFans
    (G : GeometricCycleClassSpine V H)
    (tower_live : ∀ p : Nat, HodgeWeightLive H p ->
      H.cycleClass p (projectiveCutTower V p) != 0)
    (fan : ∀ p : Nat, ∀ hlive : HodgeWeightLive H p,
      RootedStrictRelationFan
        (canonicalCutOrbitSeed G p (tower_live p hlive))) :
    ∀ p : Nat,
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) ->
      ∃ P : GradedCorrespondenceProgram V H 0 p,
        alpha = P.cohomologyEval G
          (correspondenceGeometricOriginClass V H) := by
  intro p alpha halpha
  by_cases hlive : HodgeWeightLive H p
  · exact exists_singleProgram_of_canonicalCut_rootedFan
      G p (tower_live p hlive) (fan p hlive) alpha halpha
  · have hbot : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥ := by
      exact not_ne_iff.mp hlive
    have halpha0 : alpha = 0 := by
      rw [hbot] at halpha
      exact Submodule.mem_bot.mp halpha
    subst alpha
    refine ⟨zeroOutputProgram V H p, ?_⟩
    exact (zeroOutputProgram_eval G p).symm

/-- **LIVE GST GRAPH V2 EXACT HODGE FINALE.**
Only live sheets of the ontological fan need nonzero canonical spine nodes and
outgoing strict-relation rays.  This is sufficient for the literal rational
Hodge statement. -/
theorem exactHodge_of_live_apexSpineFans
    (G : GeometricCycleClassSpine V H)
    (tower_live : ∀ p : Nat, HodgeWeightLive H p ->
      H.cycleClass p (projectiveCutTower V p) != 0)
    (fan : ∀ p : Nat, ∀ hlive : HodgeWeightLive H p,
      RootedStrictRelationFan
        (canonicalCutOrbitSeed G p (tower_live p hlive))) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply exactHodge_of_singleProgramGeneration G
  exact singleProgramGeneration_of_live_apexSpineFans G tower_live fan

#check HodgeWeightLive
#check singleProgramGeneration_of_live_apexSpineFans
#check exactHodge_of_live_apexSpineFans

#print axioms singleProgramGeneration_of_live_apexSpineFans
#print axioms exactHodge_of_live_apexSpineFans

end GSTClassicalHodgeLiveApexSpineFanFinale
