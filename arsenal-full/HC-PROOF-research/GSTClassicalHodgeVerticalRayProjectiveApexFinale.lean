import GSTClassicalHodgeExactVerticalCutRay
import GSTClassicalHodgeOmniverseProjectiveApexSpokes

/-!
# GST CLASSICAL HODGE — VERTICAL-RAY / OMNIVERSE-APEX FINALE

The live apex/spine/fan route still names a rooted strict-relation fan as its
horizontal input.  The upgraded omniverse makes that stronger than necessary.
A primitive branch is already the normalized localized two-slot `L^2` firing,
and `GSTClassicalHodgeOmniverseLefschetzRayCompiler` shows that one realized
correspondence expression from a synchronized algebraic apex to each target
basis sheet is enough.  The projective-apex-spoke package is a concrete
geometric specialization of that receipt.

This file fuses that horizontal compression with the exact vertical-cut-ray
certificate.  Dead Hodge weights require no geometry.  At a live weight:

* one exact surviving vertical ray certifies that the canonical projective-cut
  class is nonzero;
* that class becomes the canonical synchronized algebraic apex;
* one realized localized-`L^2` expression from the apex to each basis sheet
  constructs the corresponding basis cycle;
* finite Hodge-basis expansion gives the literal rational Hodge statement.

Thus no rooted fan, arbitrary omniverse compiler, all-edge materialization,
all-pairs projective generator family, or all-weight tower nonvanishing is an
input to this endpoint.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeVerticalRayProjectiveApexFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeLiveApexSpineFanFinale
open GSTClassicalHodgeExactVerticalCutRay
open GSTClassicalHodgeOmniverseLefschetzRayCompiler
open GSTClassicalHodgeOmniverseProjectiveApexSpokes
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **ONE LIVE WEIGHT: VERTICAL RAY + APEX-LOCALIZED L² EXPRESSIONS.**

An exact vertical ray makes the canonical cut node nonzero.  Source-specific
realized correspondence expressions implementing localized `L^2` on that one
apex then place the complete rational `(p,p)` Hodge sector in the true
cycle-class range. -/
theorem live_weight_range_of_verticalRay_and_apexLocalizedL2
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (hlive : HodgeWeightLive H p)
    (vertical : ExactVerticalCutRayCertificate V p)
    (localL2 : ApexLocalizedL2Realization
      (canonicalCutOrbitSeed G p
        (cycleClass_projectiveCutTower_ne_zero_of_certificate D vertical))) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_apexLocalizedL2
    (canonicalCutOrbitSeed G p
      (cycleClass_projectiveCutTower_ne_zero_of_certificate D vertical))
    localL2

/-- **LIVE-WEIGHT VERTICAL-RAY / OMNIVERSE-APEX EXACT HODGE FINALE.**

Only live Hodge weights are asked for geometry.  A live sheet needs one exact
root-to-weight vertical cut ray and source-specific realized localized-`L^2`
expressions from the resulting canonical apex to each basis direction.  Dead
sheets are zero and are discharged by the zero native cycle. -/
theorem exactHodge_of_verticalRays_and_apexLocalizedL2
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p)
    (localL2 : ∀ p : Nat, ∀ hlive : HodgeWeightLive H p,
      ApexLocalizedL2Realization
        (canonicalCutOrbitSeed G p
          (cycleClass_projectiveCutTower_ne_zero_of_certificate
            D (vertical p hlive)))) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro p alpha halpha
  by_cases hlive : HodgeWeightLive H p
  · have hrange : alpha ∈ LinearMap.range (H.cycleClass p) :=
      live_weight_range_of_verticalRay_and_apexLocalizedL2
        G D p hlive (vertical p hlive) (localL2 p hlive) halpha
    rcases hrange with ⟨Z, hZ⟩
    exact ⟨Z, hZ⟩
  · have hbot : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥ := by
      exact not_ne_iff.mp hlive
    have halpha0 : alpha = 0 := by
      rw [hbot] at halpha
      exact Submodule.mem_bot.mp halpha
    subst alpha
    exact ⟨0, LinearMap.map_zero _⟩

/-- **ONE LIVE WEIGHT: VERTICAL RAY + PROJECTIVE APEX SPOKES.**

A concrete actual-projective specialization of the omniverse-apex endpoint.
An exact vertical ray makes the canonical cut node nonzero.  Genuine
projective localized-`L^2` spokes from that node then place every target basis
sheet, and therefore the complete rational `(p,p)` Hodge sector, in the true
cycle-class range. -/
theorem live_weight_range_of_verticalRay_and_projectiveApexL2Spokes
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (hlive : HodgeWeightLive H p)
    (vertical : ExactVerticalCutRayCertificate V p)
    (spokes :
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveApexL2Spoke
          (canonicalCutOrbitSeed G p
            (cycleClass_projectiveCutTower_ne_zero_of_certificate D vertical)) j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_projectiveApexL2Spokes
    (canonicalCutOrbitSeed G p
      (cycleClass_projectiveCutTower_ne_zero_of_certificate D vertical))
    spokes

/-- **LIVE-WEIGHT VERTICAL-RAY / PROJECTIVE-APEX EXACT HODGE FINALE.**

Concrete projective-map form retained as a geometric specialization. -/
theorem exactHodge_of_verticalRays_and_projectiveApexL2Spokes
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (vertical : ∀ p : Nat, HodgeWeightLive H p →
      ExactVerticalCutRayCertificate V p)
    (spokes : ∀ p : Nat, ∀ hlive : HodgeWeightLive H p,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveApexL2Spoke
          (canonicalCutOrbitSeed G p
            (cycleClass_projectiveCutTower_ne_zero_of_certificate
              D (vertical p hlive))) j) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro p alpha halpha
  by_cases hlive : HodgeWeightLive H p
  · have hrange : alpha ∈ LinearMap.range (H.cycleClass p) :=
      live_weight_range_of_verticalRay_and_projectiveApexL2Spokes
        G D p hlive (vertical p hlive) (spokes p hlive) halpha
    rcases hrange with ⟨Z, hZ⟩
    exact ⟨Z, hZ⟩
  · have hbot : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥ := by
      exact not_ne_iff.mp hlive
    have halpha0 : alpha = 0 := by
      rw [hbot] at halpha
      exact Submodule.mem_bot.mp halpha
    subst alpha
    exact ⟨0, LinearMap.map_zero _⟩

#check live_weight_range_of_verticalRay_and_apexLocalizedL2
#check exactHodge_of_verticalRays_and_apexLocalizedL2
#check live_weight_range_of_verticalRay_and_projectiveApexL2Spokes
#check exactHodge_of_verticalRays_and_projectiveApexL2Spokes

#print axioms live_weight_range_of_verticalRay_and_apexLocalizedL2
#print axioms exactHodge_of_verticalRays_and_apexLocalizedL2
#print axioms live_weight_range_of_verticalRay_and_projectiveApexL2Spokes
#print axioms exactHodge_of_verticalRays_and_projectiveApexL2Spokes

end GSTClassicalHodgeVerticalRayProjectiveApexFinale
