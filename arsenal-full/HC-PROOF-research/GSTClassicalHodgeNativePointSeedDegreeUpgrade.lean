import GSTClassicalHodgeNativePointSeedSaturation
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeOmniversalGhostBranchClosure

/-!
# GST CLASSICAL HODGE — NATIVE POINT SEED DEGREE UPGRADE

The earlier `NativePointHodgeSeed` structure stored two facts about an actual
codimension point as separate fields: its cycle class is Hodge and its cycle
class is nonzero.  Once the genuine geometric cycle-class spine and projective
degree trace semantics are available, both facts are theorems.

Therefore an actual codimension-p point is by itself enough to manufacture the
full nonzero synchronized native/Hodge seed used by the limitless orbit and
ghost-closure machinery.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeNativePointSeedSaturation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalGhostBranchClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace NativePointHodgeSeed

/-- **DEGREE-CERTIFIED POINT SEED CONSTRUCTOR.**

For an actual codimension-p point, Hodge type follows from the genuine
cycle-class spine and nonvanishing follows from positive projective degree.
Thus the two semantic fields of `NativePointHodgeSeed` are derived rather than
supplied. -/
noncomputable def ofCodimensionPoint
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X p) :
    NativePointHodgeSeed V H p where
  point := x
  class_is_hodge := G.pointClass_is_hodge p x
  class_ne_zero := by
    intro hzero
    have htrace := D.trace_point_cycleClass p x
    rw [hzero, LinearMap.map_zero] at htrace
    exact (ne_of_gt (D.pointDegree_pos p x)) htrace.symm

/-- Every degree-certified point seed is immediately a synchronized native
Hodge orbit seed. -/
noncomputable def toNativeHodgeOrbitSeed
    (S : NativePointHodgeSeed V H p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := codimensionPointCycle V.X p S.point
  hodge := S.hodgeClass
  hodge_ne_zero := S.hodgeClass_ne_zero
  class_eq := rfl

end NativePointHodgeSeed

/-- **ONE ACTUAL CODIMENSION POINT -> NONZERO NATIVE HODGE SEED.** -/
noncomputable def nativeHodgeOrbitSeed_of_codimensionPoint
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) :=
  (NativePointHodgeSeed.ofCodimensionPoint G D x).toNativeHodgeOrbitSeed

/-- Ghost-weight native-seed survival is reduced to the literal geometric
existence of one codimension point in each ghost-selected weight.  Hodge type
and nonvanishing are no longer separate assumptions. -/
theorem ghostWeightNativeSeedSurvival_of_codimensionPoints
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ E :
      GSTClassicalHodgeOmniversalSeparatorGhostCrown.OmniversalSeparatorGhost G,
      Nonempty (CodimensionPoint V.X E.weight)) :
    GhostWeightNativeSeedSurvival G := by
  intro E
  let x := Classical.choice (hpoint E)
  exact ⟨nativeHodgeOrbitSeed_of_codimensionPoint G D x⟩

/-- Positive degree semantics really excludes the zero-cycle-class spine at
every inhabited codimension.  This check identifies precisely why the zero
spine counterinstance cannot be used against a theorem that also supplies D. -/
theorem no_degreeTrace_for_zeroCycleClass_at_point
    (H : HodgeBigradedBettiData V)
    (p : Nat) (x : CodimensionPoint V.X p) :
    IsEmpty (ProjectiveDegreeTraceSemantics V
      (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H)) := by
  refine ⟨?_⟩
  intro D
  have ht := D.trace_point_cycleClass p x
  have hz : D.pointDegree p x = 0 := by
    simpa only [GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData_cycleClass,
      LinearMap.zero_apply, map_zero] using ht.symm
  have hp := D.pointDegree_pos p x
  rw [hz] at hp
  exact (lt_irrefl 0) hp

#print axioms no_degreeTrace_for_zeroCycleClass_at_point

#check NativePointHodgeSeed.ofCodimensionPoint
#check NativePointHodgeSeed.toNativeHodgeOrbitSeed
#check nativeHodgeOrbitSeed_of_codimensionPoint
#check ghostWeightNativeSeedSurvival_of_codimensionPoints

#print axioms NativePointHodgeSeed.ofCodimensionPoint
#print axioms nativeHodgeOrbitSeed_of_codimensionPoint
#print axioms ghostWeightNativeSeedSurvival_of_codimensionPoints

end GSTClassicalHodgeNativePointSeedSaturation
