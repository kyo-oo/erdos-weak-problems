import GSTClassicalHodgeCanonicalCutProgramSpine
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — CANONICAL CUT / NORMALIZED SPINE EQUATION

The projective cut tower is the unnormalized geometric recursion

  Z_{p+1} = Cut_p(Z_p),

while `spineNativeTower` is the same recursion divided at every step by the
nonzero GST/Lefschetz coefficient `successorScalar p`.

Therefore the two towers differ by exactly the product of those coefficients.
This file proves that equation directly from the definitions.  No
`ProjectiveTowerHodgeIntertwining`, independently chosen seed family, conserved
charge, or native-mass package occurs.

Consequently the cycle class of the actual projective cut tower is the same
explicit nonzero scalar multiple of the canonical spine Hodge state.  Thus the
remaining vertical nonvanishing question is reduced to the single concrete
statement that the canonical spine state itself is nonzero; no arbitrary
source program remains anywhere in the handwritten Pi landing.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalCutSpineNormalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeLimitlessProjectiveLefschetzTower
open GSTClassicalHodgeLimitlessTowerOrbitCrown
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeCanonicalCutProgramSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Product of the true nonzero GST successor coefficients accumulated from
weight zero through weight `p`. -/
noncomputable def towerScale : Nat → ℚ
  | 0 => 1
  | p + 1 => towerScale p * successorScalar p

@[simp] theorem towerScale_zero : towerScale 0 = 1 := rfl

@[simp] theorem towerScale_succ (p : Nat) :
    towerScale (p + 1) = towerScale p * successorScalar p := rfl

/-- Every accumulated tower coefficient is nonzero. -/
theorem towerScale_ne_zero : ∀ p : Nat, towerScale p ≠ 0 := by
  intro p
  induction p with
  | zero => simp [towerScale]
  | succ p ih =>
      exact mul_ne_zero ih (successorScalar_ne_zero p)

/-- Undoing the normalization in `spineNativeTower` recovers one genuine
projective successor step exactly. -/
theorem successor_spineNativeTower
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    successorNativeOperator V p (spineNativeTower G p) =
      successorScalar p • spineNativeTower G (p + 1) := by
  rw [spineNativeTower_succ]
  rw [smul_smul]
  simp [successorScalar_ne_zero]

/-- **UNNORMALIZED PROJECTIVE TOWER = GST SCALE * NORMALIZED SPINE.** -/
theorem projectiveCutTower_eq_scale_spineNativeTower
    (G : GeometricCycleClassSpine V H) :
    ∀ p : Nat,
      projectiveCutTower V p = towerScale p • spineNativeTower G p := by
  intro p
  induction p with
  | zero =>
      simp [projectiveCutTower_zero, spineNativeTower_zero, towerScale]
  | succ p ih =>
      rw [projectiveCutTower_succ, ih, LinearMap.map_smul]
      rw [successor_spineNativeTower G p]
      simp only [towerScale_succ, smul_smul]
      rw [mul_comm (towerScale p) (successorScalar p)]

/-- Taking the genuine cycle class turns the preceding native equation into the
same exact scalar relation on the cohomological side. -/
theorem projectiveCutTower_cycleClass_eq_scale_spineHodgeSeed
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    H.cycleClass p (projectiveCutTower V p) =
      towerScale p • (spineHodgeSeed G p).1 := by
  rw [projectiveCutTower_eq_scale_spineNativeTower G p]
  rw [LinearMap.map_smul]
  rw [spineNativeTower_cycleClass G p]

/-- Since the accumulated GST coefficient is nonzero, the actual projective
cut-tower class vanishes exactly when the canonical normalized spine state
vanishes. -/
theorem projectiveCutTower_class_ne_zero_iff_spineHodgeSeed_ne_zero
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    H.cycleClass p (projectiveCutTower V p) ≠ 0 ↔
      spineHodgeSeed G p ≠ 0 := by
  rw [projectiveCutTower_cycleClass_eq_scale_spineHodgeSeed G p]
  constructor
  · intro h hseed
    apply h
    have hval : (spineHodgeSeed G p).1 = 0 := congrArg Subtype.val hseed
    rw [hval, smul_zero]
  · intro hseed hzero
    have hscale : towerScale p ≠ 0 := towerScale_ne_zero p
    have hval : towerScale p • (spineHodgeSeed G p).1 = 0 := hzero
    have hz : (spineHodgeSeed G p).1 = 0 := by
      exact (smul_eq_zero.mp hval).resolve_left hscale
    apply hseed
    apply Subtype.ext
    exact hz

/-- The canonical program's formerly free origin-nonvanishing condition is now
identical to nonvanishing of the canonical normalized spine state. -/
theorem canonicalCutProgram_origin_ne_zero_iff_spineHodgeSeed_ne_zero
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    (canonicalCutProgram (V := V) (H := H) p).cohomologyEval G
        (GSTClassicalHodgeHandwrittenPiCorrespondenceProgramLanding.correspondenceGeometricOriginClass V H) ≠ 0
      ↔ spineHodgeSeed G p ≠ 0 := by
  rw [GSTClassicalHodgeCanonicalCutProgramSpine.canonicalCutProgram_origin_ne_zero_iff G p]
  exact projectiveCutTower_class_ne_zero_iff_spineHodgeSeed_ne_zero G p

#check towerScale
#check towerScale_ne_zero
#check successor_spineNativeTower
#check projectiveCutTower_eq_scale_spineNativeTower
#check projectiveCutTower_cycleClass_eq_scale_spineHodgeSeed
#check projectiveCutTower_class_ne_zero_iff_spineHodgeSeed_ne_zero
#check canonicalCutProgram_origin_ne_zero_iff_spineHodgeSeed_ne_zero

#print axioms projectiveCutTower_eq_scale_spineNativeTower
#print axioms projectiveCutTower_cycleClass_eq_scale_spineHodgeSeed
#print axioms projectiveCutTower_class_ne_zero_iff_spineHodgeSeed_ne_zero

end GSTClassicalHodgeCanonicalCutSpineNormalization
