import GSTHodgeGSTUnifiedPrimitiveWaveRank
import GSTGraphV2NativeCurvatureBirth

/-!
# GST wave + native curvature: one-step residual elimination

Not another spectral model. This module composes the EXISTING original
seven-axis wave/N-hole geometric frame with the EXISTING true original-X
native commutator cycle. An independently geometric detector of the new
curvature-born cycle provides a second explicit native correction.

After the correction the remaining rational Hodge residual is killed by:
  (1) every old N-hole geometric wave coordinate;
  (2) the new curvature detector.

The correction is a concrete linear combination of actual native cycles.
It NEVER supplies a Hodge-to-Chow inverse for an arbitrary alpha.
The theorem holds at arbitrary finite wave-channel rank and any p.
-/

noncomputable section

namespace GSTHodgeWaveCurvatureResidualStep

open GSTHodgeWaveAllNGeometricLanding
open GSTHodgeGSTUnifiedPrimitiveWaveRank
open GSTHodgeWaveAllNHoleReadout
open GSTGraphV2NativeCurvatureBirth
open GSTClassicalHodgeCycleOperatorNaturality
open GSTNCohomology

variable {A : Type*} [AddCommGroup A] [Module ℚ A]
variable {B : Type*} [AddCommGroup B] [Module ℚ B]
variable {s : NShape} {cl : A →ₗ[ℚ] B}

/-- Subtract the existing N-hole wave coordinates from a newly born
algebraic curvature cycle. This isolates exactly the new geometric
direction without reusing previously generated information. -/
def correctedCurvatureSource
    (F : GeometricWaveFrame s cl) (z : A) : A :=
  z - F.nativeCombination (F.bettiCoordinates (cl z))

/-- The canonical class of the corrected curvature source is precisely
the old wave-invisible residual of that actual algebraic cycle. -/
theorem correctedCurvatureSource_class
    (F : GeometricWaveFrame s cl) (z : A) :
    cl (correctedCurvatureSource F z) =
      waveResidual F (cl z) := by
  unfold correctedCurvatureSource waveResidual
  rw [map_sub, F.cl_nativeCombination]

/-- A corrected curvature source carries zero OLD wave information. -/
theorem correctedCurvatureSource_oldCoordinates_zero
    (F : GeometricWaveFrame s cl) (z : A) :
    F.bettiCoordinates (cl (correctedCurvatureSource F z)) = 0 := by
  rw [correctedCurvatureSource_class]
  exact waveResidual_coordinates_zero F (cl z)

/-- Any geometrically fixed readout killing the old frame also kills
its whole rational span, with no Hodge surjectivity assumed. -/
theorem read_waveFrame_zero
    (F : GeometricWaveFrame s cl)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (v : Fin s.holes → ℚ) :
    read (F.bettiCombination v) = 0 := by
  change read (∑ i : Fin s.holes, v i • cl (F.atom i)) = 0
  rw [map_sum]
  simp [map_smul, hOld]

/-- Removing the old source span does not alter the INDEPENDENT new
curvature detector. -/
theorem read_correctedCurvatureSource
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0) :
    read (cl (correctedCurvatureSource F z)) = read (cl z) := by
  rw [correctedCurvatureSource_class]
  unfold waveResidual
  rw [map_sub, read_waveFrame_zero F read hOld]
  simp

/-- Actual native wave + curvature cycle, with a coefficient fixed by
the geometric readout of the target residual. -/
def waveCurvatureCycle
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (alpha : B) : A :=
  F.nativeWaveSource (holeReadoutLift s (F.bettiCoordinates alpha)) +
    (read (waveResidual F alpha) / read (cl z)) •
      correctedCurvatureSource F z

theorem waveCurvatureCycle_class
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (alpha : B) :
    cl (waveCurvatureCycle F z read alpha) =
      F.bettiCombination (F.bettiCoordinates alpha) +
        (read (waveResidual F alpha) / read (cl z)) •
          waveResidual F (cl z) := by
  unfold waveCurvatureCycle
  change
    cl (F.nativeCombination
      (holeReadout s (holeReadoutLift s (F.bettiCoordinates alpha))) +
       (read (waveResidual F alpha) / read (cl z)) •
         correctedCurvatureSource F z) = _
  rw [holeReadout_lift, map_add, map_smul,
    F.cl_nativeCombination, correctedCurvatureSource_class]

/-- The new wave/curvature representative leaves every previously
eliminated wave-coordinate eliminated. -/
theorem waveCurvatureCycle_coordinates
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (alpha : B) :
    F.bettiCoordinates (cl (waveCurvatureCycle F z read alpha)) =
      F.bettiCoordinates alpha := by
  rw [waveCurvatureCycle_class, map_add, map_smul,
    bettiCoordinates_bettiCombination,
    waveResidual_coordinates_zero]
  simp

/-- The new independently geometric detector is matched exactly. -/
theorem waveCurvatureCycle_read
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0)
    (alpha : B) :
    read (cl (waveCurvatureCycle F z read alpha)) = read alpha := by
  rw [waveCurvatureCycle_class, map_add, map_smul,
    read_waveFrame_zero F read hOld]
  have hz : read (waveResidual F (cl z)) = read (cl z) := by
    unfold waveResidual
    rw [map_sub, read_waveFrame_zero F read hOld]
    simp
  have ha : read (waveResidual F alpha) = read alpha := by
    unfold waveResidual
    rw [map_sub, read_waveFrame_zero F read hOld]
    simp
  rw [hz, zero_add, smul_eq_mul, div_mul_cancel₀ _ hNew, ha]

/-- Exact residual after the two completed GEOMETRIC corrections. -/
def waveCurvatureResidual
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (alpha : B) : B :=
  alpha - cl (waveCurvatureCycle F z read alpha)

/-- Combined proof: full original GST N-hole wave + one genuinely
curvature-born source gives an explicit algebraic representative plus
a residual invisible to EVERY old wave channel and the new curvature
readout. The residual is not assumed to be zero. -/
theorem waveCurvatureResidual_decomposition
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0)
    (alpha : B) :
    alpha = cl (waveCurvatureCycle F z read alpha) +
        waveCurvatureResidual F z read alpha ∧
    F.bettiCoordinates (waveCurvatureResidual F z read alpha) = 0 ∧
    read (waveCurvatureResidual F z read alpha) = 0 := by
  constructor
  · unfold waveCurvatureResidual
    abel
  constructor
  · unfold waveCurvatureResidual
    rw [map_sub, waveCurvatureCycle_coordinates]
    exact sub_self _
  · unfold waveCurvatureResidual
    rw [map_sub, waveCurvatureCycle_read F z read hOld hNew]
    exact sub_self _

/-- A completed dual frame plus curvature detector suffices to
produce an actual cycle for the prescribed target, *provided*
the common wave+curvature detector kernel is known zero on B. -/
theorem waveCurvature_exact_of_joint_detection
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0)
    (hSeparate : ∀ r : B,
      F.bettiCoordinates r = 0 → read r = 0 → r = 0)
    (alpha : B) :
    cl (waveCurvatureCycle F z read alpha) = alpha := by
  obtain ⟨hdecomp, hcoord, hread⟩ :=
    waveCurvatureResidual_decomposition F z read hOld hNew alpha
  have hz := hSeparate _ hcoord hread
  rw [hz, add_zero] at hdecomp
  exact hdecomp.symm


/-- The old N-hole GST wave coordinates and one independently
geometric curvature detector as a SINGLE rational linear map. -/
def augmentedWaveCurvatureReadout
    (F : GeometricWaveFrame s cl)
    (read : B →ₗ[ℚ] ℚ) :
    B →ₗ[ℚ] ((Fin s.holes → ℚ) × ℚ) where
  toFun x := (F.bettiCoordinates x, read x)
  map_add' := by
    intro x y
    apply Prod.ext <;> simp [map_add, Pi.add_apply]
  map_smul' := by
    intro c x
    apply Prod.ext <;> simp [map_smul, Pi.smul_apply]

/-- The augmented detector is SURJECTIVE once an actual extra
geometric curvature source has nonzero readout outside the old wave
frame. This requires no assumed Hodge basis. -/
theorem augmentedWaveCurvatureReadout_surjective
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) :
    Function.Surjective (augmentedWaveCurvatureReadout F read) := by
  intro y
  refine ⟨F.bettiCombination y.1 +
      (y.2 / read (cl z)) • waveResidual F (cl z), ?_⟩
  apply Prod.ext
  · change F.bettiCoordinates
      (F.bettiCombination y.1 +
        (y.2 / read (cl z)) • waveResidual F (cl z)) = y.1
    rw [map_add, map_smul, bettiCoordinates_bettiCombination,
      waveResidual_coordinates_zero]
    simp
  · change read
      (F.bettiCombination y.1 +
        (y.2 / read (cl z)) • waveResidual F (cl z)) = y.2
    rw [map_add, map_smul, read_waveFrame_zero F read hOld]
    have hz : read (waveResidual F (cl z)) = read (cl z) := by
      unfold waveResidual
      rw [map_sub, read_waveFrame_zero F read hOld]
      simp
    rw [hz, zero_add, smul_eq_mul]
    field_simp [hNew]

/-- FINITE-RANK CLOSURE: when the actual rational Hodge fiber has
exactly n+1 dimensions, an n-channel genuinely geometric GST wave
frame plus one independent genuine curvature source construct a
native cycle for EVERY class in that fiber. No universal target
surjectivity is a field of the input data. -/
theorem waveCurvature_exact_of_rank_succ
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0)
    [FiniteDimensional ℚ B]
    (hRank : Module.finrank ℚ B = s.holes + 1)
    (alpha : B) :
    cl (waveCurvatureCycle F z read alpha) = alpha := by
  have hdim :
      Module.finrank ℚ B =
      Module.finrank ℚ ((Fin s.holes → ℚ) × ℚ) := by
    simpa only [Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_self] using hRank
  have hinj :
      Function.Injective (augmentedWaveCurvatureReadout F read) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim).2 (augmentedWaveCurvatureReadout_surjective
        F z read hOld hNew)
  apply waveCurvature_exact_of_joint_detection
    F z read hOld hNew
  intro r hcoords hread
  apply hinj
  apply Prod.ext
  · simpa [augmentedWaveCurvatureReadout] using hcoords
  · simpa [augmentedWaveCurvatureReadout] using hread

end GSTHodgeWaveCurvatureResidualStep
