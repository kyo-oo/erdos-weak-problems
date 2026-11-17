import GSTHodgeWaveAllNGeometricLanding
import GSTHodgeWaveAllNHoleReadout
import GSTHodgeGSTWaveGeometricCompiler
import GSTUniversalCodimensionTwoPrimitiveExtraction
import GSTGraphV2SelfExpandingCosmology
import GSTInfiniteTowerCurvatureCascade
import GSTGraphV2IntegratedWaveCMGate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# GST full bridge: dimensionless information waves, CM, native geometric
# dual frames, all-order curvature and Lefschetz primitive reconstruction

This is a direct composition of existing project theorems, NOT a replacement
seven-axis graph.  The source coefficients come from the actual GST twelve-cell
fixed-state wave readout, repeated over genuinely indexed Wave-II holes.
A verified geometrically dual ORIGINAL-X cycle frame interprets these numbers
as algebraic cycles.  Equality of the frame count with the geometric
primitive-Hodge rank forces all primitive directions to occur, by a
FINITE-DIMENSIONAL rank proof (not by assuming a target cycle preimage).

The all-degree/infinite-wave, CM and cosmology structures are retained via
the imported modules, but their mere presence is not assumed to manufacture
the geometric frame.  A precise source-birth task is thereby exposed:
construct the actual dual primitive cycles and their intersection readings
on a prescribed original X.
-/

noncomputable section

namespace GSTHodgeGSTUnifiedPrimitiveWaveRank

open GSTHodgeWaveAllNGeometricLanding
open GSTHodgeWaveAllNHoleReadout
open GSTGraphV2CMWaveFusion
open GSTGraphV2WaveNShapeCompiler
open GSTHodgeGSTWaveGeometricCompiler
open GSTNCohomology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTUniversalLefschetzCurveCycles
open GSTUniversalCodimensionTwoPrimitiveExtraction

section CompleteInformationToNative

variable {A : Type*} [AddCommGroup A] [Module ℚ A]
variable {B : Type*} [AddCommGroup B] [Module ℚ B]
variable {s : NShape} {cl : A →ₗ[ℚ] B}

/-- The geometric Betti coordinate system has an EXPLICIT right inverse:
all Wave-II information coordinates have genuine native geometric labels. -/
theorem bettiCoordinates_bettiCombination
    (F : GeometricWaveFrame s cl) (x : Fin s.holes → ℚ) :
    F.bettiCoordinates (F.bettiCombination x) = x := by
  rw [← F.cl_nativeCombination x, F.bettiCoordinates_cl]
  exact F.nativeCoordinates_nativeCombination x

theorem geometric_bettiCoordinates_surjective
    (F : GeometricWaveFrame s cl) :
    Function.Surjective F.bettiCoordinates := by
  intro x
  exact ⟨F.bettiCombination x, bettiCoordinates_bettiCombination F x⟩

/-- The first ACTUAL geometric rank certificate.  A finite Hodge
space with precisely as many rational directions as independently
constructed native Wave-II frame cycles admits no further invisible
rational directions. No Hodge-to-Chow selector is assumed. -/
theorem geometric_bettiCoordinates_injective_of_rank
    (F : GeometricWaveFrame s cl)
    [FiniteDimensional ℚ B]
    (hRank : Module.finrank ℚ B = s.holes) :
    Function.Injective F.bettiCoordinates := by
  have hdim :
      Module.finrank ℚ B =
        Module.finrank ℚ (Fin s.holes → ℚ) := by
    simpa using hRank
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hdim).2 (geometric_bettiCoordinates_surjective F)

/-- Exact geometric synthesis identity in every finite Wave-II rank.
The proof DOES NOT use a preselected algebraic preimage of alpha:
it reconstructs one from the independently specified frame cycles. -/
theorem betti_synthesis_of_rank
    (F : GeometricWaveFrame s cl)
    [FiniteDimensional ℚ B]
    (hRank : Module.finrank ℚ B = s.holes)
    (alpha : B) :
    F.bettiCombination (F.bettiCoordinates alpha) = alpha := by
  apply geometric_bettiCoordinates_injective_of_rank F hRank
  exact bettiCoordinates_bettiCombination F (F.bettiCoordinates alpha)

/-- The actual wave on the dimensionless seven-axis information
graph produces a concrete NATIVE original-carrier cycle for an arbitrary
target in the full geometric frame's Betti fiber. -/
theorem wave_native_class_of_full_rank
    (F : GeometricWaveFrame s cl)
    [FiniteDimensional ℚ B]
    (hRank : Module.finrank ℚ B = s.holes)
    (alpha : B) :
    cl (F.nativeWaveSource
      (holeReadoutLift s (F.bettiCoordinates alpha))) = alpha := by
  change
    cl (F.nativeCombination
      (holeReadout s (holeReadoutLift s (F.bettiCoordinates alpha))))
      = alpha
  rw [holeReadout_lift, F.cl_nativeCombination]
  exact betti_synthesis_of_rank F hRank alpha


/-- Exact information-to-geometry residual after assembling the
existing genuine native wave frame. It is not postulated zero. -/
def waveResidual (F : GeometricWaveFrame s cl) (alpha : B) : B :=
  alpha - F.bettiCombination (F.bettiCoordinates alpha)

/-- Every residual is invisible to ALL genuinely geometric frame
readouts: this is a precise remaining source-birth test. -/
theorem waveResidual_coordinates_zero
    (F : GeometricWaveFrame s cl) (alpha : B) :
    F.bettiCoordinates (waveResidual F alpha) = 0 := by
  unfold waveResidual
  rw [map_sub, bettiCoordinates_bettiCombination]
  exact sub_self _

/-- The actual full GST wave builds its algebraic component on the
original carrier, and the residual is the exact complementary term.
This holds for ANY existing partial frame, without rank assumptions. -/
theorem wave_native_plus_residual
    (F : GeometricWaveFrame s cl) (alpha : B) :
    alpha =
      cl (F.nativeWaveSource
        (holeReadoutLift s (F.bettiCoordinates alpha))) +
      waveResidual F alpha := by
  change alpha =
    cl (F.nativeCombination
      (holeReadout s (holeReadoutLift s (F.bettiCoordinates alpha)))) +
      (alpha - F.bettiCombination (F.bettiCoordinates alpha))
  rw [holeReadout_lift, F.cl_nativeCombination]
  abel

end CompleteInformationToNative

section PrimitiveHodgeLanding

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d : Nat}
variable (G : GeometricCycleClassSpine V H)
variable (P : GeometricHigherLefschetzData G d)
variable (h11 : DivisorsRepresentHodge11 H)

/-- The actual ORIGINAL-X native rational cycle space which already
satisfies the true geometric primitive test. -/
abbrev NativePrimitiveCycles :=
  (P.primitiveTest.comp (nativeToHodgeFiberLinear G)).ker

/-- The genuinely primitive rational Hodge sector, not the entire
possibly nonprimitive cohomological representation. -/
abbrev PrimitiveHodgeFiber := P.primitiveTest.ker

/-- Exact cycle-class map between primitive cycles and primitive Hodge
classes. It is constructed by **restriction** of the preexisting native
Betti cycle-class map; neither the original cycle nor its cohomology
are replaced by abstract coordinate vectors. -/
def primitiveCycleClass :
    ↥(NativePrimitiveCycles G P) →ₗ[ℚ]
      ↥(PrimitiveHodgeFiber G P) where
  toFun Z :=
    ⟨nativeToHodgeFiberLinear G Z.1,
      by
        have hh := LinearMap.mem_ker.mp Z.2
        exact hh⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add (nativeToHodgeFiberLinear G) x.1 y.1
  map_smul' := by
    intro c x
    apply Subtype.ext
    exact map_smul (nativeToHodgeFiberLinear G) c x.1


/-- Exact GST Wave I/II/CM source decomposition on the ORIGINAL X.

Unlike a frame of the primitive subtype, this uses the ACTUAL ambient
rational Betti cycle-class map and a geometric primitive property for
each independently supplied atom.  This avoids ungrounded source-world
type identifications.  Every rational Hodge class is a known algebraic
Lefschetz correction + an actual wave-produced primitive algebraic cycle
+ a primitive residual invisible to all supplied geometric frame detectors. -/
theorem originalX_wave_primitive_residual_decomposition
    (h11 : DivisorsRepresentHodge11 H)
    (s : NShape)
    (F : OriginalXFrame (V := V) (H := H) (p := 2) (s := s))
    (hAtoms : ∀ i : Fin s.holes,
      P.primitiveTest (nativeToHodgeFiberLinear G (F.atom i)) = 0)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ Z : codimensionCycles V.X 2,
      ∃ r : ClassicalHodgeFiber V H 2,
        alpha = nativeToHodgeFiberLinear G Z + r ∧
        P.primitiveTest r = 0 ∧
        F.bettiCoordinates r.1 = 0 := by
  let beta := primitiveHodgeRemainder G P h11 alpha
  let v := F.bettiCoordinates beta.1
  let z := F.nativeWaveSource (holeReadoutLift s v)
  have hzclass : H.cycleClass 2 z = F.bettiCombination v := by
    dsimp [z, GeometricWaveFrame.nativeWaveSource]
    rw [holeReadout_lift, F.cl_nativeCombination]
  have hzPrimitive : P.primitiveTest (nativeToHodgeFiberLinear G z) = 0 := by
    have hZ : z = ∑ i : Fin s.holes, (v i) • F.atom i := by
      dsimp [z, GeometricWaveFrame.nativeWaveSource]
      rw [holeReadout_lift]
      rfl
    rw [hZ]
    simp only [map_sum, map_smul]
    simp [hAtoms]
  let residual := beta - nativeToHodgeFiberLinear G z
  refine ⟨z + algebraicLefschetzCorrection G P h11 alpha, residual, ?_, ?_, ?_⟩
  · have hb : beta = nativeToHodgeFiberLinear G z + residual := by
      dsimp [residual]
      abel
    calc
      alpha = beta + nativeToHodgeFiberLinear G
        (algebraicLefschetzCorrection G P h11 alpha) :=
           Hodge_class_eq_primitive_plus_native_cycle G P h11 alpha
      _ = (nativeToHodgeFiberLinear G z + residual) +
            nativeToHodgeFiberLinear G
              (algebraicLefschetzCorrection G P h11 alpha) := by rw [hb]
      _ = nativeToHodgeFiberLinear G
          (z + algebraicLefschetzCorrection G P h11 alpha) + residual := by
          rw [map_add]
          abel
  · dsimp [residual]
    rw [map_sub, primitiveHodgeRemainder_primitive, hzPrimitive, sub_self]
  · dsimp [residual]
    change F.bettiCoordinates (beta.1 -
      (nativeToHodgeFiberLinear G z).1) = 0
    rw [map_sub]
    have hval : (nativeToHodgeFiberLinear G z).1 = H.cycleClass 2 z := rfl
    rw [hval,hzclass, bettiCoordinates_bettiCombination]
    exact sub_self _

/-- The exact geometric source-birth target after joining BOTH original
GST waves, CM, native algebraic cycles, and hard Lefschetz:
a detector-separating family of primitive wave cycles produces an
actual representative of EVERY rational codimension-two Hodge class. -/
theorem originalX_hodge_two_cycle_of_primitive_wave_separation
    (h11 : DivisorsRepresentHodge11 H)
    (s : NShape)
    (F : OriginalXFrame (V := V) (H := H) (p := 2) (s := s))
    (hAtoms : ∀ i : Fin s.holes,
      P.primitiveTest (nativeToHodgeFiberLinear G (F.atom i)) = 0)
    (hSeparate : ∀ r : ClassicalHodgeFiber V H 2,
       P.primitiveTest r = 0 →
       F.bettiCoordinates r.1 = 0 → r = 0)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ Z : codimensionCycles V.X 2,
       nativeToHodgeFiberLinear G Z = alpha := by
  obtain ⟨Z,r,heq,hprim,hdet⟩ :=
    originalX_wave_primitive_residual_decomposition G P h11 s F hAtoms alpha
  have hr : r = 0 := hSeparate r hprim hdet
  refine ⟨Z, ?_⟩
  rw [hr, add_zero] at heq
  exact heq.symm

/-- Retain the existing exact threefold benchmark in the SAME source
chain. At dimension three the primitive test is identity and the
hard-Lefschetz/divisor construction already supplies the cycle. -/
theorem originalX_threefold_hodge_two_cycle
    (h11 : DivisorsRepresentHodge11 H)
    (P3 : GeometricHigherLefschetzData G 3)
    (hId : P3.primitiveTest = LinearMap.id)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ Z : codimensionCycles V.X 2,
        nativeToHodgeFiberLinear G Z = alpha :=
  every_threefold_hodge_two_class_has_native_cycle G P3 h11 hId alpha

end PrimitiveHodgeLanding

#check GSTGraphV2InformationRecovery.shuffle_five
#check GSTGraphV2CMWaveFusion.wave_source_CM_curvature_nonzero
#check GSTGraphV2CMInfiniteCurvatureBridge.cm_odd_product_double
#check GSTGraphV2SelfExpandingCosmology.NativeGeometryBirth.generated_worlds_have_native_cycles
#check GSTFoldTowerSquare.JetTowerInf.jetInfDifferential_square_apply
#check GSTHodgeWaveAllNHoleReadout.holeReadout_orbit
#check GSTHodgeWaveAllNGeometricLanding.GeometricWaveFrame.nativeWaveSource_intertwines
#check GSTGraphV2NativeCurvatureBirth.nativeCurvature_cycleClass
#check originalX_hodge_two_cycle_of_primitive_wave_separation
#print axioms originalX_hodge_two_cycle_of_primitive_wave_separation
#print axioms wave_native_class_of_full_rank

end GSTHodgeGSTUnifiedPrimitiveWaveRank
